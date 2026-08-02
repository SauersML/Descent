"""FAMILY 1 -- range escapes.

For every definition whose NAME forces a range (a probability in [0,1], a
correlation in [-1,1], a variance nonnegative, ...), search its admissible box
for a point where the transcribed Lean body leaves that range.

Three verdicts, and the difference between them is the whole value of the file:

  ESCAPE       a concrete input point is exhibited.  This is a positive
               finding and it is exact -- the point is printed and can be
               pasted into Lean.
  PROVED       interval branch-and-bound covered the entire box with the
               result inside the range.  A proof, not a sample.
  INCONCLUSIVE the search found nothing and the interval proof did not close.
               NOT a pass.  Sampling misses thin escapes.

Run:  python check_ranges.py  ->  results_ranges.json
"""
from __future__ import annotations

import json
import math
import pathlib
import sys

import backends
import compile_defs as C
from backends import FLOAT, INTERVAL, Iv
from search import maximize, prove_contained
import re

from semantics import (RANGE_THM, _rename, admissible_box, required_range,
                       side_constraints)
from transpile import Untranspilable, build_arity, pyname, transpile

HERE = pathlib.Path(__file__).resolve().parent
INF = math.inf


def _viol(v, lo, hi):
    """Signed violation: positive means outside [lo, hi]."""
    return max(lo - v, v - hi)


# Authoritative list of which theorem proves which bound, from the `extract`
# agent's table.  Optional: without it we fall back to matching theorem NAMES,
# which is what let twelve definitions with proved bounds be reported as
# escapes.
def _proved_bounds():
    try:
        import sys
        sys.path.insert(0, str(HERE.parents[1] / "validation" / "extract"))
        import api
    except Exception:
        return {}
    out = {}
    try:
        for n, rec in api.definition_table().items():
            c = rec.get("constraints") or {}
            lo_t = c.get("range_lo_thm")
            hi_t = c.get("range_hi_thm")
            out[(rec["file"].split("/")[-1][:-5], rec["short"])] = dict(
                lo_thms={lo_t[0].split(".")[-1]} if lo_t else set(),
                hi_thms={hi_t[0].split(".")[-1]} if hi_t else set(),
                lo=c.get("range_lo"), hi=c.get("range_hi"))
    except Exception:
        return {}
    return out


PROVED = _proved_bounds()


def theorem_guards(c, defs):
    """Per-theorem hypothesis predicates for the theorems that BOUND `c`.

    Three corrections over the first version, each of which was producing
    wrong verdicts:

    1.  Hypotheses are grouped BY THEOREM and never conjoined across
        theorems.  The union of hypotheses is not a domain: `coalFst` carries
        `100 * Ne < t` from one asymptotic lemma, and conjoining it excludes
        every sensible F_ST evaluation so the definition passes vacuously.
    2.  A theorem's guard uses ALL of its hypotheses.  Splitting them --
        numeric bounds to the box, relational ones to the guard -- left the
        guard incomplete, and a witness that violated only the numeric half
        looked like an escape.  `neiFst` was reported broken at H_S > H_T even
        though `nei_fst_in_unit` excludes exactly that.
    3.  Which theorems bound the definition comes from the `extract` agent's
        table where available, not from guessing at theorem names.  Names like
        `fstFromDriftFactor_mem_unit` and `ldPanelRetentionFraction_mem` do not
        match any reasonable regex.

    Returns [{thm, hyps, preds}], one per bounding theorem whose hypotheses
    are wholly expressible in the arithmetic fragment.
    """
    d = c.d
    ar, rn = build_arity(defs, d["module"])
    proved = PROVED.get((d["module"], d["name"]), {})
    lo_thms = proved.get("lo_thms", set())
    hi_thms = proved.get("hi_thms", set())
    named = lo_thms | hi_thms
    out, dropped = [], []
    for t in d.get("theorem_hyps", []):
        thm = t["thm"]
        if thm not in named and not RANGE_THM.search(thm):
            continue
        argmap = t.get("argmap") or {}
        preds, ok = [], True
        for h in t["hyps"]:
            h = _rename(h.strip().rstrip(","), argmap)
            if not re.search(r"[<>≤≥]", h):
                continue  # a typing binder, not a constraint
            try:
                src = transpile(h, d["params"], ar, d["name"], rn)
                ns = {"_b": FLOAT}
                args = ", ".join(pyname(p) for p, _ in d["params"])
                exec(compile(f"def _p({args}):\n return {src}", "<hyp>", "exec"), ns)
                preds.append(ns["_p"])
            except Exception as e:
                dropped.append(dict(thm=thm, hyp=h, reason=str(e)))
                ok = False
        # A theorem whose hypotheses we cannot fully model cannot excuse an
        # escape, but it also cannot be ignored: an escape near it is reported
        # with `unmodelled_hypotheses` so the reader can check by hand.
        if ok and preds:
            # WHICH bound the theorem proves decides which escapes it can
            # excuse.  `steppingStoneFst_nonneg` proves only `0 <= f`; a
            # witness of 10000 satisfies its hypotheses AND its conclusion, so
            # it says nothing about the escape above 1.  Treating any bounding
            # theorem as excusing any escape reclassified five real findings
            # as errors of mine.
            bounds = set()
            if thm in lo_thms or re.search(r"nonneg|_pos\b|in_unit|mem_unit|"
                                           r"_mem\b|_range|bounded", thm, re.I):
                bounds.add("below")
            if thm in hi_thms or re.search(r"le_one|_lt_one|in_unit|mem_unit|"
                                           r"_mem\b|_range|bounded", thm, re.I):
                bounds.add("above")
            out.append(dict(thm=thm, hyps=t["hyps"], preds=preds,
                            bounds=sorted(bounds)))
    return out, dropped


def _satisfies(guard, x):
    for p in guard["preds"]:
        try:
            if p(*x) is not True:
                return False
        except Exception:
            return False
    return True


def check_one(c, defs, budget=8000, bnb=1500):
    d = c.d
    rng = required_range(d)
    if rng is None:
        return dict(verdict="no-range", reason="name and docstring commit the "
                    "definition to no particular range")
    lo, hi, why = rng
    box, unguarded = admissible_box(d)
    names = c.names
    if not names:
        val = c(FLOAT)
        return dict(verdict="escape" if _viol(val, lo, hi) > 0 else "proved",
                    range=[lo, hi], range_why=why, value=val, witness={})

    def f(*xs):
        return _viol(c(FLOAT, *xs), lo, hi)

    # The search runs over the WHOLE admissible box.  Theorem hypotheses are
    # applied afterwards, to classify the witness, never beforehand to shrink
    # the region -- shrinking is what makes a definition pass vacuously.
    guards, dropped = theorem_guards(c, defs)
    pb = PROVED.get((d["module"], d["name"]), {})
    best, x = maximize(f, box, names, budget=budget)
    out = dict(range=[lo, hi], range_why=why,
               range_source="name-or-docstring-implied; NOT a theorem-proved "
                            "bound, so a violation is a lead, not a proof of "
                            "a defect",
               proved_bound=[pb.get("lo"), pb.get("hi")] if pb else None,
               bounding_theorems=[g["thm"] for g in guards],
               bounding_theorem_hyps={g["thm"]: g["hyps"] for g in guards},
               unmodelled_hypotheses=dropped,
               box={n: [box[n]["lo"], box[n]["hi"], box[n]["source"]] for n in names},
               unguarded=unguarded,
               box_provenance={n: box[n]["why"] for n in names})
    if best is not None and best > 1e-12 and x is not None:
        val = c(FLOAT, *x)
        # An escape that needs a coordinate whose meaning we could not read is
        # a WEAKER claim than one reachable inside a box every coordinate of
        # which is pinned by a theorem or by an unambiguous parameter name.
        # The two are reported as different verdicts and never pooled.
        blind = [n for n in names if box[n]["source"] == "none"]
        side = "above" if val > hi else "below"
        satisfied = [g["thm"] for g in guards
                     if side in g["bounds"] and _satisfies(g, x)]
        if satisfied:
            # The witness sits inside the preconditions of a theorem that
            # proves the bound.  Lean has no `sorry`s, so the theorem is true
            # and the disagreement is MINE -- a mis-transcribed body, a
            # mis-parsed hypothesis, or a hypothesis I could not model.  This
            # is never reported as a corpus defect.
            out.update(verdict="contradicts-theorem",
                       witness={n: v for n, v in zip(names, x)},
                       value=val, contradicted=satisfied,
                       note="escape found inside a theorem's own hypotheses; "
                            "this indicates an error in THIS checker, not in "
                            "the corpus, and needs manual inspection")
            return out
        relevant = [g for g in guards if side in g["bounds"]]
        # A theorem may PROVE the bound on this side while its hypotheses are
        # beyond the arithmetic fragment, so no guard could be built for it.
        # Silence from a guard we failed to construct is not evidence that no
        # guard exists: if `extract` names a theorem proving this side, the
        # claim is downgraded regardless.
        proved_this_side = bool(
            (pb.get("hi_thms") if side == "above" else pb.get("lo_thms")) or
            (pb.get("hi") is not None if side == "above"
             else pb.get("lo") is not None))
        verdict = "escape-unguarded" if blind else "escape"
        if relevant or proved_this_side:
            verdict = "escape-outside-theorem"
        if proved_this_side and not relevant:
            out["guard_not_modelled"] = (
                "a theorem proves this bound but its hypotheses are outside "
                "the arithmetic fragment, so the exclusion could not be "
                "checked directly; graded conservatively")
        out.update(verdict=verdict,
                   witness={n: v for n, v in zip(names, x)},
                   value=val, overshoot=best,
                   blind_coordinates=blind,
                   escapes_only_where_violated=[
                       g["thm"] for g in guards
                       if side in g["bounds"] and not _satisfies(g, x)],
                   side=side)
        return out

    def fiv(*xs):
        return c(INTERVAL, *xs)

    status, worst, used = prove_contained(fiv, box, names, lo, hi, max_boxes=bnb)
    out.update(verdict="proved" if status == "proved" else "inconclusive",
               bnb_boxes=used,
               searched=budget)
    if status != "proved":
        out["inconclusive_reason"] = (
            "no escape found by sampling+pattern search, and interval "
            f"branch-and-bound did not close the box within {bnb} subdivisions"
        )
    return out


def severity(r):
    """Rank escapes.  Ordering criteria, most important first.

    1. an escape reachable with EVERY coordinate unguarded outranks one that
       needs a coordinate the author explicitly bounded;
    2. sign errors (a probability going negative, a variance going negative)
       outrank magnitude errors;
    3. larger relative overshoot outranks smaller.
    """
    if r.get("verdict") not in ("escape", "escape-unguarded",
                               "escape-outside-theorem"):
        return -1.0
    lo, hi = r["range"]
    span = (hi - lo) if math.isfinite(hi - lo) else 1.0
    over = r.get("overshoot", 0.0)
    rel = min(over / span, 1e6) if span > 0 else over
    s = math.log10(1 + max(rel, 0.0)) * 10
    if r.get("side") == "below" and lo == 0.0:
        s += 30  # a nonnegative quantity going negative is a sign error
    if r.get("side") == "above" and hi == 1.0:
        s += 20  # a probability exceeding one
    if r["verdict"] == "escape-outside-theorem":
        # the range does hold where the author proved it; the finding is that
        # the definition itself does not carry the condition
        s -= 15
    if r["verdict"] == "escape-unguarded":
        # discount: the witness uses a coordinate whose admissible values we
        # could not determine, so the escape may not be physically reachable.
        s -= 25
    return s


def main(argv):
    defs = C.load_defs()
    cs, why_not, _ = C.compile_all(defs)
    results = {}
    for k in sorted(cs):
        try:
            r = check_one(cs[k], defs)
        except Exception as e:  # never let one definition abort the sweep
            r = dict(verdict="error", reason=f"{type(e).__name__}: {e}")
        r.update(name=cs[k].d["name"], module=cs[k].d["module"],
                 line=cs[k].d["line"], family="range", py=cs[k].py)
        r["severity"] = severity(r)
        results[k] = r
    for k, w in why_not.items():
        results.setdefault(k, dict(verdict="not-transpiled", reason=w,
                                   family="range", severity=-1.0))
    out = HERE / "results_ranges.json"
    out.write_text(json.dumps(results, indent=1, default=str))

    tally = {}
    for r in results.values():
        tally[r["verdict"]] = tally.get(r["verdict"], 0) + 1
    print(f"{len(results)} definitions ->", out)
    for v, n in sorted(tally.items(), key=lambda kv: -kv[1]):
        print(f"  {n:5d}  {v}")
    esc = sorted((r for r in results.values()
                  if r["verdict"] in ("escape", "escape-unguarded",
                                      "escape-outside-theorem")),
                 key=lambda r: -r["severity"])
    print(f"\nTop escapes ({len(esc)} total):")
    for r in esc[:25]:
        w = ", ".join(f"{k}={v:.6g}" for k, v in r["witness"].items())
        tag = {"escape": "!", "escape-outside-theorem": "~"}.get(
            r["verdict"], "?")
        print(f"  {tag}[{r['severity']:5.1f}] {r['module']}.{r['name']}:{r['line']}"
              f"  -> {r['value']:.6g} outside [{r['range'][0]}, {r['range'][1]}]"
              f"   at {w}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
