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
from semantics import admissible_box, required_range, side_constraints
from transpile import Untranspilable, build_arity, pyname, transpile

HERE = pathlib.Path(__file__).resolve().parent
INF = math.inf


def _viol(v, lo, hi):
    """Signed violation: positive means outside [lo, hi]."""
    return max(lo - v, v - hi)


def theorem_guards(c, defs):
    """Per-theorem hypothesis predicates for the theorems that BOUND `c`.

    Two corrections over conjoining everything into one feasibility region,
    both of which produced wrong verdicts here:

    1.  Hypotheses must be grouped BY THEOREM and never conjoined across
        theorems.  The union is not a domain.  `coalFst` carries
        `100 * Ne < t` from one asymptotic lemma; conjoining it excludes
        essentially every sensible F_ST evaluation and the definition then
        passes vacuously.
    2.  Only theorems that actually CLAIM a bound may excuse a range escape.
        A precondition like `p < 1/2`, borrowed from a monotonicity lemma,
        says nothing about where the quantity is a valid probability, and
        using it as a guard silently shrank the searched region.

    Returns [{thm, hyps, pred}], one entry per range-claiming theorem whose
    hypotheses are wholly expressible in the arithmetic fragment.
    """
    d = c.d
    ar, rn = build_arity(defs, d["module"])
    by_thm = {}
    for co in side_constraints(d):
        if not co["guards_range"]:
            continue
        by_thm.setdefault(co["thm"], []).append(co["hyp"])
    out, dropped = [], []
    for thm, hyps in by_thm.items():
        preds, ok = [], True
        for h in hyps:
            try:
                src = transpile(h, d["params"], ar, d["name"], rn)
                ns = {"_b": FLOAT}
                args = ", ".join(pyname(p) for p, _ in d["params"])
                exec(compile(f"def _p({args}):\n return {src}", "<hyp>", "exec"), ns)
                preds.append(ns["_p"])
            except Exception as e:
                dropped.append(dict(thm=thm, hyp=h, reason=str(e)))
                ok = False
        if ok and preds:
            out.append(dict(thm=thm, hyps=hyps, preds=preds))
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
    best, x = maximize(f, box, names, budget=budget)
    out = dict(range=[lo, hi], range_why=why,
               range_source="name-or-docstring-implied; NOT a theorem-proved "
                            "bound, so a violation is a lead, not a proof of "
                            "a defect",
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
        satisfied = [g["thm"] for g in guards if _satisfies(g, x)]
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
        verdict = "escape-unguarded" if blind else "escape"
        if guards:
            verdict = "escape-outside-theorem"
        out.update(verdict=verdict,
                   witness={n: v for n, v in zip(names, x)},
                   value=val, overshoot=best,
                   blind_coordinates=blind,
                   escapes_only_where_violated=[
                       g["thm"] for g in guards if not _satisfies(g, x)],
                   side="above" if val > hi else "below")
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
