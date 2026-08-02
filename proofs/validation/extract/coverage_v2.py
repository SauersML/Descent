"""Coverage accounting with a falsifiability requirement.

The rule, and the whole point of this script:

    A definition counts as COVERED only if a check exists that CAN FAIL.

Operationally, for every definition we (a) run a check on the real body and
(b) run the same check on a family of *nearby wrong bodies* (mutants) obtained
by perturbing the parsed Lean source.  The check earns coverage only if it
passes on the real body and fails on at least one mutant that is numerically
distinguishable from the real one.  A check that survives every mutant covers
nothing and is reported as VACUOUS, not as coverage.

WHAT THIS NUMBER CANNOT SEE.  Two independent blind spots, both of which make
internal coverage overstate itself.  They belong next to the number, so it never
travels without them.

  1. MODEL ERRORS.  Mutation testing perturbs a body and asks whether a check
     notices.  A body that is exactly what its author intended, and answers a
     different question from the one its name poses, survives every mutant by
     construction: the mutants are all wrong in the coordinate the definition is
     right in.  `hetRecurrence` is the specimen -- algebraically correct
     everywhere, quotes 0.9048/0.6065/0.1353 as VALIDATED, those numbers ARE
     correct for a closed population with no mutation, and it is cited about a
     population at mutation-drift equilibrium where the true retention is 1.0.
     100% here would not have caught it.  See regime.py, the second metric.

  2. UNGUARDED REGIONS.  A range check grades against the bounds the corpus
     proves.  Where no theorem reaches, there is no bound to violate.
     `neutralAFBenchmarkRatio` returns 2.4 against a true ratio of 1.0 at a
     point where four of its five theorems hold and the fifth's hypotheses do
     not reach -- every proof true, the region unguarded, and this accounting
     scores it COVERED on the strength of the bounds it does satisfy.  Coverage
     is therefore an upper bound on how much of the input space is actually
     checked, not a measure of it.

  3. SEED DEPENDENCE, which is not a blind spot of the criterion but of the
     RUN.  Every RNG here is constructed fresh at its point of use, never
     shared across definitions and never derived from a name or from iteration
     position, so processing order cannot leak into the draws.  That makes the
     run REPRODUCIBLE.  It does NOT make a verdict STABLE: always drawing the
     same 40 points is no evidence that a verdict survives drawing 40
     different ones.  Use `--seed` and diff the covered sets; a definition
     whose status moves was never covered.  (See the README's opening section
     -- "deterministic, therefore stable" is one of the four specimens of a
     claim that fits the evidence while answering a different question.)

Check kinds, by class:

  NUMERIC     range invariant over the admissible box, where the range is mined
              from theorems about the definition or from its declared quantity
              kind.  Killed mutant = a wrong body that leaves the range.
  STRUCTURAL  witness/non-witness: an admissible input making the predicate true
              and one making it false.  A predicate with no non-witness (or no
              witness) is vacuous and earns nothing.
  WRAPPER     covered exactly when its target is covered.
  NOT-EXTRACTABLE  never covered here; listed with the reason.

Usage:
    python3 validation/extract/coverage_v2.py [--json out.json] [--verbose]
"""
from __future__ import annotations

import argparse
import collections
import json
import math
import pathlib
import random
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import admissible                                   # noqa: E402
from translate import Untranslatable, pyname, translate_def   # noqa: E402

PROOFS = HERE.parent.parent
N_POINTS = 40
_ALL_STRUCTS = {}

# Below this many DISTINGUISHABLE mutants, the killed/tried ratio is not a
# measurement.  One of one is not a perfect score; it is a body the operators
# could barely perturb.
MIN_DISTINGUISHABLE_MUTANTS = 3

# Every RNG in this file is constructed FRESH at its point of use from SEED,
# never shared across definitions and never derived from a name or from
# iteration position.  That makes the run reproducible and, more importantly,
# makes a definition's verdict independent of the order definitions are
# processed in -- a shared stream would leak processing order into the draws.
#
# Reproducibility is NOT stability.  Always drawing the same 40 points is not
# evidence that the verdict survives drawing 40 different ones.  `--seed`
# exists so that can be tested: re-run with a different seed and diff the
# covered set.  Any definition whose status moves was never really covered.
SEED = 11


# ------------------------------------------------------------------ mutants

def mutants(body: str):
    """Nearby wrong bodies.  Each is a single-token perturbation of the real one."""
    out = []

    def add(tag, new):
        if new != body:
            out.append((tag, new))

    for a, b in (("+", "-"), ("-", "+"), ("*", "/"), ("/", "*")):
        idx = body.find(f" {a} ")
        if idx >= 0:
            add(f"first '{a}'->'{b}'", body[:idx] + f" {b} " + body[idx + 3:])
        idx = body.rfind(f" {a} ")
        if idx >= 0:
            add(f"last '{a}'->'{b}'", body[:idx] + f" {b} " + body[idx + 3:])
    add("negate body", f"-({body.strip()})")
    add("drop '1 -' complement", re.sub(r"\b1 - ", "1 + ", body, count=1))
    add("square -> linear", re.sub(r"\^\s*2\b", "^ 1", body, count=1))
    add("linear -> square", re.sub(r"\^\s*1\b", "^ 2", body, count=1))
    for m in re.finditer(r"(?<![\w.])(\d+(?:\.\d+)?)(?![\w.])", body):
        try:
            v = float(m.group(1))
        except ValueError:
            continue
        add(f"literal {m.group(1)}->{v + 1:g}",
            body[:m.start()] + f"{v + 1:g}" + body[m.end():])
        break
    return out[:12]


_BASE_NS = None


def base_ns():
    """The generated module's namespace, so a definition that calls another
    definition resolves the callee to its own extracted form."""
    global _BASE_NS
    if _BASE_NS is None:
        import lean_defs
        _BASE_NS = vars(lean_defs)
    return _BASE_NS


def compile_variant(d, body, fname, struct_args):
    dd = dict(d)
    dd["body"] = body
    src, argnames = translate_def(dd, struct_args, fname=fname)
    ns = dict(base_ns())
    exec(compile(src, "<variant>", "exec"), ns)
    return ns[fname], argnames


# ------------------------------------------------------------------- checks

def make_points(entry, defs_by_name, structs, rng, theorem=None):
    """Admissible points, including structure inhabitants for structure args."""
    d = defs_by_name[entry_name(entry)]
    box = admissible.box_for(d)
    structval = {}
    for a in d["args"]:
        if a["implicit"]:
            continue
        head = a["type"].split()[0].split(".")[-1] if a["type"].split() else ""
        if head in structs:
            for n in a["names"]:
                structval[pyname(n)] = structs[head]
    preds, texts, dropped = admissible.hypothesis_predicates(d, theorem)
    pts, draws = [], 0
    cand = admissible.corners(box, limit=16)
    while len(pts) < N_POINTS and draws < 4000:
        if cand:
            base = cand.pop()
        else:
            base = admissible.sample(box, rng)
            draws += 1
        pt = {pyname(k): v for k, v in base.items()}
        if preds and not admissible.satisfies(preds, pt):
            continue
        pts.append((pt, structval))
    return pts, texts, dropped


def entry_name(entry):
    return entry["_name"]


def call(fn, argnames, pt, structval, rng, vecspec=None):
    return fn(*admissible.build_args(argnames, pt, structval, vecspec, rng,
                                     _ALL_STRUCTS))


def range_check(fn, argnames, pts, lo, hi, rng, tol=1e-9, vecspec=None):
    """Return (passes, first_violation) for the invariant lo <= f <= hi."""
    for pt, sv in pts:
        try:
            v = call(fn, argnames, pt, sv, rng, vecspec)
        except Exception:                                       # noqa: BLE001
            continue
        if not isinstance(v, (int, float)) or isinstance(v, bool):
            continue
        if not math.isfinite(v):
            return False, (pt, v, "non-finite")
        if lo is not None and v < lo - tol:
            return False, (pt, v, f"below {lo}", "lo")
        if hi is not None and v > hi + tol:
            return False, (pt, v, f"above {hi}", "hi")
    return True, None


def values(fn, argnames, pts, rng, vecspec=None):
    out = []
    for pt, sv in pts:
        try:
            out.append(call(fn, argnames, pt, sv, rng, vecspec))
        except Exception:                                       # noqa: BLE001
            out.append(None)
    return out


def distinguishable(a, b):
    for x, y in zip(a, b):
        if x is None or y is None:
            continue
        if isinstance(x, bool) or isinstance(y, bool):
            if x != y:
                return True
            continue
        if isinstance(x, (int, float)) and isinstance(y, (int, float)):
            if not math.isclose(x, y, rel_tol=1e-9, abs_tol=1e-12):
                return True
    return False


# -------------------------------------------------------------------- main

def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--seed", type=int, default=SEED,
                    help="master seed for admissible-point draws. Re-run with a "
                         "different value and diff the covered set: a verdict "
                         "that moves was never coverage.")
    a = ap.parse_args(argv)

    global SEED
    SEED = a.seed
    classes = json.loads((HERE / "classes.json").read_text())
    blob = json.loads((HERE / "defs.json").read_text())
    defs_by_name = {d["name"]: d for d in blob["definitions"]}
    structs = {s["short"]: s for s in blob["structures"]}
    global _ALL_STRUCTS
    _ALL_STRUCTS = structs
    for k, v in classes.items():
        v["_name"] = k

    sys.path.insert(0, str(HERE))

    results = {}
    names = list(classes)
    if a.limit:
        names = names[:a.limit]

    for name in names:
        entry = classes[name]
        d = defs_by_name[name]
        cls = entry["class"]
        rec = {"class": cls, "file": entry["file"], "line": entry["line"],
               "status": "UNCOVERED", "check": None, "killed": [],
               # Declared, not inferred.  Everything this script produces is
               # INTERNAL CONSISTENCY: a range mined from the corpus's own
               # theorems or its own docstrings, demonstrated falsifiable by
               # mutation.  No record here is contact with anything outside the
               # development, and a consumer must not count it as such.
               "evidence_class": "internal-consistency",
               "evidence_detail": "range-invariant + mutation-rejection",
               "reason": entry["note"]}
        results[name] = rec

        if cls == "NOT-EXTRACTABLE":
            rec["reason"] = entry["note"] or "not extractable"
            continue

        struct_args = [n for arg in d["args"] for n in arg["names"]
                       if arg["type"].split()
                       and arg["type"].split()[0].split(".")[-1] in structs]
        fname = entry["python"] or pyname(d["short"])
        try:
            fn, argnames = compile_variant(d, d["body"], fname, struct_args)
        except Exception as e:                                  # noqa: BLE001
            rec["reason"] = f"could not compile body: {e!r}"[:120]
            continue

        # Run under the preconditions of the theorem that proves the bound we
        # are about to check -- not under the union over all theorems, which is
        # not a domain and would discard admissible points.
        bounding = None
        for key in ("range_lo_thm", "range_hi_thm"):
            if d["constraints"].get(key):
                bounding = d["constraints"][key][0]
                break
        pts, hyps, dropped = make_points(entry, defs_by_name, structs,
                                         random.Random(SEED), bounding)
        if not pts:
            rec["reason"] = ("mined hypotheses admit no sampled point; "
                             f"constraints: {hyps[:4]}")
            continue
        vecspec = entry.get("vector_args")
        base_vals = values(fn, argnames, pts, random.Random(SEED), vecspec)
        if all(v is None for v in base_vals):
            rec["reason"] = "no admissible point evaluates"
            continue

        # ---- choose the check
        if cls in ("NUMERIC", "WRAPPER"):
            lo, hi, kind, src_lo, src_hi = admissible.declared_range(d)
            if lo is not None and hi is not None and lo > hi:
                # Two theorems bound the definition in contradictory directions,
                # which can only mean at least one of them is CONDITIONAL on a
                # hypothesis we did not enforce.  Mining cannot tell which, so
                # this definition needs a hand-written check, not a guess.
                rec["reason"] = (f"mined bounds contradict (lo={lo} > hi={hi}); "
                                 "at least one theorem bound is conditional")
                continue
            if lo is None and hi is None:
                rec["reason"] = ("no invariant available: neither the theorems "
                                 "mentioning it nor its docstring state a range")
                continue
            rec["check"] = {"kind": "range", "lo": lo, "hi": hi,
                            "quantity": kind, "source_lo": src_lo,
                            "source_hi": src_hi,
                            "hypotheses": hyps,
                            "hypotheses_not_enforced": dropped,
                            "thm_lo": d["constraints"].get("range_lo_thm"),
                            "thm_hi": d["constraints"].get("range_hi_thm"),
                            "n_points": len(pts),
                            "box": {k: list(v) for k, v in
                                    admissible.box_for(d).items()}}
            # SIDE-AWARE.  Each end of the range has its own provenance AND its
            # own preconditions: `steppingStoneFst_nonneg` proves `0 ≤ f` and
            # says nothing whatever about an escape above 1.  Grading an upper
            # escape against a theorem that only proved a lower bound -- or
            # enforcing that theorem's hypotheses while checking the other end --
            # mis-grades in both directions.  So each side is checked separately,
            # under the hypotheses of the theorem that proved THAT side.
            violation = None
            for side, bound, src in (("lo", lo, src_lo), ("hi", hi, src_hi)):
                if bound is None:
                    continue
                thm = (d["constraints"].get(f"range_{side}_thm") or [None, 0])
                side_pts, side_hyps, side_dropped = make_points(
                    entry, defs_by_name, structs, random.Random(SEED), thm[0])
                if not side_pts:
                    continue
                ok, viol = range_check(
                    fn, argnames, side_pts,
                    bound if side == "lo" else None,
                    bound if side == "hi" else None,
                    random.Random(SEED), vecspec=vecspec)
                if ok:
                    continue
                # A range proved by a Lean theorem cannot be violated by a
                # correct translation: that is a real finding.  A range only
                # *suggested* by the docstring or the name is a conjecture, and
                # a violation is a lead for a human, never a verdict.
                if src != "theorem":
                    status = "RANGE-MISMATCH"
                elif side_dropped or len(side_hyps) < thm[1]:
                    # Some stated precondition of THAT theorem could not be
                    # enforced, so the point may be inadmissible.  Not a verdict.
                    status = "DEFECT-CANDIDATE"
                else:
                    status = "DEFECT"
                violation = (status, viol, side, thm[0], side_hyps, side_dropped)
                if status == "DEFECT":
                    break                       # strongest finding wins
            if violation is not None:
                status, viol, side, thm_name, side_hyps, side_dropped = violation
                rec["status"] = status
                rec["check"]["violated_side"] = side
                rec["check"]["violated_side_theorem"] = thm_name
                rec["check"]["hypotheses"] = side_hyps
                rec["check"]["hypotheses_not_enforced"] = side_dropped
                rec["violation"] = {"point": {k: round(v, 6) for k, v in viol[0].items()},
                                    "value": viol[1], "why": viol[2]}
                continue

        else:                                    # STRUCTURAL
            truthy = [v for v in base_vals if isinstance(v, bool)]
            if not truthy:
                rec["reason"] = "predicate did not evaluate to a Bool/Prop witness"
                continue
            has_w, has_nw = any(truthy), not all(truthy)
            rec["check"] = {"kind": "witness/non-witness",
                            "witness": has_w, "non_witness": has_nw}
            if not (has_w and has_nw):
                rec["status"] = "VACUOUS"
                rec["reason"] = ("predicate is constant over the admissible box "
                                 f"({'always true' if has_w else 'always false'})")
                continue
            rec["status"] = "COVERED"
            rec["killed"] = [{"mutation": "witness/non-witness",
                              "mutant_body": None,
                              "witness": "predicate is true somewhere in the "
                                         "admissible box and false elsewhere",
                              "mutant_value": None,
                              "violates": "constancy"}]
            rec["mutants_tried"] = 2
            rec["mutants_killed"] = 1
            rec["falsifiability"] = 0.5
            continue

        # ---- falsifiability: does the check kill a nearby wrong body?
        #
        # The evidence published here is meant to be RE-DERIVABLE by another
        # tier, not taken on trust.  For each rejected mutant we record the
        # mutated Lean body verbatim, the input at which the check failed, and
        # the value the mutant produced there.  A reader can paste the body into
        # the definition, evaluate at the witness point, and see the escape.
        # A tag alone ("first '-'->'+'") asserts a rejection; this demonstrates
        # one.
        killed, tried, survivors = [], 0, []
        for tag, mbody in mutants(d["body"]):
            try:
                mfn, man = compile_variant(d, mbody, fname + "_mut", struct_args)
            except (Untranslatable, Exception):                 # noqa: BLE001
                continue
            mvals = values(mfn, man, pts, random.Random(SEED), vecspec)
            if not distinguishable(base_vals, mvals):
                continue                                        # equivalent mutant
            tried += 1
            ok, viol = range_check(mfn, man, pts, lo, hi, random.Random(SEED),
                                   vecspec=vecspec)
            if ok:
                survivors.append(tag)
                continue
            killed.append({
                "mutation": tag,
                "mutant_body": " ".join(mbody.split()),
                "witness": {k: round(v, 6) for k, v in viol[0].items()
                            if isinstance(v, (int, float))},
                "mutant_value": viol[1],
                "violates": viol[2],
            })
        rec["mutants_tried"] = tried
        rec["mutants_killed"] = len(killed)
        rec["killed"] = killed
        rec["survived"] = survivors
        # A check that rejects one of many nearby wrong bodies is weaker than
        # one that rejects most.  Publish the ratio rather than a bare boolean,
        # so a consumer can set its own bar.
        #
        # But the ratio is UNDEFINED when too few distinguishable mutants were
        # produced to divide by.  A body the mutation operators barely apply to
        # yields killed 1 of 1 and a ratio of 1.0, which displays as the
        # strongest evidence in the set while being the weakest -- the operators
        # never got a chance to be wrong.  Reporting None forces a consumer to
        # handle the case rather than read it as a perfect score.
        if tried >= MIN_DISTINGUISHABLE_MUTANTS:
            rec["falsifiability"] = round(len(killed) / tried, 3)
        else:
            rec["falsifiability"] = None
            rec["falsifiability_undefined_reason"] = (
                f"only {tried} distinguishable mutant(s) produced; "
                f"a ratio needs at least {MIN_DISTINGUISHABLE_MUTANTS}. The "
                f"body may be too simple for the mutation operators to perturb "
                f"meaningfully -- this needs a hand-written check, not a ratio.")
        if killed:
            rec["status"] = "COVERED"
        else:
            rec["status"] = "VACUOUS"
            rec["reason"] = (f"check survives all {tried} distinguishable mutants: "
                             "it cannot detect a wrong body")

    report(results, classes, a)
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(results, indent=1))
    return results


def legacy_mentions():
    """Definition names appearing in the pre-existing validation scripts."""
    names = set()
    for p in (PROOFS / "validation").rglob("*.py"):
        if p.is_relative_to(HERE):
            continue
        txt = p.read_text(errors="ignore")
        for m in re.finditer(r"lean_([A-Za-z_][\w']*)", txt):
            names.add(m.group(1))
        for m in re.finditer(r"[\"']([a-z][A-Za-z0-9_']{4,})[\"']", txt):
            names.add(m.group(1))
    return names


def report(results, classes, args):
    total = len(results)
    by_class = collections.defaultdict(lambda: collections.Counter())
    for name, r in results.items():
        by_class[r["class"]][r["status"]] += 1

    print("=" * 74)
    print("FALSIFIABLE COVERAGE OVER proofs/Calibrator/")
    print("=" * 74)
    print("A definition is COVERED only if a check passes on the real body and "
          "fails\non at least one nearby wrong body.  Everything else is not "
          "coverage.\n")
    print(f"{'class':<18}{'defs':>6}{'COVERED':>9}{'VACUOUS':>9}"
          f"{'UNCOVERED':>11}{'DEFECT':>8}{'MISMATCH':>10}{'%cov':>7}")
    grand = collections.Counter()
    for cls in ("NUMERIC", "STRUCTURAL", "WRAPPER", "NOT-EXTRACTABLE"):  # noqa
        c = by_class[cls]
        n = sum(c.values())
        grand.update(c)
        if not n:
            continue
        print(f"{cls:<18}{n:6d}{c['COVERED']:9d}{c['VACUOUS']:9d}"
              f"{c['UNCOVERED']:11d}{c['DEFECT'] + c['DEFECT-CANDIDATE']:8d}{c['RANGE-MISMATCH']:10d}"
              f"{100 * c['COVERED'] / n:6.1f}%")
    print(f"{'ALL':<18}{total:6d}{grand['COVERED']:9d}{grand['VACUOUS']:9d}"
          f"{grand['UNCOVERED']:11d}{grand['DEFECT'] + grand['DEFECT-CANDIDATE']:8d}{grand['RANGE-MISMATCH']:10d}"
          f"{100 * grand['COVERED'] / total:6.1f}%")

    # The split belongs at the TOP, not in the detail.  "Covered" has meant two
    # different things: graded against a bound a theorem proves, and graded
    # against a bound inferred from the definition's own name.  Both are
    # falsifiable; only the first tests conformance to something the corpus
    # asserts rather than to a reading of a name.
    cv = [r for r in results.values() if r["status"] == "COVERED"]
    thm = sum(1 for r in cv
              if "theorem" in ((r.get("check") or {}).get("source_lo"),
                               (r.get("check") or {}).get("source_hi")))
    print(f"\n  of the {len(cv)} COVERED: {thm} are graded against a "
          f"THEOREM-PROVED bound,\n  {len(cv) - thm} against a bound inferred "
          f"from the name or docstring (a conjecture).")

    ext = sum(1 for r in results.values() if r["class"] != "NOT-EXTRACTABLE")
    print(f"\nextractable definitions: {ext} / {total} "
          f"({100 * ext / total:.1f}%);  covered among extractable: "
          f"{100 * grand['COVERED'] / max(ext, 1):.1f}%")

    mism = [(n, r) for n, r in results.items() if r["status"] == "RANGE-MISMATCH"]
    print(f"\nRANGE-MISMATCH -- body leaves the range its docstring/name implies, "
          f"but no theorem proves that range ({len(mism)}).")
    print("These are leads for a human: either the name is misleading or the body is.")
    for n, r in mism[:12]:
        v = r.get("violation", {})
        print(f"  {n} ({r['file']}:{r['line']}) -> {v.get('value'):.4g} {v.get('why')}")

    cand = [(n, r) for n, r in results.items() if r["status"] == "DEFECT-CANDIDATE"]
    print(f"\nDEFECT-CANDIDATE -- theorem-proved range violated, but at least one "
          f"stated\nprecondition could not be enforced, so the point may be "
          f"inadmissible ({len(cand)}).")
    for n, r in cand[:12]:
        v = r.get("violation", {})
        print(f"  {n} ({r['file']}:{r['line']}) -> {v.get('value'):.4g} {v.get('why')}")
        print(f"      unenforced: {r['check']['hypotheses_not_enforced'][:3]}")

    defects = [(n, r) for n, r in results.items() if r["status"] == "DEFECT"]
    if defects:
        print(f"\nDEFECTS -- the body leaves a range a Lean THEOREM proves for it, "
              f"under hypotheses mined from that theorem ({len(defects)}).")
        print("Each is either a real inconsistency or a translation bug; both matter.")
        for n, r in defects[:20]:
            v = r.get("violation", {})
            print(f"  {n}  ({r['file']}:{r['line']})")
            print(f"      value {v.get('value')!r} {v.get('why')} at {v.get('point')}")
            print(f"      enforced hypotheses: {r['check']['hypotheses'][:4]}")
            print(f"      range proved by: "
                  f"{r['check'].get('thm_lo') or r['check'].get('thm_hi')}")

    vac = [(n, r) for n, r in results.items() if r["status"] == "VACUOUS"]
    print(f"\nVACUOUS checks (present but cannot fail): {len(vac)}")
    for n, r in vac[:10]:
        print(f"  {n}: {r['reason'][:90]}")

    unc = collections.Counter(r["reason"].split(":")[0].split("(")[0].strip()
                              for r in results.values()
                              if r["status"] == "UNCOVERED")
    print("\nwhy the rest are uncovered:")
    for k, v in unc.most_common(12):
        print(f"  {v:5d}  {k[:88]}")

    legacy = legacy_mentions()
    claimed = [n for n in results
               if n.split(".")[-1] in legacy or n in legacy]
    unverified = [n for n in claimed if results[n]["status"] != "COVERED"]
    print(f"\nlegacy scripts name {len(claimed)} definitions; of those, "
          f"{len(claimed) - len(unverified)} also have a falsifiable check here.")
    print(f"{len(unverified)} are named by a legacy script but have no "
          "demonstrated-falsifiable check:")
    for n in unverified[:10]:
        print(f"  {n}")

    # ---- falsifiability evidence, published per definition
    cov = {n: r for n, r in results.items() if r["status"] == "COVERED"}
    strong = [n for n, r in cov.items()
              if (r.get("falsifiability") or 0) >= 0.5]
    undef = [n for n, r in cov.items() if r.get("falsifiability") is None]
    single = [n for n, r in cov.items() if r.get("mutants_killed", 0) == 1]
    onethm = [n for n, r in cov.items()
              if (r.get("check") or {}).get("source_lo") == "theorem"
              or (r.get("check") or {}).get("source_hi") == "theorem"]
    print("\nfalsifiability of the covered set (evidence is in coverage.json,")
    print("per definition: the mutated Lean body, the witness input, the value):")
    print(f"  covered                                  : {len(cov)}")
    print(f"  rejecting >=50% of distinguishable mutants: {len(strong)}")
    print(f"  rejecting exactly ONE mutant             : {len(single)}"
          f"   <- weakest evidence, audit these first")
    print(f"  ratio UNDEFINED (<{MIN_DISTINGUISHABLE_MUTANTS} distinguishable "
          f"mutants): {len(undef)}"
          f"   <- not a score; the body resists perturbation")
    print(f"  checked against a THEOREM-proved bound   : {len(onethm)}")
    print(f"  checked only against a name/docstring bound: {len(cov) - len(onethm)}"
          f"   <- the bound itself is a conjecture")

    if args.verbose:
        print("\nCOVERED, with the wrong bodies each check rejects:")
        for n, r in results.items():
            if r["status"] == "COVERED":
                for k in r["killed"][:2]:
                    print(f"  {n}\n      mutant: {k.get('mutant_body')}\n"
                          f"      -> {k.get('mutant_value')} {k.get('violates')} "
                          f"at {k.get('witness')}")


if __name__ == "__main__":
    main()
