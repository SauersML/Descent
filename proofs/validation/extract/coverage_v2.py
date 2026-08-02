"""Coverage accounting with a falsifiability requirement.

The rule, and the whole point of this script:

    A definition counts as COVERED only if a check exists that CAN FAIL.

Operationally, for every definition we (a) run a check on the real body and
(b) run the same check on a family of *nearby wrong bodies* (mutants) obtained
by perturbing the parsed Lean source.  The check earns coverage only if it
passes on the real body and fails on at least one mutant that is numerically
distinguishable from the real one.  A check that survives every mutant covers
nothing and is reported as VACUOUS, not as coverage.

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


def call(fn, argnames, pt, structval, rng):
    args = [admissible.struct_value(structval[a], rng) if a in structval
            else pt.get(a, 1.0) for a in argnames]
    return fn(*args)


def range_check(fn, argnames, pts, lo, hi, rng, tol=1e-9):
    """Return (passes, first_violation) for the invariant lo <= f <= hi."""
    for pt, sv in pts:
        try:
            v = call(fn, argnames, pt, sv, rng)
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


def values(fn, argnames, pts, rng):
    out = []
    for pt, sv in pts:
        try:
            out.append(call(fn, argnames, pt, sv, rng))
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
    a = ap.parse_args(argv)

    classes = json.loads((HERE / "classes.json").read_text())
    blob = json.loads((HERE / "defs.json").read_text())
    defs_by_name = {d["name"]: d for d in blob["definitions"]}
    structs = {s["short"]: s for s in blob["structures"]}
    for k, v in classes.items():
        v["_name"] = k

    sys.path.insert(0, str(HERE))
    rng = random.Random(4242)

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
                                         random.Random(11), bounding)
        if not pts:
            rec["reason"] = ("mined hypotheses admit no sampled point; "
                             f"constraints: {hyps[:4]}")
            continue
        base_vals = values(fn, argnames, pts, random.Random(11))
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
            ok, viol = range_check(fn, argnames, pts, lo, hi, random.Random(11))
            if not ok:
                # A range proved by a Lean theorem cannot be violated by a correct
                # translation: that is a real finding.  A range only *suggested*
                # by the docstring or the name is a conjecture, and a violation
                # is a lead for a human, never a verdict.
                src = src_lo if viol[3] == "lo" else src_hi
                if src != "theorem":
                    rec["status"] = "RANGE-MISMATCH"
                elif dropped or len(hyps) < max(
                        d["constraints"].get("range_lo_thm", ["", 0])[1],
                        d["constraints"].get("range_hi_thm", ["", 0])[1]):
                    # Some stated precondition could not be enforced, so the
                    # violating point may simply be inadmissible.  Not a verdict.
                    rec["status"] = "DEFECT-CANDIDATE"
                else:
                    rec["status"] = "DEFECT"
                rec["violation"] = {"point": {k: round(v, 6) for k, v in viol[0].items()},
                                    "value": viol[1], "why": viol[2]}
                continue
            test = lambda f, an: range_check(f, an, pts, lo, hi, random.Random(11))[0]
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
            rec["killed"] = ["separates a witness from a non-witness"]
            continue

        # ---- falsifiability: does the check kill a nearby wrong body?
        killed, tried = [], 0
        for tag, mbody in mutants(d["body"]):
            try:
                mfn, man = compile_variant(d, mbody, fname + "_mut", struct_args)
            except (Untranslatable, Exception):                 # noqa: BLE001
                continue
            mvals = values(mfn, man, pts, random.Random(11))
            if not distinguishable(base_vals, mvals):
                continue                                        # equivalent mutant
            tried += 1
            if not test(mfn, man):
                killed.append(tag)
        rec["mutants_tried"] = tried
        rec["killed"] = killed
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

    if args.verbose:
        print("\nCOVERED, with the wrong bodies each check rejects:")
        for n, r in results.items():
            if r["status"] == "COVERED":
                print(f"  {n}: {r['check']} kills {r['killed'][:3]}")


if __name__ == "__main__":
    main()
