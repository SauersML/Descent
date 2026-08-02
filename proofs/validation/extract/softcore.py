"""The soft core: coverage that is real but weakest, quantified.

`covered` has been one word for several different strengths of evidence, and
the differences matter more than the total.  Three axes, all published per
definition already; this joins them.

  SINGLE-TIER   no other checking layer touches the definition, so if this
                tier is wrong about it, nothing else notices.
  CONJECTURED   the bound the check grades against is not proved by any
                theorem -- it is inferred from the definition's name or
                docstring calling it a probability, a frequency, an F_ST.
                Mutation testing then proves the check DISCRIMINATES; it says
                nothing about whether the thing discriminated against is right.
  ONE-MUTANT    the check rejects exactly one of the nearby wrong bodies tried.
                Real falsifiability, and the weakest amount of it.

A definition that is all three is covered in name only.  That intersection is
the honest floor under every coverage number this project quotes.

    python3 validation/extract/softcore.py

The single-tier axis is RECONSTRUCTED here from the other tiers' published
results files, not taken from the cross-tier reconciliation.  Where the two
disagree the reconciliation is authoritative -- it knows about tiers this
script cannot see.  The reconstruction is stated explicitly so the difference
is checkable rather than silent.
"""
from __future__ import annotations

import collections
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import api                                                # noqa: E402

PROOFS = HERE.parent.parent
OTHER_TIERS = ("invariants", "symbolic", "differential", "popgen_defs",
               "pc_correctability", "condensation", "imitation_rigidity")

# Verdicts that record an ABSENCE of checking.  Counting these as another tier's
# coverage would understate how many definitions rest on this tier alone --
# the error would flatter the number, so it is excluded explicitly.
NON_VERDICTS = {"not-transpiled", "no-range", "inconclusive", "skipped",
                "unavailable", "not-extractable", "uncovered", "n/a", "none",
                "NOT-EXTRACTABLE", "UNCOVERED", "not_extractable", "no_range",
                "ERROR", "error", "SKIP", "untested", "UNTESTED"}


def other_tier_coverage():
    """{short name: {tier, ...}} for definitions some OTHER tier reports on."""
    hits = collections.defaultdict(set)
    for tier in OTHER_TIERS:
        root = PROOFS / "validation" / tier
        if not root.exists():
            continue
        for path in root.rglob("*.json"):
            try:
                blob = json.loads(path.read_text())
            except Exception:                                   # noqa: BLE001
                continue

            def walk(node, depth=0, key=None):
                if depth > 7:
                    return
                if isinstance(node, dict):
                    name = (node.get("definition") or node.get("fqn")
                            or node.get("name") or node.get("def"))
                    verdict = (node.get("verdict") or node.get("status")
                               or node.get("result") or node.get("check"))
                    if isinstance(name, str) and name and (
                            not isinstance(verdict, str)
                            or verdict not in NON_VERDICTS):
                        hits[name.split(".")[-1]].add(tier)
                    for k, v in node.items():
                        walk(v, depth + 1, k)
                elif isinstance(node, list):
                    for v in node[:8000]:
                        walk(v, depth + 1, key)

            # top-level dicts keyed BY definition name (invariants does this)
            if isinstance(blob, dict) and blob and all(
                    isinstance(v, dict) for v in list(blob.values())[:5]):
                for k in blob:
                    if "." in k or k[:1].islower():
                        hits[k.split(".")[-1]].add(tier)
            walk(blob)
    return hits


def main():
    api.refresh()
    cov = json.loads((HERE / "coverage.json").read_text())
    covered = {n: r for n, r in cov.items() if r["status"] == "COVERED"}
    others = other_tier_coverage()

    rows = {}
    for n, r in covered.items():
        chk = r.get("check") or {}
        theorem_bound = "theorem" in (chk.get("source_lo"), chk.get("source_hi"))
        tiers = others.get(n.split(".")[-1], set())
        rows[n] = {
            "single_tier": not tiers,
            "other_tiers": sorted(tiers),
            "conjectured_bound": not theorem_bound,
            "mutants_tried": r.get("mutants_tried", 0),
            "mutants_killed": r.get("mutants_killed", len(r.get("killed") or [])),
            "one_mutant": r.get("mutants_killed",
                                len(r.get("killed") or [])) <= 1,
            "file": r["file"], "line": r["line"],
        }

    n = len(rows)
    single = {k for k, v in rows.items() if v["single_tier"]}
    conj = {k for k, v in rows.items() if v["conjectured_bound"]}
    one = {k for k, v in rows.items() if v["one_mutant"]}

    print("=" * 74)
    print("THE SOFT CORE OF `COVERED`")
    print("=" * 74)
    print("Percentages carry their absolute counts; the denominator moves during")
    print("the run that measures it.\n")
    print(f"covered definitions (this tier)          : {n}")
    print(f"  single-tier (no other layer touches it): {len(single)}"
          f"   [reconstructed, see below]")
    print(f"  bound is CONJECTURED, not proved       : {len(conj)}")
    print(f"  rejects exactly ONE nearby wrong body  : {len(one)}")

    print("\npairwise intersections:")
    print(f"  single-tier AND conjectured            : {len(single & conj)}")
    print(f"  single-tier AND one-mutant             : {len(single & one)}")
    print(f"  conjectured AND one-mutant             : {len(conj & one)}")

    core = single & conj & one
    print(f"\n{'=' * 74}")
    print(f"ALL THREE -- covered in name only        : {len(core)}"
          f"  of {n} covered")
    print("=" * 74)
    print("Single-tier, graded against a bound nobody proved, rejecting one of")
    print("the nearby wrong bodies tried.  This is the honest floor.")
    for k in sorted(core):
        v = rows[k]
        print(f"  {k}  ({v['file']}:{v['line']})"
              f"  killed {v['mutants_killed']}/{v['mutants_tried']}")

    print(f"\nfor contrast, the strong core -- multi-tier, theorem-proved bound,")
    print(f"rejecting more than one wrong body:")
    strong = [k for k, v in rows.items()
              if not v["single_tier"] and not v["conjectured_bound"]
              and not v["one_mutant"]]
    print(f"  {len(strong)} definitions")
    for k in sorted(strong)[:12]:
        v = rows[k]
        print(f"  {k}  killed {v['mutants_killed']}/{v['mutants_tried']}"
              f"  also checked by {v['other_tiers']}")

    print("\nRECONSTRUCTION CAVEAT.  The single-tier axis is derived from other")
    print("tiers' published results files, matched on SHORT name because they")
    print("are not all keyed fully-qualified.  Short-name matching OVER-counts")
    print("other-tier coverage (22 short names in this corpus map to more than")
    print("one definition), so it UNDER-counts single-tier, and the soft core")
    print("above is therefore a LOWER bound on itself.  The cross-tier")
    print("reconciliation is authoritative; this is a check against it, not a")
    print("replacement for it.")

    out = {"covered": n, "single_tier": sorted(single),
           "conjectured_bound": sorted(conj), "one_mutant": sorted(one),
           "soft_core": sorted(core), "strong_core": sorted(strong),
           "per_definition": rows}
    (HERE / "softcore.json").write_text(json.dumps(out, indent=1))
    print(f"\nwritten: {HERE / 'softcore.json'}")


if __name__ == "__main__":
    main()
