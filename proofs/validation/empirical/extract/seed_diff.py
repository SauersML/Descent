"""Compare coverage runs made at different master seeds.

    python3 validation/extract/seed_diff.py cov_11.json cov_977.json cov_31337.json

Reproducibility is not stability.  Drawing the same 40 admissible points every
run makes a verdict REPEATABLE; it says nothing about whether the verdict
survives drawing 40 different ones.  This diffs runs that differ only in the
master seed, so anything that moves was never a property of the definition.

THREE LEVELS, because a coverage flag can be stable while what is underneath it
is not.  Diffing only the covered set catches the first and misses the rest:

  1. STATUS      COVERED / VACUOUS / UNCOVERED / DEFECT / RANGE-MISMATCH ...
                 A definition whose status moves was never covered, and should
                 be withdrawn rather than reported at whichever seed was kind.

  2. EVIDENCE    Which mutants the check rejected, compared BY IDENTITY and not
                 by count.  A definition that stays COVERED while its rejected
                 set changes from six mutants to one has an unstable verdict
                 wearing a stable flag -- and comparing counts would net that
                 out to "6 vs 1" or, worse, "6 vs 6" when the membership
                 changed but the size did not.

  3. FINDINGS    The violating point and value for DEFECT / RANGE-MISMATCH, also
                 by identity.  A defect that moves to a different triggering
                 point is still a defect, but it is a DIFFERENT one, and a
                 count-based comparison shows no change at all.

Exit code is non-zero if anything moved at any level.
"""
from __future__ import annotations

import json
import pathlib
import sys


def load(paths):
    runs = {}
    for p in paths:
        runs[pathlib.Path(p).name] = json.loads(pathlib.Path(p).read_text())
    return runs


def main(argv):
    if len(argv) < 3:
        print(__doc__)
        return 2
    runs = load(argv[1:])
    names = sorted(set().union(*(set(r) for r in runs.values())))
    labels = list(runs)

    status_moved, evidence_moved, finding_moved, absent = {}, {}, {}, []

    for n in names:
        recs = {lab: runs[lab].get(n) for lab in labels}
        if any(r is None for r in recs.values()):
            absent.append((n, [lab for lab, r in recs.items() if r is None]))
            continue

        statuses = {lab: r.get("status") for lab, r in recs.items()}
        if len(set(statuses.values())) > 1:
            status_moved[n] = statuses
            continue        # a status move subsumes the finer levels

        if statuses[labels[0]] == "COVERED":
            # by identity, not by count
            killed = {lab: frozenset(k.get("mutation")
                                     for k in (r.get("killed") or []))
                      for lab, r in recs.items()}
            if len(set(killed.values())) > 1:
                evidence_moved[n] = {lab: sorted(v) for lab, v in killed.items()}

        if statuses[labels[0]] in ("DEFECT", "DEFECT-CANDIDATE", "RANGE-MISMATCH"):
            viol = {}
            for lab, r in recs.items():
                v = r.get("violation") or {}
                viol[lab] = (json.dumps(v.get("point"), sort_keys=True),
                             v.get("why"))
            if len(set(viol.values())) > 1:
                finding_moved[n] = {lab: v for lab, v in viol.items()}

    print("=" * 74)
    print("SEED-VARIATION DIFF")
    print("=" * 74)
    for lab in labels:
        cov = sum(1 for r in runs[lab].values() if r.get("status") == "COVERED")
        print(f"  {lab:<24} definitions {len(runs[lab]):5d}   covered {cov:5d}")

    print(f"\nSTATUS moved            : {len(status_moved)}"
          f"   <- never covered; withdraw")
    for n, st in sorted(status_moved.items())[:40]:
        print(f"    {n}")
        print(f"        {st}")

    print(f"\nEVIDENCE moved          : {len(evidence_moved)}"
          f"   <- stayed COVERED, but on different mutants")
    for n, ev in sorted(evidence_moved.items())[:25]:
        print(f"    {n}")
        for lab, v in ev.items():
            print(f"        {lab}: {v}")

    print(f"\nFINDING moved           : {len(finding_moved)}"
          f"   <- same verdict, different witness")
    for n, fv in sorted(finding_moved.items())[:25]:
        print(f"    {n}")
        for lab, v in fv.items():
            print(f"        {lab}: {v}")

    if absent:
        print(f"\nabsent from some run    : {len(absent)}"
              f"   (corpus changed between runs -- rerun from one revision)")
        for n, labs in absent[:10]:
            print(f"    {n}: missing from {labs}")

    total = len(status_moved) + len(evidence_moved) + len(finding_moved)
    print(f"\n{'=' * 74}")
    if total == 0 and not absent:
        print("nothing moved across seeds.")
        print("This is ONE passing test, not a proof of stability: three seeds")
        print("sample the space of point-sets, they do not cover it.")
        return 0
    print(f"{total} definition(s) moved. Each one is a verdict that depended on")
    print("which points happened to be drawn, and should be withdrawn or")
    print("re-checked rather than reported at the seed that was kind.")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
