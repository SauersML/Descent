"""Class (A) BLIND: definitions no admissible check CAN cover.

    python3 validation/extract/blind_registry.py

Every definition not currently covered is in class (B) UNMEASURED by default.
|B| is the number that matters and its target is zero.  A definition leaves (B)
only by being covered, or by being admitted to class (A) BLIND with a recorded
argument for why every available tier is structurally incapable of separating
the real body from a mutated one.

WHY THIS FILE EXISTS AT ALL, AND WHY IT IS DANGEROUS
----------------------------------------------------
"Unmeasurable" is the perfect excuse for every definition nobody got to.  It
sounds like a property of the corpus and is usually a property of the tooling.
So admission to (A) is deliberately harder than doing the work:

  1. MACHINE PRECONDITION.  The definition must actually be uncovered right now,
     verified against coverage.json rather than asserted.  The falsifiability
     gate already computes the "no tier rejects a mutant" half; an entry whose
     definition has since become covered is rejected automatically.

  2. A STRUCTURAL REASON, naming the property of the BODY or of the TYPE that
     makes separation impossible -- not the effort spent, not the tier's current
     limits.  "Finset sum" is not a reason; sums over `Fin n` are evaluated by
     this tier today.  "Integral against an arbitrary measure on an abstract
     type with no inhabitant" might be, if no instantiation can distinguish the
     body from a perturbation of it.

  3. A REFUTATION CONDITION.  The entry must state what would have to exist for
     the claim to be FALSE -- "this is wrong if any tier can exhibit an input
     separating the real body from mutant M".  An unfalsifiable claim of
     unmeasurability is the same defect as an unfalsifiable check, one level up,
     and this project already refuses to count a check that cannot fail.

  4. AN AUTHOR.  Arguments are attributable.

Rule 3 is the one that matters.  This session recorded four bugs that were
coherent stories fitting all the available evidence while answering a different
question, plus a fifth invented outright because it rhymed with a real one.  A
blindness argument is exactly that shape of artifact: prose, plausible,
unexecuted, and load-bearing.  Requiring it to name its own refutation is the
only check available on it.

CURRENT STATE: (A) IS EMPTY, AND THAT IS A FINDING
---------------------------------------------------
I could not justify a single entry.  The obvious candidates are the 344
NOT-EXTRACTABLE definitions -- indexed sums, integrals, matrix literals,
quantifiers -- and NONE of them is blind:

  * Finset sums over `Fin n` were NOT-EXTRACTABLE until this tier implemented a
    finite-vector evaluator, at which point 68 of them became evaluable.  The
    blindness was in the tooling and it lasted until someone wrote 40 lines.
  * Integrals against a measure on an abstract type look unmeasurable, but a
    checker may instantiate the type finitely and the measure discretely; that
    the tier has not is a statement about the tier.
  * Matrix literals and quantifiers are the same story.

So the honest answer is |A| = 0 and |B| = every uncovered definition.  Anything
else would be recording "we have not built it" as "it cannot be built", which is
the specific failure the class exists to prevent.

If a genuine blind case appears -- an invariant that determines an object while
being provably invisible to every admissible measurement of it -- it goes here
with its argument.  Until then the emptiness is the result.
"""
from __future__ import annotations

import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import api                                                # noqa: E402

# --------------------------------------------------------------------------
# Class (A).  Empty by construction.  Add an entry ONLY with all four fields.
#
#   "Calibrator.someDef": {
#       "structural_reason": "what about the BODY or TYPE forbids separation",
#       "refutable_by":      "what would have to exist for this to be FALSE",
#       "tiers_considered":  ["extract", "invariants", "symbolic", "differential"],
#       "author":            "who is accountable for the argument",
#   }
# --------------------------------------------------------------------------

BLIND: dict[str, dict] = {}

REQUIRED_FIELDS = ("structural_reason", "refutable_by", "tiers_considered",
                   "author")

# Reasons that are about the TOOLING, not the corpus.  An entry citing one of
# these is rejected: each names something a tier could implement, and at least
# one of them already was.
NOT_A_REASON = {
    "finset": "sums over `Fin n` are evaluated by this tier today",
    "indexed sum": "same",
    "integral": "a checker may instantiate the measure discretely; not having "
                "done so is a fact about the tier",
    "matrix": "matrix literals are evaluable; this tier does rank-2 arguments",
    "quantifier": "a bounded quantifier over a finite instantiation is decidable",
    "too hard": "effort is not a structural property",
    "not implemented": "that is class (B)",
    "no time": "that is class (B)",
}


def validate(name, entry, covered, table):
    """Why this entry may NOT be admitted to (A).  Empty list = admissible."""
    problems = []
    if name not in table:
        problems.append("not a definition in the table")
    if name in covered:
        problems.append("ALREADY COVERED -- a covered definition cannot be blind")
    for f in REQUIRED_FIELDS:
        if not entry.get(f):
            problems.append(f"missing required field {f!r}")
    reason = (entry.get("structural_reason") or "").lower()
    for bad, why in NOT_A_REASON.items():
        if bad in reason:
            problems.append(f"reason cites {bad!r}, which is about the tooling: {why}")
    refut = entry.get("refutable_by") or ""
    if refut and len(refut.split()) < 5:
        problems.append("refutation condition is too short to be a condition")
    return problems


def main():
    api.refresh()
    table = api.definition_table()
    cov_path = HERE / "coverage.json"
    if not cov_path.exists():
        print("coverage.json missing; run coverage_v2.py first")
        return 2
    cov = json.loads(cov_path.read_text())
    covered = {n for n, r in cov.items() if r.get("status") == "COVERED"}

    total = len(table)
    unmeasured = sorted(set(table) - covered - set(BLIND))
    rejected = {}
    admitted = []
    for name, entry in BLIND.items():
        problems = validate(name, entry, covered, table)
        if problems:
            rejected[name] = problems
        else:
            admitted.append(name)

    print("=" * 74)
    print("COVERAGE PARTITION")
    print("=" * 74)
    print(f"definitions                    : {total}")
    print(f"  covered                      : {len(covered)}")
    print(f"  (A) BLIND, argued and admitted: {len(admitted)}")
    print(f"  (B) UNMEASURED               : {len(unmeasured)}"
          f"    <- the number that matters; target zero")

    if rejected:
        print(f"\n{len(rejected)} entry(ies) REJECTED from class (A):")
        for n, ps in rejected.items():
            print(f"  {n}")
            for p in ps:
                print(f"      - {p}")
        print("\nA rejected entry counts as (B). Blindness is not the default.")

    if admitted:
        print(f"\nclass (A) members and their arguments:")
        for n in admitted:
            e = BLIND[n]
            print(f"  {n}   [{e['author']}]")
            print(f"      because : {e['structural_reason']}")
            print(f"      wrong if: {e['refutable_by']}")
            print(f"      tiers   : {', '.join(e['tiers_considered'])}")
    else:
        print("\nclass (A) is EMPTY.")
        print("Not an oversight -- see this module's docstring. The obvious")
        print("candidates (indexed sums, integrals, matrix literals) are all")
        print("cases where the blindness was in the tooling: 68 Finset sums")
        print("became evaluable when this tier implemented a finite-vector")
        print("evaluator. Recording 'we have not built it' as 'it cannot be")
        print("built' is the failure this class exists to prevent.")

    if len(admitted) > 24:
        print(f"\nWARNING: class (A) has {len(admitted)} members. At that size the")
        print("likely explanation is that the tiers are too weak, not that the")
        print("corpus is unobservable. The fix for a weak tier is the tier.")

    out = {"total": total, "covered": len(covered),
           "blind_admitted": admitted, "blind_rejected": rejected,
           "unmeasured": unmeasured}
    (HERE / "partition.json").write_text(json.dumps(out, indent=1))
    print(f"\nwritten: {HERE / 'partition.json'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
