#!/usr/bin/env python3
"""Calibration for the identity gate and the scaling-invariance checks, asserted
in BOTH directions with no slack.

Why this file exists.  The identity gate's finding is that a simulation MATCH can
be an algebraic tautology: the oracle estimates its "truth" with an estimator the
definition under test reduces to, so the residual is zero for every seed and the
verdict is a property of the algebra rather than of the population.  A detector
for that has two failure modes and both are fatal:

  FALSE NEGATIVE  a definition that IS the oracle's estimator is not reported.
                  The banked MATCH then stands, and the corpus records a
                  measurement where it has a definition.  This is the failure
                  that actually happened -- `battery_bulk21` banked MATCH for
                  `driftVariance`, `twoPopDriftVariance` and `expectedFreqDiffSq`
                  and nothing in the pipeline objected.
  FALSE POSITIVE  a definition that is genuinely a different function of the same
                  inputs is reported as a tautology.  Real measurements are then
                  thrown away as worthless, which is the more expensive mistake
                  because it is invisible: nobody re-runs a battery that has been
                  declared vacuous.

So this asserts exact verdicts, not containment, on planted inputs whose right
answer is known by construction.  It runs the same `evaluate` and
`prove_can_fail` the gate runs, against stub corpora, so a change to either
routine is caught here rather than in production.

The negative cases are the traps this design can actually fall into:

  * `p0(1-p0)*fst**2` is the shape a reader mistakes for the real body.  It must
    NOT compose to the identity.
  * a body off by a constant factor composes to a CONSTANT MULTIPLE of the
    estimator, not to the estimator.  Reporting that as an identity would make
    the gate blind to exactly the ploidy-factor errors this corpus has had.
  * a scaling-invariance check whose mutants cannot break it is VACUOUS and must
    be reported as such.  Three real checks were deleted for this reason and the
    rule that deleted them is asserted here, so it cannot quietly lapse.

Run:  python3 proofs/validation/empirical/differential/test_identity_gate.py
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import checks as C          # noqa: E402
import run as R             # noqa: E402


# ---------------------------------------------------------------------------
# Stub corpora.  Each is a table of the same shape `corpus.load()` returns, so
# the gate cannot tell them from the real thing.
# ---------------------------------------------------------------------------
TRUE_BODIES = {
    # the real corpus bodies, transcribed
    "driftVariance": lambda p0, fst: p0 * (1 - p0) * fst,
    "twoPopDriftVariance": lambda p0, fst: 2 * (p0 * (1 - p0) * fst),
    "expectedFreqDiffSq": lambda fst, p0: 2 * fst * p0 * (1 - p0),
}

PLANTED_NON_IDENTITY = {
    # squared F_ST: a genuinely different function of the same inputs
    "driftVariance": lambda p0, fst: p0 * (1 - p0) * fst ** 2,
    "twoPopDriftVariance": lambda p0, fst: 2 * (p0 * (1 - p0) * fst ** 2),
    "expectedFreqDiffSq": lambda fst, p0: 2 * fst ** 2 * p0 * (1 - p0),
}

PLANTED_WRONG_FACTOR = {
    # the ploidy-factor family: right shape, wrong constant
    "driftVariance": lambda p0, fst: 2 * p0 * (1 - p0) * fst,
    "twoPopDriftVariance": lambda p0, fst: 4 * (p0 * (1 - p0) * fst),
    "expectedFreqDiffSq": lambda fst, p0: 4 * fst * p0 * (1 - p0),
}

IDENTITY_IDS = {
    "driftVariance-is-the-oracle-estimator",
    "twoPopDriftVariance-is-twice-the-oracle-estimator",
    "expectedFreqDiffSq-is-twice-the-oracle-estimator",
}

SCALING_IDS = {
    "demoSteppingStoneFst-scale-invariant",
    "steppingStoneFstQuadratic-scale-VIOLATION",
    "ibdFst-scale-VIOLATION-under-the-deme-size-reading",
}

# The three scaling checks that were written, found vacuous, and deleted.  If a
# future author re-adds one, this list is the record of why not.
DELETED_AS_VACUOUS = (
    "fstMigrationDriftEquilibrium-scale-invariant",
    "hetMutationFloor-scale-invariant",
    "coalFst-scale-invariant",
)

SCALE_BODIES = {
    "demoSteppingStoneFst": lambda d, Ne, m, s2: d / (d + 4 * Ne * m * s2),
    "steppingStoneFstQuadratic": lambda d, Ne, m, s2: d / (d + 4 * Ne * s2 ** 2 * m ** 2),
    "ibdFst": lambda d, N, s2: d / (4 * N * s2 + d),
}


def _by_id(cid):
    for chk in C.CHECKS:
        if chk.id == cid:
            return chk
    return None


def main() -> int:
    failures: list[str] = []

    # ---------------- registration ------------------------------------
    for cid in IDENTITY_IDS | SCALING_IDS:
        if _by_id(cid) is None:
            failures.append(f"MISSING         check {cid!r} is not registered in checks.CHECKS")
    for cid in DELETED_AS_VACUOUS:
        if _by_id(cid) is not None:
            failures.append(
                f"RESURRECTED     {cid!r} was deleted because its mutants cannot break it; "
                f"re-adding it puts a check that cannot fail back in the gate")

    for cid in IDENTITY_IDS:
        chk = _by_id(cid)
        if chk is None:
            continue
        if chk.kind != "identity":
            failures.append(
                f"MISFILED        {cid} has kind {chk.kind!r}, not 'identity'; kind decides "
                f"whether the finding reads as a duplicate or as a validation")
        if chk.expected_verdict != "AGREE":
            failures.append(
                f"UNPINNED        {cid} does not pin expected_verdict='AGREE'; without the pin "
                f"a body change that breaks the identity is not reported as a regression")

    # ---------------- POSITIVE: the real bodies ARE the estimator -----
    for cid in sorted(IDENTITY_IDS):
        chk = _by_id(cid)
        if chk is None:
            continue
        res = R.evaluate(chk, TRUE_BODIES)
        got = R.classify(chk, res)
        if got != "AGREE":
            failures.append(
                f"FALSE NEGATIVE  {cid} on the real body reported {got}, not AGREE; the "
                f"identity the banked MATCH rests on went undetected")
        # and it must still have power against a wrong body
        vac = R.prove_can_fail(chk, TRUE_BODIES)
        if not vac["can_fail"]:
            failures.append(
                f"VACUOUS         {cid} is not separated from any mutant; an identity check "
                f"with no power against a wrong body proves nothing in either direction")

    # ---------------- NEGATIVE: a different function is NOT an identity
    for label, table in (("squared F_ST", PLANTED_NON_IDENTITY),
                         ("wrong constant factor", PLANTED_WRONG_FACTOR)):
        for cid in sorted(IDENTITY_IDS):
            chk = _by_id(cid)
            if chk is None:
                continue
            res = R.evaluate(chk, table)
            got = R.classify(chk, res)
            if got == "AGREE":
                failures.append(
                    f"FALSE POSITIVE  {cid} reported AGREE against a planted {label}; the gate "
                    f"cannot tell a tautology from a real measurement and every verdict it "
                    f"produces is worthless")

    # ---------------- scaling invariance, both directions -------------
    control = _by_id("demoSteppingStoneFst-scale-invariant")
    violation = _by_id("steppingStoneFstQuadratic-scale-VIOLATION")
    if control is not None:
        got = R.classify(control, R.evaluate(control, SCALE_BODIES))
        if got != "AGREE":
            failures.append(
                f"FALSE POSITIVE  the diffusion-scale CONTROL demoSteppingStoneFst reported "
                f"{got}; a scaling check that fires on a correct body is measuring the harness")
        if not R.prove_can_fail(control, SCALE_BODIES)["can_fail"]:
            failures.append(
                "VACUOUS         the scaling control is not separated from any mutant; per the "
                "note in checks.py such a check must be deleted, not kept")
    if violation is not None:
        got = R.classify(violation, R.evaluate(violation, SCALE_BODIES))
        if got != "INTERNAL-INCONSISTENT":
            failures.append(
                f"FALSE NEGATIVE  steppingStoneFstQuadratic reported {got}, not "
                f"INTERNAL-INCONSISTENT; its extra power of m breaks coalescent scaling and "
                f"a gate that misses it misses the whole family")
        if violation.expected_verdict != "INTERNAL-INCONSISTENT":
            failures.append(
                "UNPINNED        steppingStoneFstQuadratic does not pin its expected verdict; "
                "a falsified body that starts agreeing must be reported as a regression")

    for f in failures:
        print(f"FAIL  {f}")
    if failures:
        print(f"\n{len(failures)} calibration failure(s).  Until these pass, neither the "
              f"identity gate's VACUOUS verdicts nor its AGREEs are evidence.")
        return 1

    print("identity gate calibration PASSED")
    print(f"  {len(IDENTITY_IDS)} identity checks: each AGREES on the real body, each is "
          f"separated from a mutant, each pins expected_verdict")
    print("  0 false positives: a squared-F_ST body and a wrong-constant-factor body are "
          "both rejected by every identity check")
    print("  scaling invariance: the diffusion-scale control AGREES and is non-vacuous; "
          "steppingStoneFstQuadratic's extra power of m is reported INTERNAL-INCONSISTENT")
    print(f"  {len(DELETED_AS_VACUOUS)} checks deleted for vacuity are asserted absent")
    return 0


if __name__ == "__main__":
    sys.exit(main())
