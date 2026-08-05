"""Calibration for the round-trip (direction/inverse) checks.

    python3 test_roundtrip.py

WHY THIS EXISTS.  A detector that reports nothing is indistinguishable from a
clean corpus.  The round-trip family in `checks.py` exists to catch a
definition written the wrong way round, and its report is not evidence until
both directions are asserted:

  * every planted wrong-direction definition is REPORTED, at the severity that
    fails the run;
  * the correct definition produces zero findings at gating severity.

This runs without a Lean build and without consulting the real corpus table:
`D` is a dict of callables, so a planted definition is just a lambda.  That is
the whole reason the differential battery threads `D` through rather than
importing the generated module directly.  It does import `run`, so it inherits
that module's imports; in CI it therefore belongs after the extraction step,
next to `run.py` itself.

What this file does NOT check is that the corpus's own definition is correct --
that is `run.py`'s job.  This checks that if the corpus's definition were
wrong, `run.py` would say so.

The planted defect on line `INVERTED` below is not hypothetical.  It is the
definition that was in `AssortativeMatingPGS.lean` until commit cd95052a, which
multiplied by the artifact instead of its reciprocal and so doubled the
distortion it claimed to remove.
"""
from __future__ import annotations

import sys

import checks
import run


# --------------------------------------------------------------------------
# Planted corpus tables.  Each is a complete stand-in for the one definition
# the round-trip check evaluates.
# --------------------------------------------------------------------------
CORRECT = {
    "amCorrectedPortability":
        lambda pm, r_src, r_tgt, h2: pm * (1 - r_tgt * h2) / (1 - r_src * h2),
}

INVERTED = {
    # the historical defect, verbatim: the artifact, not its reciprocal
    "amCorrectedPortability":
        lambda pm, r_src, r_tgt, h2: pm * (1 - r_src * h2) / (1 - r_tgt * h2),
}

PASS_THROUGH = {
    # returns the measured ratio unchanged: "corrects" nothing.  Passes every
    # q=1 cell, which is exactly why the grid carries q != 1 as well.
    "amCorrectedPortability": lambda pm, r_src, r_tgt, h2: pm,
}

NO_TARGET_TERM = {
    # drops the target inflation: right direction, incomplete correction
    "amCorrectedPortability":
        lambda pm, r_src, r_tgt, h2: pm / (1 - r_src * h2),
}

ADDITIVE = {
    # right direction, wrong algebra: an additive rather than multiplicative
    # correction.  Included because a check that only separates reciprocals
    # would pass this, and "the direction is right" is not the whole claim.
    "amCorrectedPortability":
        lambda pm, r_src, r_tgt, h2: pm + (r_src - r_tgt) * h2,
}

# NB: transposing r_src and r_tgt in CORRECT yields exactly INVERTED, so a
# separate "swapped arguments" planting would be the same defect counted twice
# and would overstate this calibration's coverage. It is deliberately absent.

ROUNDTRIP_IDS = ["amCorrectedPortability-inverts-the-AM-artifact"]

failures: list[str] = []


def _check(cid: str) -> checks.Check:
    for c in checks.CHECKS:
        if c.id == cid:
            return c
    raise SystemExit(
        f"CALIBRATION BROKEN: no check with id {cid!r}. It was renamed or "
        f"deleted; repoint this file rather than leaving it red."
    )


def verdict_of(chk: checks.Check, D: dict) -> tuple[str, float | None]:
    res = run.evaluate(chk, D)
    return run.classify(chk, res), res["max_rel_err"]


def expect_clean(cid: str) -> None:
    """The correct definition must produce no finding at gating severity."""
    chk = _check(cid)
    v, err = verdict_of(chk, CORRECT)
    if v != "AGREE":
        failures.append(
            f"{cid}: the CORRECT definition was reported as {v} "
            f"(max rel err {err}). A detector that fires on clean input is "
            f"worse than none."
        )
    if chk.expected_verdict != "AGREE":
        failures.append(
            f"{cid}: expected_verdict is {chk.expected_verdict!r}, not 'AGREE'. "
            f"Without that pin a disagreement is recorded as a number and does "
            f"NOT fail run.py, so this family would not gate."
        )


def expect_caught(cid: str, label: str, D: dict, floor: float = 1e-3) -> None:
    """A planted wrong-direction definition must be reported, and loudly."""
    chk = _check(cid)
    v, err = verdict_of(chk, D)
    if v == "AGREE":
        failures.append(
            f"{cid}: planted defect {label!r} was NOT caught (verdict AGREE). "
            f"The check cannot see this defect class."
        )
        return
    if err is None or err < floor:
        failures.append(
            f"{cid}: planted defect {label!r} produced verdict {v} but a "
            f"max relative error of {err}, below the {floor} floor. A defect "
            f"detected only at the noise level is not detected."
        )
    # and it must be a REGRESSION, i.e. it must actually fail run.py
    if chk.expected_verdict and v == chk.expected_verdict:
        failures.append(
            f"{cid}: planted defect {label!r} produced the expected verdict, "
            f"so run.py would not flag it."
        )


def expect_can_fail(cid: str) -> None:
    """run.py's own mutant screen must also rate the check non-vacuous."""
    chk = _check(cid)
    vac = run.prove_can_fail(chk, CORRECT)
    if not vac["can_fail"]:
        failures.append(
            f"{cid}: run.py rates this check VACUOUS against the correct "
            f"definition -- no mutant of the corpus table breaks it, so it "
            f"constrains nothing."
        )


def main() -> int:
    for cid in ROUNDTRIP_IDS:
        expect_clean(cid)
        expect_can_fail(cid)
        expect_caught(cid, "inverted correction factor (the historical bug)",
                      INVERTED)
        expect_caught(cid, "pass-through: corrects nothing", PASS_THROUGH)
        expect_caught(cid, "target inflation term dropped", NO_TARGET_TERM)
        expect_caught(cid, "additive instead of multiplicative", ADDITIVE)

    if failures:
        print("ROUND-TRIP CALIBRATION FAILED")
        for f in failures:
            print("  * " + f)
        return 1
    print(f"round-trip calibration OK: {len(ROUNDTRIP_IDS)} check(s); "
          f"correct definition clean, 4 planted defects each reported as a "
          f"verdict regression")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
