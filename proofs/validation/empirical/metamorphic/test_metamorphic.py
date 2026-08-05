#!/usr/bin/env python3
"""CALIBRATION of the metamorphic gate, in both directions.

    python3 proofs/validation/empirical/metamorphic/test_metamorphic.py

A detector that reports nothing is indistinguishable from a clean corpus, so
run.py's silence is not evidence until both directions are asserted:

  POSITIVE  every planted defect must be caught, one per relation kind, so a
            relation kind that silently stopped evaluating is detected.  The
            plants are the defect classes this instrument exists for: an
            allele-relabelling asymmetry, a wrong scaling exponent, an argument
            asymmetry, an ORDER dependence, and a cancellation that destroys the
            answer.
  NEGATIVE  the real corpus bodies must produce zero findings at gating
            severity, and each planted defect must be caught by the relation
            that names it and NOT by the others -- a detector that fires on
            everything is as useless as one that fires on nothing.

This runs BEFORE run.py in CI, for the same reason test_check.py runs before
check.py and test_identity_gate.py runs before the differential battery.  It
uses stub bodies only: no Lean, no generated table, well under a second.
"""

import sys
import os
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import relations as R      # noqa: E402
import run as G            # noqa: E402

FAILURES = []


def expect(condition, message):
    if not condition:
        FAILURES.append(message)


def check(fn, argnames, rel):
    return G.check_relation("<stub>", rel, fn, argnames)


# ---------------------------------------------------------------------------
# NEGATIVE DIRECTION: correct bodies must produce no findings.
# ---------------------------------------------------------------------------

def correct_hudson(p1, p2):
    return (p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1))


def correct_ncp(n, b):
    return n * b ** 2


def correct_coal_fst(t, ne):
    return t / (t + 2 * ne)


def negative_direction():
    expect(not check(correct_hudson, ["p1", "p2"],
                     R.invariant_under_allele_swap(["p1", "p2"])),
           "clean Hudson F_ST was reported as violating allele-swap invariance")
    expect(not check(correct_hudson, ["p1", "p2"],
                     R.symmetric_in("p1", "p2")),
           "clean Hudson F_ST was reported as asymmetric in its populations")
    expect(not check(correct_ncp, ["n", "b"], R.scales("b", 2)),
           "clean NCP was reported as violating its quadratic effect scaling")
    expect(not check(correct_ncp, ["n", "b"], R.scales("n", 1)),
           "clean NCP was reported as violating its linear sample scaling")
    expect(not check(correct_coal_fst, ["t", "ne"],
                     R.jointly_scales(["t", "ne"], 0)),
           "clean coalescent F_ST was reported as not rescaling-invariant")


# ---------------------------------------------------------------------------
# POSITIVE DIRECTION: planted defects, one per relation kind.
# ---------------------------------------------------------------------------

def planted_allele_asymmetry(p1, p2):
    """Uses p1 raw where the correct body uses the symmetric combination, so
    relabelling the reference allele moves the answer. This is the shape of a
    body that reads the assembly instead of the biology."""
    return (p1 - p2) ** 2 / (p1 + p2 - 2 * p1 * p2) + p1 / 1000


def planted_wrong_exponent(n, b):
    """Linear in the effect size where the noncentrality parameter is quadratic.
    Monotone in b, so every monotonicity theorem in the corpus still passes."""
    return n * abs(b)


def planted_argument_asymmetry(p1, p2):
    """Antisymmetric in the two populations, so which one is named first moves
    the answer -- but built from `(p1-p2)(p1+p2-1)`, which IS invariant under
    the allele swap. That combination is deliberate: it lets the specificity
    assertion below distinguish the two relations instead of conflating them.
    A plant that broke both would prove nothing about localisation."""
    return ((p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1))
            + Q(1, 100) * (p1 - p2) * (p1 + p2 - 1))


def planted_broken_rescaling(t, ne):
    """Drops the factor that makes time dimensionless, so the answer depends on
    the unit in which time is measured."""
    return t / (t + 2)


def planted_order_dependence(p1, p2):
    """Order dependence, made visible through argument exchange: the body
    returns a different number depending on which population is passed first,
    which is exactly what a sample-order-sensitive estimator does."""
    return p1 * 0.75 + p2 * 0.25


def planted_cancellation(h_t, h_s):
    """A ratio written so the units do NOT cancel: multiplying both
    heterozygosities by a common factor moves the answer, which is the signature
    of a body that lost a normalisation."""
    return (h_t - h_s) / (h_t * h_t)


def positive_direction():
    plants = [
        ("allele relabelling asymmetry", planted_allele_asymmetry,
         ["p1", "p2"], R.invariant_under_allele_swap(["p1", "p2"])),
        ("wrong scaling exponent", planted_wrong_exponent,
         ["n", "b"], R.scales("b", 2)),
        ("argument asymmetry", planted_argument_asymmetry,
         ["p1", "p2"], R.symmetric_in("p1", "p2")),
        ("broken coalescent rescaling", planted_broken_rescaling,
         ["t", "ne"], R.jointly_scales(["t", "ne"], 0)),
        ("order dependence", planted_order_dependence,
         ["p1", "p2"], R.symmetric_in("p1", "p2")),
        ("lost normalisation / cancellation", planted_cancellation,
         ["h_t", "h_s"], R.jointly_scales(["h_t", "h_s"], 0)),
    ]
    for label, fn, args, rel in plants:
        expect(bool(check(fn, args, rel)),
               f"PLANTED DEFECT NOT CAUGHT: {label} "
               f"({rel['id']}) passed the gate")


# ---------------------------------------------------------------------------
# SPECIFICITY: a planted defect must be caught by the relation that names it,
# and the OTHER relations of the same body must still pass. A detector that
# fires on everything cannot localise anything.
# ---------------------------------------------------------------------------

def specificity():
    # planted_wrong_exponent breaks the effect exponent but keeps the sample
    # one, so scales("n", 1) must still hold.
    expect(not check(planted_wrong_exponent, ["n", "b"], R.scales("n", 1)),
           "the wrong-effect-exponent plant was also reported against the "
           "sample-size scaling it does not break; the gate cannot localise")
    # planted_argument_asymmetry keeps allele-swap invariance.
    expect(not check(planted_argument_asymmetry, ["p1", "p2"],
                     R.invariant_under_allele_swap(["p1", "p2"])),
           "the argument-asymmetry plant was also reported against allele-swap "
           "invariance, which it does not break")


# ---------------------------------------------------------------------------
# The table's own integrity: pinned violations must name relations that the
# table actually declares, or the pin is decoration.
# ---------------------------------------------------------------------------

def table_integrity():
    declared_ids = {(fqn, rel["id"])
                    for fqn, rels in R.RELATIONS.items() for rel in rels}
    for key in R.EXPECTED_VIOLATIONS:
        expect(key in declared_ids,
               f"PINNED VIOLATION {key} names a relation that is not declared "
               f"in RELATIONS; the pin can never fire.")
    overlap = set(R.RELATIONS) & set(R.NO_RELATIONS)
    expect(not overlap,
           f"{sorted(overlap)} appear in both RELATIONS and NO_RELATIONS")
    for fqn, reason in R.NO_RELATIONS.items():
        expect(len(reason) > 40,
               f"NO_RELATIONS[{fqn}] has no substantive reason; "
               f"'nobody looked' and 'none applies' must not be confusable")


def main():
    negative_direction()
    positive_direction()
    specificity()
    table_integrity()
    if FAILURES:
        print(f"metamorphic gate calibration FAILED ({len(FAILURES)}):\n")
        for f in FAILURES:
            print("  " + f)
        return 1
    print("metamorphic gate calibration passed: 6 planted defects all caught, "
          "3 clean bodies all silent, specificity and table integrity hold.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
