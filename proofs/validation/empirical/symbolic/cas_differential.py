"""DIAGNOSTIC -- computer-algebra differential testing of the definition surface.

NOT A GATE, and deliberately so.  It needs sympy, and `sympy.simplify` has no
bounded running time: a `simplify` that does not close is a false NEGATIVE (it
reports "cannot decide", and a caller that reads that as agreement has been
lied to), while a convention mismatch is a false POSITIVE (the algebra is right
and the units the comparison assumed are wrong).  Neither belongs in a required
check.  Per `.github/workflows/prover.yml`'s own exclusion list, sympy-dependent
and unbounded-runtime work stays a committed instrument that a person runs and
reads.

WHAT WAS PROMOTED OUT OF HERE INTO THE GATE.  Two findings were reducible to
exact arithmetic on a fixed grid, and those are gated, in
`proofs/validation/empirical/differential/checks.py` sections 20 and 21, with a
two-directional calibration in `differential/test_identity_gate.py`:

  * the IDENTITY GATE -- `driftVariance`, `twoPopDriftVariance` and
    `expectedFreqDiffSq` reduce to the simulation oracle's own F_ST estimator,
    so `battery_bulk21`'s three MATCH verdicts are algebraic tautologies.
  * COALESCENT SCALING INVARIANCE -- dimensional homogeneity in the only form
    that survives this corpus's conventions.

WHAT STAYS HERE.  Everything that needs symbolic simplification rather than
numeric evaluation: closed forms compared against independently derived
references, and asymptotic limits.  Note that `check1_fixedpoints.py`,
`check2_derivations.py` and `check4_limits.py` in this directory already cover
much of that ground; this file is the differential-testing view of the same
surface and exists to carry the convention arguments, which are prose the other
checks have nowhere to put.

CALIBRATION.  Every sub-instrument carries a planted-WRONG and a planted-RIGHT
case and reports both before any verdict.  A run whose calibration line does not
say PASSED is not evidence.  The last recorded run, sympy 1.14.0:

    closed form   Sved r^2 with 2Nc for 4Nc -> DISAGREE, residual
                  2*Ne*c/((2*Ne*c + 1)*(4*Ne*c + 1))
                  Ohta-Kimura sigma_d^2      -> AGREE
    identity      p0(1-p0)*fst^2             -> INFORMATIVE, residual
                  Varp*(-Varp - p0**2 + p0)/(p0*(p0 - 1))
                  p0(1-p0)*fst               -> IDENTITY
    limits        1/(1+4*Ne*m) as m->1 = 1   -> FAILS (planted)
                  1/(1+theta) as theta->oo   -> HOLDS

TWO REPORTED DISAGREEMENTS THAT ARE THE INSTRUMENT'S OWN, NOT THE CORPUS'S, and
they are recorded rather than tuned away because a reader must be able to tell
them from findings:

  * `hweMellinDrift` reported a residual `2*q*(q-1)*(log(1-q) + log(-1/(q-1)))`.
    That is identically zero on `0 < q < 1` -- the two logs are negatives of one
    another -- but sympy's symbols are declared positive, not less than one, so
    it will not close the branch.  The body is CORRECT.  This is the false
    negative the header warns about, caught only because the derivation was also
    done by hand.
  * `mutationSelectionBalanceRecessive` reported a sign-flipped residual because
    the root selector picked the negative branch of the fixed-point quadratic:
    both roots tend to 0 as mu -> 0, so the filter that distinguishes them is
    wrong, not the body.  The body is CORRECT.

Run:  python3 proofs/validation/empirical/symbolic/cas_differential.py
      (needs sympy; see cluster_run.sh for the module that provides it)
"""
from __future__ import annotations

import signal
import sys

import sympy as sp

# A per-expression wall clock.  An unbounded `simplify` is the failure mode this
# instrument is excluded from the gate for; bounding it here means a slow
# expression reports TIMEOUT, which is a non-answer, instead of hanging the run
# or -- far worse -- being read as agreement.
TIMEOUT_S = 20


class _Timeout(Exception):
    pass


def _alarm(_sig, _frm):
    raise _Timeout


def bounded_simplify(expr):
    """simplify(expr) under a wall clock.  Returns (value, status)."""
    if not hasattr(signal, "SIGALRM"):
        return sp.simplify(expr), "OK"
    old = signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(TIMEOUT_S)
    try:
        return sp.simplify(sp.together(expr)), "OK"
    except _Timeout:
        return None, "TIMEOUT"
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)


def residual(body, reference):
    """Exact symbolic residual, with a timeout reported as a timeout.

    A `None` residual NEVER means agreement.  Callers must branch on the status.
    """
    val, status = bounded_simplify(body - reference)
    if status != "OK":
        return None, status
    return val, ("AGREE" if val == 0 else "DISAGREE")


# --------------------------------------------------------------------------
Ne, t, m, c, mu, theta, p0, q, s, alpha, rho = sp.symbols(
    "Ne t m c mu theta p0 q s alpha rho", positive=True)
Varp, b = sp.symbols("Varp b", positive=True)
_y = sp.Symbol("_y")

# (label, lean location, body, independently derived reference, convention)
CLOSED = [
    ("CALIBRATION+ ohtaKimuraSigmaDSq", "LDDecayTheory.lean:547",
     (10 + 4 * Ne * c) / ((2 + 4 * Ne * c) * (11 + 4 * Ne * c)),
     (10 + 4 * Ne * c) / ((2 + 4 * Ne * c) * (11 + 4 * Ne * c)),
     "Ohta-Kimura 1971, rho = 4*Ne*c"),
    ("CALIBRATION- Sved r^2 with 2Nc for 4Nc", "PLANTED",
     1 / (1 + 2 * Ne * c), 1 / (1 + 4 * Ne * c),
     "Sved 1971 E[r^2] = 1/(1 + 4*Ne*c)"),

    ("ibdRecurrenceFixedPoint", "PortabilityDrift.lean:6309",
     (1 - m) ** 2 / ((1 - m) ** 2 + 2 * Ne * m * (2 - m)),
     sp.solve(sp.Eq(_y, (1 - m) ** 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * _y)), _y)[0],
     "fixed point of the file's own ibdRecurrenceStep"),
    ("driftLDEquilibrium", "LDDecayTheory.lean:504",
     (1 - c) ** 2 * (1 / (2 * Ne)) / (1 - (1 - c) ** 2 * (1 - 1 / (2 * Ne))),
     sp.solve(sp.Eq(_y, (1 - c) ** 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * _y)), _y)[0],
     "fixed point of the file's own driftLDStep"),
    ("selectionMigrationEquilibrium", "PopulationGeneticsFoundations.lean:528",
     (s - m - m * s) / s,
     [r for r in sp.solve(sp.Eq(_y, (1 - m) * (_y * (1 + s) / (1 + s * _y))), _y) if r != 0][0],
     "fixed point of continentIslandStepSelectionFirst, unclamped branch"),
    ("selectionMigrationEquilibriumMigrationFirst",
     "PopulationGeneticsFoundations.lean:558",
     (s - m - m * s) / (s * (1 - m)),
     [r for r in sp.solve(sp.Eq(_y, ((1 - m) * _y) * (1 + s) / (1 + s * ((1 - m) * _y))), _y)
      if r != 0][0],
     "fixed point of continentIslandStepMigrationFirst, unclamped branch"),
    ("hetMutationFloor", "PortabilityDrift.lean:858",
     4 * Ne * mu / (1 + 4 * Ne * mu),
     [r for r in sp.solve(sp.Eq(_y, (1 - 1 / (2 * Ne)) * _y + 2 * mu * (1 - _y)), _y)][0],
     "fixed point of the file's own hetStepWithMutation"),
    ("ldPrecisionTrace", "ImitationRigidity.lean:952",
     (sp.Symbol("n", positive=True) * (1 + c ** 2) - 2 * c ** 2) / (1 - c ** 2),
     ((sp.Symbol("n", positive=True) - 2) * (1 + c ** 2) + 2) / (1 - c ** 2),
     "AR(1) Toeplitz precision over n sites: n-2 interior rows and 2 boundary rows"),
    ("hweMellinDrift  [KNOWN FALSE NEGATIVE, see header]",
     "PolygenicSpectroscopy.lean:213",
     (1 - 2 * q) ** 2 * sp.log((1 - 2 * q) ** 2 / (2 * q * (1 - q)))
     + 4 * q * (1 - q) * sp.log(2),
     sum(pr * z * sp.log(z) for pr, z in [
         ((1 - q) ** 2, (2 * q) ** 2 / (2 * q * (1 - q))),
         (2 * q * (1 - q), (1 - 2 * q) ** 2 / (2 * q * (1 - q))),
         (q ** 2, (2 - 2 * q) ** 2 / (2 * q * (1 - q)))]),
     "E[Z^2 log Z^2] over the HWE genotype distribution, alt frequency q"),

    # The convention finding.  Both readings are listed so the residual that
    # separates them is on the record rather than asserted in prose.
    ("ancestryRecalibratedSlope  [alpha = SD ratio: the body's reading]",
     "AncestryCalibration.lean:37",
     rho * (b * alpha) / alpha ** 2, rho * b / alpha,
     "alpha = sd(PGS_target)/sd(PGS_source); Cov scales with one power, Var with two"),
    ("ancestryRecalibratedSlope  [alpha = VARIANCE ratio: the docstring's old word]",
     "AncestryCalibration.lean:37",
     rho * (b * alpha) / alpha ** 2, rho * b / sp.sqrt(alpha),
     "alpha = Var(PGS_target)/Var(PGS_source) -- the reading the docstring used to name"),
]

# (label, location, body, estimator the simulation oracle computes)
# F_ST := Var(p)/(p0(1-p0)) is Wright's DEFINITION, and it is what the harness
# estimates on the same run.  A body that collapses onto the estimator under it
# alone has an empirical verdict that is a property of the algebra.
FST_DEF = Varp / (p0 * (1 - p0))
IDENTITIES = [
    ("CALIBRATION- p0(1-p0)*fst^2 (a different function)", "PLANTED",
     p0 * (1 - p0) * sp.Symbol("fst", positive=True) ** 2, Varp),
    ("CALIBRATION+ p0(1-p0)*fst", "PLANTED",
     p0 * (1 - p0) * sp.Symbol("fst", positive=True), Varp),
    ("driftVariance", "AncestrySpecificArchitecture.lean:126",
     p0 * (1 - p0) * sp.Symbol("fst", positive=True), Varp),
    ("twoPopDriftVariance", "AncestrySpecificArchitecture.lean:172",
     2 * p0 * (1 - p0) * sp.Symbol("fst", positive=True), 2 * Varp),
    ("expectedFreqDiffSq", "AncestrySpecificArchitecture.lean:218",
     2 * sp.Symbol("fst", positive=True) * p0 * (1 - p0), 2 * Varp),
    ("coalFst (control: NOT an identity against the same estimator)",
     "PopulationGeneticsFoundations.lean:343",
     t / (t + 2 * Ne), Varp),
]

# (label, location, expr, var, point, required limit, why it must hold)
LIMITS = [
    ("CALIBRATION- 1/(1+4*Ne*m) as m->1 is not 1", "PLANTED",
     1 / (1 + 4 * Ne * m), m, 1, 1, "planted-wrong limit; must FAIL"),
    ("CALIBRATION+ fstMutationDriftEquilibrium theta->oo", "DGP.lean:113",
     1 / (1 + theta), theta, sp.oo, 0, "infinite mutation erases differentiation"),
    ("coalFst t->0", "PopulationGeneticsFoundations.lean:343",
     t / (t + 2 * Ne), t, 0, 0, "no divergence time, no differentiation"),
    ("coalFst t->oo", "PopulationGeneticsFoundations.lean:343",
     t / (t + 2 * Ne), t, sp.oo, 1, "infinite divergence, complete differentiation"),
    ("driftLDEquilibrium c->0", "LDDecayTheory.lean:504",
     (1 - c) ** 2 * (1 / (2 * Ne)) / (1 - (1 - c) ** 2 * (1 - 1 / (2 * Ne))), c, 0, 1,
     "no recombination: drift drives sigma_d^2 to its maximum"),
    ("driftLDEquilibrium Ne->oo", "LDDecayTheory.lean:504",
     (1 - c) ** 2 * (1 / (2 * Ne)) / (1 - (1 - c) ** 2 * (1 - 1 / (2 * Ne))), Ne, sp.oo, 0,
     "no drift: no LD generated"),
    ("hetMutationFloor mu->0", "PortabilityDrift.lean:858",
     4 * Ne * mu / (1 + 4 * Ne * mu), mu, 0, 0, "no mutation, no floor"),
    ("hetMutationFloor Ne->oo", "PortabilityDrift.lean:858",
     4 * Ne * mu / (1 + 4 * Ne * mu), Ne, sp.oo, 1, "no drift: heterozygosity saturates"),
    ("islandDemeCorrection d->oo", "PopulationGeneticsFoundations.lean:1380",
     sp.Symbol("d", positive=True) / (sp.Symbol("d", positive=True) - 1),
     sp.Symbol("d", positive=True), sp.oo, 1,
     "infinitely many demes recovers the classic 1/(1 + 4*Ne*m)"),
    ("ibdRecurrenceFixedPoint m->0", "PortabilityDrift.lean:6309",
     (1 - m) ** 2 / ((1 - m) ** 2 + 2 * Ne * m * (2 - m)), m, 0, 1,
     "no migration: complete identity by descent"),
    ("effectCorrelationStabilizing Ns->0+", "SelectionArchitecture.lean:142",
     1 - 1 / (2 * sp.Symbol("Ns", positive=True)), sp.Symbol("Ns", positive=True), 0, 0,
     "the file's junk-point note discusses the VALUE at Ns = 0, which Lean makes 1; "
     "the LIMIT is -oo, so the definition is unbounded on the punctured neighbourhood. "
     "Not a defect -- every bounding theorem in the file hypothesises 1 < Ns, and "
     "invariants/check_ranges.py boxes it there -- but the note names only the point"),
]


def main() -> int:
    print("sympy %s, per-expression timeout %ds" % (sp.__version__, TIMEOUT_S))
    calib_ok = True
    timeouts = 0

    print("\n== closed form: simplify(body - independently derived reference)")
    for label, loc, body, ref, conv in CLOSED:
        val, verdict = residual(body, ref)
        if verdict == "TIMEOUT":
            timeouts += 1
        print("  [%-8s] %s  (%s)" % (verdict, label, loc))
        print("             convention: %s" % conv)
        if verdict == "DISAGREE":
            print("             residual  : %s" % val)
        if label.startswith("CALIBRATION+") and verdict != "AGREE":
            calib_ok = False
        if label.startswith("CALIBRATION-") and verdict != "DISAGREE":
            calib_ok = False

    print("\n== identity: does the body collapse onto the oracle's own estimator?")
    for label, loc, body, est in IDENTITIES:
        val, verdict = residual(body.subs(sp.Symbol("fst", positive=True), FST_DEF), est)
        if verdict == "TIMEOUT":
            timeouts += 1
            tag = "TIMEOUT"
        else:
            tag = "IDENTITY" if verdict == "AGREE" else "INFORMATIVE"
        print("  [%-11s] %s  (%s)" % (tag, label, loc))
        if tag == "INFORMATIVE":
            print("                residual: %s" % val)
        if label.startswith("CALIBRATION+") and tag != "IDENTITY":
            calib_ok = False
        if label.startswith("CALIBRATION-") and tag != "INFORMATIVE":
            calib_ok = False

    print("\n== limits that must hold")
    for label, loc, expr, var, pt, need, why in LIMITS:
        try:
            got = sp.simplify(sp.limit(expr, var, pt))
        except Exception as e:
            print("  [NO LIMIT] %s (%s): %s" % (label, loc, e))
            continue
        holds = sp.simplify(got - need) == 0
        print("  [%-7s] %s  (%s)" % ("HOLDS" if holds else "FAILS", label, loc))
        if not holds:
            print("            limit %s, required %s" % (got, need))
            print("            %s" % why)
        if label.startswith("CALIBRATION+") and not holds:
            calib_ok = False
        if label.startswith("CALIBRATION-") and holds:
            calib_ok = False

    print("\ncalibration %s" % ("PASSED -- planted-wrong and planted-right separated on "
                                "every sub-instrument" if calib_ok else
                                "FAILED -- no verdict above is evidence"))
    if timeouts:
        print("%d expression(s) TIMED OUT. A timeout is a non-answer, never an "
              "agreement; re-run those with cancel/together/radsimp." % timeouts)
    print("DIAGNOSTIC: this instrument does not gate. The two findings that could "
          "be reduced to exact arithmetic were promoted into "
          "differential/checks.py sections 20 and 21.")
    return 0 if calib_ok else 1


if __name__ == "__main__":
    sys.exit(main())
