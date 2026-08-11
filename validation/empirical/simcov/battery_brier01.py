"""#41/#37: `liabilityBrierExact` put on trial, which its own head says nothing has.

Its `Empirical status: UNTESTED` paragraph is unusually precise about what is
missing: the form reproduces four stored cells and closes in elementary terms at
`π = 1/2`, "but that was quadrature run by hand against a stored table, not a
battery, and no battery has yet put THIS DECLARATION on trial." This is that
battery.

WHAT IS PREDICTED, AND WHY THE MEASURED SIDE IS A DIFFERENT COMPUTATION. For a
calibrated predictor `Brier = E[p(1-p)] = π - E[p²]`, and under the liability-
threshold model `E[p²]` is the probability that two conditionally independent
replicate draws sharing the score component both land on the case side -- a
bivariate normal orthant at correlation `r²`. The predicted side evaluates that
orthant. The measured side never forms `p²` analytically: it draws a liability,
derives each individual's calibrated risk from their score alone, draws the
ACTUAL disease outcome, and averages `(p - Y)²`. If the orthant were the wrong
functional of `r²` the two would part.

THE RIVAL IS THE BODY THE CORPUS ACTUALLY USED. `calibratedBrier π r² =
π(1-π)(1-r²)` is the linear chart, correct when `r²` is an OBSERVED-scale
explained fraction and wrong when the outcome is a truncated liability tail.
That is the defect #41 exists to repair, so it is the rival that has to be
rejected here or the repair rests on nothing measured.

THE READABILITY RULE IS THE ANCHOR-POINT TELL, MADE MECHANICAL. The two bodies
agree exactly at `r² = 0` and `r² = 1` -- which is why, as `liabilityBrierExact`'s
own docstring says, "the chart's two anchor theorems could not tell a line from a
curve through the same two points". A cell where the two predictions differ by
less than three Monte-Carlo floors therefore discriminates nothing, no matter how
tight its agreement looks, and is EXCLUDED by a rule fixed before the run and
printed with its separation. Reporting such a cell as confirmation would be
reporting the anchor, not the curve.

MY OWN QUADRATURE IS CHECKED BEFORE IT IS USED, against the closed form the
declaration's docstring supplies: at `π = 1/2` the orthant is
`Φ₂(0,0;ρ) = 1/4 + arcsin ρ / (2π)`. That check runs first and the battery
raises rather than records if it fails, because a battery whose predicted side is
wrong would falsify a correct body.

THE SIX TEMPLATE CHECKS:
 1. SLICE IN THE NAME: `p_calib` is the individual's calibrated risk from the
    SCORE component alone; `y_event` is the realised outcome. Neither is `p`.
 2. ESTIMAND FORM IN THE REGIME STRING: the measured quantity is the mean over
    individuals of `(p_calib - y_event)²`, an unweighted per-capita mean.
 3. CURRENCY: both sides are Brier risk in squared-probability units over the
    same individuals; nothing is weighted.
 4. BOUNDS BESIDE QUANTITIES: every cell prints its Monte-Carlo floor and its
    rival separation next to the measurement.
 5. NO CROSS-CONFIG COMPARISON: config travels in the regime string.
 6. ONE FILTERED SET: one draw per cell, handed to the predicted side, the
    measured side and the rival.
"""
import math
import os

import numpy as np

from battery_core import dump_results, record, run_groups

FRESH_TOKEN = "SIMCOV-BATTERY-BRIER01-LIABILITY-20260811"
LEAN_FILE = "PopGen/DGP.lean"

N_IND = 2000000
BLOCKS = 6
PREVALENCES = (0.01, 0.05, 0.20, 0.50)
R2_GRID = (0.05, 0.20, 0.50, 0.80)
SEED = 410041


def freshness():
    return FRESH_TOKEN


def _ndtr(x):
    from scipy.special import ndtr
    return ndtr(x)


def _ndtri(p):
    from scipy.special import ndtri
    return ndtri(p)


def orthant_both_cases(thr, r2):
    """P(both of two replicates sharing the score are cases), correlation r2.

    Computed from its MEANING -- two conditionally independent draws sharing the
    score component -- by direct grid quadrature over the shared score, rather
    than from a helper whose argument order would have to be assumed.
    """
    if r2 <= 0.0:
        return float((1.0 - _ndtr(thr)) ** 2)
    if r2 >= 1.0:
        return float(1.0 - _ndtr(thr))
    # A DIRECT GRID over the shared score rather than Gauss-Hermite: at the order
    # needed for six-figure accuracy `hermegauss` overflows computing its weights
    # and returns NaN, which then propagated silently -- see the guard below.
    z = np.linspace(-9.0, 9.0, 40001)
    dens = np.exp(-0.5 * z * z) / math.sqrt(2.0 * math.pi)
    g = z * math.sqrt(r2)
    cond = 1.0 - _ndtr((thr - g) / math.sqrt(1.0 - r2))
    return float(np.trapezoid(dens * cond ** 2, z))


def liability_brier_exact(prev, r2):
    """`liabilityBrierExact`: pi - E[p^2], E[p^2] the orthant."""
    thr = _ndtri(1.0 - prev)
    return prev - orthant_both_cases(thr, r2)


def calibrated_brier(prev, r2):
    """The linear chart -- correct on the OBSERVED scale, the rival here."""
    return prev * (1.0 - prev) * (1.0 - r2)


def check_quadrature():
    """The declaration's own closed form at pi = 1/2, before anything is recorded."""
    worst = 0.0
    for r2 in (0.05, 0.2, 0.5, 0.8):
        closed = 0.25 + math.asin(r2) / (2.0 * math.pi)
        mine = orthant_both_cases(0.0, r2)
        # NaN-SAFE ON PURPOSE. `max(0.0, nan)` returns 0.0 in Python, so a
        # quadrature returning NaN passed this check silently on the first run
        # and every cell came back NaN with the control reporting OK. A guard
        # that a broken input can slip through is not a guard.
        if not np.isfinite(mine):
            raise RuntimeError("quadrature returned non-finite at r2=%.2f" % r2)
        worst = max(worst, abs(mine - closed))
    if not np.isfinite(worst) or worst > 1e-9:
        raise RuntimeError("quadrature disagrees with the closed form at pi=1/2 "
                           "by %.3e; refusing to score a body against it" % worst)
    print("  quadrature vs Phi2(0,0;rho) = 1/4 + arcsin(rho)/2pi : "
          "worst |diff| %.2e -- OK" % worst)


def one_block(rng, prev, r2):
    thr = _ndtri(1.0 - prev)
    g = rng.standard_normal(N_IND) * math.sqrt(r2)
    e = rng.standard_normal(N_IND) * math.sqrt(1.0 - r2)
    # p_calib is the risk implied by the SCORE COMPONENT alone -- the calibrated
    # predictor the body is about. It is not the realised outcome and not a fit.
    p_calib = 1.0 - _ndtr((thr - g) / math.sqrt(1.0 - r2))
    y_event = ((g + e) > thr).astype(np.float64)
    return dict(brier=float(np.mean((p_calib - y_event) ** 2)),
                prev_realised=float(np.mean(y_event)),
                mean_p=float(np.mean(p_calib)))


def blocked(v):
    a = np.asarray(v, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


def group_brier():
    print("\n== liabilityBrierExact against a realised Brier risk")
    check_quadrature()
    rng = np.random.default_rng(SEED)
    cells, rival_cells, ctrl, skipped = [], [], [], []
    print("  %-22s %10s %10s %10s %9s %10s %9s"
          % ("cell", "exact", "realised", "chart", "floor", "separation", "readable"))
    for prev in PREVALENCES:
        for r2 in R2_GRID:
            blocks = [one_block(rng, prev, r2) for _ in range(BLOCKS)]
            meas, sem = blocked([b["brier"] for b in blocks])
            pred = liability_brier_exact(prev, r2)
            rival = calibrated_brier(prev, r2)
            floor = max(sem, 1e-12)
            sep = abs(pred - rival)
            lab = "prev=%.2f r2=%.2f" % (prev, r2)
            ok = sep > 3 * floor
            print("  %-22s %10.6f %10.6f %10.6f %9.6f %10.6f %9s"
                  % (lab, pred, meas, rival, floor, sep, "yes" if ok else "NO"))
            if not ok:
                skipped.append((lab, sep, floor))
                continue
            cells.append(dict(design=lab, lean=pred, truth=meas, sem=floor))
            rival_cells.append(dict(design=lab, lean=rival, truth=meas, sem=floor))
            pr, prsem = blocked([b["prev_realised"] for b in blocks])
            ctrl.append(dict(design="realised prevalence at " + lab,
                             lean=prev, truth=pr, sem=max(prsem, 1e-12)))

    if skipped:
        print("\n  CELLS EXCLUDED BY THE PRE-SET READABILITY RULE (the two bodies")
        print("  differ by less than three Monte-Carlo floors, so the cell cannot")
        print("  tell a line from a curve -- the anchor-point problem, mechanised):")
        for lab, sep, floor in skipped:
            print("    %-22s separation %.3e  floor %.3e" % (lab, sep, floor))

    reg = ("liability-threshold DGP: standard normal liability split into a score "
           "component of variance r2 and an independent residual, disease when the "
           "liability clears the prevalence threshold; %d individuals per block, %d "
           "blocks. The predictor is the calibrated risk implied by the SCORE "
           "component alone. THE MEASURED SIDE DRAWS THE ACTUAL OUTCOME and "
           "averages (p_calib - y_event)^2; it never forms E[p^2] analytically. "
           "The estimand is that unweighted per-individual mean, in squared-"
           "probability units. The predicted side evaluates the orthant by "
           "direct grid quadrature over the shared score on +/-9 sd, checked "
           "against the declaration's own closed form at pi=1/2 before any cell "
           "is scored and refusing to run if it disagrees or returns non-finite. "
           "Cells are admitted only where the two competing bodies differ by more "
           "than three Monte-Carlo floors, because they agree exactly at r2=0 and "
           "r2=1 and a cell between them discriminates nothing"
           % (N_IND, BLOCKS))
    control = ctrl[len(ctrl) // 2] if ctrl else None

    record("liabilityBrierExact", LEAN_FILE,
           "pi - bivariateNormalOrthant (Phi_inv pi) (Phi_inv pi) r2",
           cells, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="the measured side draws the outcome and averages (p-y)^2, so it "
                "is a different computation from the orthant rather than the same "
                "one twice")
    record("liabilityBrierExact [calibratedBrier's LINEAR chart, correct on the "
           "OBSERVED scale and used here on the liability scale, competing]",
           LEAN_FILE, "pi * (1 - pi) * (1 - r2)",
           rival_cells, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="this is the body #41 repairs: it is the linear chart through the "
                "same two anchor points, and the cells where it is separable from "
                "the curve are exactly the ones the anchor theorems could not see")


def main():
    print(freshness())
    failed = run_groups(group_brier)
    here = os.path.dirname(os.path.abspath(__file__))
    sha = dump_results(os.path.join(here, "battery_brier01_results.json"),
                       failed_groups=failed)
    print("\nbattery sha %s" % sha)


if __name__ == "__main__":
    main()
