#!/usr/bin/env python3
"""Q1: what fraction of the variance of an INDIVIDUAL squared prediction error
is explainable in principle by any function of covariates?

Wang, Lin, Zietz, Mares, Smith, Rathouz & Harpak, Nat Commun 17:942 (2026)
report that a cubic spline in genetic distance explains R^2 = 0.51% of the
individual squared prediction error for height, and that the Townsend
Deprivation Index explains a comparable 0.02-0.53%. The paper reads these as
comparably weak.

The outcome is a squared residual for ONE individual -- a single draw. Most of
its variance CAN be conditional noise that a distance-only predictor cannot
explain. This computes conditional model examples, not an empirical ceiling.
The residual moments must come from the same individual prediction and
residualization procedure. Bin-level partial R2 does not supply those moments.

THE DERIVATION
    Let r be the prediction residual for an individual with covariates x, and
    suppose r | x has mean 0, variance s2(x), and standardised fourth moment
    kappa = E[(r/s)^4 | x]. The outcome variable is r^2.

        E[r^2 | x]   = s2(x)
        Var(r^2 | x) = E[r^4|x] - (E[r^2|x])^2 = (kappa - 1) s2(x)^2

    By the law of total variance,

        Var(r^2) = E[(kappa-1) s2^2]  +  Var(s2)
                   \\____ irreducible ____/   \\__ explainable __/

    The BEST POSSIBLE predictor of r^2 from x is E[r^2 | x] = s2(x), so

        CEILING  =  Var(s2) / [ (kappa-1) E[s2^2] + Var(s2) ]

    Write s2(x) = s2bar (1 + delta(x)) with E[delta] = 0, Var(delta) = v^2.
    For Gaussian residuals (kappa = 3) this collapses to

        CEILING  =  v^2 / (2 + 3 v^2)

    which depends on NOTHING but the coefficient of variation of the
    conditional error variance. At v = 0.1 the ceiling is 0.49%; at v = 0.2 it
    is 1.9%; at v = 0.5 it is 9.1%. Heavier tails only lower it.

WHY THIS MATTERS
    If the ceiling is a couple of percent, then 0.51% is a large share of what
    is achievable rather than a negligible share of the total, and the paper's
    central comparison is between two numbers whose scale was never fixed. The
    irony is that this is the paper's own argument -- that R^2 depends on
    variation in the independent variable and can be arbitrarily small under a
    correct model -- applied to its own headline number.

HONEST IN BOTH DIRECTIONS
    The ceiling depends on v, and v is set by how much prediction accuracy
    actually varies across the genetic-distance range. If the observed decline
    in R^2 implies a LARGE v, the ceiling is high, genetic distance really is
    weak, and the paper is right as stated. The noise model is fixed BEFORE
    looking at where the answer lands, and both branches are reported.

    A scenario below 0.51% only shows that scenario does not reproduce the
    reported value. It does not identify bias, outcome heterogeneity, optimism,
    or any other empirical mechanism. The distributional assumptions and the
    connection between population and fitted R2 would first need validation.

CONTROLS PINNED BY THEORY
    C1  Homoscedastic null. With s2(x) constant, v = 0 and the ceiling is
        EXACTLY 0. Any R^2 a spline achieves there is pure overfitting, and it
        calibrates the finite-sample floor at the paper's n. Not fitted.
    C2  Oracle recovery. A predictor handed the TRUE s2(x) must achieve the
        analytic ceiling, up to Monte Carlo error. This checks the derivation
        against the simulator rather than asserting it.

Run: /projects/standard/hsiehph/sauer354/popgenv/bin/python q1_ceiling.py
or with the anaconda module; numpy only.
"""

import json
import sys

import numpy as np

N_PRED = 69_500          # Harpak et al. prediction-set size
REPS = 40
SEED = 20260802


def ceiling_analytic(v, kappa=3.0):
    """Var(s2) / [ (kappa-1) E[s2^2] + Var(s2) ] for s2 = s2bar (1 + delta)."""
    # E[s2^2] = s2bar^2 (1 + v^2);  Var(s2) = s2bar^2 v^2   (s2bar factors out)
    return v * v / ((kappa - 1.0) * (1.0 + v * v) + v * v)


def uniform_variance_scenario(r2_near, r2_far):
    """CV in a hypothetical uniform conditional-error-variance scenario.

    The substitution s2=1-R2 requires unit within-cell outcome variance and
    the corresponding within-cell optimal affine prediction. It cannot be
    applied automatically to a fixed deployed score or to partial R2 from a
    different residualization. A uniform law does not maximize CV on an interval.
    """
    lo, hi = 1.0 - r2_near, 1.0 - r2_far
    if not 0 < lo <= hi:
        raise ValueError("Require 0 < 1-r2_near <= 1-r2_far")
    mean = 0.5 * (lo + hi)
    sd = (hi - lo) / np.sqrt(12.0)
    return sd / mean


def simulate(v, n=N_PRED, reps=REPS, rng=None):
    """Empirical ceiling and the two controls, at the paper's sample size."""
    if not 0 <= v < 1 / np.sqrt(3.0):
        raise ValueError("Uniform conditional variances must stay strictly positive")
    rng = rng or np.random.default_rng(SEED)
    oracle_r2, null_r2 = [], []
    for _ in range(reps):
        # covariate x -> conditional error variance s2(x), CV = v
        x = rng.uniform(0.0, 1.0, n)
        s2 = 1.0 + v * np.sqrt(12.0) * (x - 0.5)      # uniform, CV = v exactly
        r = rng.normal(0.0, np.sqrt(s2))
        y = r * r

        # ORACLE predictor: the true conditional mean of y given x.
        pred = s2
        oracle_r2.append(1.0 - np.var(y - pred) / np.var(y))

        # NULL: same machinery, but s2 constant -> ceiling is exactly 0.
        r0 = rng.normal(0.0, 1.0, n)
        y0 = r0 * r0
        # a 5-df cubic spline in x, fit by least squares on the null
        B = np.vstack([np.ones(n), x, x ** 2, x ** 3,
                       np.clip(x - 0.5, 0, None) ** 3]).T
        beta, *_ = np.linalg.lstsq(B, y0, rcond=None)
        null_r2.append(1.0 - np.var(y0 - B @ beta) / np.var(y0))
    return (float(np.mean(oracle_r2)), float(np.std(oracle_r2) / np.sqrt(reps)),
            float(np.mean(null_r2)), float(np.std(null_r2) / np.sqrt(reps)))


def ceiling_with_bias(B, s2=1.0, kappa=3.0):
    """Ceiling when the residual MEAN also moves with x.

    The pure-variance derivation assumes E[r|x] = 0. If the score is
    miscalibrated in a distance-dependent way then E[r|x] = b(x) != 0 and

        E[r^2|x]   = b(x)^2 + s2
        Var(r^2|x) = 2 s2^2 + 4 b(x)^2 s2        (Gaussian r with mean b)

    so the EXPLAINABLE part gains Var(b^2), which is quartic in the bias and
    can dwarf the heteroscedastic channel. b(x) is taken with mean 0 and
    standard deviation B, uniform in x, so Var(b^2) = 0.8 B^4.
    """
    explainable = 0.8 * B ** 4
    irreducible = (kappa - 1.0) * s2 ** 2 + 4.0 * B ** 2 * s2
    return explainable / (irreducible + explainable)


def bias_needed_for(target, s2=1.0, kappa=3.0):
    """Bisect for the residual-mean spread B that reproduces `target` R^2."""
    lo, hi = 0.0, 5.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if ceiling_with_bias(mid, s2, kappa) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def main():
    rng = np.random.default_rng(SEED)
    out = {"paper": {"reported_spline_r2_height": 0.0051,
                     "reported_tdi_range": [0.0002, 0.0053],
                     "n_prediction": N_PRED}}

    # --- the ceiling as a function of the only parameter it depends on -----
    grid = []
    for v in (0.02, 0.05, 0.10, 0.15, 0.20, 0.30, 0.50):
        grid.append({"cv_of_conditional_variance": v,
                     "ceiling_gaussian": ceiling_analytic(v, 3.0),
                     "ceiling_kurtosis_6": ceiling_analytic(v, 6.0)})
    out["ceiling_vs_v"] = grid
    print("CEILING ON EXPLAINABLE VARIANCE OF AN INDIVIDUAL SQUARED RESIDUAL")
    print("  %-10s %-14s %-14s" % ("CV of s2", "ceiling(k=3)", "ceiling(k=6)"))
    for g in grid:
        print("  %-10.3f %-14.5f %-14.5f"
              % (g["cv_of_conditional_variance"], g["ceiling_gaussian"],
                 g["ceiling_kurtosis_6"]))

    # --- illustrative uniform-variance scenarios ----------------------------
    print("")
    print("HYPOTHETICAL UNIFORM VARIANCE SCENARIOS; NOT ESTIMATED COHORT MOMENTS")
    print("  %-22s %-8s %-10s %-12s %s"
          % ("trait scenario", "v", "ceiling", "reported", "reported/ceiling"))
    scen = [("height 0.15 -> 0.05", 0.15, 0.05, 0.0051),
            ("height 0.15 -> 0.10", 0.15, 0.10, 0.0051),
            ("strong decline 0.30 -> 0.05", 0.30, 0.05, 0.0051),
            ("weak decline 0.10 -> 0.08", 0.10, 0.08, 0.0051)]
    rows = []
    for name, a, b, rep in scen:
        v = uniform_variance_scenario(a, b)
        c = ceiling_analytic(v, 3.0)
        rows.append({"scenario": name, "r2_near": a, "r2_far": b,
                     "v_implied": v, "ceiling": c,
                     "reported_r2": rep,
                     "share_of_ceiling": rep / c if c > 0 else None})
        print("  %-22s %-8.4f %-10.5f %-12.4f %s"
              % (name, v, c, rep,
                 ("%.2f" % (rep / c)) if c > 0 else "n/a"))
    out["scenarios"] = rows

    # --- conditional bias examples, without empirical attribution ----------
    print("")
    print("THE SCENARIOS DO NOT IDENTIFY THE PAPER'S EMPIRICAL EXPLANATION")
    print("  Their moments and residualization have not been established for")
    print("  the paper's individual residuals. In-sample fitted R2 is also")
    print("  distinct from population oracle R2. The following bias examples")
    print("  assume a centered uniform bias and independent symmetric noise.")
    print("")
    print("  If the residual MEAN moves with distance -- a distance-dependent")
    print("  calibration bias rather than an accuracy loss -- the explainable")
    print("  part gains Var(b^2), quartic in the bias:")
    print("")
    print("  %-12s %-14s %-14s" % ("bias SD B", "ceiling", "(units of sd(y))"))
    bias_rows = []
    for B in (0.0, 0.05, 0.10, 0.20, 0.30, 0.40, 0.50):
        c = ceiling_with_bias(B)
        bias_rows.append({"bias_sd": B, "ceiling": c})
        print("  %-12.2f %-14.5f" % (B, c))
    B_needed = bias_needed_for(0.0051)
    print("")
    print("  Residual-mean spread required to produce R^2 = 0.51%%: B = %.4f"
          % B_needed)
    print("  i.e. bias SD %.2f in the model's unit residual-noise scale." % B_needed)
    out["bias_channel"] = {"rows": bias_rows,
                           "bias_sd_needed_for_reported": B_needed}

    # --- controls -----------------------------------------------------------
    print("")
    print("CONTROLS")
    v_test = 0.20
    o_m, o_s, n_m, n_s = simulate(v_test, rng=rng)
    analytic = ceiling_analytic(v_test, 3.0)
    c2_ok = abs(o_m - analytic) <= max(4 * o_s, 0.002)
    c1_ok = abs(n_m) <= 5e-4
    print("  C2 oracle recovers the analytic ceiling at v=%.2f: "
          "simulated %.5f +-%.5f vs analytic %.5f  -> %s"
          % (v_test, o_m, o_s, analytic, "PASS" if c2_ok else "FAIL"))
    print("  C1 homoscedastic null, 5-df spline at n=%d: R^2 = %.6f +-%.6f "
          "(ceiling is exactly 0) -> %s"
          % (N_PRED, n_m, n_s, "PASS" if c1_ok else "FAIL"))
    out["controls"] = {"oracle_simulated": o_m, "oracle_sem": o_s,
                       "oracle_analytic": analytic, "C2_pass": bool(c2_ok),
                       "null_spline_r2": n_m, "null_spline_sem": n_s,
                       "C1_pass": bool(c1_ok)}
    out["READ_THE_TEST"] = bool(c1_ok and c2_ok)

    print("")
    print("READ_THE_TEST: %s" % out["READ_THE_TEST"])
    fh = open("q1_ceiling_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> q1_ceiling_results.json")
    return 0 if out["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
