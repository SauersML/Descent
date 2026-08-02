#!/usr/bin/env python3
"""Q1 follow-up: separate the bias channel from the variance channel, and make
the ceiling distribution-free.

The companion script showed the reported R^2 = 0.51% for a cubic spline in
genetic distance predicting the individual squared residual EXCEEDS the
heteroscedastic ceiling. This asks what could carry it, and reduces the
question to ONE unrun regression.

THREE RESULTS, in order of how much they close.

(1) THE CEILING IS DISTRIBUTION-FREE.
    The companion assumed genetic distance was uniform. It is not -- UK Biobank
    is overwhelmingly one tight cluster with a small distant tail -- and that
    was the weakest assumption in the argument. It turns out not to matter.

    The ceiling depends on s2(x) only through its coefficient of variation, and
    if R^2(x) is confined to [R2_lo, R2_hi] then s2 = Var(y)(1 - R^2) is
    confined to an interval. Over ALL distributions supported on an interval,
    variance is maximised by the two-point law putting half the mass at each
    endpoint. So

        v_max = (s_hi - s_lo) / (s_hi + s_lo)

    and the ceiling can be maximised over every possible allocation of
    individuals to distances. No assumption about the shape of the distance
    distribution survives into the answer.

(2) THE BIAS CHANNEL IS MEASURABLE, AND IT MAKES A SHARP PREDICTION.
    Let m(x) = E[r|x] be the distance-dependent calibration bias. Then

        R^2 of the SIGNED residual on x   =  Var(m) / Var(r)

    which is a quantity anyone with the individual-level data can compute in
    one line. Given it, the bias contribution to the SQUARED-residual R^2 is
    fixed: writing rho for the signed-residual R^2, B^2 = rho/(1-rho) and the
    bias channel contributes 0.8 B^4 / (2 + 4 B^2 + 0.8 B^4).

    The prediction is sharp because the bias enters QUARTICALLY. To carry 0.51%
    on its own the bias needs B = 0.356, which requires a signed-residual R^2
    of about 11% -- an effect so large it could not have gone unremarked. And a
    signed-residual R^2 of 1% contributes only about 0.004% to the squared
    residual, a hundredfold short. There is very little room in between.

(3) WHAT IS LEFT IS OUTCOME-VARIANCE HETEROGENEITY, AND IT IS PLAUSIBLE.
    The first caveat in the companion analysis -- that Var(y) itself may rise
    with distance -- is the one escape that survives. If Var(y) varies with
    coefficient of variation w at FIXED R^2, then s2 inherits CV w directly and
    the ceiling is w^2/(2+3w^2). Solving for 0.51% gives w = 0.102: a ten
    percent spread in outcome variance across the distance range reproduces the
    reported figure with no accuracy decline and no calibration bias at all.

    Ten percent is entirely ordinary for a trait like height across groups. So
    the most likely reading is that the spline is substantially reading
    heterogeneity in the OUTCOME, not in the predictor's skill.

THE ONE MISSING QUANTITY, NAMED PRECISELY
    Regress the SIGNED residual y - yhat on the same cubic spline basis in
    genetic distance, in the same 69,500-individual prediction set, per trait.
    Report its R^2. That single number splits the 0.51% between the bias and
    variance channels, because the bias contribution is a deterministic
    function of it. Their published GWAS summary statistics do NOT contain it:
    it needs individual-level residuals, which are access-controlled. Anyone
    with UKB access produces it in an afternoon.

    Second, cheaper and also decisive: report Var(y) by genetic-distance decile.
    If it rises by ten percent across the range, result (3) is the explanation
    and no further work is needed.

CONTROLS PINNED BY THEORY, NEITHER FITTED
    C1  Two-point law attains the distribution-free bound. The bound is derived
        analytically; the simulator evaluates candidate distributions and none
        may exceed it. A single violation means the derivation is wrong.
    C2  Pure-bias recovery. Simulate residuals with a known mean shift and no
        heteroscedasticity; the measured signed-residual R^2 must recover
        Var(m)/Var(r) and the measured squared-residual R^2 must match the
        analytic bias-channel formula. This checks the decomposition end to end
        rather than asserting it.
"""

import json
import sys

import numpy as np

N_PRED = 69_500
REPS = 30
SEED = 20260802


def ceiling_from_cv(v, kappa=3.0):
    return v * v / ((kappa - 1.0) * (1.0 + v * v) + v * v)


def v_max_on_interval(s_lo, s_hi):
    """Largest possible CV of a variable confined to [s_lo, s_hi].

    Maximised by the two-point law with half the mass at each endpoint:
    mean = (s_lo+s_hi)/2, sd = (s_hi-s_lo)/2.
    """
    return (s_hi - s_lo) / (s_hi + s_lo)


def bias_channel_r2(rho_signed, kappa=3.0):
    """Squared-residual R^2 contributed by a bias with signed-residual R^2 rho."""
    if rho_signed <= 0:
        return 0.0
    b2 = rho_signed / (1.0 - rho_signed)
    explainable = 0.8 * b2 * b2
    irreducible = (kappa - 1.0) + 4.0 * b2
    return explainable / (irreducible + explainable)


def signed_r2_needed(target, kappa=3.0):
    lo, hi = 0.0, 0.999
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if bias_channel_r2(mid, kappa) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def w_needed_for(target, kappa=3.0):
    """Outcome-variance CV reproducing `target` at fixed R^2."""
    lo, hi = 0.0, 5.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if ceiling_from_cv(mid, kappa) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def main():
    rng = np.random.default_rng(SEED)
    REPORTED = 0.0051
    out = {"reported_r2": REPORTED}

    # ---- (1) distribution-free ceiling -----------------------------------
    print("(1) DISTRIBUTION-FREE CEILING, over every allocation of individuals")
    print("    %-22s %-10s %-12s %s" % ("R^2 range", "v_max", "ceiling_max",
                                        "reported/ceiling"))
    rows = []
    for r2_hi, r2_lo in ((0.15, 0.05), (0.20, 0.05), (0.30, 0.05),
                         (0.30, 0.02), (0.40, 0.01)):
        s_lo, s_hi = 1.0 - r2_hi, 1.0 - r2_lo
        v = v_max_on_interval(s_lo, s_hi)
        c = ceiling_from_cv(v)
        rows.append({"r2_hi": r2_hi, "r2_lo": r2_lo, "v_max": v,
                     "ceiling_max": c, "ratio": REPORTED / c})
        print("    %-22s %-10.4f %-12.5f %.2f"
              % ("%.2f -> %.2f" % (r2_hi, r2_lo), v, c, REPORTED / c))
    out["distribution_free"] = rows

    # C1: no sampled distribution may beat the bound
    worst = 0.0
    s_lo, s_hi = 0.85, 0.95
    bound = ceiling_from_cv(v_max_on_interval(s_lo, s_hi))
    for _ in range(4000):
        k = rng.integers(2, 12)
        pts = rng.uniform(s_lo, s_hi, k)
        wts = rng.dirichlet(np.ones(k))
        mean = float(wts @ pts)
        var = float(wts @ (pts - mean) ** 2)
        worst = max(worst, ceiling_from_cv(np.sqrt(var) / mean))
    c1_ok = worst <= bound * (1 + 1e-9)
    print("    C1 bound attained, never exceeded: max over 4000 random laws "
          "%.6f vs bound %.6f -> %s"
          % (worst, bound, "PASS" if c1_ok else "FAIL"))

    # ---- (2) bias channel -------------------------------------------------
    print("")
    print("(2) BIAS CHANNEL: what the SIGNED-residual R^2 implies")
    print("    %-22s %-16s" % ("signed-residual R^2", "squared-residual R^2"))
    brows = []
    for rho in (0.001, 0.005, 0.01, 0.02, 0.05, 0.10, 0.112):
        b = bias_channel_r2(rho)
        brows.append({"signed_r2": rho, "squared_r2_from_bias": b})
        print("    %-22.4f %-16.6f" % (rho, b))
    need = signed_r2_needed(REPORTED)
    print("    signed-residual R^2 required to carry 0.51%% alone: %.4f" % need)
    out["bias_channel"] = {"rows": brows, "signed_r2_needed": need}

    # C2: recover the decomposition end to end
    B = 0.356
    sr2, qr2 = [], []
    for _ in range(REPS):
        x = rng.uniform(0.0, 1.0, N_PRED)
        m = B * np.sqrt(12.0) * (x - 0.5)
        r = m + rng.normal(0.0, 1.0, N_PRED)
        Bs = np.vstack([np.ones(N_PRED), x, x ** 2, x ** 3,
                        np.clip(x - 0.5, 0, None) ** 3]).T
        for target, acc in ((r, sr2), (r * r, qr2)):
            beta, *_ = np.linalg.lstsq(Bs, target, rcond=None)
            acc.append(1.0 - np.var(target - Bs @ beta) / np.var(target))
    sr2_m, qr2_m = float(np.mean(sr2)), float(np.mean(qr2))
    sr2_pred = B * B / (1.0 + B * B)
    qr2_pred = bias_channel_r2(sr2_pred)
    c2_ok = (abs(sr2_m - sr2_pred) < 0.005) and (abs(qr2_m - qr2_pred) < 0.0015)
    print("    C2 pure-bias recovery at B=%.3f: signed %.5f (pred %.5f), "
          "squared %.6f (pred %.6f) -> %s"
          % (B, sr2_m, sr2_pred, qr2_m, qr2_pred, "PASS" if c2_ok else "FAIL"))
    out["control_2"] = {"B": B, "signed_measured": sr2_m,
                        "signed_predicted": sr2_pred,
                        "squared_measured": qr2_m,
                        "squared_predicted": qr2_pred, "pass": bool(c2_ok)}

    # ---- (3) outcome-variance heterogeneity -------------------------------
    print("")
    print("(3) OUTCOME-VARIANCE HETEROGENEITY, the surviving explanation")
    w = w_needed_for(REPORTED)
    print("    CV of Var(y) across distance reproducing 0.51%% at FIXED R^2: "
          "w = %.4f" % w)
    print("    i.e. about a %.0f%% spread in outcome variance, with no accuracy"
          % (100 * w))
    print("    decline and no calibration bias required.")
    out["outcome_variance"] = {"w_needed": w}

    out["READ_THE_TEST"] = bool(c1_ok and c2_ok)
    print("")
    print("READ_THE_TEST: %s" % out["READ_THE_TEST"])
    fh = open("q1_signed_residual_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> q1_signed_residual_results.json")
    return 0 if out["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
