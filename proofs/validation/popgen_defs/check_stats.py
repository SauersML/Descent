"""Round 3: statistical definitions in PowerAnalysis / StratificationConfounding.

These are cheap to check to high precision -- exact numerical integration where
a closed form exists, Monte Carlo where it does not -- so the error bars are far
tighter than the coalescent checks.
"""
from __future__ import annotations

import json
import os
import sys

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "4"

import numpy as np  # noqa: E402
from scipy import stats  # noqa: E402

Phi = stats.norm.cdf
phi = stats.norm.pdf


# --------------------------------------------------------------------------
# Lean definitions, transcribed literally
# --------------------------------------------------------------------------

def lean_approxPower(ncp):
    """PowerAnalysis.lean:74  `1 - Real.exp (-ncp / 2)`"""
    return 1 - np.exp(-ncp / 2)


def lean_truncationBias(se, beta, z_alpha):
    """PowerAnalysis.lean:215
    `se * Real.exp (-(z_alpha - beta / se)^2 / 2) / Real.sqrt (2 * Real.pi)`"""
    return se * np.exp(-((z_alpha - beta / se) ** 2) / 2) / np.sqrt(2 * np.pi)


def lean_winnersCurseInflation(true_beta, sigma, n):
    """PowerAnalysis.lean:389  `true_beta + sigma / Real.sqrt n`"""
    return true_beta + sigma / np.sqrt(n)


def lean_r2EstimatorVariance(r2, n):
    """StratificationConfounding.lean:629  `4 * r2 * (1 - r2) ^ 2 / n`"""
    return 4 * r2 * (1 - r2) ** 2 / n


def lean_noncentralityParam(n, beta, p):
    """PowerAnalysis.lean:38  `n * beta^2 * (2 * p * (1 - p))`"""
    return n * beta**2 * (2 * p * (1 - p))


# --------------------------------------------------------------------------
# exact truths
# --------------------------------------------------------------------------

def exact_power_twosided(ncp, alpha):
    """P(chi2_1(ncp) > crit) -- the actual power of the Wald test."""
    crit = stats.chi2.ppf(1 - alpha, 1)
    return float(stats.ncx2.sf(crit, 1, ncp))


def exact_power_onesided_normal(ncp, alpha):
    """Phi(sqrt(ncp) - z_alpha): the approximation the docstring calls 'true'."""
    z = stats.norm.isf(alpha / 2)
    return float(Phi(np.sqrt(ncp) - z))


def exact_truncbias_twosided(se, beta, z):
    """E[eps | |beta+eps| > z*se], eps ~ N(0, se^2).  Matches `isSelected`."""
    b = beta / se
    num = phi(z - b) - phi(z + b)
    den = Phi(b - z) + Phi(-b - z)
    return float(se * num / den)


def exact_truncbias_onesided(se, beta, z):
    """E[eps | beta+eps > z*se] -- the formula quoted in the docstring."""
    b = beta / se
    return float(se * phi(z - b) / Phi(b - z))


def mc_truncbias(se, beta, z, seed, n=20_000_000):
    """Monte Carlo cross-check of the two-sided conditional mean."""
    rng = np.random.default_rng(seed)
    eps = rng.normal(0, se, size=n)
    sel = np.abs(beta + eps) > z * se
    if sel.sum() < 500:
        return float("nan"), int(sel.sum())
    return float(eps[sel].mean()), int(sel.sum())


def mc_r2_variance(r2, n, reps, seed):
    """Var of the plug-in R^2 estimator from a simple bivariate regression."""
    rng = np.random.default_rng(seed)
    rho = np.sqrt(r2)
    x = rng.standard_normal((reps, n))
    e = rng.standard_normal((reps, n))
    y = rho * x + np.sqrt(1 - r2) * e
    x -= x.mean(axis=1, keepdims=True)
    y -= y.mean(axis=1, keepdims=True)
    num = (x * y).sum(axis=1) ** 2
    den = (x * x).sum(axis=1) * (y * y).sum(axis=1)
    r2hat = num / den
    return float(r2hat.var()), float(r2hat.mean())


def mc_ncp(n, beta, p, reps, seed):
    """Mean chi-square statistic from an actual genotype regression = 1 + NCP."""
    rng = np.random.default_rng(seed)
    stats_out = np.empty(reps)
    for i in range(reps):
        g = rng.binomial(2, p, size=n).astype(float)
        y = beta * g + rng.standard_normal(n)
        gc = g - g.mean()
        yc = y - y.mean()
        sxx = (gc * gc).sum()
        if sxx <= 0:
            stats_out[i] = np.nan
            continue
        b = (gc * yc).sum() / sxx
        resid = yc - b * gc
        s2 = (resid**2).sum() / (n - 2)
        stats_out[i] = b**2 / (s2 / sxx)
    return float(np.nanmean(stats_out) - 1)


def main():
    out = {}

    # ---- approxPower ----
    rows = []
    for alpha, label in ((0.05, "alpha=0.05"), (5e-8, "GWAS alpha=5e-8")):
        for ncp in (1, 2, 5, 10, 20, 30, 50):
            rows.append(dict(alpha=alpha, label=label, ncp=ncp,
                             exact_chi2=exact_power_twosided(ncp, alpha),
                             docstring_normal=exact_power_onesided_normal(ncp, alpha),
                             lean=lean_approxPower(ncp)))
    out["approxPower"] = rows

    # ---- truncationBias ----
    rows = []
    for z in (1.96, 5.45):
        for b in (0.0, 0.5, 1.0, 2.0, 4.0, 6.0):
            se = 1.0
            beta = b * se
            mc, nsel = (mc_truncbias(se, beta, z, seed=17 + int(b * 10))
                        if z < 3 else (float("nan"), 0))
            rows.append(dict(z=z, beta_over_se=b, se=se,
                             lean=lean_truncationBias(se, beta, z),
                             exact_twosided=exact_truncbias_twosided(se, beta, z),
                             exact_onesided=exact_truncbias_onesided(se, beta, z),
                             mc_twosided=mc, n_selected=nsel))
    out["truncationBias"] = rows

    # ---- winnersCurseInflation ----
    rows = []
    for z in (1.96, 5.45):
        for b in (0.0, 0.5, 1.0, 2.0, 4.0):
            se = 1.0
            rows.append(dict(z=z, beta_over_se=b,
                             lean=lean_winnersCurseInflation(b * se, se, 1),
                             exact_selected_mean=b * se
                             + exact_truncbias_twosided(se, b * se, z)))
    out["winnersCurseInflation"] = rows

    # ---- r2EstimatorVariance ----
    rows = []
    for r2 in (0.01, 0.05, 0.2, 0.5):
        for n in (200, 1000, 5000):
            v, mean = mc_r2_variance(r2, n, reps=40000, seed=3 + n + int(r2 * 100))
            rows.append(dict(r2=r2, n=n, mc_var=v, mc_mean=mean,
                             lean=lean_r2EstimatorVariance(r2, n)))
    out["r2EstimatorVariance"] = rows

    # ---- noncentralityParam ----
    rows = []
    for p in (0.05, 0.2, 0.5):
        for beta in (0.05, 0.1):
            n = 4000
            rows.append(dict(n=n, beta=beta, p=p,
                             mc=mc_ncp(n, beta, p, reps=3000, seed=99 + int(p * 100)),
                             lean=lean_noncentralityParam(n, beta, p)))
    out["noncentralityParam"] = rows

    with open(sys.argv[1] if len(sys.argv) > 1 else "stats.json", "w") as fh:
        json.dump(out, fh)
    print("done")


if __name__ == "__main__":
    main()
