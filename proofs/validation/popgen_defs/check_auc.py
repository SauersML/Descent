"""Check the prevalence-free AUC charts in PortabilityDrift.lean.

    equalVarianceGaussianAUCFromSNR         snr   = Phi(sqrt(snr / 2))
    equalVarianceGaussianAUCFromSignalVariance vS vE
                                                  = Phi(sqrt(vS / (2 * vE)))
    equalVarianceGaussianAUCFromExplainedR2 r2    = Phi(sqrt(r2 / (2 * (1 - r2))))
    presentDayEqualVarianceGaussianAUC      ...   = Phi(sqrt(snr / 2))

None of these takes a disease prevalence.  Under the liability-threshold model
the AUC of a score against case/control status depends on prevalence, because
cases are a truncated tail of the liability distribution and the truncation
point sets how far the case and control score distributions separate.

Ground truth here is the exact AUC = P(S_case > S_control) computed two ways:
Gauss-Legendre integration of the bivariate normal, and a large Monte Carlo.

RESOLVED.  These four were named `liabilityAUCFrom*` and `presentDayAUC` when
this check was written, and the run reported below is what retired those names:
RMSE 0.1199 over 25 cells against the exact bivariate-normal AUC, every cell
biased low, worst at R2 = 0.20 and prevalence 0.001 where the exact AUC is
0.8686 and the chart returns 0.6382, 26.5 per cent low.  The charts are correct
for the equal-variance Gaussian model and were renamed to it; the binary-trait
formula the old names promised is `liabilityThresholdAUCFromExplainedR2`, which
takes prevalence and measures at pooled RMSE 0.0121.  Keep running this: it is
the instrument that holds the equal-variance charts to the model they now name,
and its failure against the liability-threshold oracle is the expected result,
not a regression.
"""
from __future__ import annotations

import json
import sys

import numpy as np
from scipy import stats, integrate

Phi = stats.norm.cdf
phi = stats.norm.pdf


def lean_equalVarianceGaussianAUCFromExplainedR2(r2):
    """equalVarianceGaussianAUCFromExplainedR2
    `Phi (Real.sqrt (r2 / (2 * (1 - r2))))`"""
    return float(Phi(np.sqrt(r2 / (2 * (1 - r2)))))


def lean_equalVarianceGaussianAUCFromSNR(snr):
    """equalVarianceGaussianAUCFromSNR
    `Phi (Real.sqrt (snr / 2))`"""
    return float(Phi(np.sqrt(snr / 2)))


def exact_auc(rho, K):
    """AUC of score S (corr rho with liability L) for cases L > T, P(L>T)=K.

    P(S_case > S_ctrl) = E_{s}[ f_case(s) * F_ctrl(s) ] integrated exactly.
    S ~ N(0,1) marginally; density of S among cases is
        f_case(s) = phi(s) * P(L > T | S=s) / K,
    with L | S=s ~ N(rho s, 1 - rho^2).
    """
    T = stats.norm.isf(K)
    sd = np.sqrt(1 - rho**2)

    def p_case_given_s(s):
        return stats.norm.sf((T - rho * s) / sd)

    def f_case(s):
        return phi(s) * p_case_given_s(s) / K

    def f_ctrl(s):
        return phi(s) * (1 - p_case_given_s(s)) / (1 - K)

    # F_ctrl(s) via cumulative integration on a fine grid, then integrate
    grid = np.linspace(-9, 9, 20001)
    fc = f_ctrl(grid)
    Fctrl = integrate.cumulative_trapezoid(fc, grid, initial=0.0)
    Fctrl /= Fctrl[-1]
    return float(np.trapezoid(f_case(grid) * Fctrl, grid))


def mc_auc(rho, K, seed, n=4_000_000):
    rng = np.random.default_rng(seed)
    s = rng.standard_normal(n)
    l = rho * s + np.sqrt(1 - rho**2) * rng.standard_normal(n)
    T = stats.norm.isf(K)
    case = s[l > T]
    ctrl = s[l <= T]
    m = min(len(case), len(ctrl), 400_000)
    if m < 1000:
        return float("nan")
    a = rng.choice(case, m, replace=False)
    b = rng.choice(ctrl, m, replace=False)
    return float((a > b).mean() + 0.5 * (a == b).mean())


def main():
    rows = []
    for r2 in (0.01, 0.05, 0.1, 0.2, 0.3):
        rho = np.sqrt(r2)
        for K in (0.5, 0.2, 0.05, 0.01, 0.001):
            rows.append(dict(
                r2=r2, K=K,
                exact=exact_auc(rho, K),
                mc=mc_auc(rho, K, seed=7 + int(r2 * 1000) + int(K * 10000)),
                lean_fromR2=lean_equalVarianceGaussianAUCFromExplainedR2(r2),
                lean_fromSNR=lean_equalVarianceGaussianAUCFromSNR(r2 / (1 - r2)),
            ))
    with open(sys.argv[1] if len(sys.argv) > 1 else "auc.json", "w") as fh:
        json.dump(rows, fh)

    print(f"{'R2':>6} {'K':>7} {'exact AUC':>10} {'MC':>9} {'lean':>9} {'err%':>8}")
    for r in rows:
        e = 100 * (r["lean_fromR2"] - r["exact"]) / r["exact"]
        print(f"{r['r2']:6.2f} {r['K']:7.3f} {r['exact']:10.4f} {r['mc']:9.4f} "
              f"{r['lean_fromR2']:9.4f} {e:8.1f}")


if __name__ == "__main__":
    main()
