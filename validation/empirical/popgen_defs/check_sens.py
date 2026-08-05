"""Check `liabilitySensitivity` / `liabilitySpecificity` (ClinicalUtilityFairness).

    liabilitySensitivity Phi m R2 T' =
      Phi ((sqrt R2 * sqrt h_sq * case_mean - T') / sqrt (h_sq*(1-R2) + (1-h_sq)))

Writing rho = sqrt(R2 * h_sq) for the score-liability correlation, this is
P(S > T' | L = mu_case): the conditional exceedance probability evaluated AT the
mean case liability.  The sensitivity is P(S > T' | L > T), which averages that
conditional probability over the case liability distribution.  Phi is nonlinear,
so by Jensen these differ.  Both docstrings say "Exact".

Ground truth: numerical integration over the case/control liability densities,
cross-checked by Monte Carlo.
"""
from __future__ import annotations

import json
import sys

import numpy as np
from scipy import stats

Phi = stats.norm.cdf
phi = stats.norm.pdf


def lean_sensitivity(R2, h_sq, case_mean, Tprime):
    R = np.sqrt(R2)
    h = np.sqrt(h_sq)
    sd = np.sqrt(h_sq * (1 - R2) + (1 - h_sq))
    return float(Phi((R * h * case_mean - Tprime) / sd))


def exact_sensitivity(rho, K, Tprime):
    """P(S > T' | L > T) with (S, L) standard bivariate normal, corr rho."""
    T = stats.norm.isf(K)
    grid = np.linspace(T, T + 12, 40001)
    dens = phi(grid)                       # unnormalized case liability density
    cond = stats.norm.sf((Tprime - rho * grid) / np.sqrt(1 - rho**2))
    return float(np.trapezoid(dens * cond, grid) / np.trapezoid(dens, grid))


def exact_specificity(rho, K, Tprime):
    T = stats.norm.isf(K)
    grid = np.linspace(T - 12, T, 40001)
    dens = phi(grid)
    cond = stats.norm.cdf((Tprime - rho * grid) / np.sqrt(1 - rho**2))
    return float(np.trapezoid(dens * cond, grid) / np.trapezoid(dens, grid))


def mc(rho, K, Tprime, seed, n=8_000_000):
    rng = np.random.default_rng(seed)
    s = rng.standard_normal(n)
    l = rho * s + np.sqrt(1 - rho**2) * rng.standard_normal(n)
    T = stats.norm.isf(K)
    case = l > T
    return (float((s[case] > Tprime).mean()),
            float((s[~case] <= Tprime).mean()))


def main():
    rows = []
    for K in (0.2, 0.05, 0.01):
        T = stats.norm.isf(K)
        case_mean = float(phi(T) / K)             # E[L | L > T]
        ctrl_mean = float(-phi(T) / (1 - K))
        for h_sq in (0.5,):
            for R2 in (0.05, 0.2, 0.5):
                rho = np.sqrt(R2 * h_sq)
                for Tprime in (0.0, 1.0, 2.0):
                    mc_sens, mc_spec = mc(rho, K, Tprime,
                                          seed=3 + int(K * 1000) + int(R2 * 100)
                                          + int(Tprime))
                    rows.append(dict(
                        K=K, h_sq=h_sq, R2=R2, Tprime=Tprime,
                        case_mean=case_mean, ctrl_mean=ctrl_mean,
                        exact_sens=exact_sensitivity(rho, K, Tprime),
                        mc_sens=mc_sens,
                        lean_sens=lean_sensitivity(R2, h_sq, case_mean, Tprime),
                        exact_spec=exact_specificity(rho, K, Tprime),
                        mc_spec=mc_spec,
                    ))
    with open(sys.argv[1] if len(sys.argv) > 1 else "sens.json", "w") as fh:
        json.dump(rows, fh)

    print(f"{'K':>6} {'R2':>5} {chr(84)+chr(39):>5} {'exact sens':>11} {'MC':>8} "
          f"{'lean':>8} {'err%':>8}")
    for r in rows:
        e = 100 * (r["lean_sens"] - r["exact_sens"]) / r["exact_sens"]
        print(f"{r['K']:6.2f} {r['R2']:5.2f} {r['Tprime']:5.1f} "
              f"{r['exact_sens']:11.4f} {r['mc_sens']:8.4f} {r['lean_sens']:8.4f} "
              f"{e:8.1f}")


if __name__ == "__main__":
    main()
