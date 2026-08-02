"""A battery of fast checks -- exact numerics and small Monte Carlo only.

No coalescent simulation: every check here runs in well under a second, which
is where the yield per CPU-second turned out to be.  Each entry states the Lean
source, the transcribed formula, and an independent ground truth.
"""
from __future__ import annotations

import json
import sys

import numpy as np
from scipy import stats

Phi = stats.norm.cdf
phi = stats.norm.pdf
RES = []


def report(name, source, lean, truth, params, note=""):
    rel = abs(lean - truth) / abs(truth) if truth not in (0, None) and np.isfinite(truth) else float("nan")
    RES.append(dict(name=name, source=source, lean=float(lean),
                    truth=float(truth), rel=float(rel), params=params, note=note))


# --------------------------------------------------------------------------
# 1. ppv / metricPPV  (Bayes; should be exact)
# --------------------------------------------------------------------------
def check_ppv(rng):
    for prev, sens, spec in [(0.01, 0.9, 0.9), (0.1, 0.8, 0.95), (0.3, 0.7, 0.7)]:
        fpr = 1 - spec
        lean = prev * sens / (prev * sens + (1 - prev) * fpr)
        n = 4_000_000
        d = rng.random(n) < prev
        pos = np.where(d, rng.random(n) < sens, rng.random(n) < fpr)
        truth = float(d[pos].mean())
        report("ppv", "ClinicalUtilityFairness.lean:699", lean, truth,
               dict(prev=prev, sens=sens, spec=spec))


# --------------------------------------------------------------------------
# 2. proportionCorrectlyClassified = sens*prev + spec*(1-prev)
# --------------------------------------------------------------------------
def check_pcc(rng):
    for prev, sens, spec in [(0.01, 0.9, 0.9), (0.2, 0.75, 0.85)]:
        lean = sens * prev + spec * (1 - prev)
        n = 2_000_000
        d = rng.random(n) < prev
        pos = np.where(d, rng.random(n) < sens, rng.random(n) < (1 - spec))
        truth = float((pos == d).mean())
        report("proportionCorrectlyClassified", "ClinicalUtilityFairness.lean:805",
               lean, truth, dict(prev=prev, sens=sens, spec=spec))


# --------------------------------------------------------------------------
# 3. numberNeededToScreen = 1/(sens*prev)
# --------------------------------------------------------------------------
def check_nns(rng):
    for prev, sens in [(0.01, 0.9), (0.05, 0.6)]:
        lean = 1 / (sens * prev)
        n = 4_000_000
        d = rng.random(n) < prev
        detected = d & (rng.random(n) < sens)
        truth = float(n / detected.sum())
        report("numberNeededToScreen", "ClinicalUtilityFairness.lean:951",
               lean, truth, dict(prev=prev, sens=sens))


# --------------------------------------------------------------------------
# 4. fisherAverageEffect a + d(1-2p): the average effect of substitution
# --------------------------------------------------------------------------
def check_fisher_alpha(rng):
    for a, d_, p in [(1.0, 0.5, 0.3), (1.0, -0.4, 0.7), (2.0, 1.0, 0.5)]:
        lean = a + d_ * (1 - 2 * p)
        n = 2_000_000
        g = rng.binomial(2, p, size=n)
        # genotypic values: -a, d, +a for 0, 1, 2 copies
        gv = np.where(g == 0, -a, np.where(g == 1, d_, a))
        # average effect = regression slope of genotypic value on dosage
        truth = float(np.cov(g, gv)[0, 1] / np.var(g))
        report("fisherAverageEffect", "EpistasisAndNonAdditivity.lean:69",
               lean, truth, dict(a=a, d=d_, p=p))


# --------------------------------------------------------------------------
# 5. effectivePolygenicity = (sum b^2)^2 / sum b^4  (participation ratio)
# --------------------------------------------------------------------------
def check_effective_polygenicity(rng):
    for M, frac in [(1000, 1.0), (1000, 0.1), (1000, 0.01)]:
        b = np.zeros(M)
        k = max(1, int(M * frac))
        b[:k] = rng.standard_normal(k)
        lean = (b**2).sum() ** 2 / (b**4).sum()
        # ground truth: for k equal-effect loci the participation ratio is k
        b_eq = np.zeros(M)
        b_eq[:k] = 1.0
        truth_eq = (b_eq**2).sum() ** 2 / (b_eq**4).sum()
        report("effectivePolygenicity", "PolygenicArchitecture.lean:103",
               truth_eq, float(k), dict(M=M, k=k),
               "equal-effect case must return exactly k")


# --------------------------------------------------------------------------
# 6. narrowSenseH2 = V_A/(V_A+V_D+V_I+V_E)
# --------------------------------------------------------------------------
def check_h2(rng):
    for V_A, V_D, V_E in [(0.4, 0.1, 0.5), (0.2, 0.05, 0.75)]:
        lean = V_A / (V_A + V_D + 0.0 + V_E)
        n = 2_000_000
        A = rng.standard_normal(n) * np.sqrt(V_A)
        D = rng.standard_normal(n) * np.sqrt(V_D)
        E = rng.standard_normal(n) * np.sqrt(V_E)
        P = A + D + E
        truth = float(np.var(A) / np.var(P))
        report("narrowSenseH2", "VarianceComponents.lean:39", lean, truth,
               dict(V_A=V_A, V_D=V_D, V_E=V_E))


# --------------------------------------------------------------------------
# 7. reliabilityRatio / pgsAttenuationFactor = sqrt(r2)
#    regression dilution: slope of y on a noisy proxy
# --------------------------------------------------------------------------
def check_attenuation(rng):
    # The PGS must explain exactly r2 of the PHENOTYPE variance, i.e.
    # corr(pgs, y) = sqrt(r2).  Building it as a noisy copy of a liability that
    # is itself a noisy predictor of y applies the attenuation twice.
    for r2 in (0.05, 0.2, 0.5):
        lean = np.sqrt(r2)
        n = 2_000_000
        pgs = rng.standard_normal(n)
        y = np.sqrt(r2) * pgs + np.sqrt(1 - r2) * rng.standard_normal(n)
        y = (y - y.mean()) / y.std()
        truth = float(np.cov(pgs, y)[0, 1] / np.var(pgs))
        report("pgsAttenuationFactor", "StratificationConfounding.lean:436",
               lean, truth, dict(r2=r2),
               "slope of phenotype on the standardized PGS")


# --------------------------------------------------------------------------
# 8. calibratedBrier = pi(1-pi)(1-r2)
# --------------------------------------------------------------------------
def check_brier(rng):
    for pi_, r2 in [(0.1, 0.2), (0.3, 0.5)]:
        lean = pi_ * (1 - pi_) * (1 - r2)
        n = 4_000_000
        # Use a Beta with the exact mean pi and variance r2*pi*(1-pi); this
        # stays inside (0,1) by construction, so no clipping distorts it.
        target_var = r2 * pi_ * (1 - pi_)
        conc = pi_ * (1 - pi_) / target_var - 1          # a + b
        a, b = pi_ * conc, (1 - pi_) * conc
        p = rng.beta(a, b, size=n)
        y = rng.random(n) < p
        truth = float(np.mean((y - p) ** 2))
        report("calibratedBrier", "DGP.lean:2048", lean, truth,
               dict(pi=pi_, r2=r2), "beta-distributed p, no clipping")


def main():
    rng = np.random.default_rng(12345)
    for fn in (check_ppv, check_pcc, check_nns, check_fisher_alpha,
               check_effective_polygenicity, check_h2, check_attenuation,
               check_brier):
        try:
            fn(rng)
        except Exception as e:  # keep the battery running
            print(f"  [{fn.__name__} failed: {e}]")

    with open(sys.argv[1] if len(sys.argv) > 1 else "quick.json", "w") as fh:
        json.dump(RES, fh)

    print(f"{'definition':<32} {'lean':>10} {'truth':>10} {'rel err':>9}  params")
    for r in RES:
        flag = "  <-- CHECK" if r["rel"] > 0.02 else ""
        ps = " ".join(f"{k}={v:g}" for k, v in r["params"].items())
        print(f"{r['name']:<32} {r['lean']:10.5f} {r['truth']:10.5f} "
              f"{r['rel']*100:8.2f}%  {ps}{flag}")


if __name__ == "__main__":
    main()
