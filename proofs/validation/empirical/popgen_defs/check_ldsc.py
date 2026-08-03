"""Check the LD-score-regression and LD-correlation definitions.

  CovarianceStructure.lean:308  ldsrExpectedChi2 N h2 M ell_j a
                                  = N*h2/M*ell_j + N*a/M + 1
  CovarianceStructure.lean:301  ldsrExpectedBetaSq h2 M ell_j N
                                  = h2/M*ell_j + 1/N
  CovarianceStructure.lean:91   ldCorrelationSq D p_i p_j
                                  = D^2 / (2 p_i(1-p_i) * 2 p_j(1-p_j))

For LDSC the reference law is E[chi2_j] = (N h2 / M) ell_j + N a + 1, where a is
the confounding (inflation) term and ell_j the LD score.  The transcribed Lean
form divides the confounding term by M as well; this checks the slope directly
and then whether an intercept-vs-N regression recovers `a` or `a/M`.

For ldCorrelationSq the question is which D convention makes the formula equal
r^2: haplotype D or dosage covariance.  We compute all three from the same
simulated genotypes.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402


def lean_ldsrExpectedChi2(N, h2, M, ell_j, a):
    return N * h2 / M * ell_j + N * a / M + 1


def reference_ldsrExpectedChi2(N, h2, M, ell_j, a):
    return N * h2 / M * ell_j + N * a + 1


def lean_ldCorrelationSq(D, p_i, p_j):
    return D**2 / ((2 * p_i * (1 - p_i)) * (2 * p_j * (1 - p_j)))


# --------------------------------------------------------------------------

def ld_convention(args):
    """Compare haplotype-D and dosage-covariance conventions against r^2."""
    n_hap, pA, pB, D_hap, seed = args
    rng = np.random.default_rng(seed)
    # haplotype frequencies from allele freqs plus D
    f11 = pA * pB + D_hap
    f10 = pA * (1 - pB) - D_hap
    f01 = (1 - pA) * pB - D_hap
    f00 = (1 - pA) * (1 - pB) + D_hap
    f = np.array([f11, f10, f01, f00])
    if np.any(f < 0):
        return None
    idx = rng.choice(4, size=n_hap, p=f / f.sum())
    hA = np.isin(idx, [0, 1]).astype(float)
    hB = np.isin(idx, [0, 2]).astype(float)
    # pair haplotypes into diploids
    gA = hA[0::2] + hA[1::2]
    gB = hB[0::2] + hB[1::2]

    pA_hat = hA.mean()
    pB_hat = hB.mean()
    D_hat = float(np.mean(hA * hB) - pA_hat * pB_hat)       # haplotype D
    cov_dos = float(np.cov(gA, gB)[0, 1])                    # dosage covariance
    r2_direct = float(np.corrcoef(gA, gB)[0, 1] ** 2)

    return dict(check="ld_convention", pA=pA, pB=pB, D_hap=D_hap,
                r2_direct=r2_direct,
                lean_with_hapD=lean_ldCorrelationSq(D_hat, pA_hat, pB_hat),
                lean_with_dosagecov=lean_ldCorrelationSq(cov_dos, pA_hat, pB_hat))


def ldsc_sim(args):
    """Simulate a polygenic GWAS on independent SNPs (ell_j = 1) and read off
    the mean chi-square, which pins the LDSC slope and intercept."""
    n, M, h2, seed = args
    rng = np.random.default_rng(seed)
    # independent markers -> every LD score is exactly 1
    X = rng.standard_normal((n, M)).astype(np.float64)
    X -= X.mean(axis=0)
    X /= X.std(axis=0)
    beta = rng.standard_normal(M) * np.sqrt(h2 / M)
    g = X @ beta
    g *= np.sqrt(h2) / g.std()
    y = g + np.sqrt(1 - h2) * rng.standard_normal(n)
    y -= y.mean()
    y /= y.std()
    bhat = (X.T @ y) / n
    chi2 = n * bhat**2
    return dict(check="ldsc", n=n, M=M, h2=h2,
                mean_chi2=float(chi2.mean()), ell_j=1.0,
                lean=lean_ldsrExpectedChi2(n, h2, M, 1.0, 0.0),
                reference=reference_ldsrExpectedChi2(n, h2, M, 1.0, 0.0))


def main():
    jobs = []
    for n, M, h2 in [(2000, 500, 0.5), (5000, 1000, 0.5), (10000, 2000, 0.3),
                     (20000, 5000, 0.8), (5000, 200, 0.2)]:
        jobs.append((ldsc_sim, (n, M, h2, 11 + n + M)))
    for pA, pB, D in [(0.5, 0.5, 0.2), (0.3, 0.4, 0.1), (0.2, 0.7, 0.05),
                      (0.5, 0.5, 0.0)]:
        jobs.append((ld_convention, (400000, pA, pB, D, 7 + int(pA * 100))))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "10"))) as ex:
        out = [f.result() for f in [ex.submit(fn, a) for fn, a in jobs]]
    out = [o for o in out if o]
    with open(sys.argv[1] if len(sys.argv) > 1 else "ldsc.json", "w") as fh:
        json.dump(out, fh)

    print("=== LDSC: E[chi2] with independent SNPs (ell_j = 1, a = 0) ===")
    print(f"{'n':>7} {'M':>6} {'h2':>5} {'sim mean chi2':>14} {'lean':>9} "
          f"{'reference':>10}")
    for r in [x for x in out if x["check"] == "ldsc"]:
        print(f"{r['n']:7d} {r['M']:6d} {r['h2']:5.2f} {r['mean_chi2']:14.4f} "
              f"{r['lean']:9.4f} {r['reference']:10.4f}")
    print("\n(with a = 0 the two forms coincide; this validates the slope term)")

    print("\n=== ldCorrelationSq: which D convention gives r^2? ===")
    print(f"{'pA':>5} {'pB':>5} {'D':>6} {'r2 direct':>10} {'lean(hapD)':>11} "
          f"{'lean(dosage cov)':>17}")
    for r in [x for x in out if x["check"] == "ld_convention"]:
        print(f"{r['pA']:5.2f} {r['pB']:5.2f} {r['D_hap']:6.2f} "
              f"{r['r2_direct']:10.4f} {r['lean_with_hapD']:11.4f} "
              f"{r['lean_with_dosagecov']:17.4f}")


if __name__ == "__main__":
    main()
