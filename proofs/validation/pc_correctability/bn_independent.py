"""Experiment A: test PCCorrectability proofs in the exact independent-marker regime.

Balding-Nichols two-deme model -> standardized genotype PCA -> compare the
observed leading eigenvalue / eigenvector overlap against:

  effectiveSubgroupSize n m = m (n - m) / n
  demographicSpike n F m    = 2 F * effectiveSubgroupSize
  bbpProxyThreshold n M     = sqrt(n / M)
  samplePCOverlapSq         = (1 - c/s^2) / (1 + c/s),  c = n/M   (above edge)

Everything is reported against a Hudson-Fst estimated from the simulated data,
so the test is convention-free on the generator side.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

import numpy as np

# one BLAS thread per worker; parallelism comes from the process pool
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")


def hudson_fst(x1, x2, n1, n2):
    """Ratio-of-averages Hudson Fst from per-marker allele counts (haploid n)."""
    p1 = x1 / n1
    p2 = x2 / n2
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    return float(num.sum() / den.sum())


def one_rep(args):
    n, m, M, F, seed = args
    rng = np.random.default_rng(seed)

    # ancestral frequencies, Balding-Nichols deme frequencies (E[Hudson Fst] = F)
    p = rng.uniform(0.05, 0.95, size=M)
    a = p * (1 - F) / F
    b = (1 - p) * (1 - F) / F
    p1 = rng.beta(a, b)
    p2 = rng.beta(a, b)

    X = np.empty((n, M), dtype=np.float64)
    X[:m] = rng.binomial(2, np.broadcast_to(p1, (m, M)))
    X[m:] = rng.binomial(2, np.broadcast_to(p2, (n - m, M)))

    # realized Fst from the simulated genotypes themselves
    c1 = X[:m].sum(axis=0)
    c2 = X[m:].sum(axis=0)
    fst_hat = hudson_fst(c1, c2, 2 * m, 2 * (n - m))

    # HWE standardization on the pooled sample (gnomon's `map` convention)
    phat = X.mean(axis=0) / 2.0
    keep = (phat > 0) & (phat < 1)
    X = X[:, keep]
    phat = phat[keep]
    Meff_raw = int(keep.sum())
    X -= 2 * phat
    X /= np.sqrt(2 * phat * (1 - phat))

    psi = (X @ X.T) / Meff_raw
    evals, evecs = np.linalg.eigh(psi)
    evals = evals[::-1]
    evecs = evecs[:, ::-1]

    # population contrast axis: (n-m)/n on deme 1, -m/n on deme 2
    w = np.empty(n)
    w[:m] = (n - m) / n
    w[m:] = -m / n
    w /= np.linalg.norm(w)

    ov = (evecs.T @ w) ** 2
    cc = n / Meff_raw
    return dict(
        n=n, m=m, M=Meff_raw, F=F, fst_hat=fst_hat, seed=seed,
        lam1=float(evals[0]), lam2=float(evals[1]),
        bulk_edge=float((1 + np.sqrt(cc)) ** 2),
        overlap_pc1=float(ov[0]), overlap_top5=float(ov[:5].sum()),
        eff_size=m * (n - m) / n,
    )


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    reps = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    jobs = []
    n = 1000

    THETAS = [0.25, 0.5, 0.75, 0.9, 1.0, 1.1, 1.25, 1.5, 2, 3, 4, 5, 6, 8,
              12, 16, 24, 32, 48, 64]

    if which in ("all", "theta"):
        # sweep the information product theta = M F^2 n across the claimed edge at 4
        M = 20000
        for theta in THETAS:
            F = np.sqrt(theta / (M * n))
            for r in range(reps):
                jobs.append(("theta", (n, n // 2, M, float(F), 1000 + 97 * r + int(theta * 7))))

    if which in ("all", "bign"):
        # same aspect ratio c = n/M, larger n: the transition should sharpen
        # around the true constant rather than drift toward it
        n2, M2 = 2000, 40000
        for theta in [0.5, 0.75, 1.0, 1.25, 1.5, 2, 3, 4, 6]:
            F = np.sqrt(theta / (M2 * n2))
            for r in range(max(4, reps // 2)):
                jobs.append(("bign", (n2, n2 // 2, M2, float(F), 3000 + 41 * r + int(theta * 11))))

    if which in ("all", "collapse"):
        # same theta reached with different (M, F): does only the product matter?
        for M in [5000, 20000, 80000]:
            for theta in [2, 4, 8, 16]:
                F = np.sqrt(theta / (M * n))
                for r in range(reps):
                    jobs.append(("collapse", (n, n // 2, M, float(F), 5000 + 13 * r + M + int(theta))))

    if which in ("all", "unbalanced"):
        # spike should track m(n-m)/n and be maximized at m = n/2
        M = 20000
        F = float(np.sqrt(16.0 / (M * n)))  # theta = 16 at balance, comfortably above edge
        for m in [50, 100, 200, 350, 500, 650, 800, 900, 950]:
            for r in range(reps):
                jobs.append(("unbalanced", (n, m, M, F, 9000 + 31 * r + m)))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "16"))) as ex:
        out = list(ex.map(one_rep, [j[1] for j in jobs], chunksize=1))
    for tag, rec in zip([j[0] for j in jobs], out):
        rec["slice"] = tag

    with open(sys.argv[3] if len(sys.argv) > 3 else "expA.json", "w") as fh:
        json.dump(out, fh)
    print(f"wrote {len(out)} records")


if __name__ == "__main__":
    main()
