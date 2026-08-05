"""Experiment A: test the PCCorrectability proofs in the exact regime they assume.

Balding-Nichols two-deme model with independent markers -> HWE-standardized
genotype PCA -> compare the observed leading eigenvalue and eigenvector overlap
against the Lean definitions in `Descent/Portability/PCCorrectability/`:

    effectiveSubgroupSize n m = m (n - m) / n
    demographicSpike n F m    = 2 F * effectiveSubgroupSize n m
    bbpProxyThreshold n M     = sqrt (n / M)
    samplePCOverlapSq         = (1 - c/s^2) / (1 + c/s),   c = n / M

Fst is estimated from the simulated genotypes (Hudson, ratio of averages), so
the comparison does not depend on the generator's parameterization.

Performance notes: the kernel is a rank-M symmetric update, so we use float32
`ssyrk` (half the flops of a general matmul) and draw genotypes as a pair of
Bernoulli comparisons rather than through the slower binomial sampler.
"""
from __future__ import annotations

import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

# Must precede `import numpy`: OpenBLAS fixes its thread pool at import time and
# would otherwise take every core on a shared node, once per worker process.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402
from scipy.linalg.blas import ssyrk  # noqa: E402


def hudson_fst(c1, c2, n1, n2):
    """Ratio-of-averages Hudson Fst from per-marker allele counts (n haploid)."""
    p1 = c1 / n1
    p2 = c2 / n2
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    return float(num.sum() / den.sum())


def _draw_block(rng, p_row, rows, M, out):
    """Binomial(2, p) genotypes as two Bernoulli comparisons, written into `out`."""
    u = rng.random((rows, M), dtype=np.float32)
    out[:] = (u < p_row)
    u = rng.random((rows, M), dtype=np.float32)
    out += (u < p_row)


def one_rep(args):
    n, m, M, F, seed = args
    rng = np.random.default_rng(seed)

    p = rng.uniform(0.05, 0.95, size=M)
    a = p * (1 - F) / F
    b = (1 - p) * (1 - F) / F
    p1 = rng.beta(a, b).astype(np.float32)
    p2 = rng.beta(a, b).astype(np.float32)

    X = np.empty((n, M), dtype=np.float32)
    _draw_block(rng, p1, m, M, X[:m])
    _draw_block(rng, p2, n - m, M, X[m:])

    c1 = X[:m].sum(axis=0, dtype=np.float64)
    c2 = X[m:].sum(axis=0, dtype=np.float64)
    fst_hat = hudson_fst(c1, c2, 2 * m, 2 * (n - m))

    # HWE standardization on the pooled sample (gnomon `map` convention)
    phat = ((c1 + c2) / (2.0 * n)).astype(np.float32)
    keep = (phat > 0) & (phat < 1)
    if not keep.all():
        X = np.ascontiguousarray(X[:, keep])
        phat = phat[keep]
    Mk = int(keep.sum())
    X -= 2 * phat
    X *= (1.0 / np.sqrt(2 * phat * (1 - phat))).astype(np.float32)

    psi = ssyrk(alpha=1.0 / Mk, a=X, lower=0)
    psi = np.asarray(psi, dtype=np.float64)
    evals, evecs = np.linalg.eigh(psi, UPLO="U")
    evals = evals[::-1]
    evecs = evecs[:, ::-1]

    w = np.empty(n)
    w[:m] = (n - m) / n
    w[m:] = -m / n
    w /= np.linalg.norm(w)
    ov = (evecs.T @ w) ** 2

    cc = n / Mk
    bulk = evals[5:]
    return dict(
        n=n, m=m, M=Mk, F=F, fst_hat=fst_hat, seed=seed,
        lam1=float(evals[0]), lam2=float(evals[1]),
        bulk_edge=float((1 + np.sqrt(cc)) ** 2),
        c_eff=float(bulk.var()),
        overlap_pc1=float(ov[0]), overlap_top5=float(ov[:5].sum()),
        eff_size=m * (n - m) / n,
    )


THETAS = [0.25, 0.5, 0.75, 0.9, 1.0, 1.1, 1.25, 1.5, 2, 3, 4, 5, 6, 8,
          12, 16, 24, 32, 48, 64]


def build_jobs(which, reps):
    jobs = []
    n = 1000

    if which in ("all", "theta"):
        # sweep the information product theta = M F^2 n across the claimed edge
        M = 8000
        for theta in THETAS:
            F = np.sqrt(theta / (M * n))
            for r in range(reps):
                jobs.append(("theta", (n, n // 2, M, float(F), 1000 + 97 * r + int(theta * 7))))

    if which in ("all", "bign"):
        # same aspect ratio c = n/M at larger n: the transition should sharpen
        n2, M2 = 3000, 24000
        for theta in [0.5, 0.75, 0.9, 1.0, 1.1, 1.25, 1.5, 2, 3, 4]:
            F = np.sqrt(theta / (M2 * n2))
            for r in range(max(4, reps // 2)):
                jobs.append(("bign", (n2, n2 // 2, M2, float(F), 3000 + 41 * r + int(theta * 11))))

    if which in ("all", "collapse"):
        # the same theta reached with different (M, F): only the product should matter
        for M in [2000, 8000, 32000]:
            for theta in [2, 4, 8, 16]:
                F = np.sqrt(theta / (M * n))
                for r in range(reps):
                    jobs.append(("collapse", (n, n // 2, M, float(F), 5000 + 13 * r + M + int(theta))))

    if which in ("all", "unbalanced"):
        # the spike should track m(n-m)/n and be maximized at m = n/2
        M = 8000
        F = float(np.sqrt(16.0 / (M * n)))
        for m in [50, 100, 200, 350, 500, 650, 800, 900, 950]:
            for r in range(reps):
                jobs.append(("unbalanced", (n, m, M, F, 9000 + 31 * r + m)))

    return jobs


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    reps = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    out_path = sys.argv[3] if len(sys.argv) > 3 else "expA.json"
    jobs = build_jobs(which, reps)

    t0 = time.time()
    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "32"))) as ex:
        out = list(ex.map(one_rep, [j[1] for j in jobs], chunksize=1))
    for tag, rec in zip([j[0] for j in jobs], out):
        rec["slice"] = tag

    with open(out_path, "w") as fh:
        json.dump(out, fh)
    print(f"wrote {len(out)} records in {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
