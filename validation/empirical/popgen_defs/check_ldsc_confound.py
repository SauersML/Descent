"""Does the LDSC confounding term scale as N*a or N*a/M?

  CovarianceStructure.lean:308  ldsrExpectedChi2 = N*h2/M*ell_j + N*a/M + 1
  reference (Bulik-Sullivan)    E[chi2] = N*h2/M*ell_j + N*a + 1

`a` is a property of the confounding, not of the marker panel.  So the decisive,
convention-free test is: hold the confounding fixed and vary M.  The reference
law says the confounding contribution to E[chi2] is independent of M; the
transcribed Lean form says it falls as 1/M.

Design: two subpopulations with allele-frequency divergence and a mean phenotype
offset (pure stratification, zero true genetic effect).  All SNPs are otherwise
independent, so ell_j = 1 and h2 = 0; every bit of chi-square above 1 is
confounding.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402


def one(args):
    n, M, fst, offset, seed = args
    rng = np.random.default_rng(seed)
    half = n // 2
    p = rng.uniform(0.1, 0.9, size=M)
    # Balding-Nichols divergence between the two strata
    alpha = p * (1 - fst) / fst
    beta = (1 - p) * (1 - fst) / fst
    p1 = rng.beta(alpha, beta)
    p2 = rng.beta(alpha, beta)
    X = np.empty((n, M))
    X[:half] = rng.binomial(2, np.broadcast_to(p1, (half, M)))
    X[half:] = rng.binomial(2, np.broadcast_to(p2, (n - half, M)))

    # phenotype: NO genetic effect, only a stratum offset plus noise
    y = np.concatenate([np.full(half, offset / 2),
                        np.full(n - half, -offset / 2)])
    y = y + rng.standard_normal(n)
    y -= y.mean()

    Xs = X - X.mean(axis=0)
    sd = Xs.std(axis=0)
    keep = sd > 0
    Xs = Xs[:, keep] / sd[keep]
    Mk = int(keep.sum())
    bhat = (Xs.T @ y) / n / y.std()
    chi2 = n * bhat**2
    mean_chi2 = float(chi2.mean())
    # excess over the null expectation of 1
    return dict(n=n, M=Mk, fst=fst, offset=offset,
                mean_chi2=mean_chi2, excess=mean_chi2 - 1.0,
                implied_a_reference=(mean_chi2 - 1.0) / n,
                implied_a_lean=(mean_chi2 - 1.0) * Mk / n)


def main():
    jobs = []
    for M in (250, 500, 1000, 2000, 4000):
        for rep in range(3):
            jobs.append((4000, M, 0.01, 0.6, 17 + M + rep * 101))
    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "10"))) as ex:
        out = [f.result() for f in [ex.submit(one, a) for a in jobs]]
    with open(sys.argv[1] if len(sys.argv) > 1 else "ldscconf.json", "w") as fh:
        json.dump(out, fh)

    from collections import defaultdict
    g = defaultdict(list)
    for r in out:
        g[r["M"] // 10 * 10].append(r)
    print("Pure stratification (h2 = 0, ell_j = 1), n = 4000, Fst = 0.01")
    print("If the reference law holds, `implied a` is constant across M.")
    print("If the Lean /M form holds, `implied a (lean)` is constant instead.\n")
    print(f"{'M':>6} {'mean chi2':>10} {'excess':>8} {'implied a (ref)':>16} "
          f"{'implied a (lean)':>17}")
    for k in sorted(g):
        rows = g[k]
        M = np.mean([r["M"] for r in rows])
        mc = np.mean([r["mean_chi2"] for r in rows])
        ex_ = np.mean([r["excess"] for r in rows])
        ar = np.mean([r["implied_a_reference"] for r in rows])
        al = np.mean([r["implied_a_lean"] for r in rows])
        print(f"{M:6.0f} {mc:10.4f} {ex_:8.4f} {ar:16.6f} {al:17.4f}")


if __name__ == "__main__":
    main()
