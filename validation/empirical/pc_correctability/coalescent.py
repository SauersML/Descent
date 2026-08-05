"""Experiment B: the same PCCorrectability test under a real coalescent with LD.

The Lean threshold model takes `M` = "effectively independent markers" as an
input and explicitly declines to supply the bridge from a dependent genotype
matrix (see PCCorrectability/Threshold.lean).  This script measures that bridge:

  * simulate a two-deme split with msprime (real LD, real allele-frequency
    spectrum, real drift);
  * compute the same spike / overlap quantities as Experiment A;
  * compare three candidate marker counts:
      M_raw     - number of SNPs actually used
      M_thin    - SNPs thinned to one per LD block (physically spaced)
      M_eff     - read off the Marchenko-Pastur bulk, where Var(bulk) = n / M

If the model transfers, the observed overlap should follow the Johnstone-Paul
curve when fed M_eff, and should NOT follow it when fed M_raw.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

# Must precede `import numpy`: OpenBLAS fixes its thread pool at import time.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402
from scipy.linalg.blas import ssyrk  # noqa: E402

NE = 10000
MU = 1.25e-8
RHO = 1e-8


def hudson_fst(c1, c2, n1, n2):
    p1 = c1 / n1
    p2 = c2 / n2
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    return float(num.sum() / den.sum())


def simulate(n_dip_per_deme, split_gens, length, seed):
    import msprime

    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=NE)
    dem.add_population(name="B", initial_size=NE)
    dem.add_population(name="ANC", initial_size=NE)
    dem.add_population_split(time=split_gens, derived=["A", "B"], ancestral="ANC")

    ts = msprime.sim_ancestry(
        samples={"A": n_dip_per_deme, "B": n_dip_per_deme},
        demography=dem,
        sequence_length=length,
        recombination_rate=RHO,
        random_seed=seed,
    )
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 1)
    return ts


def genotypes(ts, n_dip):
    """Diploid dosage matrix (individuals x sites) plus site positions."""
    G = ts.genotype_matrix()  # sites x haploids, 0/1
    pos = ts.sites_position
    D = G[:, 0::2] + G[:, 1::2]  # sum the two haplotypes of each individual
    return D.T.astype(np.float64), pos


def analyze_matrix(X, m, n):
    """Standardize, eigendecompose, return spike/overlap diagnostics."""
    phat = X.mean(axis=0) / 2.0
    keep = (phat > 0) & (phat < 1)
    X = X[:, keep]
    phat = phat[keep]
    M = int(keep.sum())
    X = X - 2 * phat
    X /= np.sqrt(2 * phat * (1 - phat))

    psi = np.asarray(ssyrk(alpha=1.0 / M, a=X.astype(np.float32), lower=0),
                     dtype=np.float64)
    evals, evecs = np.linalg.eigh(psi, UPLO="U")
    evals = evals[::-1]
    evecs = evecs[:, ::-1]

    w = np.empty(n)
    w[:m] = (n - m) / n
    w[m:] = -m / n
    w /= np.linalg.norm(w)
    ov = float(((evecs[:, 0] @ w) ** 2))

    # Marchenko-Pastur bulk: mean 1, variance c = n / M_eff.  Drop the leading
    # eigenvalues that carry the spike so the bulk moment is not contaminated.
    bulk = evals[5:]
    c_eff = float(bulk.var())
    return dict(M=M, lam1=float(evals[0]), lam2=float(evals[1]),
                overlap_pc1=ov, c_eff=c_eff, M_eff=float(n / c_eff))


def thin(pos, min_gap):
    """Indices of sites kept when enforcing a minimum physical spacing."""
    keep, last = [], -np.inf
    for i, p in enumerate(pos):
        if p - last >= min_gap:
            keep.append(i)
            last = p
    return np.array(keep, dtype=int)


def one_rep(args):
    n_dip_per_deme, split_gens, length, n_snps, seed = args
    n = 2 * n_dip_per_deme
    m = n_dip_per_deme

    ts = simulate(n_dip_per_deme, split_gens, length, seed)
    D, pos = genotypes(ts, n)

    # common-variant filter, then a random subset of the requested size
    p = D.mean(axis=0) / 2.0
    common = np.where((p > 0.05) & (p < 0.95))[0]
    rng = np.random.default_rng(seed)
    if n_snps is not None and len(common) > n_snps:
        common = np.sort(rng.choice(common, size=n_snps, replace=False))
    Xc, posc = D[:, common], pos[common]

    c1 = Xc[:m].sum(axis=0)
    c2 = Xc[m:].sum(axis=0)
    fst = hudson_fst(c1, c2, 2 * m, 2 * (n - m))

    res_all = analyze_matrix(Xc.copy(), m, n)
    idx = thin(posc, min_gap=20_000)  # one marker per 20 kb
    res_thin = analyze_matrix(np.ascontiguousarray(Xc[:, idx]), m, n)

    return dict(
        split_gens=split_gens, seed=seed, n=n, m=m, eff_size=m * (n - m) / n,
        fst_hat=fst, length=length,
        n_sites_total=int(D.shape[1]), n_common=int(len(common)),
        full=res_all, thinned=res_thin,
    )


def main():
    n_dip_per_deme = int(os.environ.get("NDIP", "250"))
    length = float(os.environ.get("LEN", "3e7"))
    reps = int(os.environ.get("REPS", "3"))
    n_snps = int(os.environ.get("NSNPS", "30000"))

    jobs = []
    for split in [5, 10, 20, 40, 80, 160]:
        for r in range(reps):
            jobs.append((n_dip_per_deme, split, length, n_snps, 100 + 17 * r + split))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "12"))) as ex:
        out = list(ex.map(one_rep, jobs, chunksize=1))

    with open(sys.argv[1] if len(sys.argv) > 1 else "expB.json", "w") as fh:
        json.dump(out, fh)
    print(f"wrote {len(out)} records")


if __name__ == "__main__":
    main()
