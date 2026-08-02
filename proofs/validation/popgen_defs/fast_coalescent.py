"""Fast coalescent battery: tiny genomes, many replicates.

Earlier msprime runs used 20-30 Mb because I was thinking about LD.  For any
claim that is a per-site expectation (F_ST, SFS, heterozygosity) a 100 kb region
replicated a few hundred times gives tighter error bars far cheaper, and it
parallelizes perfectly.

Also cross-checks the hand-rolled Hudson F_ST against scikit-allel's reference
implementation -- three of the flags raised during this work turned out to be
estimator-construction errors in the harness rather than bugs in the repo, so
the estimators themselves need validating.

Target: `admixedFst (1-alpha)^2 * fst_AB` (DemographicHistory.lean:186), which
is still unfixed, measured across realistic F_ST so a corrected law can be read
off directly.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402

NE = 1000
MU = 2e-8
RHO = 1e-8
LEN = 1e5          # 100 kb, not 30 Mb


def hudson_fst_manual(c1, c2, n1, n2):
    p1, p2 = c1 / n1, c2 / n2
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    ok = den > 0
    return float(num[ok].sum() / den[ok].sum())


def hudson_fst_allel(g1, g2):
    """Reference implementation from scikit-allel."""
    import allel
    ac1 = np.column_stack([(g1 == 0).sum(1), (g1 == 1).sum(1)])
    ac2 = np.column_stack([(g2 == 0).sum(1), (g2 == 1).sum(1)])
    num, den = allel.hudson_fst(ac1, ac2)
    return float(np.sum(num) / np.sum(den))


def one(args):
    import msprime
    split_t, alpha, g_admix, seed = args
    dem = msprime.Demography()
    for name in ("A", "B", "ADM", "ANC"):
        dem.add_population(name=name, initial_size=NE)
    dem.add_admixture(time=g_admix, derived="ADM", ancestral=["A", "B"],
                      proportions=[alpha, 1 - alpha])
    dem.add_population_split(time=split_t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": 30, "B": 30, "ADM": 30},
                              demography=dem, sequence_length=LEN,
                              recombination_rate=RHO, random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 1)
    G = ts.genotype_matrix()
    if G.shape[0] < 20:
        return None
    A, B, ADM = G[:, :60], G[:, 60:120], G[:, 120:180]

    fst_AB = hudson_fst_manual(A.sum(1).astype(float), B.sum(1).astype(float), 60, 60)
    fst_ADM_A = hudson_fst_manual(ADM.sum(1).astype(float), A.sum(1).astype(float), 60, 60)
    try:
        fst_AB_ref = hudson_fst_allel(A, B)
    except Exception:
        fst_AB_ref = float("nan")
    return dict(split_t=split_t, alpha=alpha, g=g_admix,
                fst_AB=fst_AB, fst_ADM_A=fst_ADM_A, fst_AB_allel=fst_AB_ref,
                lean=(1 - alpha) ** 2 * fst_AB, n_sites=int(G.shape[0]))


def main():
    reps = int(os.environ.get("REPS", "200"))
    jobs = []
    for split_t in (100, 300, 1000):
        for alpha in (0.2, 0.5, 0.8):
            for r in range(reps):
                jobs.append((split_t, alpha, 20, 1 + r * 7919 + split_t + int(alpha * 10)))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "24"))) as ex:
        out = [f.result() for f in [ex.submit(one, a) for a in jobs]]
    out = [o for o in out if o]
    with open(sys.argv[1] if len(sys.argv) > 1 else "fastcoal.json", "w") as fh:
        json.dump(out, fh)

    from collections import defaultdict
    g = defaultdict(list)
    for r in out:
        g[(r["split_t"], r["alpha"])].append(r)

    print(f"{len(out)} replicates of {LEN/1e3:.0f} kb\n")
    print(f"{'split':>6} {'alpha':>6} {'Fst(A,B)':>9} {'allel':>9} "
          f"{'Fst(ADM,A)':>11} {'+-':>7} {'lean':>9} {'err%':>8} {'ratio':>7}")
    for k in sorted(g):
        rows = g[k]
        ab = np.mean([r["fst_AB"] for r in rows])
        ab_ref = np.nanmean([r["fst_AB_allel"] for r in rows])
        obs = np.mean([r["fst_ADM_A"] for r in rows])
        se = np.std([r["fst_ADM_A"] for r in rows]) / np.sqrt(len(rows))
        lean = np.mean([r["lean"] for r in rows])
        print(f"{k[0]:6d} {k[1]:6.2f} {ab:9.5f} {ab_ref:9.5f} {obs:11.5f} "
              f"{se:7.5f} {lean:9.5f} {100*(lean-obs)/obs:8.1f} {obs/ab:7.4f}")
    print("\nratio = Fst(ADM,A)/Fst(A,B); the Lean law predicts (1-alpha)^2 =",
          [f"{(1-a)**2:.2f}" for a in (0.2, 0.5, 0.8)])


if __name__ == "__main__":
    main()
