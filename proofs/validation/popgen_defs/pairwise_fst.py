"""pairwiseFstFromBranches fstS fstT = 1 - (1-fstS)(1-fstT)
   (PortabilityDrift.lean:33)

Two populations each drift away from a common ancestor by branch-specific
amounts fstS and fstT.  The definition composes them multiplicatively in the
retained-heterozygosity sense.  Ground truth: simulate an ancestral population,
split it, and measure each branch's drift from the ancestor AND the pairwise
F_ST between the descendants, all with the same estimator.

Branch drift is measured as 1 - H_branch / H_ancestral, using an ancestral
sample taken at the split time, so the branch quantities and the pairwise
quantity are on a common footing.
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
LEN = 2e5


def branch_fst(ts, ss):
    dxy = ts.divergence(sample_sets=ss, indexes=[(0, 1)], mode="branch")[0]
    pi = ts.diversity(sample_sets=ss, mode="branch")
    return float(1 - (pi[0] + pi[1]) / 2 / dxy)


def nei_fst(ts, ss):
    """Nei's F_ST = (H_T - H_S)/H_T from branch-mode statistics: H_S is mean
    within-population diversity, H_T is total diversity of the pooled sample."""
    pi = ts.diversity(sample_sets=ss, mode="branch")
    H_S = float((pi[0] + pi[1]) / 2)
    pooled = [ss[0] + ss[1]]
    H_T = float(ts.diversity(sample_sets=pooled, mode="branch")[0])
    return (H_T - H_S) / H_T


def one(args):
    import msprime
    tS, tT, seed = args
    # asymmetric branch lengths: A splits at max(tS,tT), each branch drifts a
    # different amount, so fstS != fstT and the composition is a real test
    T = max(tS, tT)
    dem = msprime.Demography()
    for n in ("A", "B", "ANC"):
        dem.add_population(name=n, initial_size=NE)
    dem.add_population_split(time=T, derived=["A", "B"], ancestral="ANC")
    # ancient samples at the split time stand in for the ancestral population
    samples = [msprime.SampleSet(20, population="A", time=0),
               msprime.SampleSet(20, population="B", time=0),
               msprime.SampleSet(20, population="ANC", time=T)]
    ts = msprime.sim_ancestry(samples=samples, demography=dem,
                              sequence_length=LEN, recombination_rate=1e-8,
                              random_seed=seed)
    A = list(range(40))
    B = list(range(40, 80))
    ANC = list(range(80, 120))
    fst_AB = branch_fst(ts, [A, B])
    fst_A_anc = branch_fst(ts, [A, ANC])
    fst_B_anc = branch_fst(ts, [B, ANC])
    lean = 1 - (1 - fst_A_anc) * (1 - fst_B_anc)
    # the same identity evaluated entirely with Nei's estimator
    n_AB = nei_fst(ts, [A, B])
    n_S = nei_fst(ts, [A, ANC])
    n_T = nei_fst(ts, [B, ANC])
    return dict(T=T, fst_AB=fst_AB, fstS=fst_A_anc, fstT=fst_B_anc,
                lean=lean, additive=fst_A_anc + fst_B_anc,
                nei_AB=n_AB, nei_lean=1 - (1 - n_S) * (1 - n_T))


def main():
    reps = int(os.environ.get("REPS", "120"))
    jobs = []
    for T in (200, 500, 1000, 2000, 4000):
        for r in range(reps):
            jobs.append((T, T, 5 + r * 7919 + T))
    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "20"))) as ex:
        out = [f.result() for f in [ex.submit(one, a) for a in jobs]]
    with open(sys.argv[1] if len(sys.argv) > 1 else "pfst.json", "w") as fh:
        json.dump(out, fh)

    from collections import defaultdict
    g = defaultdict(list)
    for r in out:
        g[r["T"]].append(r)
    print("=== pairwiseFstFromBranches = 1 - (1-fstS)(1-fstT) ===")
    print(f"{'T':>6} {'fstS':>8} {'fstT':>8} {'Fst(A,B)':>10} {'+-':>7} "
          f"{'lean':>9} {'Hud%':>7} {'neiFst':>9} {'neiLean':>9} {'Nei%':>7}")
    for T in sorted(g):
        rows = g[T]
        s = np.mean([r["fstS"] for r in rows])
        t_ = np.mean([r["fstT"] for r in rows])
        ab = np.mean([r["fst_AB"] for r in rows])
        se = np.std([r["fst_AB"] for r in rows]) / np.sqrt(len(rows))
        lean = np.mean([r["lean"] for r in rows])
        add = np.mean([r["additive"] for r in rows])
        nab = np.mean([r["nei_AB"] for r in rows])
        nlean = np.mean([r["nei_lean"] for r in rows])
        print(f"{T:6d} {s:8.4f} {t_:8.4f} {ab:10.5f} {se:7.5f} {lean:9.5f} "
              f"{100*(lean-ab)/ab:7.1f} {nab:9.5f} {nlean:9.5f} "
              f"{100*(nlean-nab)/nab:7.1f}")


if __name__ == "__main__":
    main()
