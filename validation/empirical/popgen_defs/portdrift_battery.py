"""PortabilityDrift battery -- the file with 165 definitions and one tested.

  :26   fstFromTau tau                 = 1 - exp(-tau)
  :33   pairwiseFstFromBranches fS fT  = 1 - (1-fS)(1-fT)
  :162  targetHetFromFst het fst       = het * (1 - fst)
  :2424 neutralAFBenchmarkRatio        = (1-fstT)/(1-fstS)

`fstFromTau` is a THIRD formula for F_ST after a split, alongside coalFst
(t/(t+2Ne), validated) and heterozygosityLossDerived (1-(1-1/2Ne)^t, falsified at +15-28%).
With tau = t/(2Ne), coalFst is tau/(1+tau) while fstFromTau is 1-exp(-tau);
1-exp(-tau) is the continuous limit of the falsified form, so this checks
whether the same error recurs a third time.

Tiny genomes, many replicates, branch-mode statistics.
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


def split_rep(args):
    import msprime
    t, seed = args
    dem = msprime.Demography()
    for n in ("A", "B", "ANC"):
        dem.add_population(name=n, initial_size=NE)
    dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": 20, "B": 20}, demography=dem,
                              sequence_length=LEN, recombination_rate=1e-8,
                              random_seed=seed)
    ss = [list(range(40)), list(range(40, 80))]
    tau = t / (2 * NE)
    return dict(check="split", t=t, tau=tau, sim=branch_fst(ts, ss),
                coalFst=t / (t + 2 * NE),
                fstFromTau=1 - np.exp(-tau))


def het_rep(args):
    """targetHetFromFst: expected heterozygosity in the derived population."""
    import msprime
    t, seed = args
    dem = msprime.Demography()
    for n in ("A", "B", "ANC"):
        dem.add_population(name=n, initial_size=NE)
    dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": 20, "B": 20}, demography=dem,
                              sequence_length=LEN, recombination_rate=1e-8,
                              random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=2e-8, random_seed=seed + 1)
    G = ts.genotype_matrix()
    if G.shape[0] < 10:
        return None
    A, B = G[:, :40], G[:, 40:]
    pA = A.mean(1)
    pB = B.mean(1)
    hetA = float(np.mean(2 * pA * (1 - pA)))
    hetB = float(np.mean(2 * pB * (1 - pB)))
    # ancestral heterozygosity proxy: the pooled sample
    pP = G.mean(1)
    hetP = float(np.mean(2 * pP * (1 - pP)))
    ss = [list(range(40)), list(range(40, 80))]
    fst = branch_fst(ts, ss)
    return dict(check="het", t=t, fst=fst, hetA=hetA, hetB=hetB, hetPooled=hetP,
                lean_targetHet=hetP * (1 - fst))


def main():
    reps = int(os.environ.get("REPS", "150"))
    jobs = []
    for t in (200, 500, 1000, 2000, 4000, 8000):
        for r in range(reps):
            jobs.append((split_rep, (t, 3 + r * 7919 + t)))
    for t in (500, 2000):
        for r in range(reps // 2):
            jobs.append((het_rep, (t, 11 + r * 6151 + t)))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "20"))) as ex:
        out = [f.result() for f in [ex.submit(fn, a) for fn, a in jobs]]
    out = [o for o in out if o]
    with open(sys.argv[1] if len(sys.argv) > 1 else "pd.json", "w") as fh:
        json.dump(out, fh)

    from collections import defaultdict
    g = defaultdict(list)
    for r in out:
        if r["check"] == "split":
            g[r["t"]].append(r)
    print("=== three formulas for F_ST after a split ===")
    print(f"{'t':>6} {'tau':>6} {'sim':>9} {'+-':>7} {'coalFst':>9} {'err%':>7} "
          f"{'fstFromTau':>11} {'err%':>7}")
    for t in sorted(g):
        rows = g[t]
        s = np.mean([r["sim"] for r in rows])
        se = np.std([r["sim"] for r in rows]) / np.sqrt(len(rows))
        c, f = rows[0]["coalFst"], rows[0]["fstFromTau"]
        print(f"{t:6d} {rows[0]['tau']:6.2f} {s:9.5f} {se:7.5f} {c:9.5f} "
              f"{100*(c-s)/s:7.1f} {f:11.5f} {100*(f-s)/s:7.1f}")

    h = [r for r in out if r["check"] == "het"]
    if h:
        print("\n=== targetHetFromFst = het_source * (1 - fst) ===")
        gg = defaultdict(list)
        for r in h:
            gg[r["t"]].append(r)
        print(f"{'t':>6} {'fst':>8} {'het pooled':>11} {'het derived':>12} "
              f"{'lean':>9} {'err%':>8}")
        for t in sorted(gg):
            rows = gg[t]
            fst = np.mean([r["fst"] for r in rows])
            hp = np.mean([r["hetPooled"] for r in rows])
            hd = np.mean([r["hetA"] for r in rows])
            lean = np.mean([r["lean_targetHet"] for r in rows])
            print(f"{t:6d} {fst:8.4f} {hp:11.5f} {hd:12.5f} {lean:9.5f} "
                  f"{100*(lean-hd)/hd:8.1f}")


if __name__ == "__main__":
    main()
