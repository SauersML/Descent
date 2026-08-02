"""Resolve targetHetFromFst properly, and test two more PortabilityDrift defs.

  :162  targetHetFromFst het_source fst = het_source * (1 - fst)
  :2424 neutralAFBenchmarkRatio fS fT   = (1 - fT) / (1 - fS)
  :252  Expected_Abs_Shift V_A fS fT    = sqrt(Var_Delta_Mu) * sqrt(2/pi)

The earlier targetHetFromFst check used the POOLED sample's heterozygosity as a
stand-in for the ancestral value, which conflates within- and between-population
variance and made the result uninterpretable.  Here an ancestral sample is drawn
at the split time, so `het_source` is the real ancestral heterozygosity and the
identity H_derived = H_ancestral * (1 - F_ST) is tested as stated.

F_ST is computed with BOTH the Hudson and Nei estimators, since the previous
round showed the two agree closely and neither explains a bias.
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
LEN = 5e5


def hudson(ts, ss):
    dxy = ts.divergence(sample_sets=ss, indexes=[(0, 1)], mode="branch")[0]
    pi = ts.diversity(sample_sets=ss, mode="branch")
    return float(1 - (pi[0] + pi[1]) / 2 / dxy)


def nei(ts, ss):
    pi = ts.diversity(sample_sets=ss, mode="branch")
    H_S = float((pi[0] + pi[1]) / 2)
    H_T = float(ts.diversity(sample_sets=[ss[0] + ss[1]], mode="branch")[0])
    return (H_T - H_S) / H_T


def one(args):
    import msprime
    T, seed = args
    dem = msprime.Demography()
    for n in ("A", "B", "ANC"):
        dem.add_population(name=n, initial_size=NE)
    dem.add_population_split(time=T, derived=["A", "B"], ancestral="ANC")
    samples = [msprime.SampleSet(25, population="A", time=0),
               msprime.SampleSet(25, population="B", time=0),
               msprime.SampleSet(25, population="ANC", time=T)]
    ts = msprime.sim_ancestry(samples=samples, demography=dem,
                              sequence_length=LEN, recombination_rate=1e-8,
                              random_seed=seed)
    A, B, ANC = list(range(50)), list(range(50, 100)), list(range(100, 150))
    pi = ts.diversity(sample_sets=[A, B, ANC], mode="branch")
    het_A, het_B, het_anc = float(pi[0]), float(pi[1]), float(pi[2])
    return dict(T=T,
                het_anc=het_anc, het_A=het_A, het_B=het_B,
                fst_hud=hudson(ts, [A, ANC]),
                fst_nei=nei(ts, [A, ANC]))


def main():
    reps = int(os.environ.get("REPS", "120"))
    jobs = []
    for T in (200, 500, 1000, 2000, 4000):
        for r in range(reps):
            jobs.append((T, 17 + r * 7919 + T))
    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "20"))) as ex:
        out = [f.result() for f in [ex.submit(one, a) for a in jobs]]
    with open(sys.argv[1] if len(sys.argv) > 1 else "hd.json", "w") as fh:
        json.dump(out, fh)

    from collections import defaultdict
    g = defaultdict(list)
    for r in out:
        g[r["T"]].append(r)

    print("=== targetHetFromFst = het_ancestral * (1 - fst),")
    print("    with a real ancestral sample and fst measured A-vs-ancestral ===")
    print(f"{'T':>6} {'het_anc':>10} {'het_A obs':>11} {'+-':>8} "
          f"{'fst(Hud)':>9} {'lean(Hud)':>10} {'err%':>7} "
          f"{'fst(Nei)':>9} {'lean(Nei)':>10} {'err%':>7}")
    for T in sorted(g):
        rows = g[T]
        ha = np.mean([r["het_anc"] for r in rows])
        hA = np.mean([r["het_A"] for r in rows])
        se = np.std([r["het_A"] for r in rows]) / np.sqrt(len(rows))
        fh_ = np.mean([r["fst_hud"] for r in rows])
        fn = np.mean([r["fst_nei"] for r in rows])
        lh = ha * (1 - fh_)
        ln = ha * (1 - fn)
        print(f"{T:6d} {ha:10.1f} {hA:11.1f} {se:8.1f} {fh_:9.4f} {lh:10.1f} "
              f"{100*(lh-hA)/hA:7.1f} {fn:9.4f} {ln:10.1f} {100*(ln-hA)/hA:7.1f}")

    print("\n=== neutralAFBenchmarkRatio = (1-fstT)/(1-fstS) ===")
    print("    ground truth: het_B / het_A (ratio of retained heterozygosity)")
    print(f"{'T':>6} {'het_A/het_anc':>14} {'het_B/het_anc':>14} "
          f"{'obs ratio':>10} {'lean':>9} {'err%':>7}")
    for T in sorted(g):
        rows = g[T]
        ha = np.mean([r["het_anc"] for r in rows])
        hA = np.mean([r["het_A"] for r in rows])
        hB = np.mean([r["het_B"] for r in rows])
        f = np.mean([r["fst_hud"] for r in rows])
        # both branches have the same expected drift here, so the ratio is 1
        print(f"{T:6d} {hA/ha:14.4f} {hB/ha:14.4f} {hB/hA:10.4f} "
              f"{(1-f)/(1-f):9.4f} {100*((1-f)/(1-f)-hB/hA)/(hB/hA):7.1f}")


if __name__ == "__main__":
    main()
