"""neutralAFBenchmarkRatio = (1 - fstT) / (1 - fstS)   PortabilityDrift.lean:2424

The previous check used a symmetric split, so fstS = fstT and the formula
trivially returned 1 -- it could not have detected a wrong functional form.
Here the two descendant populations have DIFFERENT effective sizes, so they
drift by different amounts and the ratio is genuinely informative.

Ground truth: the ratio of retained heterozygosity, het_T / het_S, measured
against a real ancestral sample taken at the split time.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402

LEN = 5e5


def hudson(ts, ss):
    dxy = ts.divergence(sample_sets=ss, indexes=[(0, 1)], mode="branch")[0]
    pi = ts.diversity(sample_sets=ss, mode="branch")
    return float(1 - (pi[0] + pi[1]) / 2 / dxy)


def one(args):
    import msprime
    T, NeA, NeB, NeAnc, seed = args
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=NeA)
    dem.add_population(name="B", initial_size=NeB)
    dem.add_population(name="ANC", initial_size=NeAnc)
    dem.add_population_split(time=T, derived=["A", "B"], ancestral="ANC")
    samples = [msprime.SampleSet(25, population="A", time=0),
               msprime.SampleSet(25, population="B", time=0),
               msprime.SampleSet(25, population="ANC", time=T)]
    ts = msprime.sim_ancestry(samples=samples, demography=dem,
                              sequence_length=LEN, recombination_rate=1e-8,
                              random_seed=seed)
    A, B, ANC = list(range(50)), list(range(50, 100)), list(range(100, 150))
    pi = ts.diversity(sample_sets=[A, B, ANC], mode="branch")
    return dict(T=T, NeA=NeA, NeB=NeB,
                het_A=float(pi[0]), het_B=float(pi[1]), het_anc=float(pi[2]),
                fstS=hudson(ts, [A, ANC]), fstT=hudson(ts, [B, ANC]))


def main():
    reps = int(os.environ.get("REPS", "120"))
    jobs = []
    # asymmetric: A bottlenecked (drifts hard), B large (drifts little)
    for T, NeA, NeB in [(500, 200, 2000), (1000, 200, 2000),
                        (1000, 500, 5000), (2000, 300, 3000)]:
        for r in range(reps):
            jobs.append((T, NeA, NeB, 1000, 23 + r * 7919 + T + NeA))
    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "20"))) as ex:
        out = [f.result() for f in [ex.submit(one, a) for a in jobs]]
    with open(sys.argv[1] if len(sys.argv) > 1 else "asym.json", "w") as fh:
        json.dump(out, fh)

    from collections import defaultdict
    g = defaultdict(list)
    for r in out:
        g[(r["T"], r["NeA"], r["NeB"])].append(r)

    print("=== neutralAFBenchmarkRatio, ASYMMETRIC branches ===")
    print(f"{'T':>6} {'NeA':>6} {'NeB':>6} {'fstS':>8} {'fstT':>8} "
          f"{'het_B/het_A':>12} {'+-':>7} {'lean':>9} {'err%':>8}")
    for k in sorted(g):
        rows = g[k]
        fS = np.mean([r["fstS"] for r in rows])
        fT = np.mean([r["fstT"] for r in rows])
        ratios = [r["het_B"] / r["het_A"] for r in rows]
        obs = float(np.mean(ratios))
        se = float(np.std(ratios) / np.sqrt(len(ratios)))
        lean = (1 - fT) / (1 - fS)
        print(f"{k[0]:6d} {k[1]:6d} {k[2]:6d} {fS:8.4f} {fT:8.4f} "
              f"{obs:12.4f} {se:7.4f} {lean:9.4f} {100*(lean-obs)/obs:8.1f}")


if __name__ == "__main__":
    main()
