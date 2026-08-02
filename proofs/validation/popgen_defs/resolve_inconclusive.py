"""Resolve the two checks that were previously left un-claimed.

  islandModelFst = 1/(1+4*Ne*m)          PopulationGeneticsFoundations.lean:669
      Round 1 set msprime's PAIRWISE migration rate, so total immigration scaled
      with deme count and the deme-count trend was an artifact.  Round 2 fixed
      that but had one replicate per cell.  Here: total immigration held fixed,
      many replicates, and the finite-deme correction 1/(1+4*Ne*m*(d/(d-1))^2)
      evaluated alongside.

  demoSteppingStoneFst d Ne m s2 = d/(d+4*Ne*m*s2)   DemographicHistory.lean:64
      s2 is a free dispersal parameter that was fixed to 1 arbitrarily, so the
      earlier 30-123% gap was not evidence.  Here we fit a single s2 across all
      distances: if one value fits, the form is right; if the fitted value must
      change with distance, the form is wrong.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402

LEN = 2e5


def branch_fst(ts, ss):
    dxy = ts.divergence(sample_sets=ss, indexes=[(0, 1)], mode="branch")[0]
    pi = ts.diversity(sample_sets=ss, mode="branch")
    return float(1 - (pi[0] + pi[1]) / 2 / dxy)


def island(args):
    import msprime
    Ne, m_total, ndemes, seed = args
    pairwise = m_total / (ndemes - 1)          # total immigration per deme fixed
    dem = msprime.Demography.island_model([Ne] * ndemes, migration_rate=pairwise)
    samples = {f"pop_{i}": (20 if i < 2 else 0) for i in range(ndemes)}
    ts = msprime.sim_ancestry(samples=samples, demography=dem,
                              sequence_length=LEN, recombination_rate=1e-8,
                              random_seed=seed)
    d = ndemes
    return dict(check="island", ndemes=d, Nm=Ne * m_total,
                sim=branch_fst(ts, [list(range(40)), list(range(40, 80))]),
                lean=1 / (1 + 4 * Ne * m_total),
                finite_deme=1 / (1 + 4 * Ne * m_total * (d / (d - 1)) ** 2))


def stepping(args):
    import msprime
    ndemes, Ne, m, d, seed = args
    dem = msprime.Demography.stepping_stone_model([Ne] * ndemes,
                                                  migration_rate=m,
                                                  boundaries=True)
    samples = {f"pop_{i}": (20 if i in (0, d) else 0) for i in range(ndemes)}
    ts = msprime.sim_ancestry(samples=samples, demography=dem,
                              sequence_length=LEN, recombination_rate=1e-8,
                              random_seed=seed)
    return dict(check="stepping", ndemes=ndemes, Ne=Ne, m=m, d=d,
                sim=branch_fst(ts, [list(range(40)), list(range(40, 80))]))


def main():
    reps = int(os.environ.get("REPS", "60"))
    jobs = []
    for ndemes in (2, 5, 10, 40):
        for Nm in (0.25, 1.0, 4.0):
            for r in range(reps):
                jobs.append((island, (1000, Nm / 1000, ndemes,
                                      11 + r * 6151 + ndemes + int(Nm * 10))))
    for d in (1, 2, 3, 5, 8):
        for r in range(reps):
            jobs.append((stepping, (20, 1000, 0.002, d, 5 + r * 7919 + d)))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "24"))) as ex:
        out = [f.result() for f in [ex.submit(fn, a) for fn, a in jobs]]
    with open(sys.argv[1] if len(sys.argv) > 1 else "resolve.json", "w") as fh:
        json.dump(out, fh)

    from collections import defaultdict
    g = defaultdict(list)
    for r in out:
        if r["check"] == "island":
            g[(r["ndemes"], r["Nm"])].append(r)
    print("=== islandModelFst = 1/(1+4*Ne*m), total immigration held fixed ===")
    print(f"{'demes':>6} {'Nm':>6} {'sim':>9} {'+-':>7} {'lean':>9} {'err%':>7} "
          f"{'finite-deme':>12} {'err%':>7}")
    for k in sorted(g):
        rows = g[k]
        s = np.mean([r["sim"] for r in rows])
        se = np.std([r["sim"] for r in rows]) / np.sqrt(len(rows))
        lean, fd = rows[0]["lean"], rows[0]["finite_deme"]
        print(f"{k[0]:6d} {k[1]:6.2f} {s:9.5f} {se:7.5f} {lean:9.5f} "
              f"{100*(lean-s)/s:7.1f} {fd:12.5f} {100*(fd-s)/s:7.1f}")

    g2 = defaultdict(list)
    for r in out:
        if r["check"] == "stepping":
            g2[r["d"]].append(r)
    print("\n=== demoSteppingStoneFst = d/(d+4*Ne*m*s2): fit a single s2 ===")
    print(f"{'d':>4} {'sim':>9} {'+-':>7} {'implied s2':>11}")
    for k in sorted(g2):
        rows = g2[k]
        s = np.mean([r["sim"] for r in rows])
        se = np.std([r["sim"] for r in rows]) / np.sqrt(len(rows))
        Ne, m = rows[0]["Ne"], rows[0]["m"]
        # d/(d + 4*Ne*m*s2) = s  ->  s2 = d(1-s)/(4*Ne*m*s)
        s2 = k * (1 - s) / (4 * Ne * m * s)
        print(f"{k:4d} {s:9.5f} {se:7.5f} {s2:11.3f}")
    print("\nIf the form is right, implied s2 is constant across distance.")


if __name__ == "__main__":
    main()
