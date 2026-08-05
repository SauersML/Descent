"""Battery 20b: `hetMutationFloor`, with the infinite-alleles engine repaired.

Battery 20's group B was VOID: its Ewens control returned E[K] = 2 in every
cell above theta = 0.1, which is not a number the sampling formula can produce,
so the engine and not the definition was what the cells were measuring.  The
cause was `discrete_genome=False`: under a continuous genome every mutation
lands at its OWN position, so a run with twenty mutations is twenty biallelic
SITES rather than one twenty-allele LOCUS, and reading the first variant sees
two states no matter how large theta is.

Repaired: `sequence_length=1` with the default discrete genome puts every
mutation at position 0, where `InfiniteAlleles` stacks them into one locus whose
allelic state is the last mutation on each lineage's path -- the infinite-alleles
model the body's `4 Ne mu / (1 + 4 Ne mu)` is the equilibrium heterozygosity of.

The Ewens control is carried unchanged and now has to pass before any verdict on
`hetMutationFloor` is allowed to stand.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def main():
    import msprime

    cells, cells_k = [], []
    control = None
    Ne, n_dip = 1000, 50
    for theta in (0.1, 0.5, 1.0, 3.0, 10.0):
        mu = theta / (4.0 * Ne)
        hets, ks = [], []
        for r in range(40):
            ts = msprime.sim_ancestry(
                samples=n_dip, population_size=Ne, sequence_length=1,
                random_seed=81001 + r)
            mts = msprime.sim_mutations(
                ts, rate=mu, model=msprime.InfiniteAlleles(),
                random_seed=181001 + r)
            states = None
            for v in mts.variants():
                states = np.asarray(v.genotypes)
                break
            if states is None:
                states = np.zeros(mts.num_samples, dtype=int)
            _, counts = np.unique(states, return_counts=True)
            n = states.size
            p = counts / n
            hets.append(float(n / (n - 1.0) * (1.0 - np.sum(p ** 2))))
            ks.append(float(counts.size))
        s = simlib.summarize(hets)
        sk = simlib.summarize(ks)
        n = 2 * n_dip
        ewens_k = sum(theta / (theta + i - 1.0) for i in range(1, n + 1))
        lab = "theta=4*Ne*mu=%.1f" % theta
        print("  %-22s  H = %.5f ± %.5f  (lean %.5f) | K = %.2f ± %.2f "
              "(Ewens %.2f)"
              % (lab, s["mean"], s["sem"], theta / (1 + theta),
                 sk["mean"], sk["sem"], ewens_k))
        cells.append(dict(design=lab, lean=theta / (1.0 + theta),
                          truth=s["mean"], sem=s["sem"]))
        cells_k.append(dict(design=lab, lean=ewens_k, truth=sk["mean"],
                            sem=sk["sem"]))
        if abs(theta - 1.0) < 1e-9:
            control = dict(design=lab + " [Ewens E(K), independent]",
                           lean=ewens_k, truth=sk["mean"], sem=sk["sem"])

    reg = ("single-locus INFINITE-ALLELES mutation at coalescent equilibrium, "
           "Ne = 1000, 100 sampled chromosomes, 40 independent replicates; "
           "heterozygosity is the unbiased 1 - sum p_i^2 over the WHOLE "
           "sample, never conditioned on the locus being polymorphic")
    record("[control] Ewens expected allele count on the same samples",
           "PortabilityDrift.lean", "sum_i theta/(theta+i-1)", cells_k,
           regime=reg + "; an independent classical result sharing no algebra "
                        "with the body under test")
    record("hetMutationFloor", "PortabilityDrift.lean",
           "4 * Ne * mu / (1 + 4 * Ne * mu)", cells, regime=reg,
           control=control)

    json.dump(RESULTS, open("battery_bulk20b_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-56s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
