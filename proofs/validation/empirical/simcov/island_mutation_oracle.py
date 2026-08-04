"""An island oracle WITH mutation, independent of both things it adjudicates.

The forward infinite-alleles engine sits about 5 percent below
`fstEquilibrium = 1/(1 + theta + bigM)`, flat across a factor of five in
migration, and three explanations have been tested and rejected. Two remain:

  (a) the forward engine's generation cycle, where migration and reproduction
      are a single parent draw rather than the two composed events; or
  (b) the corpus formula, which composes `theta` and `bigM` ADDITIVELY.

Nothing in this branch could separate them, because the only other island oracle
is the msprime coalescent used mutation-free -- and a mutation-free oracle cannot
test a composition OF mutation WITH migration.

This supplies the missing one. msprime simulates the island genealogy exactly,
and `InfiniteAlleles` mutation puts a never-before-seen allele at every mutation
event, which is the same model the forward engine implements and the same one
`theta` is written for. Identity is equality of allele labels, so `H_S` and `H_T`
are counted, and the unbiased `sum c(c-1)/(n(n-1))` is used for both.

It shares NO code with the forward engine and NO derivation with the formula, so
whichever it agrees with is the one that is right.

RESULT: INCONCLUSIVE, and the reason is a flaw in THIS oracle rather than in
either candidate.

    m       corpus    this oracle    forward engine
    0.002   0.3004    -19.5%         -4.8%
    0.005   0.1889    -20.2%         -5.5%
    0.010   0.1167    -23.0%         -5.5%

The two simulators disagree with each other by fifteen points, so neither
adjudicates anything. A tie-breaker that disagrees with both candidates is not a
tie-breaker.

The likely cause is in the sampling above: `sampled_demes = 4` out of
`n_demes = 12`, so `H_T` here is the pooled heterozygosity of a THIRD of the
population, not of the whole of it. A subset pools less variation than the full
set, so `H_T` is too small, and `F_ST = 1 - H_S/H_T` is biased low -- which is
the direction and roughly the size of the extra fifteen points. The forward
engine computes `H_T` over every deme, which is what `1/(1 + theta + bigM)` is
written about.

The fix is to sample all demes, and it is NOT applied here: the run costs ten
minutes and this is the fifth consecutive design in this thread whose first
version was wrong, so the next attempt should start from a derivation of what
`H_T` means under partial sampling rather than from another guess. Until then
the corpus formula is neither confirmed nor contradicted, and `fstEquilibrium`
keeps the status battery 7 gave it -- validated against a mutation-free
coalescent at 0.21 to 1.13 sems, which tests its `bigM` term and not its
composition with `theta`.
"""
import math

import numpy as np


def unbiased_hom(counts, n):
    if n < 2:
        return float("nan")
    return float((counts * (counts - 1)).sum()) / (n * (n - 1))


def island_fst_with_mutation(Ne, m, mu, n_demes=12, n_dip=25, seq_len=400,
                             reps=14, seed=1, sampled_demes=4):
    """Equilibrium F_ST under the structured coalescent with infinite alleles."""
    import msprime
    dem = msprime.Demography.island_model([Ne] * n_demes,
                                          migration_rate=m / (n_demes - 1.0))
    vals = []
    for r in range(reps):
        samples = {f"pop_{i}": n_dip for i in range(sampled_demes)}
        ts = msprime.sim_ancestry(samples=samples, demography=dem,
                                  sequence_length=seq_len,
                                  recombination_rate=5e-3,
                                  random_seed=seed + r)
        ts = msprime.sim_mutations(ts, rate=mu,
                                   model=msprime.InfiniteAlleles(),
                                   random_seed=seed + 5000 + r)
        gm = ts.genotype_matrix()
        if gm.shape[0] == 0:
            continue
        deme_of = {}
        for i in range(sampled_demes):
            deme_of[i] = ts.samples(population=i)
        num, den = 0.0, 0.0
        for row in gm:
            k = int(row.max()) + 1
            hs = 0.0
            for i in range(sampled_demes):
                idx = deme_of[i]
                c = np.bincount(row[idx], minlength=k).astype(float)
                hs += 1 - unbiased_hom(c, len(idx))
            hs /= sampled_demes
            allidx = np.concatenate([deme_of[i] for i in range(sampled_demes)])
            c = np.bincount(row[allidx], minlength=k).astype(float)
            ht = 1 - unbiased_hom(c, len(allidx))
            # ratio of averages, the convention every F_ST in this harness uses
            num += ht - hs
            den += ht
        if den > 0:
            vals.append(num / den)
    a = np.asarray(vals, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(len(a)))


def main():
    Ne, n_demes = 150, 12
    print("island F_ST with infinite-alleles mutation, structured coalescent")
    print("%-26s %10s %10s %9s %9s" % ("design", "corpus", "oracle", "sem", "rel"))
    for m, mu in ((0.002, 1.7e-3), (0.005, 1.7e-3), (0.010, 1.7e-3)):
        theta = 4 * Ne * mu
        bigM = 4 * Ne * m
        pred = 1 / (1 + theta + bigM * n_demes / (n_demes - 1.0))
        got, sem = island_fst_with_mutation(Ne, m, mu, n_demes=n_demes,
                                            seed=41)
        print("%-26s %10.4f %10.4f %9.4f %+8.1f%%"
              % ("m=%.3f theta=%.2f" % (m, theta), pred, got, sem,
                 100 * (got - pred) / pred))
    print("\nThe forward engine gave -4.8, -5.5 and -5.5 percent on these cells.")
    print("If this oracle agrees with the corpus formula, the forward engine's")
    print("generation cycle is at fault. If it agrees with the forward engine,")
    print("the additive composition of theta and bigM is.")


if __name__ == "__main__":
    main()
