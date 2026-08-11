"""Why are battery_bulk14's two heterozygosity recurrences 631 sems off?

THE ROWS. hetMutationDriftRecurrence and hetMutationRecurrence, both held as LEAD
for want of a control. The battery itself records that the two are an exact
reparametrisation of each other, so they stand or fall together.

THE CANDIDATE, derived from the simulator rather than guessed. The battery mutates
FREQUENCIES two ways, `p <- p(1-mu) + (1-p)mu`, so the deviation from one half
contracts by `(1-2mu)` and heterozygosity `H = 0.5 - 2(p-0.5)^2` contracts toward
one half by `(1-2mu)^2`. With drift first, the simulator's expected map is

    H' = 0.5 - (0.5 - (1 - 1/(2Ne)) H) (1 - 2mu)^2

whose rate is about `1/(2Ne) + 4mu` and whose fixed point is
`0.5(1-d)/(1-cd)` with `c = 1-1/(2Ne)`, `d = (1-2mu)^2`. The bodies carry
`1/(2Ne) + 2mu` and `theta/(1+theta)`: the INFINITE-ALLELES rate, where a mutation
always makes a new allele. That is a factor of two in the mutation term, and it is
the same convention gap battery_dis2's docstring already records -- "a biallelic
two-way mutation model contracts the between-deme deviation by (1-2mu)^2 per
generation, so its rate is 2 theta ... while hetDecayFromScaled carries the
INFINITE-ALLELES rate theta" -- which dis2 answered by switching mutation off.

Four columns: simulated, the two bodies (identical by construction), and the
biallelic map derived above. The bar is the block sem over independent replicate
BLOCKS rather than the battery's across-loci sem, so pairing and locus
correlation cannot flatter it.
"""
import math

import numpy as np

DESIGNS = ((100, 1e-3), (500, 1e-3), (100, 5e-3))
STEPS, N_LOCI, REPS, BLOCKS = 15, 4000, 40, 10


def main():
    print("%-30s %11s %11s %11s %10s"
          % ("cell", "simulated", "body", "biallelic", "sem(blocks)"))
    for Ne, mu in DESIGNS:
        rng = np.random.default_rng(24101)
        two_n = int(2 * Ne)
        sims, bodies, bials = [], [], []
        for _ in range(BLOCKS):
            p = rng.uniform(0.1, 0.9, (REPS, N_LOCI))
            for _ in range(20):
                p = rng.binomial(two_n, p) / two_n
                p = p * (1 - mu) + (1 - p) * mu
            H0 = float((2 * p * (1 - p)).mean())
            for _ in range(STEPS):
                p = rng.binomial(two_n, p) / two_n
                p = p * (1 - mu) + (1 - p) * mu
            sims.append(float((2 * p * (1 - p)).mean()))
            h = H0
            for _ in range(STEPS):
                h = (1 - 1 / (2 * Ne)) * h + 2 * mu * (1 - h)
            bodies.append(h)
            c, d = 1 - 1 / (2 * Ne), (1 - 2 * mu) ** 2
            b = H0
            for _ in range(STEPS):
                b = 0.5 - (0.5 - c * b) * d
            bials.append(b)
        s = float(np.mean(sims))
        sem = float(np.std(sims, ddof=1) / math.sqrt(BLOCKS))
        bo, bi = float(np.mean(bodies)), float(np.mean(bials))
        print("%-30s %11.6f %11.6f %11.6f %10.6f"
              % ("Ne=%d mu=%.0e" % (Ne, mu), s, bo, bi, sem))
        print("%-30s %11s %11.2f %11.2f"
              % ("", "sems off:", abs(s - bo) / sem, abs(s - bi) / sem))


if __name__ == "__main__":
    main()
