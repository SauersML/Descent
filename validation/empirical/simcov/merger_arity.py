"""Does the TRIPLE-merger rate see what the pairwise law cannot?

Instance 9 showed the normalised pairwise coalescence law is identical across
Lambda-coalescents. The complement of that claim is that lambda_{3,3} -- the rate
at which three lineages merge at once, normalised by the pairwise rate -- DOES
separate them. Measured directly by counting merger sizes in the genealogies:
a Kingman coalescent has no multiple mergers at all, so its multiple-merger
fraction is exactly zero, and any nonzero fraction is a distinction the pairwise
probe returned the same number on.
"""
import numpy as np, msprime, collections

print("%-18s %12s %12s %12s" % ("model", "binary", "multi(>=3)", "multi frac"))
for name, mdl in [("Kingman", msprime.StandardCoalescent()),
                  ("Beta alpha=1.9", msprime.BetaCoalescent(alpha=1.9)),
                  ("Beta alpha=1.5", msprime.BetaCoalescent(alpha=1.5)),
                  ("Beta alpha=1.1", msprime.BetaCoalescent(alpha=1.1)),
                  ("Dirac psi=0.3", msprime.DiracCoalescent(psi=0.3, c=1.0))]:
    binary = multi = 0
    for ts in msprime.sim_ancestry(samples=10, ploidy=2, population_size=1000,
                                   model=mdl, num_replicates=3000,
                                   random_seed=5):
        t = ts.first()
        for u in t.nodes():
            nc = len(t.children(u))
            if nc == 2:
                binary += 1
            elif nc >= 3:
                multi += 1
    tot = binary + multi
    frac = multi / tot if tot else 0.0
    sem = (frac * (1 - frac) / tot) ** 0.5 if tot else 0.0
    print("%-18s %12d %12d   %.4f±%.4f" % (name, binary, multi, frac, sem))
print("\nKingman is exactly zero by construction; every other row is a")
print("distinction the normalised pairwise law reported as identical.")
