"""Battery 40: ibdRecurrenceFixedPoint, on the estimator that actually worked.

Two earlier attempts at this body were VOID. Both read F_ST in BRANCH mode and
both had their controls fail. `battery_bulk34.py` then established that the
site-frequency Hudson estimator -- the corpus convention, and the one
`simlib.island_fst` used for the run that validated
`fstMigrationMutationEquilibrium` -- reproduces its control cleanly on this same
demography. So this repeats the comparison on that estimator.

    ibdRecurrenceFixedPoint Ne rate = (1-rate)^2 / ((1-rate)^2 + 2 Ne rate (2-rate))

The exact fixed point and the diffusion form `1/(1 + 4 Ne m)` agree to first
order in `m`, so what separates them is `m` ITSELF, not `4 Ne m`. Holding
`4 Ne m` roughly fixed while shrinking `Ne` therefore raises the discrimination
and lowers the cost together: at `4 Ne m = 24`, `Ne = 100` puts the two forms 9%
apart, `Ne = 15` puts them far further.

Control: one panmictic population split into two arbitrary halves, through the
same estimator and filters -- F_ST must be 0. That is the control that worked in
battery 34, after two invented ones failed.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record

SEQ = 4e6
RHO = 1e-8
MU = 1e-8


def island_fst_sites(Ne, m, reps, seed):
    import msprime
    dem = msprime.Demography.island_model([Ne, Ne], migration_rate=m)
    vals = []
    for r in range(reps):
        ts = msprime.sim_ancestry(samples={"pop_0": 40, "pop_1": 40},
                                  demography=dem, sequence_length=SEQ,
                                  recombination_rate=RHO, random_seed=seed + r)
        mts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 4000 + r)
        if mts.num_sites < 50:
            continue
        gm = mts.genotype_matrix()
        A, B = mts.samples(population=0), mts.samples(population=1)
        vals.append(simlib.hudson_fst(gm[:, A].sum(1).astype(float), len(A),
                                      gm[:, B].sum(1).astype(float), len(B)))
    return simlib.summarize(vals)


def panmictic_control(seed):
    import msprime
    vals = []
    for r in range(6):
        ts = msprime.sim_ancestry(samples=80, population_size=500,
                                  sequence_length=SEQ, recombination_rate=RHO,
                                  random_seed=seed + r)
        mts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 900 + r)
        if mts.num_sites < 50:
            continue
        gm = mts.genotype_matrix()
        A, B = np.arange(0, 80), np.arange(80, 160)
        vals.append(simlib.hudson_fst(gm[:, A].sum(1).astype(float), len(A),
                                      gm[:, B].sum(1).astype(float), len(B)))
    return simlib.summarize(vals)


def main():
    cs = panmictic_control(40777)
    print("  CONTROL one population split: F_ST=%.5f ± %.5f (expect 0)"
          % (cs["mean"], cs["sem"]))
    control = dict(design="one population split arbitrarily [F_ST = 0]",
                   lean=0.0, truth=cs["mean"], sem=max(cs["sem"], 1e-6))
    cells_exact, cells_diff = [], []
    for Ne, m in ((400, 0.0025), (100, 0.02), (50, 0.06), (25, 0.16),
                  (15, 0.30)):
        s = island_fst_sites(Ne, m, reps=24, seed=40001 + int(1e5 * m))
        exact = (1 - m) ** 2 / ((1 - m) ** 2 + 2 * Ne * m * (2 - m))
        diff = 1.0 / (1.0 + 4 * Ne * m)
        lab = "Ne=%d m=%.4f (4Nm=%.1f)" % (Ne, m, 4 * Ne * m)
        print("  %-28s F_ST=%.5f ± %.5f | exact %.5f  diffusion %.5f (gap %.0f%%)"
              % (lab, s["mean"], s["sem"], exact, diff,
                 100 * abs(exact - diff) / max(exact, 1e-12)))
        cells_exact.append(dict(design=lab, lean=exact, truth=s["mean"],
                                sem=max(s["sem"], 1e-6)))
        cells_diff.append(dict(design=lab, lean=diff, truth=s["mean"],
                               sem=max(s["sem"], 1e-6)))
    reg = ("two-deme island model, 4 Mb with recombination, 24 replicates; "
           "F_ST is the site-frequency Hudson estimator as a ratio of averages "
           "-- the corpus convention, and the one whose control reproduces on "
           "this demography. m is swept 120-fold because m, not 4*Ne*m, is what "
           "separates the exact fixed point from the diffusion form")
    record("ibdRecurrenceFixedPoint / fstIslandMultiplicativeEquilibrium",
           "PortabilityDrift.lean",
           "(1-m)^2 / ((1-m)^2 + 2*Ne*m*(2-m))", cells_exact, regime=reg,
           control=control)
    record("fstMigrationDriftEquilibrium [diffusion form, competing]",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*m)", cells_diff,
           regime=reg, control=control)
    json.dump(RESULTS, open("battery_bulk40_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
