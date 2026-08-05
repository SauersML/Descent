"""Battery 25: neiFst against Hudson, the convention relation itself.

`neiFst = (H_T - H_S) / H_T` is a definition in terms of heterozygosities, so
comparing it against a transcription of the same formula measures nothing. What
IS measurable is the relation between the two conventions this corpus uses:
Nei's G_ST and Hudson's F_ST are different estimators of "differentiation" and
differ by a factor that depends on the allele-frequency spectrum. Feeding the
wrong one somewhere has already cost this corpus a factor of four.

So the design measures BOTH estimators on the same simulated split, each through
its own code path -- `neiFst` applied to measured H_T and H_S, and
`simlib.hudson_fst` applied to the same genotype matrix -- and puts the RATIO on
trial across a divergence sweep. Two competing readings are carried: that the
two agree (ratio 1), and that Nei is half of Hudson (ratio 1/2).

IDENTITY RISK, screened first: the two estimators share the genotype matrix but
no algebra -- Nei is a ratio of average heterozygosities, Hudson a ratio of
averages of a different numerator and denominator. Their ratio is not forced to
any constant, which is exactly why it is worth measuring.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def main():
    import msprime
    cells_one, cells_half, cells_nei = [], [], []
    control = None
    Ne = 1000
    for t in (200, 500, 2000, 6000):
        nei_v, hud_v = [], []
        for r in range(16):
            dem = msprime.Demography()
            dem.add_population(name="A", initial_size=Ne)
            dem.add_population(name="B", initial_size=Ne)
            dem.add_population(name="ANC", initial_size=Ne)
            dem.add_population_split(time=t, derived=["A", "B"],
                                     ancestral="ANC")
            ts = msprime.sim_ancestry(samples={"A": 30, "B": 30},
                                      demography=dem, sequence_length=2e6,
                                      recombination_rate=1e-8,
                                      random_seed=25001 + r + t)
            mts = msprime.sim_mutations(ts, rate=1e-8, random_seed=125001 + r)
            if mts.num_sites == 0:
                continue
            gm = mts.genotype_matrix()
            a, b = mts.samples(population=0), mts.samples(population=1)
            ac1 = gm[:, a].sum(1).astype(float)
            ac2 = gm[:, b].sum(1).astype(float)
            nei_v.append(simlib.nei_gst(ac1, len(a), ac2, len(b)))
            hud_v.append(simlib.hudson_fst(ac1, len(a), ac2, len(b)))
        sn, sh = simlib.summarize(nei_v), simlib.summarize(hud_v)
        ratio = sn["mean"] / sh["mean"]
        sem = ratio * math.hypot(sn["sem"] / sn["mean"], sh["sem"] / sh["mean"])
        tau = t / (2.0 * Ne)
        lab = "t=%d (tau=%.2f)" % (t, tau)
        print("  %-20s nei=%.5f hud=%.5f  ratio=%.4f ± %.4f"
              % (lab, sn["mean"], sh["mean"], ratio, sem))
        cells_one.append(dict(design=lab, lean=1.0, truth=ratio, sem=sem))
        cells_half.append(dict(design=lab, lean=0.5, truth=ratio, sem=sem))
        cells_nei.append(dict(design=lab, lean=tau / (1 + tau),
                              truth=sn["mean"], sem=sn["sem"]))
        if t == 2000:
            control = dict(design=lab + " [Hudson vs tau/(1+tau), VALIDATED]",
                           lean=tau / (1 + tau), truth=sh["mean"],
                           sem=sh["sem"])
    reg = ("clean two-population split, no migration, 2 Mb with recombination, "
           "16 replicates; both estimators computed from the SAME genotype "
           "matrix through separate code paths, and the observable is their "
           "ratio across a thirtyfold divergence sweep")
    record("neiFst / hudsonFst ratio [agree, ratio = 1]",
           "PopulationGeneticsFoundations.lean", "neiGst / hudsonFst = 1",
           cells_one, regime=reg, control=control)
    record("neiFst / hudsonFst ratio [Nei = half Hudson, competing]",
           "PopulationGeneticsFoundations.lean", "neiGst / hudsonFst = 1/2",
           cells_half, regime=reg, control=control)
    record("neiFst [read against the split law tau/(1+tau)]",
           "PopulationGeneticsFoundations.lean", "(H_T - H_S) / H_T",
           cells_nei, regime=reg, control=control)
    json.dump(RESULTS, open("battery_bulk25_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
