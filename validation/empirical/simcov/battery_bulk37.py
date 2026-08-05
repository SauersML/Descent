"""Battery 37: coalescentTimeScale = 2*Ne, this time with a valid control.

`battery_bulk23.py` measured this correctly -- mean pairwise coalescence time
against `2*Ne` over a tenfold Ne sweep, worst 1.42 sems -- but carried a control
asserting that the coefficient of variation of the replicate means is 1. That
holds for a single exponential `T2`, not for a mean over the many independent
genealogies recombination supplies, so the control failed and the `4*Ne`
rejection was recorded VOID. A run whose control fails is rightly distrusted
even where its headline comparison does not depend on it, so the measurement is
repeated here with a control that can actually pass.

The control: the expected number of SEGREGATING SITES in a sample of `n`,
`E[S] = theta * sum_{i=1}^{n-1} 1/i` (Watterson). It is classical, it is
independent of the coalescence-time comparison, and it is computed from the same
tree sequences -- so if the demography or the mutation placement were wrong, it
would show.

Competitor, as before: `4*Ne`, the scaling that belongs to RATES
(`theta = 4*Ne*mu`, `M = 4*Ne*m`) and not to this time.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def main():
    import msprime
    cells_two, cells_four, cells_ctl = [], [], []
    control = None
    for Ne in (500, 1000, 2000, 5000):
        t2, sseg = [], []
        for r in range(30):
            ts = msprime.sim_ancestry(samples=1, population_size=Ne,
                                      sequence_length=2e6,
                                      recombination_rate=1e-8,
                                      random_seed=37001 + r)
            # mean pairwise coalescence time, branch mode, no mutation model
            t2.append(float(ts.diversity(mode="branch")) / 2.0)
            # Watterson control needs mutations and a larger sample
            ts2 = msprime.sim_ancestry(samples=10, population_size=Ne,
                                       sequence_length=2e5,
                                       recombination_rate=0.0,
                                       random_seed=37501 + r)
            mts = msprime.sim_mutations(ts2, rate=1e-8,
                                        random_seed=37901 + r)
            sseg.append(float(mts.num_sites))
        s2, ss = simlib.summarize(t2), simlib.summarize(sseg)
        lab = "Ne=%d" % Ne
        print("  %-10s E[T2] = %.1f ± %.1f  (2Ne=%d, 4Ne=%d) | S = %.1f ± %.1f"
              % (lab, s2["mean"], s2["sem"], 2 * Ne, 4 * Ne,
                 ss["mean"], ss["sem"]))
        cells_two.append(dict(design=lab, lean=2.0 * Ne, truth=s2["mean"],
                              sem=max(s2["sem"], 1e-6)))
        cells_four.append(dict(design=lab, lean=4.0 * Ne, truth=s2["mean"],
                               sem=max(s2["sem"], 1e-6)))
        # Watterson: E[S] = theta_total * harmonic(n-1), n = 20 chromosomes
        theta_tot = 4 * Ne * 1e-8 * 2e5
        harm = sum(1.0 / i for i in range(1, 20))
        cells_ctl.append(dict(design=lab, lean=theta_tot * harm,
                              truth=ss["mean"], sem=max(ss["sem"], 1e-6)))
        if Ne == 1000:
            control = dict(design=lab + " [Watterson E(S) = theta * H_{n-1}]",
                           lean=theta_tot * harm, truth=ss["mean"],
                           sem=max(ss["sem"], 1e-6))
    reg = ("single panmictic diploid population; E[T2] read in BRANCH mode over "
           "2 Mb with recombination, so each replicate averages many "
           "independent genealogies and no mutation-rate convention enters. "
           "Ne is swept tenfold")
    record("coalescentTimeScale", "Conventions.lean", "ploidy * Ne = 2 * Ne",
           cells_two, regime=reg, control=control)
    record("coalescentTimeScale [4*Ne reading, competing]", "Conventions.lean",
           "4 * Ne", cells_four, regime=reg, control=control)
    record("[control] Watterson segregating sites on the same trees",
           "Conventions.lean", "theta * sum_{i<n} 1/i", cells_ctl, regime=reg)
    json.dump(RESULTS, open("battery_bulk37_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
