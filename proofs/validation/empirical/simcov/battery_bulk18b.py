"""Battery 33b: the deme sweep again, holding the right thing fixed.

Battery 33 swept the deme count with msprime's `migration_rate` held at 2e-4 and
read the result as a failure of every candidate. That reading was wrong, and the
reason is a convention: `Demography.island_model(migration_rate=m)` sets the rate
between EACH PAIR of demes, so a deme's TOTAL emigration rate is `m (n-1)` and
grows with the number of demes. The corpus's `m` is the total rate. So that sweep
held the pairwise rate fixed while the quantity the formulas take was rising
linearly in `n`, and the measured `F_ST` fell for a reason no formula under test
was being asked about.

Read correctly the same three cells already agree: with `4 Ne m_pair n` as the
argument, the measurement lands at 0.29, 0.20 and 0.52 sems for n = 2, 4 and 10.

This run fixes the design rather than the arithmetic after the fact. The TOTAL
emigration rate is held fixed at `4 Ne m_total = 2` by setting the pairwise rate
to `m_total/(n-1)`, so the deme count is the only thing moving, which is what a
deme-count sweep is supposed to be. Three predictions are carried:

  no correction        1/(1 + bigM)              -- constant, the many-deme limit
  linear correction    1/(1 + bigM n/(n-1))      -- islandDemeCorrection
  squared correction   1/(1 + bigM (n/(n-1))^2)  -- the form the original detect
                                                    proposed, kept so the power
                                                    on the correction is chosen
                                                    by the data
"""
import json, math
import numpy as np
import simlib
from battery_core import RESULTS, record

def main():
    import msprime
    Ne, bigM = 1000, 2.0
    m_total = bigM / (4 * Ne)
    c_none, c_lin, c_sq = [], [], []
    for n in (2, 3, 5, 10, 25):
        m_pair = m_total / (n - 1)
        dem = msprime.Demography.island_model([Ne] * n, migration_rate=m_pair)
        vals = []
        for r in range(24):
            ts = msprime.sim_ancestry(samples={"pop_0": 25, "pop_1": 25},
                                      demography=dem, sequence_length=4e6,
                                      recombination_rate=1e-8,
                                      random_seed=30001 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            da = ts.diversity([A], mode="branch")[0]
            db = ts.diversity([B], mode="branch")[0]
            dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            vals.append(1.0 - ((da + db) / 2.0) / dab)
        s = simlib.summarize(vals)
        corr = n / (n - 1.0)
        lab = "%d demes (4 Ne m_total = %.1f held fixed)" % (n, bigM)
        print("  %2d demes: F_ST=%.5f ± %.5f | none %.5f  linear %.5f  sq %.5f"
              % (n, s["mean"], s["sem"], 1/(1+bigM), 1/(1+bigM*corr),
                 1/(1+bigM*corr**2)))
        c_none.append(dict(design=lab, lean=1/(1+bigM), truth=s["mean"], sem=s["sem"]))
        c_lin.append(dict(design=lab, lean=1/(1+bigM*corr), truth=s["mean"], sem=s["sem"]))
        c_sq.append(dict(design=lab, lean=1/(1+bigM*corr**2), truth=s["mean"], sem=s["sem"]))
    reg = ("island model with the TOTAL emigration rate held fixed at "
           "4*Ne*m = 2.0 -- the pairwise rate is set to m_total/(n-1) because "
           "msprime's migration_rate is per ordered pair -- while the deme "
           "count runs 2, 3, 5, 10, 25; F_ST from coalescence times")
    record("fstDriftMigration [no deme correction]", "DGP.lean",
           "1 / (1 + bigM)", c_none, regime=reg)
    record("islandDemeCorrection [linear n/(n-1)]",
           "PopulationGeneticsFoundations.lean",
           "1 / (1 + bigM * n/(n-1))", c_lin, regime=reg)
    record("islandDemeCorrection [squared (n/(n-1))^2, competing]",
           "PopulationGeneticsFoundations.lean",
           "1 / (1 + bigM * (n/(n-1))^2)", c_sq, regime=reg)
    json.dump(RESULTS, open("battery_bulk18b_results.json","w"), indent=1, default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-18s %-52s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100*w.get("rel_err", float("nan"))))

if __name__ == "__main__":
    main()
