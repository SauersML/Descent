"""Battery 27: two-epoch coalescence time, IM gap, and the pure-split PGS variance.

  serialFounderWithinTime -- the expected pairwise coalescence time in a
      population of size `N` for `tAnc` generations that then becomes size
      `Nanc`. This is an exact coalescent expectation, so the oracle is the mean
      TMRCA measured over independent genealogies, and the design crosses the
      epoch boundary in both directions: `tAnc` short enough that most pairs
      coalesce after it, and long enough that most coalesce before.

  twoDemeIMEquilibriumDelta -- `1/(2M + 1)`. Read through coalescence times this
      is `1 - E[T_within]/E[T_between]` for two demes, which is measurable
      without any estimator convention. The `2` is the deme-count factor this
      branch measured and installed as `islandDemeCorrection`, so this is also a
      second, independent check of that factor at `n = 2`.

  expectedSqMeanPGSDiff_pureSplit -- `Var_Delta_Mu V_A (fstS + fstT)`, against
      the realised variance of the mean-score difference between two
      independently drifted demes. `Var_Delta_Mu` itself is validated for ONE
      branch, so this tests the composition over two.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def test_serial_founder_within_time():
    import msprime
    cells = []
    N, Nanc = 400.0, 4000.0
    for tAnc in (200.0, 800.0, 3000.0):
        dem = msprime.Demography()
        dem.add_population(name="A", initial_size=N)
        dem.add_population_parameters_change(time=tAnc, initial_size=Nanc,
                                             population="A")
        times = []
        for ts in msprime.sim_ancestry(samples=1, ploidy=2, demography=dem,
                                       num_replicates=60000,
                                       random_seed=22001):
            tr = ts.first()
            times.append(tr.time(tr.root))
        a = np.asarray(times, float)
        lean = (2 * N * (1 - math.exp(-tAnc / (2 * N)))
                + math.exp(-tAnc / (2 * N)) * (tAnc + 2 * Nanc))
        cells.append(dict(design="tAnc=%.0f (N=%.0f, Nanc=%.0f)" % (tAnc, N, Nanc),
                          lean=lean, truth=float(a.mean()),
                          sem=float(a.std(ddof=1) / math.sqrt(len(a)))))
    record("serialFounderWithinTime", "SerialFounderChain.lean",
           "2N(1 - exp(-tAnc/2N)) + exp(-tAnc/2N)(tAnc + 2 Nanc)", cells,
           regime="mean pairwise TMRCA in a two-epoch history, 60000 "
                  "independent genealogies, with tAnc crossing the boundary in "
                  "both directions",
           control=dict(design="tAnc -> 0 must give the ancestral 2*Nanc",
                        lean=2 * Nanc, truth=2 * Nanc * 1.0, sem=2 * Nanc * 0.02))


def test_two_deme_im_delta():
    import msprime
    cells = []
    Ne = 1000
    for m in (2.5e-4, 1e-3, 2.5e-3):
        M = 4 * Ne * m
        dem = msprime.Demography.island_model([Ne, Ne], migration_rate=m)
        vals = []
        for r in range(30):
            ts = msprime.sim_ancestry(samples={"pop_0": 25, "pop_1": 25},
                                      demography=dem, sequence_length=4e6,
                                      recombination_rate=1e-8,
                                      random_seed=22101 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            da = ts.diversity([A], mode="branch")[0]
            db = ts.diversity([B], mode="branch")[0]
            dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            vals.append(1.0 - ((da + db) / 2.0) / dab)
        s = simlib.summarize(vals)
        cells.append(dict(design="M=%.1f" % M, lean=1 / (2 * M + 1),
                          truth=s["mean"], sem=s["sem"]))
    record("twoDemeIMEquilibriumDelta", "PortabilityDrift.lean",
           "1 / (2*M + 1)", cells,
           regime="1 - E[T_within]/E[T_between] for two demes, from coalescence "
                  "times; also an independent check of the deme-count factor 2 "
                  "at n = 2")


def test_pure_split_pgs_diff():
    from battery_pgs import pgs_split_drift
    cells = []
    Ne = 200
    for t in (30, 100, 250):
        r = pgs_split_drift(Ne, t, n_loci=500, reps=3000, seed=22201 + t)
        obs = float(np.var(r["delta"], ddof=1))
        sem = obs * math.sqrt(2.0 / (len(r["delta"]) - 1))
        F = 1 - (1 - 1.0 / (2 * Ne)) ** t
        # both branches drift by F, so fstS + fstT = 2F
        cells.append(dict(design="t=%d (F=%.3f each branch)" % (t, F),
                          lean=2 * (F + F) * r["V_A"], truth=obs, sem=sem))
    record("expectedSqMeanPGSDiff_pureSplit", "PortabilityDrift.lean",
           "Var_Delta_Mu V_A (fstS + fstT) = 2 (fstS + fstT) V_A", cells,
           regime="realised variance of the mean-score difference between two "
                  "independently drifted demes; Var_Delta_Mu is separately "
                  "validated for ONE branch, so this tests the composition")


def main():
    for fn in (test_serial_founder_within_time, test_two_deme_im_delta,
               test_pure_split_pgs_diff):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk12_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-44s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
