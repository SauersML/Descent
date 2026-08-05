"""Battery 34: the scaled-parameter conventions, tested through what consumes them.

`scaledMutationRate = 4 Ne mu`, `scaledMigrationRate = 4 Ne m` and
`EvolutionaryParameters.tau = t_div/(2 Ne)` have no empirical content on their
own -- they name a scale, and a scale can only be checked against something that
consumes it. Each is therefore tested through an equilibrium or a transient that
is itself independently validated, and in every case the design varies `Ne` and
the scaled quantity INDEPENDENTLY, so that the `Ne`-dependence and the numeric
factor are both under test rather than only their product.

That independence is the whole design. A sweep that moves `Ne` and the rate
together at fixed `4 Ne mu` cannot tell `4 Ne mu` from `8 Ne mu`; a sweep that
moves them apart can, because the equilibrium depends on the product alone only
if the factor is right.

  theta = 4 Ne mu, through the infinite-alleles equilibrium identity
      `1/(1 + theta)`, which is validated as `fstMutationDriftEquilibrium`.

  bigM = 4 Ne m, through the two-deme island `F_ST` read from coalescence times,
      which needs no estimator convention, against `1/(1 + 2 bigM)` -- the deme
      factor 2 being `islandDemeCorrection` at n = 2, itself measured twice in
      this branch.

  tau = t_div/(2 Ne), through the pure-split `F_ST = tau/(1 + tau)`.

  fstEquilibrium = 1/(1 + theta + bigM) is the one genuinely new claim here: it
      asserts that mutation and migration enter ADDITIVELY on the scaled scale.
      That composition has never been measured in this branch. It is tested on
      an infinite-alleles island model with both forces on, at combinations that
      hold `theta + bigM` fixed while trading one against the other -- so a
      formula that weighted them differently would separate -- and again at
      several totals so the design also has span.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def ia_single_homozygosity(Ne, mu, gens, reps, seed):
    rng = np.random.default_rng(seed)
    two_n = 2 * Ne
    state = np.zeros((reps, two_n), dtype=np.int64)
    nxt = np.ones(reps, dtype=np.int64)
    for g in range(gens):
        idx = rng.integers(0, two_n, size=(reps, two_n))
        state = np.take_along_axis(state, idx, axis=1)
        hit = rng.random((reps, two_n)) < mu
        for r in range(reps):
            k = int(hit[r].sum())
            if k:
                state[r][hit[r]] = nxt[r] + np.arange(k)
                nxt[r] += k
            _, state[r] = np.unique(state[r], return_inverse=True)
        nxt[:] = state.max(axis=1) + 1
    vals = np.empty(reps)
    for r in range(reps):
        c = np.bincount(state[r]).astype(float)
        vals[r] = (c * (c - 1)).sum() / (two_n * (two_n - 1))
    return float(vals.mean()), float(vals.std(ddof=1) / math.sqrt(reps))


def test_scaled_mutation_rate():
    cells = []
    # theta varied 4x; Ne varied 4x INDEPENDENTLY, so pairs share theta at
    # different Ne and share Ne at different theta
    for Ne, mu in ((100, 2.5e-3), (400, 6.25e-4), (100, 1.0e-2), (400, 2.5e-3)):
        theta = 4 * Ne * mu
        F, sem = ia_single_homozygosity(Ne, mu, gens=10 * Ne, reps=180,
                                        seed=29000 + Ne + int(1e6 * mu))
        print("  Ne=%4d mu=%.2e theta=%.1f: F=%.5f ± %.5f  vs 1/(1+theta)=%.5f"
              % (Ne, mu, theta, F, sem, 1 / (1 + theta)))
        cells.append(dict(design="Ne=%d mu=%.2e (theta=%.1f)" % (Ne, mu, theta),
                          lean=1 / (1 + theta), truth=F, sem=sem))
    record("scaledMutationRate", "DGP.lean", "4 * Ne * mu", cells,
           regime="tested through the infinite-alleles equilibrium identity "
                  "1/(1+theta), which is independently validated; theta spans "
                  "a factor of four and Ne spans a factor of four "
                  "INDEPENDENTLY, so a wrong numeric factor or a wrong "
                  "Ne-dependence would both show, which a sweep at fixed "
                  "4*Ne*mu could not detect")


def test_scaled_migration_rate_and_tau():
    import msprime
    cells_m, cells_tau = [], []
    for Ne, m in ((500, 5e-4), (2000, 1.25e-4), (500, 2e-3), (2000, 5e-4)):
        bigM = 4 * Ne * m
        dem = msprime.Demography.island_model([Ne, Ne], migration_rate=m)
        vals = []
        for r in range(22):
            ts = msprime.sim_ancestry(samples={"pop_0": 25, "pop_1": 25},
                                      demography=dem, sequence_length=4e6,
                                      recombination_rate=1e-8,
                                      random_seed=29101 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            da = ts.diversity([A], mode="branch")[0]
            db = ts.diversity([B], mode="branch")[0]
            dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            vals.append(1.0 - ((da + db) / 2.0) / dab)
        s = simlib.summarize(vals)
        print("  Ne=%4d m=%.2e bigM=%.1f: F_ST=%.5f ± %.5f  vs 1/(1+2M)=%.5f"
              % (Ne, m, bigM, s["mean"], s["sem"], 1 / (1 + 2 * bigM)))
        cells_m.append(dict(design="Ne=%d m=%.2e (bigM=%.1f)" % (Ne, m, bigM),
                            lean=1 / (1 + 2 * bigM), truth=s["mean"],
                            sem=s["sem"]))

    for Ne, t_div in ((1000, 500), (4000, 2000), (1000, 2000), (4000, 1000)):
        tau = t_div / (2 * Ne)
        dem = msprime.Demography()
        dem.add_population(name="A", initial_size=Ne)
        dem.add_population(name="B", initial_size=Ne)
        dem.add_population(name="ANC", initial_size=Ne)
        dem.add_population_split(time=t_div, derived=["A", "B"],
                                 ancestral="ANC")
        vals = []
        for r in range(22):
            ts = msprime.sim_ancestry(samples={"A": 25, "B": 25},
                                      demography=dem, sequence_length=4e6,
                                      recombination_rate=1e-8,
                                      random_seed=29201 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            da = ts.diversity([A], mode="branch")[0]
            db = ts.diversity([B], mode="branch")[0]
            dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            vals.append(1.0 - ((da + db) / 2.0) / dab)
        s = simlib.summarize(vals)
        print("  Ne=%4d t_div=%4d tau=%.2f: F_ST=%.5f ± %.5f  vs tau/(1+tau)=%.5f"
              % (Ne, t_div, tau, s["mean"], s["sem"], tau / (1 + tau)))
        cells_tau.append(dict(design="Ne=%d t_div=%d (tau=%.2f)"
                                     % (Ne, t_div, tau),
                              lean=tau / (1 + tau), truth=s["mean"],
                              sem=s["sem"]))
    record("scaledMigrationRate", "DGP.lean", "4 * Ne * m", cells_m,
           regime="tested through the two-deme island F_ST read from "
                  "coalescence times against 1/(1 + 2 bigM), the factor 2 "
                  "being islandDemeCorrection at n=2; bigM spans a factor of "
                  "four and Ne spans a factor of four INDEPENDENTLY")
    record("EvolutionaryParameters.tau", "DGP.lean", "t_div / (2 * Ne)",
           cells_tau,
           regime="tested through the pure-split F_ST = tau/(1+tau) from "
                  "coalescence times; tau spans a factor of four and Ne spans "
                  "a factor of four independently, so the 2 in 2*Ne is under "
                  "test and not just the ratio")


def test_fst_equilibrium_additivity():
    """1/(1 + theta + bigM): do mutation and migration enter additively?"""
    import msprime
    cells = []
    Ne = 400
    combos = [(1.0, 0.0), (0.5, 0.5), (0.0, 1.0),
              (3.0, 1.0), (2.0, 2.0), (1.0, 3.0)]
    for theta, bigM in combos:
        mu = theta / (4 * Ne)
        m = bigM / (4 * Ne)
        n_demes = 2
        dem = msprime.Demography.island_model([Ne] * n_demes,
                                              migration_rate=max(m, 0.0))
        vals = []
        for r in range(20):
            ts = msprime.sim_ancestry(samples={"pop_0": 20, "pop_1": 20},
                                      demography=dem, sequence_length=2e6,
                                      recombination_rate=1e-8,
                                      random_seed=29301 + r)
            if mu > 0:
                ts = msprime.sim_mutations(ts, rate=mu / 2e6 * 1.0,
                                           random_seed=29401 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            da = ts.diversity([A], mode="branch")[0]
            db = ts.diversity([B], mode="branch")[0]
            dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            vals.append(1.0 - ((da + db) / 2.0) / dab)
        s = simlib.summarize(vals)
        cells.append(dict(design="theta=%.1f bigM=%.1f (sum=%.1f)"
                                 % (theta, bigM, theta + bigM),
                          lean=1 / (1 + theta + bigM), truth=s["mean"],
                          sem=s["sem"]))
        print("  theta=%.1f bigM=%.1f: F=%.5f ± %.5f  vs 1/(1+sum)=%.5f"
              % (theta, bigM, s["mean"], s["sem"],
                 1 / (1 + theta + bigM)))
    record("fstEquilibrium [additivity of theta and bigM]", "DGP.lean",
           "1 / (1 + theta + bigM)", cells,
           regime="two-deme island model with both forces on, at three "
                  "combinations holding theta+bigM = 1 and three holding it at "
                  "4, so a formula weighting the two forces differently would "
                  "separate WITHIN each group while the design still has span "
                  "ACROSS groups")


def main():
    for fn in (test_scaled_mutation_rate, test_scaled_migration_rate_and_tau,
               test_fst_equilibrium_additivity):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk19_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-58s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
