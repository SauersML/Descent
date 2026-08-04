"""Battery 9: the migration-drift recurrences and their three rival equilibria.

The corpus carries TWO one-step maps for the island-model inbreeding coefficient
and THREE closed forms for its fixed point:

  ibdRecurrenceStep        (1-rate)^2 * (1/(2Ne) + (1 - 1/(2Ne)) * x)
  fstMigDriftNext          (1 - 2m - 1/(2Ne)) * Fst + 1/(2Ne)

  ibdRecurrenceFixedPoint  (1-rate)^2 / ((1-rate)^2 + 2 Ne rate (2 - rate))
  fstMigDriftEquil         1 / (4 Ne m + 1)
  fstMigrationDriftEquil.  1 / (1 + 4 Ne m)

The last two are the same body under two names. The first is a different
function, and no theorem in the corpus relates it to either -- which is the
unresolved-fork pattern the new guard reports. One simulation settles all five,
because they are all predictions about the same measured trajectory.

The oracle is an explicit island model of allele frequencies: `n` demes, each
resampled from `2 Ne` gametes, with a fraction `m` of each deme replaced by
migrants drawn from the global pool each generation. `F_ST` is read as
`Var_between(p) / (p_bar (1 - p_bar))`, which is the quantity all five formulas
are written about. Mutation is included at a low rate purely to keep the process
from absorbing at fixation, and is small enough not to move the equilibrium.

The one-step maps are tested as ONE-STEP MAPS: predict `F_{t+1}` from the
measured `F_t` and compare against the measured `F_{t+1}`. A map tested only at
its own fixed point cannot distinguish a wrong slope from a right one.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def island_trajectory(Ne, m, n_demes=40, n_loci=3000, gens=400, mu=1e-5,
                      seed=1):
    """Allele frequencies in `n_demes` demes under drift, migration, mutation."""
    rng = np.random.default_rng(seed)
    two_n = int(2 * Ne)
    p = np.full((n_demes, n_loci), 0.5)
    fst = []
    for _ in range(gens + 1):
        pbar = p.mean(axis=0)
        var_b = p.var(axis=0)
        denom = (pbar * (1 - pbar))
        keep = denom > 1e-9
        fst.append(float(var_b[keep].mean() / denom[keep].mean())
                   if keep.any() else float("nan"))
        # migration: a fraction m of each deme is replaced by the global pool
        p = (1 - m) * p + m * pbar[None, :]
        # drift
        p = rng.binomial(two_n, np.clip(p, 0, 1)) / two_n
        # two-way mutation, kept small
        p = p * (1 - mu) + (1 - p) * mu
    return np.array(fst)


def test_one_step_maps():
    """Two rival one-step maps, predicted from the measured F_t."""
    cells_ibd, cells_lin = [], []
    for Ne, m in ((200, 0.002), (200, 0.01), (500, 0.005)):
        traj = island_trajectory(Ne, m, seed=6001)
        pred_i, pred_l, obs = [], [], []
        for t in range(50, len(traj) - 1):
            F = traj[t]
            pred_i.append((1 - m) ** 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * F))
            pred_l.append((1 - 2 * m - 1 / (2 * Ne)) * F + 1 / (2 * Ne))
            obs.append(traj[t + 1])
        obs = np.array(obs)
        sem = float(obs.std(ddof=1) / math.sqrt(len(obs)))
        lab = "Ne=%d m=%.3f" % (Ne, m)
        cells_ibd.append(dict(design=lab, lean=float(np.mean(pred_i)),
                              truth=float(obs.mean()), sem=max(sem, 1e-9)))
        cells_lin.append(dict(design=lab, lean=float(np.mean(pred_l)),
                              truth=float(obs.mean()), sem=max(sem, 1e-9)))
    record("ibdRecurrenceStep (one-step map)", "PortabilityDrift.lean",
           "(1-rate)^2 * (1/(2*Ne) + (1 - 1/(2*Ne)) * x)", cells_ibd,
           regime="island model, F_ST = Var_between(p)/(pbar(1-pbar))")
    record("fstMigDriftNext (one-step map)", "PortabilityDrift.lean",
           "(1 - 2*m - 1/(2*Ne)) * Fst + 1/(2*Ne)", cells_lin,
           regime="same trajectories, the rival linear map")


def test_equilibria():
    """Three closed forms for the fixed point, against the measured plateau."""
    cells_ibd, cells_simple = [], []
    for Ne, m in ((200, 0.002), (200, 0.005), (200, 0.01), (500, 0.005)):
        traj = island_trajectory(Ne, m, gens=800, seed=6101)
        plateau = traj[-200:]
        obs = float(plateau.mean())
        sem = float(plateau.std(ddof=1) / math.sqrt(len(plateau)))
        lab = "Ne=%d m=%.3f (4Nm=%.1f)" % (Ne, m, 4 * Ne * m)
        cells_ibd.append(dict(
            design=lab,
            lean=(1 - m) ** 2 / ((1 - m) ** 2 + 2 * Ne * m * (2 - m)),
            truth=obs, sem=max(sem, 1e-9)))
        cells_simple.append(dict(design=lab, lean=1 / (1 + 4 * Ne * m),
                                 truth=obs, sem=max(sem, 1e-9)))
    record("ibdRecurrenceFixedPoint / fstIslandMultiplicativeEquilibrium",
           "PortabilityDrift.lean",
           "(1-rate)^2 / ((1-rate)^2 + 2*Ne*rate*(2-rate))", cells_ibd,
           regime="island-model equilibrium F_ST, measured plateau")
    record("fstMigDriftEquil / fstMigrationDriftEquilibrium",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*m)", cells_simple,
           regime="same plateaus, the rival closed form")


def test_asymmetric_migration():
    """asymmetricFst = 1/(1 + 4 Ne m_into), and the symmetric-average reduction."""
    def two_deme(Ne, m12, m21, n_loci=4000, gens=900, mu=1e-5, seed=6201):
        rng = np.random.default_rng(seed)
        two_n = int(2 * Ne)
        p1 = np.full(n_loci, 0.5)
        p2 = np.full(n_loci, 0.5)
        out = []
        for g in range(gens + 1):
            pbar = (p1 + p2) / 2
            var_b = ((p1 - pbar) ** 2 + (p2 - pbar) ** 2) / 2
            den = pbar * (1 - pbar)
            keep = den > 1e-9
            out.append(float(var_b[keep].mean() / den[keep].mean())
                       if keep.any() else float("nan"))
            n1 = (1 - m12) * p1 + m12 * p2
            n2 = (1 - m21) * p2 + m21 * p1
            p1 = rng.binomial(two_n, np.clip(n1, 0, 1)) / two_n
            p2 = rng.binomial(two_n, np.clip(n2, 0, 1)) / two_n
            p1 = p1 * (1 - mu) + (1 - p1) * mu
            p2 = p2 * (1 - mu) + (1 - p2) * mu
        return np.array(out)

    cells_asym, cells_eff = [], []
    for Ne, m12, m21 in ((200, 0.004, 0.004), (200, 0.002, 0.006),
                         (200, 0.001, 0.007)):
        traj = two_deme(Ne, m12, m21)
        plateau = traj[-250:]
        obs = float(plateau.mean())
        sem = float(plateau.std(ddof=1) / math.sqrt(len(plateau)))
        lab = "m12=%.3f m21=%.3f" % (m12, m21)
        # asymmetricFst reads a single "into" rate; take the larger, which is
        # the reading that makes it a statement about the receiving deme
        cells_asym.append(dict(design=lab,
                               lean=1 / (1 + 4 * Ne * max(m12, m21)),
                               truth=obs, sem=max(sem, 1e-9)))
        m_eff = (m12 + m21) / 2
        cells_eff.append(dict(design=lab, lean=1 / (1 + 4 * Ne * m_eff),
                              truth=obs, sem=max(sem, 1e-9)))
    record("asymmetricFst [m_into read as the larger rate]",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*m_into)", cells_asym,
           regime="two demes with unequal migration, equilibrium F_ST")
    record("effectiveSymmetricMigration", "PortabilityDrift.lean",
           "1/(1 + 4*Ne*(m12 + m21)/2)", cells_eff,
           regime="same runs; does the asymmetric pair behave like its average?")


def test_coalescent_hazard():
    """The hazard trio, against a piecewise-constant-size coalescent."""
    import msprime
    # A two-epoch history: size Ne0 until T, then Ne1.  The pairwise coalescent
    # hazard is 1/(2 Ne(t)), so the integrated hazard is exactly computable and
    # the survival is exp(-that).
    Ne0, Ne1, T = 500.0, 3000.0, 800.0
    cells_s, cells_c = [], []
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne0)
    dem.add_population_parameters_change(time=T, initial_size=Ne1,
                                         population="A")
    ts_times = []
    for ts in msprime.sim_ancestry(samples=1, ploidy=2, demography=dem,
                                   num_replicates=60000, random_seed=6301):
        tr = ts.first()
        ts_times.append(tr.time(tr.root))
    tt = np.array(ts_times)
    for t in (200.0, 500.0, 800.0, 1500.0, 3000.0):
        integ = (min(t, T) / (2 * Ne0)
                 + max(0.0, t - T) / (2 * Ne1))
        surv = math.exp(-integ)
        obs_s = float((tt > t).mean())
        sem = math.sqrt(obs_s * (1 - obs_s) / len(tt))
        cells_s.append(dict(design="t=%.0f" % t, lean=surv, truth=obs_s,
                            sem=max(sem, 1e-9)))
        cells_c.append(dict(design="t=%.0f" % t, lean=1 - surv,
                            truth=1 - obs_s, sem=max(sem, 1e-9)))
    record("integratedCoalescentHazard / coalescenceSurvivalFromHazard",
           "PortabilityDrift.lean", "exp(-int_0^t hazard)", cells_s,
           regime="two-epoch coalescent, hazard 1/(2 Ne(t)), 60000 genealogies")
    record("coalescenceCdfFromHazard", "PortabilityDrift.lean",
           "1 - survival", cells_c, regime="same runs")


def main():
    for fn in (test_one_step_maps, test_equilibria, test_asymmetric_migration,
               test_coalescent_hazard):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk1_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-56s worst %8.1f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
