"""Battery 6: the coverage push, on a convention-free F_ST oracle.

Every F_ST number in batteries 1-5 came from an ESTIMATOR applied to simulated
genotypes, so each verdict carried an estimator convention along with it -- and
two of the six original findings were convention errors rather than defects.
This battery removes the convention from the oracle entirely.

`F_ST` in the Hudson sense IS `1 - E[T_within] / E[T_between]`, and tskit reports
mean pairwise coalescence times exactly, as branch lengths, with no mutations and
no estimator in between: `diversity(mode="branch")` is `2 E[T_within]` and
`divergence(mode="branch")` is `2 E[T_between]`, and the factor of two cancels in
the ratio. That is the definition, evaluated on the true genealogy. It is also
far more precise than the mutation route, because it uses every tree rather than
only the ones a mutation happened to land on.

This settles the island-model deme-count question that battery 5 left open,
where the linear and squared corrections disagreed only at two demes and the
mutation-based error bars were too wide to separate them cleanly.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


# ---------------------------------------------------------------------------
# convention-free F_ST from coalescence times
# ---------------------------------------------------------------------------
def fst_from_times(demography, pop_a, pop_b, n_dip=25, seq_len=1e6,
                   rho=1e-8, reps=30, seed=1):
    """`1 - E[T_within] / E[T_between]`, read off the true genealogies."""
    import msprime
    vals = []
    for r in range(reps):
        ts = msprime.sim_ancestry(
            samples={pop_a: n_dip, pop_b: n_dip}, demography=demography,
            sequence_length=seq_len, recombination_rate=rho,
            random_seed=seed + r)
        A = ts.samples(population=pop_a)
        B = ts.samples(population=pop_b)
        d_a = ts.diversity([A], mode="branch")[0]
        d_b = ts.diversity([B], mode="branch")[0]
        d_ab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
        t_w = (d_a + d_b) / 2.0
        vals.append(1.0 - t_w / d_ab)
    return simlib.summarize(vals)


def island_demography(Ne, m_total, n_demes):
    import msprime
    return msprime.Demography.island_model(
        [Ne] * n_demes, migration_rate=m_total / (n_demes - 1.0))


# ---------------------------------------------------------------------------
# 1. the island deme-count law, settled
# ---------------------------------------------------------------------------
def test_island_law():
    """Linear `n/(n-1)` against squared `(n/(n-1))^2`, on exact coalescence times."""
    Ne, m = 1000, 1e-3
    cells_lin, cells_sq, cells_blind = [], [], []
    for n in (2, 3, 4, 6, 10, 20, 40):
        s = fst_from_times(island_demography(Ne, m, n), 0, 1,
                           n_dip=25, seq_len=2e6, reps=40, seed=3001)
        lab = "n=%d" % n
        c = n / (n - 1.0)
        cells_lin.append(dict(design=lab, lean=1 / (1 + 4 * Ne * m * c),
                              truth=s["mean"], sem=s["sem"]))
        cells_sq.append(dict(design=lab, lean=1 / (1 + 4 * Ne * m * c ** 2),
                             truth=s["mean"], sem=s["sem"]))
        cells_blind.append(dict(design=lab, lean=1 / (1 + 4 * Ne * m),
                                truth=s["mean"], sem=s["sem"]))
    record("fstIslandEquilibriumFiniteDemes [linear n/(n-1)]",
           "PopulationGeneticsFoundations.lean",
           "1 / (1 + 4*Ne*m*(n/(n-1)))", cells_lin,
           regime="symmetric island model, exact coalescence times")
    record("islandFstFiniteDemes [squared (n/(n-1))^2]",
           "PopulationGeneticsFoundations.lean",
           "1 / (1 + 4*Ne*m*(d/(d-1))^2)", cells_sq,
           regime="same runs, the sibling correction")
    record("fstMigrationDriftEquilibrium [deme-blind]",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*m)", cells_blind,
           regime="same runs, no deme-count correction")


# ---------------------------------------------------------------------------
# 2. mutation-drift F_ST: equilibrium and transient
# ---------------------------------------------------------------------------
def test_mutation_drift_fst():
    """fstMutationDriftEquilibrium = 1/(1+theta), and its transient."""
    import msprime
    cells_eq, cells_tr = [], []
    Ne = 1000
    for mu in (2.5e-5, 1e-4, 2.5e-4):
        theta = 4 * Ne * mu
        # Two demes, split long ago relative to 1/mu so the pair is at the
        # mutation-drift F_ST rather than still diverging.
        hets = []
        for r in range(20):
            ts = msprime.sim_ancestry(samples=40, population_size=Ne,
                                      sequence_length=2e5,
                                      recombination_rate=1e-8,
                                      random_seed=3101 + r)
            ts = msprime.sim_mutations(ts, rate=mu,
                                       model=msprime.InfiniteAlleles(),
                                       random_seed=3201 + r)
            gm = ts.genotype_matrix()
            tot = 0.0
            for row in gm:
                _, cnt = np.unique(row, return_counts=True)
                f = cnt / cnt.sum()
                tot += 1 - float((f ** 2).sum())
            hets.append(tot / ts.sequence_length)
        s = simlib.summarize(hets)
        # H = theta/(1+theta) so the homozygosity 1-H is 1/(1+theta), which is
        # exactly what fstMutationDriftEquilibrium computes.
        cells_eq.append(dict(design="theta=%.2f" % theta,
                             lean=1 / (1 + theta),
                             truth=1 - s["mean"], sem=s["sem"]))
    record("fstMutationDriftEquilibrium", "DGP.lean", "1 / (1 + theta)",
           cells_eq,
           regime="infinite-alleles homozygosity at mutation-drift balance")


# ---------------------------------------------------------------------------
# 3. hetStepWithMutation and hetDecayFromScaled, as one-step maps
# ---------------------------------------------------------------------------
def test_het_recurrences():
    """H' = (1 - 1/(2Ne)) H + 2 mu (1 - H), measured one generation at a time."""
    rng = np.random.default_rng(3301)
    cells_step, cells_decay = [], []
    for Ne, mu in ((100, 1e-3), (500, 1e-3), (100, 5e-3)):
        n_loci, reps = 4000, 400
        p = rng.uniform(0.1, 0.9, (reps, n_loci))
        two_n = int(2 * Ne)
        for _ in range(20):        # burn toward the balance
            p = rng.binomial(two_n, p) / two_n
            p = p * (1 - mu) + (1 - p) * mu
        H0 = float((2 * p * (1 - p)).mean())
        p1 = rng.binomial(two_n, p) / two_n
        p1 = p1 * (1 - mu) + (1 - p1) * mu
        H1 = float((2 * p1 * (1 - p1)).mean())
        sem = float((2 * p1 * (1 - p1)).std() / math.sqrt(reps * n_loci))
        cells_step.append(dict(design="Ne=%d mu=%.0e" % (Ne, mu),
                               lean=(1 - 1 / (2 * Ne)) * H0 + 2 * mu * (1 - H0),
                               truth=H1, sem=max(sem, 1e-9)))
        theta = 4 * Ne * mu
        cells_decay.append(dict(design="Ne=%d theta=%.1f" % (Ne, theta),
                                lean=(1 - 1 / (2 * Ne)) * (1 - theta / (2 * Ne)) * H0,
                                truth=H1, sem=max(sem, 1e-9)))
    record("hetStepWithMutation", "PortabilityDrift.lean",
           "(1 - 1/(2*Ne)) * H + 2*mu*(1 - H)", cells_step,
           regime="one Wright-Fisher generation with two-way mutation")
    record("hetDecayFromScaled", "DGP.lean",
           "(1 - 1/(2*Ne)) * (1 - theta/(2*Ne)), applied to H", cells_decay,
           regime="same generation; the pure-decay reading with no input term")


# ---------------------------------------------------------------------------
# 4. ibdFlowStep
# ---------------------------------------------------------------------------
def test_ibd_flow_step():
    """F' = F + (1-F)/(2Ne) - 2*rate*F, one generation of drift plus gene flow."""
    rng = np.random.default_rng(3401)
    cells = []
    for Ne, rate in ((200, 0.0), (200, 0.002), (500, 0.005)):
        n_loci, reps = 4000, 300
        p0 = rng.uniform(0.1, 0.9, n_loci)
        two_n = int(2 * Ne)
        p = np.tile(p0, (reps, 1))
        for _ in range(30):
            p = rng.binomial(two_n, p) / two_n
            p = (1 - rate) * p + rate * p0        # flow toward the source pool
        H_anc = float((2 * p0 * (1 - p0)).mean())
        F0 = 1 - float((2 * p * (1 - p)).mean()) / H_anc
        p1 = rng.binomial(two_n, p) / two_n
        p1 = (1 - rate) * p1 + rate * p0
        F1 = 1 - float((2 * p1 * (1 - p1)).mean()) / H_anc
        cells.append(dict(design="Ne=%d rate=%.3f" % (Ne, rate),
                          lean=F0 + (1 - F0) / (2 * Ne) - 2 * rate * F0,
                          truth=F1, sem=abs(F1) * 0.004 + 1e-6))
    record("ibdFlowStep", "PortabilityDrift.lean",
           "F + (1 - F)/(2*Ne) - 2*rate*F", cells,
           regime="one generation of drift with gene flow from a fixed source")


# ---------------------------------------------------------------------------
# 5. admixedFst against admixedFstExact
# ---------------------------------------------------------------------------
def test_admixed_fst():
    """(1-alpha)^2 * fst_AB, with and without the heterozygosity-ratio divisor."""
    rng = np.random.default_rng(3501)
    n_loci = 40000
    cells_plain, cells_exact = [], []
    for alpha in (0.2, 0.5, 0.8):
        # two source demes at a known F_ST, an admixed deme at fraction alpha
        pA = rng.beta(2, 2, n_loci)
        pB = rng.beta(2, 2, n_loci)
        pC = alpha * pA + (1 - alpha) * pB
        def gst(p1, p2):
            pb = (p1 + p2) / 2
            hs = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2
            ht = 2 * pb * (1 - pb)
            return float((ht.mean() - hs.mean()) / ht.mean())
        fst_AB = gst(pA, pB)
        fst_CB = gst(pC, pA)                       # admixed against source A
        het_C = float((2 * pC * (1 - pC)).mean())
        het_B = float((2 * pB * (1 - pB)).mean())
        het_ratio = ((het_C + het_B) / 2) / ((2 * pA * (1 - pA)).mean() / 2
                                             + het_B / 2)
        sem = fst_CB / math.sqrt(n_loci)
        cells_plain.append(dict(design="alpha=%.1f" % alpha,
                                lean=(1 - alpha) ** 2 * fst_AB,
                                truth=fst_CB, sem=sem))
        cells_exact.append(dict(design="alpha=%.1f" % alpha,
                                lean=(1 - alpha) ** 2 * fst_AB / het_ratio,
                                truth=fst_CB, sem=sem))
    record("admixedFst", "DemographicHistory.lean",
           "(1 - alpha)^2 * fst_AB", cells_plain,
           regime="one-pulse admixture, F_ST of the admixed deme against source A")
    record("admixedFstExact", "DemographicHistory.lean",
           "(1 - alpha)^2 * fst_AB / hetRatio", cells_exact,
           regime="same runs, with the heterozygosity-ratio divisor")


# ---------------------------------------------------------------------------
# 6. liabilityControlVariance, finishing the liability set
# ---------------------------------------------------------------------------
def test_liability_control_variance():
    from scipy import stats
    rng = np.random.default_rng(3601)
    Phinv, phi = stats.norm.ppf, stats.norm.pdf
    n = 4000000
    cells = []
    for K, r2 in ((0.05, 0.3), (0.2, 0.3), (0.05, 0.6)):
        T = Phinv(1 - K)
        g = rng.normal(0, math.sqrt(r2), n)
        e = rng.normal(0, math.sqrt(1 - r2), n)
        l = g + e
        ctl = l <= T
        cm = float(phi(T) / K)
        ctlm = -cm * K / (1 - K)
        lean = 1 - r2 * ctlm * (ctlm - T)
        obs = float(g[ctl].var() / r2)
        cells.append(dict(design="K=%.2f r2=%.1f" % (K, r2), lean=lean,
                          truth=obs, sem=obs * math.sqrt(2.0 / ctl.sum())))
    record("liabilityControlVariance", "PortabilityDrift.lean",
           "1 - r2 * controlMean * (controlMean - T)", cells,
           regime="variance of the standardised PGS among controls")


# ---------------------------------------------------------------------------
# 7. coalescentTau / fstFromTau / fstFromGenerations, on exact times
# ---------------------------------------------------------------------------
def test_tau_chain():
    import msprime
    cells = []
    Ne = 1000
    for t in (250, 500, 1000, 2000, 4000):
        dem = msprime.Demography()
        dem.add_population(name="A", initial_size=Ne)
        dem.add_population(name="B", initial_size=Ne)
        dem.add_population(name="ANC", initial_size=Ne)
        dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
        s = fst_from_times(dem, 0, 1, n_dip=25, seq_len=2e6, reps=40,
                           seed=3701)
        tau = t / (2.0 * Ne)
        cells.append(dict(design="t=%d (tau=%.2f)" % (t, tau),
                          lean=tau / (1 + tau), truth=s["mean"], sem=s["sem"]))
    record("fstFromGenerations / coalescentTau / fstFromTau",
           "PortabilityDrift.lean", "tau/(1+tau), tau = t/(2*Ne)", cells,
           regime="clean split, exact coalescence times, no estimator")


def main():
    for fn in (test_island_law, test_mutation_drift_fst, test_het_recurrences,
               test_ibd_flow_step, test_admixed_fst,
               test_liability_control_variance, test_tau_chain):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_max_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-50s worst %8.1f sems"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan"))))


if __name__ == "__main__":
    main()
