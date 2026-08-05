"""Battery 20: the PortabilityDrift coalescent/mutation/island core.

Four groups, each chosen because a SIMULATION can separate the written body from
a nearby wrong one, and each carrying a positive control whose answer is known
independently of the body under test.

  A. `coalescentTau`, `fstFromTau`, `fstFromGenerations`, and
     `hudsonFstFromCoalescenceTimes`.  A clean split has two independent
     estimators of the same F_ST: the ratio of mean coalescence times (branch
     mode) and the site-frequency Hudson estimator (ratio of averages over
     mutations).  `hudsonFstFromCoalescenceTimes` is the claim that the FIRST
     computes the second, so feeding it branch-mode times and comparing against
     the site-based estimate is a comparison of two engines, not a formula
     against a transcription of itself.

  B. `hetMutationFloor = 4 Ne mu / (1 + 4 Ne mu)`.  This is the INFINITE-ALLELES
     equilibrium heterozygosity, so the oracle must be an infinite-alleles
     mutation model -- under infinite SITES the per-site heterozygosity is
     ~theta and the saturation the body claims is invisible.  theta runs 0.1 to
     10, over which the prediction spans 0.09 to 0.91.  Control: Ewens' sampling
     formula for the expected number of distinct alleles, E[K] = sum theta/(theta+i-1),
     a classical result about the same simulated samples that shares no algebra
     with the body under test.

  C. `ibdRecurrenceFixedPoint` and `fstIslandMultiplicativeEquilibrium`.  The
     exact fixed point (1-m)^2 / ((1-m)^2 + 2 Ne m (2-m)) differs from the
     diffusion form 1/(1+4 Ne m) only when m is not small, so the sweep is
     driven to m = 0.1 with a small Ne rather than staying in the regime where
     the two forms agree and nothing is being decided.  Both forms are carried
     so the data picks.  Control: the small-m cell, where 1/(1+4 Ne m) is
     already VALIDATED (battery_core, `fstMigrationMutationEquilibrium`).

  D. `admixtureLDDecay` and `admixtureLDBoost`.  Forward Wright-Fisher two-locus
     with an admixture pulse; the boost is the ratio of the pulse's excess D to
     the equilibrium D, which is what the body divides by.

Trap notes honoured here: every coalescent cell carries RECOMBINATION (a single
genealogy per replicate makes the error bar honest but useless); heterozygosity
is per SAMPLE not per segregating site; F_ST is pairwise-between-two-demes,
ratio-of-averages, the corpus convention.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record

SEQ = 8e6
RHO = 1e-8
MU = 1e-8


# ---------------------------------------------------------------------------
# A.  coalescentTau / fstFromTau / fstFromGenerations / hudsonFstFromCoalescenceTimes
# ---------------------------------------------------------------------------
def group_a():
    import msprime

    cells_gen, cells_hud, cells_tau = [], [], []
    control = None
    for Ne, t in ((1000, 500), (1000, 2000), (2000, 500), (500, 2000), (1000, 8000)):
        dem = msprime.Demography()
        dem.add_population(name="A", initial_size=Ne)
        dem.add_population(name="B", initial_size=Ne)
        dem.add_population(name="ANC", initial_size=Ne)
        dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
        site_fst, time_fst = [], []
        for r in range(20):
            ts = msprime.sim_ancestry(
                samples={"A": 30, "B": 30}, demography=dem,
                sequence_length=SEQ, recombination_rate=RHO,
                random_seed=70001 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            # branch-mode mean coalescence times: within and total
            ETss = float((ts.diversity([A], mode="branch")[0]
                          + ts.diversity([B], mode="branch")[0]) / 2.0) / 2.0
            ETst = float(ts.divergence([A, B], indexes=[(0, 1)],
                                       mode="branch")[0]) / 2.0
            # `hudsonFstFromCoalescenceTimes` applied to the branch-mode times
            time_fst.append(1.0 - ETss / ETst)
            # the independent estimator: site frequencies, ratio of averages
            mts = msprime.sim_mutations(ts, rate=MU, random_seed=170001 + r)
            gm = mts.genotype_matrix()
            site_fst.append(simlib.hudson_fst(
                gm[:, A].sum(1).astype(float), len(A),
                gm[:, B].sum(1).astype(float), len(B)))
        s_site = simlib.summarize(site_fst)
        s_time = simlib.summarize(time_fst)
        tau = t / (2.0 * Ne)
        lab = "Ne=%d t=%d (tau=%.2f)" % (Ne, t, tau)
        print("  %-28s tau=%.3f  site %.5f ± %.5f   times %.5f ± %.5f"
              % (lab, tau, s_site["mean"], s_site["sem"],
                 s_time["mean"], s_time["sem"]))
        # fstFromGenerations = fstFromTau (coalescentTau t Ne)
        cells_gen.append(dict(design=lab, lean=tau / (1.0 + tau),
                              truth=s_site["mean"], sem=s_site["sem"]))
        # hudsonFstFromCoalescenceTimes: branch-time reading vs site reading
        cells_hud.append(dict(design=lab, lean=s_time["mean"],
                              truth=s_site["mean"],
                              sem=math.hypot(s_site["sem"], s_time["sem"])))
        # coalescentTau alone, read through the saturation the corpus pairs it
        # with: the SCALE is what t/(2Ne) fixes, so a wrong divisor (t/Ne or
        # t/(4Ne)) shows up as a systematic miss across the tau grid.
        cells_tau.append(dict(design=lab, lean=tau,
                              truth=s_site["mean"] / max(1e-12, 1 - s_site["mean"]),
                              sem=s_site["sem"] / max(1e-12, (1 - s_site["mean"]) ** 2)))
        if abs(tau - 1.0) < 1e-9:
            control = dict(design=lab + " [coalFst, already VALIDATED]",
                           lean=t / (t + 2.0 * Ne), truth=s_site["mean"],
                           sem=s_site["sem"])

    reg = ("clean two-population split, no migration, equal sizes, "
           "sequence 8 Mb with recombination 1e-8; F_ST is pairwise Hudson, "
           "ratio of averages")
    record("fstFromGenerations", "PortabilityDrift.lean",
           "fstFromTau (coalescentTau t Ne) = (t/(2Ne)) / (1 + t/(2Ne))",
           cells_gen, regime=reg, control=control)
    record("coalescentTau", "PortabilityDrift.lean", "t / (2 * Ne)", cells_tau,
           regime=reg + "; read as F_ST/(1-F_ST), the odds the saturation "
                        "law inverts to, so the DIVISOR is what is on trial",
           control=control)
    record("hudsonFstFromCoalescenceTimes", "PortabilityDrift.lean",
           "1 - ETss / ETst", cells_hud, regime=reg,
           note="prediction is the branch-mode coalescence-time reading; truth "
                "is the site-frequency estimator -- two engines, not one",
           control=control)


# ---------------------------------------------------------------------------
# B.  hetMutationFloor -- infinite alleles
# ---------------------------------------------------------------------------
def group_b():
    import msprime

    cells, cells_k = [], []
    control = None
    Ne = 1000
    for theta in (0.1, 0.5, 1.0, 3.0, 10.0):
        mu = theta / (4.0 * Ne)
        hets, ks = [], []
        for r in range(24):
            ts = msprime.sim_ancestry(
                samples=50, population_size=Ne, sequence_length=1,
                discrete_genome=False, random_seed=80001 + r)
            mts = msprime.sim_mutations(
                ts, rate=mu, model=msprime.InfiniteAlleles(),
                discrete_genome=False, random_seed=180001 + r)
            # one locus: the allelic state of each sample is the state at the
            # single site, or the ancestral state where no mutation fell.
            var = None
            for v in mts.variants():
                var = v
                break
            if var is None:
                states = np.zeros(mts.num_samples, dtype=int)
            else:
                states = np.asarray(var.genotypes)
            _, counts = np.unique(states, return_counts=True)
            n = states.size
            p = counts / n
            # unbiased sample heterozygosity, over the WHOLE sample
            hets.append(float(n / (n - 1.0) * (1.0 - np.sum(p ** 2))))
            ks.append(float(counts.size))
        s = simlib.summarize(hets)
        sk = simlib.summarize(ks)
        n = 50 * 2
        ewens_k = sum(theta / (theta + i - 1.0) for i in range(1, n + 1))
        lab = "theta=4*Ne*mu=%.1f" % theta
        print("  %-22s  H = %.5f ± %.5f  (lean %.5f) | K = %.2f ± %.2f "
              "(Ewens %.2f)"
              % (lab, s["mean"], s["sem"], theta / (1 + theta),
                 sk["mean"], sk["sem"], ewens_k))
        cells.append(dict(design=lab, lean=theta / (1.0 + theta),
                          truth=s["mean"], sem=s["sem"]))
        cells_k.append(dict(design=lab, lean=ewens_k, truth=sk["mean"],
                            sem=sk["sem"]))
        if abs(theta - 1.0) < 1e-9:
            control = dict(design=lab + " [Ewens E(K), independent]",
                           lean=ewens_k, truth=sk["mean"], sem=sk["sem"])
    record("hetMutationFloor", "PortabilityDrift.lean",
           "4 * Ne * mu / (1 + 4 * Ne * mu)", cells,
           regime="single-locus INFINITE-ALLELES mutation at coalescent "
                  "equilibrium, Ne = 1000, 100 sampled chromosomes; "
                  "heterozygosity is 1 - sum p_i^2 over the whole sample, "
                  "not conditioned on polymorphism",
           control=control)
    record("[control] Ewens expected allele count on the same samples",
           "PortabilityDrift.lean", "sum_i theta/(theta+i-1)", cells_k,
           regime="same infinite-alleles samples; an independent classical "
                  "result, carried so the engine itself is on trial too")


# ---------------------------------------------------------------------------
# C.  ibdRecurrenceFixedPoint / fstIslandMultiplicativeEquilibrium
# ---------------------------------------------------------------------------
def group_c():
    import msprime

    Ne, n_demes = 100, 40
    cells_exact, cells_diff = [], []
    control = None
    for m in (0.002, 0.01, 0.03, 0.06, 0.12):
        dem = msprime.Demography.island_model(
            [Ne] * n_demes, migration_rate=m / (n_demes - 1.0))
        vals = []
        for r in range(24):
            ts = msprime.sim_ancestry(
                samples={"pop_0": 30, "pop_1": 30}, demography=dem,
                sequence_length=SEQ, recombination_rate=RHO,
                random_seed=90001 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            da = ts.diversity([A], mode="branch")[0]
            db = ts.diversity([B], mode="branch")[0]
            dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            vals.append(1.0 - ((da + db) / 2.0) / dab)
        s = simlib.summarize(vals)
        exact = (1 - m) ** 2 / ((1 - m) ** 2 + 2 * Ne * m * (2 - m))
        diff = 1.0 / (1.0 + 4 * Ne * m)
        lab = "Ne=%d m=%.3f (4Nm=%.1f)" % (Ne, m, 4 * Ne * m)
        print("  %-26s F_ST = %.5f ± %.5f | exact %.5f  diffusion %.5f"
              % (lab, s["mean"], s["sem"], exact, diff))
        cells_exact.append(dict(design=lab, lean=exact, truth=s["mean"],
                                sem=s["sem"]))
        cells_diff.append(dict(design=lab, lean=diff, truth=s["mean"],
                               sem=s["sem"]))
        if abs(m - 0.002) < 1e-9:
            control = dict(design=lab + " [1/(1+4Nm), already VALIDATED here]",
                           lean=diff, truth=s["mean"], sem=s["sem"])
    reg = ("symmetric island model, 40 demes so the many-deme limit the body "
           "declares actually holds; m is the TOTAL emigration rate, so each "
           "of the 39 sources gets m/39; F_ST between two demes from "
           "coalescence times, 8 Mb with recombination")
    record("ibdRecurrenceFixedPoint / fstIslandMultiplicativeEquilibrium",
           "PortabilityDrift.lean",
           "(1-m)^2 / ((1-m)^2 + 2*Ne*m*(2-m))", cells_exact, regime=reg,
           control=control)
    record("fstMigrationDriftEquilibrium [diffusion form, competing]",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*m)", cells_diff,
           regime=reg, control=control)


# ---------------------------------------------------------------------------
# D.  admixtureLDDecay / admixtureLDBoost
# ---------------------------------------------------------------------------
def group_d():
    rng = np.random.default_rng(2020)
    Ne, alpha = 2000, 0.5
    pA1, pB1, pA2, pB2 = 0.8, 0.2, 0.75, 0.15
    n_hap = 2 * Ne
    reps = 400
    cells_decay, cells_boost = [], []
    control = None
    for r_rate in (0.005, 0.02, 0.05, 0.15):
        # gametic D through an admixture pulse at generation 0, then WF drift
        # with recombination.  Track the mean D across replicates.
        D0 = alpha * (1 - alpha) * (pA1 - pB1) * (pA2 - pB2)
        # haplotype frequency vector (11, 10, 01, 00) at the pulse
        p1 = alpha * pA1 + (1 - alpha) * pB1
        p2 = alpha * pA2 + (1 - alpha) * pB2
        base = np.array([p1 * p2 + D0, p1 * (1 - p2) - D0,
                         (1 - p1) * p2 - D0, (1 - p1) * (1 - p2) + D0])
        H = np.tile(base, (reps, 1))
        traj = []
        for gen in range(41):
            f1 = H[:, 0] + H[:, 1]
            f2 = H[:, 0] + H[:, 2]
            traj.append(H[:, 0] - f1 * f2)
            D = H[:, 0] - f1 * f2
            # recombination
            H = H.copy()
            H[:, 0] -= r_rate * D
            H[:, 1] += r_rate * D
            H[:, 2] += r_rate * D
            H[:, 3] -= r_rate * D
            H = np.clip(H, 0, None)
            H /= H.sum(axis=1, keepdims=True)
            H = rng.multinomial(n_hap, H) / float(n_hap)
        traj = np.asarray(traj)                     # (gens, reps)
        for t in (10, 40):
            d_t = traj[t]
            ratio = d_t / traj[0]
            truth = float(np.mean(ratio))
            sem = float(np.std(ratio, ddof=1) / math.sqrt(reps))
            lab = "r=%.3f t=%d" % (r_rate, t)
            lean = (1 - r_rate) ** t
            print("  %-18s retention %.5f ± %.5f  (lean %.5f)"
                  % (lab, truth, sem, lean))
            cells_decay.append(dict(design=lab, lean=lean, truth=truth,
                                    sem=sem))
            # the boost: the same retention divided by an equilibrium LD level.
            # `equilibrium_ld` is an INPUT to the body, so the test is that the
            # body is the ratio -- carried at a fixed nonzero baseline.
            eq = 0.25
            cells_boost.append(dict(design=lab + " eq=0.25",
                                    lean=lean / eq, truth=truth / eq,
                                    sem=sem / eq))
            if r_rate == 0.005 and t == 10:
                # drift-only control: the validated per-generation retention
                # (1-r)(1 - 1/(2Ne)) compounded, an independently derived form
                control = dict(design=lab + " [(1-r)^t (1-1/(2Ne))^t, validated]",
                               lean=((1 - r_rate) * (1 - 1.0 / (2 * Ne))) ** t,
                               truth=truth, sem=sem)
    reg = ("one-pulse 50/50 admixture into a Wright-Fisher population of "
           "Ne = 2000, then %d generations of recombination and drift; the "
           "observable is E[D_t]/E[D_0] over 400 replicates" % 40)
    record("admixtureLDDecay", "PortabilityDrift.lean",
           "(1 - r) ^ generations_since", cells_decay, regime=reg,
           control=control)
    record("admixtureLDBoost", "PortabilityDrift.lean",
           "admixtureLDDecay r t_since / equilibrium_ld", cells_boost,
           regime=reg + "; equilibrium_ld held at 0.25",
           control=control)


def main():
    for fn in (group_a, group_b, group_c, group_d):
        print("\n===== %s =====" % fn.__name__)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (fn.__name__, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk20_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-56s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
