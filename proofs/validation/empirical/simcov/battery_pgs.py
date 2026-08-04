"""Battery 2: the drift / PGS / liability surface of PortabilityDrift.lean.

Adds two oracles to `simlib`'s coalescent and Wright-Fisher engines:

  a PGS drift engine -- two demes split from a common ancestor, neutral drift on
  every causal locus, and the population MEAN polygenic score recomputed in each
  deme.  This is the only oracle that can see `Var_Delta_Mu`, because that
  quantity is a variance ACROSS replicate population pairs: a single simulated
  pair gives one draw of it, and the corpus's `2 * fst * V_A` is a statement
  about the ensemble.

  a liability-threshold engine -- explicit normal liabilities with an
  ascertainment threshold, for the case/control moment formulas.  These are
  written as exact normal theory, so the Monte Carlo either confirms them to
  simulation precision or finds a real algebra error; there is no modelling
  slack to hide in.
"""
import json
import math

import numpy as np
from scipy import stats

import simlib
from battery_core import RESULTS, record

Phi, phi, Phinv = stats.norm.cdf, stats.norm.pdf, stats.norm.ppf


# ---------------------------------------------------------------------------
# PGS drift engine
# ---------------------------------------------------------------------------
def pgs_split_drift(Ne, t, n_loci=500, reps=600, p0=None, seed=1):
    """Two demes drift independently for `t` generations from a shared start.

    Returns, over replicates: realised F_ST (from the realised frequencies),
    the additive variance in the ancestral generation, and the difference in
    population mean PGS between the two demes.
    """
    rng = np.random.default_rng(seed)
    if p0 is None:
        p0 = rng.uniform(0.05, 0.95, n_loci)
    beta = rng.normal(0, 1, n_loci)
    two_n = int(2 * Ne)
    p1 = np.tile(p0, (reps, 1))
    p2 = np.tile(p0, (reps, 1))
    for _ in range(t):
        p1 = rng.binomial(two_n, p1) / two_n
        p2 = rng.binomial(two_n, p2) / two_n
    # mean PGS in each deme: sum_i ploidy * p_i * beta_i
    mu1 = (2 * p1 * beta).sum(axis=1)
    mu2 = (2 * p2 * beta).sum(axis=1)
    delta = mu1 - mu2
    # V_A in the ancestral population
    V_A = float((2 * p0 * (1 - p0) * beta ** 2).sum())
    # realised F_ST as 1 - H_S/H_T over the pair, averaged over loci and reps
    pbar = (p1 + p2) / 2
    hs = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2
    ht = 2 * pbar * (1 - pbar)
    fst = float((ht.mean() - hs.mean()) / ht.mean())
    # theoretical drift F_ST for a pure split of duration t in each branch
    fst_theory = 1 - (1 - 1.0 / (2 * Ne)) ** t
    return dict(V_A=V_A, delta=delta, fst_realised=fst,
                fst_theory=fst_theory, p1=p1, p2=p2, p0=p0, beta=beta)


def test_var_delta_mu():
    """Var_Delta_Mu = 2 * fst * V_A, as a variance across replicate deme pairs."""
    Ne = 200
    cells = []
    for t in (20, 60, 150, 300):
        r = pgs_split_drift(Ne, t, n_loci=400, reps=1500, seed=101 + t)
        obs = float(np.var(r["delta"], ddof=1))
        # sem of a variance estimate ~ var * sqrt(2/(n-1))
        sem = obs * math.sqrt(2.0 / (len(r["delta"]) - 1))
        # `fst` here is the pairwise divergence between the two demes
        fst = r["fst_realised"]
        cells.append(dict(design="t=%d (Fst=%.3f)" % (t, fst),
                          lean=2 * fst * r["V_A"], truth=obs, sem=sem))
    record("Var_Delta_Mu", "PortabilityDrift.lean", "2 * fst * V_A", cells,
           regime="variance of the mean-PGS difference across replicate "
                  "deme pairs, neutral drift, F_ST measured on the same run")


def test_freq_corr_from_fst():
    """freqCorrFromFst = 1 - fst: the correlation of allele frequencies."""
    Ne = 200
    cells = []
    for t in (20, 60, 150, 300):
        r = pgs_split_drift(Ne, t, n_loci=800, reps=400, seed=201 + t)
        # correlation across loci between the two demes' frequencies,
        # pooled over replicates
        a, b = r["p1"].ravel(), r["p2"].ravel()
        corr = float(np.corrcoef(a, b)[0, 1])
        sem = (1 - corr ** 2) / math.sqrt(len(a))
        cells.append(dict(design="t=%d (Fst=%.3f)" % (t, r["fst_realised"]),
                          lean=1 - r["fst_realised"], truth=corr,
                          sem=max(sem, 1e-6)))
    record("freqCorrFromFst", "PortabilityDrift.lean", "1 - fst", cells,
           regime="Pearson correlation of allele frequencies across loci "
                  "between two drifted demes")


def test_pgs_variance_from_het():
    """pgsVarianceFromHet = beta_sq_sum * het, checked against the realised V_A."""
    rng = np.random.default_rng(5)
    cells = []
    for p in (0.1, 0.3, 0.5):
        n_loci, n_ind = 300, 40000
        beta = rng.normal(0, 1, n_loci)
        g = rng.binomial(2, p, (n_ind, n_loci)).astype(float)
        pgs = g @ beta
        het = 2 * p * (1 - p)
        cells.append(dict(design="p=%.1f (het=%.2f)" % (p, het),
                          lean=float((beta ** 2).sum() * het),
                          truth=float(pgs.var()),
                          sem=float(pgs.var()) * math.sqrt(2.0 / n_ind)))
    record("pgsVarianceFromHet", "PortabilityDrift.lean", "beta_sq_sum * het",
           cells, regime="PGS variance over individuals, HWE, linkage equilibrium")


def test_wf_drift_retention():
    """wrightFisherDriftRetention = (1 - 1/(2N))^t against realised H_t/H_0."""
    cells = []
    for N, t in ((100, 50), (100, 200), (500, 200), (50, 100)):
        h = simlib.wf_drift_het([N] * t, reps=400, n_loci=600, seed=301)
        obs = float(h[-1] / h[0])
        cells.append(dict(design="N=%d t=%d" % (N, t),
                          lean=(1 - 1.0 / (2 * N)) ** t, truth=obs,
                          sem=obs * 0.008))
    record("wrightFisherDriftRetention", "PortabilityDrift.lean",
           "(1 - 1/(2*N))^t", cells, regime="H_t / H_0 under neutral WF drift")


def test_pairwise_fst_branches():
    """pairwiseFstFromBranchTaus = fstFromTau(tauS + tauT), asymmetric branches.

    The design uses UNEQUAL daughter sizes on purpose.  With equal sizes the two
    branch taus are equal and the additive-tau form is indistinguishable from
    several others; a symmetric design here would have no power, which is the
    failure `Calibrator.DriftRegime.symmetric_design_has_no_power` records.
    """
    import msprime
    fstFromTau = lambda tau: tau / (1 + tau)
    cells = []
    for NeA, NeB, t in ((1000, 1000, 1000), (500, 2000, 1000), (300, 3000, 800)):
        dem = msprime.Demography()
        dem.add_population(name="A", initial_size=NeA)
        dem.add_population(name="B", initial_size=NeB)
        dem.add_population(name="ANC", initial_size=1000)
        dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
        hud = []
        for r in range(30):
            ts = msprime.sim_ancestry(samples={"A": 50, "B": 50}, demography=dem,
                                      sequence_length=1e7, random_seed=401 + r)
            ts = msprime.sim_mutations(ts, rate=1e-8, random_seed=901 + r)
            if ts.num_sites == 0:
                continue
            gm = ts.genotype_matrix()
            a, b = ts.samples(population=0), ts.samples(population=1)
            hud.append(simlib.hudson_fst(gm[:, a].sum(1).astype(float), len(a),
                                         gm[:, b].sum(1).astype(float), len(b)))
        s = simlib.summarize(hud)
        tauS, tauT = t / (2.0 * NeA), t / (2.0 * NeB)
        cells.append(dict(design="NeA=%d NeB=%d t=%d" % (NeA, NeB, t),
                          lean=fstFromTau(tauS + tauT), truth=s["mean"],
                          sem=s["sem"]))
    record("pairwiseFstFromBranchTaus", "PortabilityDrift.lean",
           "fstFromTau(tauS + tauT) = (tauS+tauT)/(1+tauS+tauT)", cells,
           regime="clean split with UNEQUAL daughter sizes, Hudson F_ST")


def test_het_mutation_floor():
    """hetMutationFloor = 4*Ne*mu/(1 + 4*Ne*mu), infinite-alleles heterozygosity."""
    import msprime
    cells = []
    Ne = 1000
    for mu in (1e-5, 3e-5, 1e-4, 3e-4):
        hets = []
        for r in range(12):
            ts = msprime.sim_ancestry(samples=60, population_size=Ne,
                                      sequence_length=2000,
                                      random_seed=501 + r)
            ts = msprime.sim_mutations(ts, rate=mu,
                                       model=msprime.InfiniteAlleles(),
                                       random_seed=1501 + r)
            gm = ts.genotype_matrix()
            if gm.shape[0] == 0:
                continue
            # heterozygosity = P(two random samples differ), per site
            site_het = []
            for row in gm:
                _, cnt = np.unique(row, return_counts=True)
                f = cnt / cnt.sum()
                site_het.append(1 - float((f ** 2).sum()))
            hets.append(float(np.mean(site_het)))
        s = simlib.summarize(hets)
        theta = 4 * Ne * mu
        cells.append(dict(design="theta=4*Ne*mu=%.1f" % theta,
                          lean=theta / (1 + theta), truth=s["mean"],
                          sem=s["sem"]))
    record("hetMutationFloor", "PortabilityDrift.lean",
           "4*Ne*mu / (1 + 4*Ne*mu)", cells,
           regime="infinite-alleles equilibrium heterozygosity, coalescent")


# ---------------------------------------------------------------------------
# liability-threshold engine
# ---------------------------------------------------------------------------
def test_liability_moments():
    """The case/control moment formulas, against explicit normal liabilities."""
    rng = np.random.default_rng(77)
    n = 4000000
    for K in (0.01, 0.05, 0.2):
        T = Phinv(1 - K)
        l = rng.normal(0, 1, n)
        case = l > T
        cm_obs = float(l[case].mean())
        ctl_obs = float(l[~case].mean())
        cells = [dict(design="K=%.2f caseMean" % K, lean=float(phi(T) / K),
                      truth=cm_obs,
                      sem=float(l[case].std() / math.sqrt(case.sum()))),
                 dict(design="K=%.2f controlMean" % K,
                      lean=float(-(phi(T) / K) * K / (1 - K)), truth=ctl_obs,
                      sem=float(l[~case].std() / math.sqrt((~case).sum())))]
        record("liabilityCaseMean / liabilityControlMean [K=%.2f]" % K,
               "PortabilityDrift.lean",
               "phi(T)/K  and  -caseMean*K/(1-K),  T = Phi^-1(1-K)", cells,
               regime="standard normal liability, threshold ascertainment")

    # variance formulas: read on the STANDARDISED score, as written
    for K, r2 in ((0.05, 0.3), (0.2, 0.3), (0.05, 0.6)):
        T = Phinv(1 - K)
        g = rng.normal(0, math.sqrt(r2), n)      # PGS component of liability
        e = rng.normal(0, math.sqrt(1 - r2), n)
        l = g + e
        case = l > T
        cm = float(phi(T) / K)
        # Lean: liabilityCaseVariance = 1 - r2 * cm * (cm - T)
        lean_case = 1 - r2 * cm * (cm - T)
        # candidate readings of what that variance is OF
        v_liab_case = float(l[case].var())
        v_g_case_scaled = float(g[case].var() / r2)
        cells = [dict(design="K=%.2f r2=%.1f | var(liability|case)" % (K, r2),
                      lean=lean_case, truth=v_liab_case,
                      sem=v_liab_case * math.sqrt(2.0 / case.sum())),
                 dict(design="K=%.2f r2=%.1f | var(PGS|case)/r2" % (K, r2),
                      lean=lean_case, truth=v_g_case_scaled,
                      sem=v_g_case_scaled * math.sqrt(2.0 / case.sum()))]
        record("liabilityCaseVariance [K=%.2f r2=%.1f]" % (K, r2),
               "PortabilityDrift.lean",
               "1 - r2 * caseMean * (caseMean - T)", cells,
               regime="two candidate readings of the variance; at most one "
                      "can be the quantity the name denotes")


def main():
    for fn in (test_var_delta_mu, test_freq_corr_from_fst,
               test_pgs_variance_from_het, test_wf_drift_retention,
               test_pairwise_fst_branches, test_het_mutation_floor,
               test_liability_moments):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_pgs_results.json", "w"), indent=1, default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-52s worst %8.1f sems, %6.1f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
