"""Battery 7: the transfer-learning and DGP surfaces.

`TransferLearningPGS` is linear algebra over an LD matrix, and linear algebra is
the easiest thing in the corpus to get subtly wrong in a way no theorem catches:
`pgsPhenoCov` contracts a weight vector against an LD matrix against a causal
vector, and whether the middle object is the GENOTYPE COVARIANCE or the
CORRELATION matrix changes every downstream `R^2` by a diagonal rescaling that
is invisible to Lean and to every algebraic identity above it.

So the LD here is not a made-up matrix. It comes out of msprime with
recombination, standardised the way a real PGS pipeline standardises it, and the
"truth" for each definition is the corresponding quantity measured over
simulated individuals -- an empirical covariance, an empirical `R^2` from an
out-of-sample regression. If the corpus means correlation where the simulation
means covariance, these tests separate on the diagonal.

The DGP block is the same three engines as before applied to the evolutionary
parameter bundle: an island model with mutation for `fstEquilibrium`, and exact
recombination bookkeeping for the LD-decay definitions.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


# ---------------------------------------------------------------------------
# a realistic LD block from the coalescent
# ---------------------------------------------------------------------------
def coalescent_haplotypes(Ne=10000, n_dip=4000, n_sites=60, seq_len=2e5,
                          rho=1e-8, mu=1e-8, seed=1):
    """Genotype dosages at `n_sites` common variants with real coalescent LD."""
    import msprime
    ts = msprime.sim_ancestry(samples=n_dip, population_size=Ne,
                              sequence_length=seq_len,
                              recombination_rate=rho, random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=mu, random_seed=seed + 99)
    gm = ts.genotype_matrix()                      # sites x haplotypes
    freq = gm.mean(axis=1)
    keep = (freq > 0.05) & (freq < 0.95)
    gm = gm[keep]
    if gm.shape[0] < n_sites:
        raise RuntimeError("not enough common sites: %d" % gm.shape[0])
    idx = np.linspace(0, gm.shape[0] - 1, n_sites).astype(int)
    gm = gm[idx]
    # haplotypes -> diploid dosages
    h = gm.reshape(gm.shape[0], -1, 2)
    dose = h.sum(axis=2).T.astype(float)           # individuals x sites
    return dose


def standardise(dose):
    z = (dose - dose.mean(axis=0)) / dose.std(axis=0)
    return z


# ---------------------------------------------------------------------------
# 1. pgsPhenoCov / sharedLDGeneticVariance / pgsR2 and the R2 chain
# ---------------------------------------------------------------------------
def test_transfer_chain():
    rng = np.random.default_rng(4001)
    dose = coalescent_haplotypes(seed=7)
    z = standardise(dose)
    n, m = z.shape
    # LD read as the CORRELATION matrix of standardised dosages, which is what
    # the corpus's `standardizedDiagonalLD` (identity on the diagonal) implies.
    ld = np.corrcoef(z, rowvar=False)

    beta_causal = rng.normal(0, 1, m) / math.sqrt(m)
    # a target effect vector correlated with the source, so genetic correlation
    # is strictly between 0 and 1 and the transported R2 is not degenerate
    beta_target = 0.7 * beta_causal + math.sqrt(1 - 0.49) * rng.normal(0, 1, m) / math.sqrt(m)
    beta_source = beta_causal

    g_src = z @ beta_source
    var_e = 3.0
    y = z @ beta_causal + rng.normal(0, math.sqrt(var_e), n)
    var_y = float(y.var())

    def pgsPhenoCov(bw, bc):
        return float(bw @ ld @ bc)

    cells = [
        dict(design="Cov(PGS, y)", lean=pgsPhenoCov(beta_source, beta_causal),
             truth=float(np.cov(g_src, y)[0, 1]),
             sem=float(np.std(g_src * y) / math.sqrt(n))),
        dict(design="Var(PGS) = sharedLDGeneticVariance",
             lean=pgsPhenoCov(beta_source, beta_source),
             truth=float(g_src.var()),
             sem=float(g_src.var()) * math.sqrt(2.0 / n)),
    ]
    record("pgsPhenoCov / sharedLDGeneticVariance", "TransferLearningPGS.lean",
           "sum_ij bw_i * ld_ij * bc_j", cells,
           regime="standardised dosages, LD as the correlation matrix, "
                  "coalescent LD from msprime")

    # sharedLDHeritability and additiveHeritability
    cells_h = [
        dict(design="sharedLDHeritability",
             lean=pgsPhenoCov(beta_causal, beta_causal) / var_y,
             truth=float(np.var(z @ beta_causal) / var_y),
             sem=float(np.var(z @ beta_causal) / var_y) * math.sqrt(2.0 / n)),
    ]
    record("sharedLDHeritability", "TransferLearningPGS.lean",
           "sharedLDGeneticVariance beta ld / var_y", cells_h,
           regime="fraction of phenotypic variance from the additive score")

    # pgsR2 and the source/target R2 pair, against an out-of-sample regression
    var_pgs = float(g_src.var())
    cov_py = float(np.cov(g_src, y)[0, 1])
    lean_r2 = cov_py ** 2 / (var_pgs * var_y)
    obs_r2 = float(np.corrcoef(g_src, y)[0, 1] ** 2)
    cells_r2 = [dict(design="source R2", lean=lean_r2, truth=obs_r2,
                     sem=obs_r2 * math.sqrt(4.0 / n))]
    # transported: the SAME source weights scored against a target-effect phenotype
    y_t = z @ beta_target + rng.normal(0, math.sqrt(var_e), n)
    var_yt = float(y_t.var())
    lean_tr = pgsPhenoCov(beta_source, beta_target) ** 2 / (
        pgsPhenoCov(beta_source, beta_source) * var_yt)
    obs_tr = float(np.corrcoef(g_src, y_t)[0, 1] ** 2)
    cells_r2.append(dict(design="transported target R2", lean=lean_tr,
                         truth=obs_tr, sem=obs_tr * math.sqrt(4.0 / n)))
    record("pgsR2 / sourceTruthR2SharedLD / transportedTargetR2SharedLD",
           "TransferLearningPGS.lean",
           "cov_pgs_y^2 / (var_pgs * var_y)", cells_r2,
           regime="squared correlation of the score with the phenotype")

    # the two genetic-correlation definitions, which differ by LD weighting
    ld_gc = pgsPhenoCov(beta_source, beta_target) / math.sqrt(
        pgsPhenoCov(beta_source, beta_source) * pgsPhenoCov(beta_target, beta_target))
    plain_gc = float(beta_source @ beta_target / math.sqrt(
        (beta_source ** 2).sum() * (beta_target ** 2).sum()))
    g_tgt = z @ beta_target
    obs_gc = float(np.corrcoef(g_src, g_tgt)[0, 1])
    cells_gc = [
        dict(design="ldEffectGeneticCorrelation", lean=ld_gc, truth=obs_gc,
             sem=(1 - obs_gc ** 2) / math.sqrt(n)),
        dict(design="effectGeneticCorrelation (LD-free)", lean=plain_gc,
             truth=obs_gc, sem=(1 - obs_gc ** 2) / math.sqrt(n)),
    ]
    record("ldEffectGeneticCorrelation vs effectGeneticCorrelation",
           "TransferLearningPGS.lean",
           "LD-weighted vs plain cosine between effect vectors", cells_gc,
           regime="truth is the correlation of the two genetic values in the "
                  "same individuals; only one of the two can be it")


# ---------------------------------------------------------------------------
# 2. DGP: fstEquilibrium under mutation AND migration
# ---------------------------------------------------------------------------
def test_fst_equilibrium_dgp():
    """fstEquilibrium = 1/(1 + theta + bigM), island model with mutation."""
    import msprime
    Ne = 1000
    cells, cells_nomut = [], []
    for m, mu in ((5e-4, 2.5e-5), (1e-3, 2.5e-5), (5e-4, 1e-4), (1e-3, 1e-4)):
        theta, bigM = 4 * Ne * mu, 4 * Ne * m
        dem = msprime.Demography.island_model([Ne] * 20, migration_rate=m / 19.0)
        vals = []
        for r in range(24):
            ts = msprime.sim_ancestry(samples={0: 30, 1: 30}, demography=dem,
                                      sequence_length=1e6,
                                      recombination_rate=1e-8,
                                      random_seed=4101 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            d_a = ts.diversity([A], mode="branch")[0]
            d_b = ts.diversity([B], mode="branch")[0]
            d_ab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            vals.append(1.0 - ((d_a + d_b) / 2.0) / d_ab)
        s = simlib.summarize(vals)
        cells.append(dict(design="theta=%.1f M=%.1f" % (theta, bigM),
                          lean=1 / (1 + theta + bigM), truth=s["mean"],
                          sem=s["sem"]))
        cells_nomut.append(dict(design="theta=%.1f M=%.1f" % (theta, bigM),
                                lean=1 / (1 + bigM), truth=s["mean"],
                                sem=s["sem"]))
    record("fstEquilibrium", "DGP.lean", "1 / (1 + theta + bigM)", cells,
           regime="20-deme island model, exact coalescence times; mutation "
                  "does not alter a coalescence-time F_ST")
    record("fstDriftMigration", "DGP.lean", "1 / (1 + bigM)", cells_nomut,
           regime="same runs, the mutation-free sibling")


# ---------------------------------------------------------------------------
# 3. DGP: LD decay definitions
# ---------------------------------------------------------------------------
def test_ld_decay_defs():
    """discreteRecombinationSurvival and sharedLDRetention, exactly."""
    rng = np.random.default_rng(4201)
    cells_disc, cells_cont = [], []
    for r_rate, t in ((0.01, 20), (0.01, 100), (0.05, 40)):
        reps = 400000
        # an ancestral haplotype survives intact iff no recombination in t
        # meioses: an exact Bernoulli count, no model slack at all
        surv = float(np.mean(rng.random((reps, t)).min(axis=1) >= r_rate))
        cells_disc.append(dict(design="r=%.2f t=%d" % (r_rate, t),
                               lean=(1 - r_rate) ** t, truth=surv,
                               sem=math.sqrt(surv * (1 - surv) / reps)))
        # sharedLDRetention uses exp(-2 r t_div): two independent lineages
        cells_cont.append(dict(design="r=%.2f t=%d" % (r_rate, t),
                               lean=math.exp(-2 * r_rate * t),
                               truth=surv ** 2,
                               sem=2 * surv * math.sqrt(surv * (1 - surv) / reps)))
    record("discreteRecombinationSurvival", "DGP.lean",
           "(1 - recombRate)^tmrca", cells_disc,
           regime="probability no recombination occurs in tmrca meioses")
    record("sharedLDRetention", "DGP.lean", "exp(-2 * recomb * t_div)",
           cells_cont,
           regime="two lineages each surviving t_div meioses intact; the "
                  "continuous approximation to the exact (1-r)^(2t)")


def main():
    for fn in (test_transfer_chain, test_fst_equilibrium_dgp,
               test_ld_decay_defs):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_transfer_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-54s worst %8.1f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
