"""Battery: the disagreements that are still LIVE in the Lean corpus.

Every entry below is a definition whose docstring, as it stands in the repo,
either says UNTESTED while an earlier battery reported a defect, or says
FALSIFIED while the body is unchanged. Each is re-run here with the gates in
`verdict.py` doing the classifying, and with the specific instrument error the
earlier run made removed by design:

  alleleFreqDivergenceRate / fstTransientAt
      The rate at which differentiation ACCUMULATES and the level it settles at
      are different quantities. The corpus writes the rate as the equilibrium
      divided by 2Ne, and writes the transient's decay base as the
      heterozygosity decay, which carries mutation but not migration. Both are
      tested here, and the second is tested CONVENTION-FREE: F(t)/F(plateau) is
      invariant to the F_ST convention, so the fitted decay exponent can be
      compared against the two candidate bases without committing to one.

  asymmetricFst
      Battery 28 tested the two readings of the single `m_into` argument and
      falsified both. It did not test the reading that the symmetric row
      implies: that F_ST depends on the SUM of the two rates. Same design, same
      runs, third candidate added.

  gwasHeritability
      The earlier run compared against the NOMINAL h2 while drawing only 60
      effects, whose realised sum of squares scatters by 18 percent. The
      realised heritability is used here.

  driftLDRetention
      The definition is the SLOPE of the E[D^2] recurrence in its own argument;
      the earlier run measured the RATIO E[D^2_{t+1}]/E[D^2_t], which also
      carries the drift CREATION term and therefore exceeds one at c = 0. The
      slope is measured here by differencing two arms that share p and q, so
      the creation term cancels exactly.

  pgsDriftVarianceFromLoci
      Measured on the scale the docstring declares (standardized, each locus
      carrying its 2p(1-p) inside beta), against the one-branch drift variance.

  admixedFstExact
      Measured with the heterozygosity ratio in the orientation the docstring
      states, rather than the one the earlier run used.

  spikeAndSlabVariance / sourceBestLinearWeightsFromLD
      Declared rather than re-measured: the first drew its effects FROM the
      distribution whose variance it then checked, and the second reported the
      worst of forty coordinates against a one-coordinate error bar.
"""
import math

import numpy as np

from battery_core import RESULTS, record


# ---------------------------------------------------------------------------
# 1.  The island transient: what sets the RATE and what sets the LEVEL.
# ---------------------------------------------------------------------------
def island_transient(Ne, d, theta, bigM, gens, n_loci=240, reps=10, seed=1):
    """Forward Wright-Fisher island model started identical in every deme.

    Returns, per replicate, the F_ST trajectory as a Nei-style ratio of
    averages over loci: mean_l Var_demes(p) / mean_l pbar(1-pbar). Only the
    SHAPE of that trajectory is used, and the shape is invariant to the
    constant any F_ST convention would put in front of it.
    """
    mu = theta / (4.0 * Ne)
    m = bigM / (4.0 * Ne)
    two_n = int(2 * Ne)
    rng = np.random.default_rng(seed)
    traj = np.zeros((reps, gens + 1))
    for r in range(reps):
        p0 = rng.uniform(0.15, 0.85, n_loci)
        p = np.tile(p0, (d, 1))
        for t in range(gens + 1):
            pbar = p.mean(axis=0)
            num = p.var(axis=0).mean()
            den = (pbar * (1 - pbar)).mean()
            traj[r, t] = num / den if den > 0 else 0.0
            if t == gens:
                break
            # migration: each deme replaces a fraction m of itself with the
            # island average, which is the standard island model
            p = (1 - m) * p + m * pbar[None, :]
            # two-way mutation
            p = p * (1 - mu) + (1 - p) * mu
            p = rng.binomial(two_n, np.clip(p, 0, 1)) / two_n
    return traj


def fit_decay(traj, gens):
    """Fitted per-generation decay base of the approach to the plateau.

    F(t) = Fstar (1 - lam^t)  =>  log(1 - F(t)/Fstar) = t log lam.
    The plateau is read from the last fifth of the run; the fit uses the window
    where the approach is between 20 and 80 percent complete, which is where
    log(1 - F/Fstar) is well conditioned.
    """
    out = []
    for r in range(traj.shape[0]):
        f = traj[r]
        fstar = f[int(0.8 * gens):].mean()
        if fstar <= 0:
            continue
        y = 1.0 - f / fstar
        t = np.arange(len(f))
        ok = (y > 0.2) & (y < 0.8)
        if ok.sum() < 5:
            ok = (y > 0.05) & (y < 0.95)
        if ok.sum() < 5:
            continue
        slope = np.polyfit(t[ok], np.log(y[ok]), 1)[0]
        out.append(math.exp(slope))
    return np.array(out)


def test_transient_rate():
    """The decay base of the F_ST transient, in units of 1/(2Ne).

    R = (1 - lam) * 2Ne. The corpus's `fstTransientAt` uses `hetDecayFactor`,
    which is drift times mutation and carries NO migration, so it predicts
    R = 1 + theta. The alternative that is forced by the corpus's own
    equilibrium `1/(1 + theta + bigM)` -- a process cannot settle at a level set
    by three forces while approaching it at the rate of two -- predicts
    R = 1 + theta + bigM.
    """
    Ne, d, gens = 200, 24, 900
    cells_corpus, cells_cand = [], []
    control = None
    for theta, bigM in ((4.0, 0.0), (0.0, 4.0), (2.0, 2.0), (0.0, 12.0)):
        traj = island_transient(Ne, d, theta, bigM, gens, seed=9001 +
                                int(10 * theta) + int(bigM))
        lams = fit_decay(traj, gens)
        R = (1.0 - lams) * 2 * Ne
        obs, sem = float(R.mean()), float(R.std(ddof=1) / math.sqrt(len(R)))
        lab = "theta=%.1f M=%.1f" % (theta, bigM)
        cells_corpus.append(dict(design=lab, lean=1.0 + theta, truth=obs,
                                 sem=sem))
        cells_cand.append(dict(design=lab, lean=1.0 + theta + bigM, truth=obs,
                               sem=sem))
        if bigM == 0.0:
            # At zero migration the two candidates coincide and the answer is
            # the independently known heterozygosity decay 1 + theta. A design
            # that cannot reproduce that has no standing to report anything.
            control = dict(design="theta=4 M=0 vs heterozygosity decay 1+theta",
                           lean=1.0 + theta, truth=obs, sem=sem)
    record("fstTransientAt [decay base = hetDecayFactor: R = 1 + theta]",
           "PortabilityDrift.lean",
           "(1/(1+theta+bigM)) * (1 - hetDecayFactor^t)", cells_corpus,
           control=control,
           regime="24-deme forward Wright-Fisher island model with two-way "
                  "mutation started identical; the fitted per-generation decay "
                  "base of F(t)/F(plateau), which is invariant to the F_ST "
                  "convention, expressed as R = (1 - lam) * 2Ne")
    record("fstTransientAt [CANDIDATE: R = 1 + theta + bigM]",
           "PortabilityDrift.lean",
           "(1/(1+theta+bigM)) * (1 - (1 - (1+theta+bigM)/(2Ne))^t)",
           cells_cand, control=control, regime="same runs, same fits")


def test_divergence_rate():
    """The per-generation allele-frequency divergence rate from a common start.

    `alleleFreqDivergenceRate` divides by `(1 + theta + bigM)`, which says
    mutation and migration SLOW the accumulation of divergence. From a common
    start they cannot: both are deterministic maps applied identically to every
    replicate, so at the first generation they contribute nothing to the
    across-replicate variance, and the rate is the drift rate alone.
    """
    n_loci, reps = 400, 20000
    cells_corpus, cells_cand = [], []
    control = None
    for Ne, theta, bigM in ((200, 0.0, 0.0), (200, 0.8, 0.0), (200, 0.0, 0.8),
                            (200, 4.0, 4.0), (500, 0.0, 4.0)):
        mu, m = theta / (4.0 * Ne), bigM / (4.0 * Ne)
        two_n = int(2 * Ne)
        rng = np.random.default_rng(7001 + Ne + int(10 * theta) + int(bigM))
        p0 = rng.uniform(0.15, 0.85, n_loci)
        p = np.tile(p0, (reps, 1))
        # one generation: migration toward the common ancestral mean, mutation,
        # then binomial sampling
        p = (1 - m) * p + m * p0[None, :]
        p = p * (1 - mu) + (1 - p) * mu
        p = rng.binomial(two_n, np.clip(p, 0, 1)) / two_n
        rate_l = p.var(axis=0, ddof=1) / (p0 * (1 - p0))
        obs = float(rate_l.mean())
        sem = float(rate_l.std(ddof=1) / math.sqrt(n_loci))
        lab = "Ne=%d theta=%.1f M=%.1f" % (Ne, theta, bigM)
        cells_corpus.append(dict(design=lab,
                                 lean=1.0 / (2 * Ne * (1 + theta + bigM)),
                                 truth=obs, sem=sem))
        cells_cand.append(dict(design=lab, lean=1.0 / (2 * Ne), truth=obs,
                               sem=sem))
        if theta == 0.0 and bigM == 0.0:
            control = dict(design="Ne=200 no mutation no migration vs 1/(2Ne)",
                           lean=1.0 / (2 * Ne), truth=obs, sem=sem)
    record("alleleFreqDivergenceRate", "DGP.lean",
           "1 / (2*Ne*(1 + theta + bigM))", cells_corpus, control=control,
           regime="across-replicate variance of the allele frequency after ONE "
                  "generation from a common start, normalised by p0(1-p0), "
                  "20000 replicate populations and 400 loci")
    record("alleleFreqDivergenceRate [CANDIDATE: 1/(2Ne)]", "DGP.lean",
           "1 / (2*Ne)", cells_cand, control=control,
           regime="same runs, the drift rate alone")


# ---------------------------------------------------------------------------
# 2.  asymmetricFst: the reading battery 28 did not try.
# ---------------------------------------------------------------------------
def two_deme_asym_fst(Ne, m12, m21, reps=24, seed=1):
    import msprime
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne)
    dem.add_population(name="B", initial_size=Ne)
    dem.set_migration_rate(source="A", dest="B", rate=m12)
    dem.set_migration_rate(source="B", dest="A", rate=m21)
    vals = []
    for r in range(reps):
        ts = msprime.sim_ancestry(samples={"A": 25, "B": 25}, demography=dem,
                                  sequence_length=4e6, recombination_rate=1e-8,
                                  random_seed=seed + r)
        A, B = ts.samples(population=0), ts.samples(population=1)
        da = ts.diversity([A], mode="branch")[0]
        db = ts.diversity([B], mode="branch")[0]
        dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
        vals.append(1.0 - 0.5 * (da + db) / dab)
    v = np.array(vals)
    return float(v.mean()), float(v.std(ddof=1) / math.sqrt(len(v)))


def test_asymmetric_fst():
    Ne = 1000
    cells_big, cells_small, cells_sum = [], [], []
    control = None
    for m12, m21 in ((1.0e-3, 1.0e-3), (1.5e-3, 5.0e-4), (1.8e-3, 2.0e-4)):
        obs, sem = two_deme_asym_fst(Ne, m12, m21, seed=31001)
        lab = "m12=%.1e m21=%.1e" % (m12, m21)
        big, small = max(m12, m21), min(m12, m21)
        cells_big.append(dict(design=lab, lean=1 / (1 + 4 * Ne * big),
                              truth=obs, sem=sem))
        cells_small.append(dict(design=lab, lean=1 / (1 + 4 * Ne * small),
                                truth=obs, sem=sem))
        cells_sum.append(dict(design=lab, lean=1 / (1 + 4 * Ne * (m12 + m21)),
                              truth=obs, sem=sem))
        if m12 == m21:
            # the two-deme island value, validated independently in
            # battery_correct.py at 0.6 sems
            control = dict(design="symmetric cell vs the validated two-deme "
                                  "island value 1/(1 + 2*4Ne*m)",
                           lean=1 / (1 + 2 * 4 * Ne * m12), truth=obs, sem=sem)
    reg = ("two demes with asymmetric migration, Ne=1000, F_ST read as "
           "1 - E[T_within]/E[T_between] from branch lengths so no estimator "
           "convention enters, 24 replicates of 4 Mb")
    record("asymmetricFst [m_into = the larger rate]", "PortabilityDrift.lean",
           "1 / (1 + 4*Ne*m_into)", cells_big, control=control, regime=reg)
    record("asymmetricFst [m_into = the smaller rate]", "PortabilityDrift.lean",
           "1 / (1 + 4*Ne*m_into)", cells_small, control=control,
           regime="same runs, the other reading of the single rate argument")
    record("asymmetricFst [CANDIDATE: the SUM of the two rates]",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*(m12 + m21))", cells_sum,
           control=control,
           regime="same runs; the reading the symmetric row forces, since "
                  "there 1/(1 + 4Ne(m+m)) is the two-deme island value")


# ---------------------------------------------------------------------------
# 3.  gwasHeritability, against the REALISED heritability.
# ---------------------------------------------------------------------------
def test_gwas_heritability():
    rng = np.random.default_rng(14401)
    cells_nom, cells_real = [], []
    n, m = 100000, 300
    for h2, rho in ((0.5, 0.9), (0.5, 0.6), (0.8, 0.8)):
        causal = rng.normal(0, 1, (n, m))
        tag = rho * causal + math.sqrt(1 - rho ** 2) * rng.normal(0, 1, (n, m))
        beta = rng.normal(0, math.sqrt(h2 / m), m)
        g = causal @ beta
        e = rng.normal(0, math.sqrt(1 - h2), n)
        y = g + e
        # the heritability this REPLICATE actually has, not the nominal one:
        # the effects are drawn, so sum beta^2 scatters by sqrt(2/m)
        h2_real = float(np.var(g) / np.var(y))
        A = tag - tag.mean(0)
        coef, *_ = np.linalg.lstsq(A, y - y.mean(), rcond=None)
        captured = float(np.var(A @ coef) / np.var(y))
        # in-sample R^2 with m predictors overstates by (1-R2)*m/n
        captured -= (1 - captured) * m / n
        lab = "h2=%.1f rho=%.1f (realised h2=%.3f)" % (h2, rho, h2_real)
        sem = captured * math.sqrt(4.0 / n)
        cells_nom.append(dict(design=lab, lean=h2 * rho ** 2, truth=captured,
                              sem=sem))
        cells_real.append(dict(design=lab, lean=h2_real * rho ** 2,
                               truth=captured, sem=sem))
    record("gwasHeritability [nominal h2, the earlier reading]",
           "AncestrySpecificArchitecture.lean", "h2_true * avg_r2_tag",
           cells_nom,
           regime="variance explained by regressing on tag variants at "
                  "r-squared rho^2, with h2_true read as the NOMINAL "
                  "per-effect variance times M")
    record("gwasHeritability [realised h2]",
           "AncestrySpecificArchitecture.lean", "h2_true * avg_r2_tag",
           cells_real,
           regime="same runs, h2_true read as the heritability the drawn "
                  "effects actually produce, and the in-sample R^2 corrected "
                  "for its m/n optimism")


# ---------------------------------------------------------------------------
# 4.  driftLDRetention: the SLOPE, with the creation term differenced out.
# ---------------------------------------------------------------------------
def test_drift_ld_retention():
    cells = []
    control = None
    reps = 400000
    for Ne, c in ((100, 0.0), (100, 0.02), (100, 0.05), (500, 0.02)):
        rng = np.random.default_rng(41001 + Ne + int(1000 * c))
        two_n = int(2 * Ne)
        p = q = 0.5
        means = {}
        for D0 in (0.05, 0.15):
            D = (1 - c) * D0
            f = np.array([p * q + D, p * (1 - q) - D,
                          (1 - p) * q - D, (1 - p) * (1 - q) + D])
            counts = rng.multinomial(two_n, f, size=reps) / two_n
            p1 = counts[:, 0] + counts[:, 1]
            q1 = counts[:, 0] + counts[:, 2]
            D1 = counts[:, 0] - p1 * q1
            d2 = D1 ** 2
            means[D0] = (float(d2.mean()),
                         float(d2.std(ddof=1) / math.sqrt(reps)))
        num = means[0.15][0] - means[0.05][0]
        den = 0.15 ** 2 - 0.05 ** 2
        slope = num / den
        sem = math.hypot(means[0.15][1], means[0.05][1]) / den
        lab = "Ne=%d c=%.2f" % (Ne, c)
        cells.append(dict(design=lab, lean=(1 - c) ** 2 * (1 - 1 / (2 * Ne)),
                          truth=slope, sem=sem))
        if c == 0.0:
            control = dict(design="Ne=100 c=0 vs the pure-drift retention "
                                  "1 - 1/(2Ne)",
                           lean=1 - 1 / (2 * Ne), truth=slope, sem=sem)
    record("driftLDRetention [slope of the E[D^2] recurrence]",
           "LDDecayTheory.lean", "(1 - c)^2 * (1 - 1/(2*Ne))", cells,
           control=control,
           regime="the SLOPE in Q, obtained by differencing two arms that "
                  "share p and q and differ only in D0, so the drift CREATION "
                  "term -- which is what makes the raw ratio E[D^2_{t+1}]/"
                  "E[D^2_t] exceed one at c = 0 -- cancels exactly")


# ---------------------------------------------------------------------------
# 5.  pgsDriftVarianceFromLoci on the scale its docstring declares.
# ---------------------------------------------------------------------------
def test_pgs_drift_from_loci():
    cells_body, cells_twice = [], []
    control = None
    for Ne, t in ((200, 30), (200, 100), (200, 250)):
        n_loci, reps = 400, 2500
        rng = np.random.default_rng(51001 + t)
        p0 = rng.uniform(0.05, 0.95, n_loci)
        # STANDARDIZED effects: each locus carries its 2p(1-p) inside beta, so
        # sum beta_std^2 IS V_A and the dosage-scale effect is beta_std /
        # sqrt(2p(1-p))
        beta_std = rng.normal(0, 1, n_loci)
        beta_dos = beta_std / np.sqrt(2 * p0 * (1 - p0))
        two_n = int(2 * Ne)
        p = np.tile(p0, (reps, 1))
        for _ in range(t):
            p = rng.binomial(two_n, p) / two_n
        mu1 = (2 * p * beta_dos).sum(axis=1)
        mu_anc = float((2 * p0 * beta_dos).sum())
        obs = float(np.var(mu1 - mu_anc, ddof=1))
        sem = obs * math.sqrt(2.0 / (reps - 1))
        F = 1 - (1 - 1.0 / (2 * Ne)) ** t
        s = float((beta_std ** 2).sum())
        lab = "Ne=%d t=%d (F=%.3f)" % (Ne, t, F)
        cells_body.append(dict(design=lab, lean=F * s, truth=obs, sem=sem))
        cells_twice.append(dict(design=lab, lean=2 * F * s, truth=obs,
                                sem=sem))
        if t == 30:
            # pgsDriftVariance_one_pop is 2 * fst * V_A and was validated on
            # this same engine in battery_bulk3 at 0.4 sems
            control = dict(design="t=30 vs the validated pgsDriftVariance_"
                                  "one_pop = 2 fst V_A",
                           lean=2 * F * s, truth=obs, sem=sem)
    reg = ("variance of ONE population's mean score about the ancestral mean, "
           "effects on the STANDARDIZED scale the docstring declares, so that "
           "sum beta^2 is V_A")
    record("pgsDriftVarianceFromLoci [as the docstring's displayed equation "
           "reads it: Var(dPGS) = sum fst beta^2]", "PolygenicAdaptation.lean",
           "sum_i fst * beta_i^2", cells_body, control=control, regime=reg)
    record("pgsDriftVarianceFromLoci [as the file's own theorem reads it: "
           "2 * sum fst beta^2]", "PolygenicAdaptation.lean",
           "2 * sum_i fst * beta_i^2", cells_twice, control=control,
           regime="same runs; pgsDriftVarianceFromLoci_eq_closedForm states "
                  "2 * this sum = pgsDriftVariance_one_pop")


# ---------------------------------------------------------------------------
# 6.  admixedFst / admixedFstExact with the docstring's het ratio.
# ---------------------------------------------------------------------------
def test_admixed_fst():
    cells_plain, cells_exact = [], []
    control = None
    n_loci, Ne, t = 40000, 500, 200
    rng = np.random.default_rng(61001)
    p_anc = rng.uniform(0.05, 0.95, n_loci)
    two_n = int(2 * Ne)
    pA, pB = p_anc.copy(), p_anc.copy()
    for _ in range(t):
        pA = rng.binomial(two_n, pA) / two_n
        pB = rng.binomial(two_n, pB) / two_n

    def gst(px, py):
        d2 = ((px - py) ** 2).mean()
        pb = (px + py) / 2
        return d2 / (4 * (pb * (1 - pb)).mean())

    fst_AB = gst(pA, pB)
    for alpha in (0.2, 0.5, 0.8):
        pC = alpha * pA + (1 - alpha) * pB
        obs = gst(pC, pA)
        # block-jackknife over 40 blocks of loci for an honest error bar
        blocks = np.array_split(np.arange(n_loci), 40)
        vals = np.array([gst(pC[b], pA[b]) for b in blocks])
        sem = float(vals.std(ddof=1) / math.sqrt(len(vals)))
        pbCA = (pC + pA) / 2
        pbAB = (pA + pB) / 2
        het_ratio = ((pbCA * (1 - pbCA)).mean() /
                     (pbAB * (1 - pbAB)).mean())
        lab = "alpha=%.1f (het ratio %.3f)" % (alpha, het_ratio)
        cells_plain.append(dict(design=lab, lean=(1 - alpha) ** 2 * fst_AB,
                                truth=obs, sem=sem))
        cells_exact.append(dict(design=lab,
                                lean=(1 - alpha) ** 2 * fst_AB / het_ratio,
                                truth=obs, sem=sem))
        if alpha == 0.2:
            nr = np.array([float(((pC[b] - pA[b]) ** 2).mean() /
                                 ((pA[b] - pB[b]) ** 2).mean())
                           for b in blocks])
            control = dict(design="alpha=0.2 numerator ratio vs the "
                                  "independently validated (1-alpha)^2",
                           lean=(1 - alpha) ** 2, truth=float(nr.mean()),
                           sem=float(nr.std(ddof=1) / math.sqrt(len(nr))))
    reg = ("one-pulse admixture with no post-admixture drift, Nei G_ST as a "
           "ratio of averages over 40000 loci, het ratio in the orientation "
           "the docstring states: pbar_adm(1-pbar_adm) over pbar_AB(1-pbar_AB)")
    record("admixedFst", "DemographicHistory.lean", "(1 - alpha)^2 * fst_AB",
           cells_plain, control=control, regime=reg)
    record("admixedFstExact", "DemographicHistory.lean",
           "(1 - alpha)^2 * fst_AB / hetRatio", cells_exact, control=control,
           regime="same runs, with the heterozygosity-ratio divisor")


# ---------------------------------------------------------------------------
# 7.  Two earlier falsifications that the gates retract on declaration alone.
# ---------------------------------------------------------------------------
def test_declared_retractions():
    rng = np.random.default_rng(11101)
    cells_ss = []
    for pi, s_large, s_small in ((0.01, 1.0, 0.001), (0.1, 0.5, 0.01),
                                 (0.5, 0.2, 0.05)):
        M = 400000
        big = rng.random(M) < pi
        beta = np.where(big, rng.normal(0, math.sqrt(s_large), M),
                        rng.normal(0, math.sqrt(s_small), M))
        obs = float(beta.var())
        cells_ss.append(dict(design="pi=%.2f" % pi,
                             lean=pi * s_large + (1 - pi) * s_small,
                             truth=obs, sem=obs * math.sqrt(2.0 / M)))
    record("spikeAndSlabVariance", "PolygenicArchitecture.lean",
           "pi*sigma_large + (1-pi)*sigma_small", cells_ss,
           oracle_independent=False,
           regime="the effects are DRAWN from the two-component mixture whose "
                  "variance is then measured, so agreement is guaranteed by "
                  "construction; the earlier run also used a Gaussian error "
                  "bar for a mixture whose kurtosis at pi=0.01 is enormous")

    n, c, t = 40000, 40, 12
    rng = np.random.default_rng(71001)
    L = rng.normal(0, 1, (c + t, c + t)) * 0.25 + np.eye(c + t)
    Sigma = L @ L.T
    X = rng.multivariate_normal(np.zeros(c + t), Sigma, n)
    X = (X - X.mean(0)) / X.std(0)
    S = X.T @ X / n
    beta_c = rng.normal(0, 1, c)
    y = X[:, :c] @ beta_c + rng.normal(0, 1, n)
    w_lean = np.linalg.solve(S[c:, c:], S[c:, :c] @ beta_c)
    A = X[:, c:]
    w_fit, *_ = np.linalg.lstsq(A, y, rcond=None)
    resid = y - A @ w_fit
    cov = np.linalg.inv(A.T @ A) * float(resid @ resid) / (n - t)
    se = np.sqrt(np.diag(cov))
    k = int(np.argmax(np.abs(w_lean - w_fit) / se))
    record("sourceBestLinearWeightsFromLD", "DGP.lean",
           "sigmaTagSource^-1 * sigmaTagCausal * betaCausal",
           [dict(design="worst of %d coordinates" % t, lean=float(w_lean[k]),
                 truth=float(w_fit[k]), sem=float(se[k]))],
           selected_from=t,
           regime="least-squares weights from an explicit regression on "
                  "standardised dosages; the reported cell is the worst "
                  "coordinate, which is why the selection correction applies")


def main():
    for fn in (test_divergence_rate, test_transient_rate, test_asymmetric_fst,
               test_gwas_heritability, test_drift_ld_retention,
               test_pgs_drift_from_loci, test_admixed_fst,
               test_declared_retractions):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    import json
    with open("battery_dis1_results.json", "w") as f:
        json.dump(RESULTS, f, indent=1, default=float)


if __name__ == "__main__":
    main()
