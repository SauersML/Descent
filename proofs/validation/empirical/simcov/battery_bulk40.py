"""Battery 40: quantitative-genetics scalars that had no verdict at all.

Eight definitions that the cross-reference of `battery_*_results.json` against
`inventory.json` showed carry NO battery row and no docstring status.  Every one
is measured from simulated individuals -- genotypes drawn, phenotypes built,
then a realised regression slope, variance, F-statistic or estimator precision
read off the sample.  No body under test generates the data it is compared
against.

Every group carries a COMPETING formula on the same cells, because a MATCH with
no rejected competitor measures nothing:

  A `averageEffect = a + d(1-2p)`      vs a + d(1-p), a + d p, a alone
  B `variantGeneticVarianceContribution = b^2 2p(1-p)`
                                       vs b^2 p(1-p), b^2 4p(1-p)
  C `effectiveGeneticEffect = bG + bGxE E_mean`
                                       vs bG alone, bG + bGxE
  D `fStat = n b^2 H(p) / s2`          vs H -> p(1-p), H -> 4p(1-p), H -> 1
  E `effectiveFisherInformation = n 2p(1-p) r2`
                                       vs r^1, r^4
  F `multiAncestryEffectiveN = n_t + rg^2 n_o`
                                       vs n_t + rg n_o, n_t + n_o, n_t alone
  G `screeningBreakEvenPrevalence`     vs the numerator/denominator swaps
  H `effectMutualInformation = -(m/2) log(1-rho^2)`
                                       vs -m log(1-rho^2), -(m/2) log(1-rho)

Scale conventions, stated because an unstated one is how this harness has
manufactured factor-of-two findings before:

  * `p` is the ALT-allele frequency and dosage is the ALT-allele count in
    {0,1,2}, so genotype variance is 2p(1-p) under Hardy-Weinberg. Every
    prediction is evaluated at the REALISED frequency (mean dosage / 2), never
    at the nominal one.
  * `fStat` is the noncentrality itself, not E[F]; a first-stage F has
    E[F] = 1 + ncp under the alternative, so the oracle is mean(F) - 1 and that
    subtraction is stated here rather than absorbed.
  * `effectiveFisherInformation` is compared against 1/Var(beta_hat) for the
    estimator of the CAUSAL effect obtained through the tag, with residual
    variance 1, which is what makes it an information about beta rather than
    about the tag's own slope.
  * Group F's genetic correlation is REALISED: `rg` is remeasured as the
    sample correlation between the two effect vectors actually drawn.

FRESHNESS: this file prints FRESHNESS=OK only if its own source carries the
token below, so a stale copy on the cluster cannot report these numbers.
"""
import json
import math
import os

import numpy as np

from battery_core import RESULTS, record

FRESH_TOKEN = "SIMCOV-BATTERY40-KESTREL-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def hwe_dosage(rng, p, n):
    """Alt-allele counts under Hardy-Weinberg: two independent Bernoulli(p)."""
    return ((rng.random(n) < p).astype(np.int8)
            + (rng.random(n) < p).astype(np.int8)).astype(float)


def ols(x, y):
    """(slope, standard error of the slope) for y on x."""
    n = len(x)
    xc = x - x.mean()
    sxx = float(xc @ xc)
    b = float(xc @ (y - y.mean())) / sxx
    resid = y - y.mean() - b * xc
    s2 = float(resid @ resid) / (n - 2)
    return b, math.sqrt(s2 / sxx)


# ---------------------------------------------------------------------------
# A.  OneLocusArchitecture.averageEffect -- BlindnessRegistry.lean:293
# ---------------------------------------------------------------------------
def group_a():
    """Fisher's average effect as the slope a dosage regression recovers.

    Genotypic values are homRef -> -a, het -> d, homAlt -> a, exactly the Lean
    `genotypicValue`, and the observable is the realised least-squares slope of
    that value on alt dosage.  `d` is large and `p` is swept across 1/2 so the
    competing readings of the dominance factor separate; at p = 0.85 the body
    predicts a - 0.7 d and `a + d(1-p)` predicts a + 0.15 d, a difference of
    0.85 d.
    """
    rng = np.random.default_rng(40001)
    n = 4000000
    a, d = 1.0, 0.8
    cells, c_1mp, c_p, c_a = [], [], [], []
    control = None
    for p in (0.2, 0.35, 0.5, 0.7, 0.85):
        g = hwe_dosage(rng, p, n)
        p_hat = float(g.mean()) / 2.0
        value = np.where(g == 0.0, -a, np.where(g == 1.0, d, a))
        b, se = ols(g, value)
        lab = "p=%.2f (realised %.4f)" % (p, p_hat)
        print("  %-26s slope = %+.5f ± %.5f | body %+.5f  (1-p) %+.5f  "
              "p %+.5f  a %+.5f"
              % (lab, b, se, a + d * (1 - 2 * p_hat), a + d * (1 - p_hat),
                 a + d * p_hat, a))
        cells.append(dict(design=lab, lean=a + d * (1 - 2 * p_hat), truth=b,
                          sem=se))
        c_1mp.append(dict(design=lab, lean=a + d * (1 - p_hat), truth=b, sem=se))
        c_p.append(dict(design=lab, lean=a + d * p_hat, truth=b, sem=se))
        c_a.append(dict(design=lab, lean=a, truth=b, sem=se))
        if p == 0.35:
            # Control: with NO dominance the genotypic value is exactly linear
            # in dosage, so the regression must return `a` at any frequency.
            # Both sides are measured on the same code path and it can fail.
            g0 = hwe_dosage(rng, p, n)
            v0 = np.where(g0 == 0.0, -a, np.where(g0 == 1.0, 0.0, a))
            b0, se0 = ols(g0, v0)
            control = dict(design="p=0.35 d=0 [additive locus: slope = a]",
                           lean=a, truth=b0, sem=max(se0, 1e-12))
    reg = ("one diploid locus in Hardy-Weinberg proportions, 4e6 individuals, "
           "genotypic values -a / d / a on the three genotypes; the observable "
           "is the realised OLS slope of genotypic value on alt-allele dosage. "
           "p is swept across 1/2 so 1-2p changes sign, and every prediction "
           "uses the REALISED allele frequency")
    record("averageEffect", "BlindnessRegistry.lean", "a + d * (1 - 2 * p)",
           cells, regime=reg, control=control)
    record("averageEffect [dominance factor 1-p, competing]",
           "BlindnessRegistry.lean", "a + d * (1 - p)", c_1mp, regime=reg,
           control=control)
    record("averageEffect [dominance factor p, competing]",
           "BlindnessRegistry.lean", "a + d * p", c_p, regime=reg,
           control=control)
    record("averageEffect [dominance dropped, competing]",
           "BlindnessRegistry.lean", "a", c_a, regime=reg, control=control)


# ---------------------------------------------------------------------------
# B.  variantGeneticVarianceContribution -- RareVariantPortability.lean:94
# ---------------------------------------------------------------------------
def group_b():
    """Additive variance a single variant contributes, measured as Var(beta*g).

    `p` is swept fortyfold so 2p(1-p), p(1-p) and 4p(1-p) separate by exactly
    the factors under test rather than by a scale that a fitted constant could
    absorb.
    """
    rng = np.random.default_rng(40002)
    n = 4000000
    beta = 0.35
    cells, c_half, c_four = [], [], []
    control = None
    for p in (0.02, 0.1, 0.3, 0.5, 0.8):
        g = hwe_dosage(rng, p, n)
        p_hat = float(g.mean()) / 2.0
        v = float((beta * g).var(ddof=1))
        sem = v * math.sqrt(2.0 / n) * 3.0        # heavy tail at small p
        lab = "p=%.2f (realised %.4f)" % (p, p_hat)
        print("  %-26s Var = %.6f ± %.6f | body %.6f  half %.6f  four %.6f"
              % (lab, v, sem, beta ** 2 * 2 * p_hat * (1 - p_hat),
                 beta ** 2 * p_hat * (1 - p_hat),
                 beta ** 2 * 4 * p_hat * (1 - p_hat)))
        cells.append(dict(design=lab,
                          lean=beta ** 2 * (2 * p_hat * (1 - p_hat)),
                          truth=v, sem=sem))
        c_half.append(dict(design=lab, lean=beta ** 2 * p_hat * (1 - p_hat),
                           truth=v, sem=sem))
        c_four.append(dict(design=lab,
                           lean=beta ** 2 * 4 * p_hat * (1 - p_hat),
                           truth=v, sem=sem))
        if p == 0.3:
            # Control: the sampler's mean dosage must be 2p. Independent of
            # every formula under test and capable of failing.
            control = dict(design="p=0.30 [mean dosage = 2p]", lean=2 * 0.3,
                           truth=float(g.mean()),
                           sem=math.sqrt(2 * 0.3 * 0.7 / n))
    reg = ("one diploid locus in Hardy-Weinberg proportions, 4e6 individuals; "
           "the observable is the realised sample variance of beta times the "
           "alt-allele dosage. p is swept fortyfold and every prediction uses "
           "the REALISED allele frequency")
    record("variantGeneticVarianceContribution", "RareVariantPortability.lean",
           "beta^2 * (2 * p * (1 - p))", cells, regime=reg, control=control)
    record("variantGeneticVarianceContribution [p(1-p), competing]",
           "RareVariantPortability.lean", "beta^2 * p * (1 - p)", c_half,
           regime=reg, control=control)
    record("variantGeneticVarianceContribution [4p(1-p), competing]",
           "RareVariantPortability.lean", "beta^2 * 4 * p * (1 - p)", c_four,
           regime=reg, control=control)


# ---------------------------------------------------------------------------
# C.  effectiveGeneticEffect -- GeneEnvironmentInterplay.lean:56
# ---------------------------------------------------------------------------
def group_c():
    """The marginal genetic effect under the file's own linear GxE model.

    Y = bG*G + bE*E + bGxE*G*E + eps with G a standardized dosage and E drawn
    independently with mean E_mean and variance 1.  The observable is the
    realised OLS slope of Y on G.  E_mean is swept through zero and negative so
    `bG + bGxE E_mean` separates from `bG` and from `bG + bGxE`.
    """
    rng = np.random.default_rng(40003)
    n = 2000000
    bG, bE, bGxE = 0.4, 0.3, 0.25
    cells, c_none, c_one = [], [], []
    control = None
    for E_mean in (-1.5, -0.5, 0.0, 1.0, 2.5):
        g = rng.normal(0, 1, n)
        E = rng.normal(E_mean, 1.0, n)
        y = bG * g + bE * E + bGxE * g * E + rng.normal(0, 1, n)
        b, se = ols(g, y)
        E_hat = float(E.mean())
        lab = "E_mean=%+.1f (realised %+.4f)" % (E_mean, E_hat)
        print("  %-30s slope = %+.5f ± %.5f | body %+.5f  bG %+.5f  "
              "bG+bGxE %+.5f" % (lab, b, se, bG + bGxE * E_hat, bG, bG + bGxE))
        cells.append(dict(design=lab, lean=bG + bGxE * E_hat, truth=b, sem=se))
        c_none.append(dict(design=lab, lean=bG, truth=b, sem=se))
        c_one.append(dict(design=lab, lean=bG + bGxE, truth=b, sem=se))
        if E_mean == 1.0:
            # Control: switch the interaction off and the marginal slope must
            # be bG at the same E_mean, measured on the same code path.
            g0 = rng.normal(0, 1, n)
            E0 = rng.normal(E_mean, 1.0, n)
            y0 = bG * g0 + bE * E0 + rng.normal(0, 1, n)
            b0, se0 = ols(g0, y0)
            control = dict(design="E_mean=+1.0 bGxE=0 [marginal slope = bG]",
                           lean=bG, truth=b0, sem=se0)
    reg = ("the file's own linear GxE model Y = bG G + bE E + bGxE G E + eps, "
           "2e6 individuals, G standardized and E independent of G with unit "
           "variance; the observable is the realised marginal OLS slope of Y "
           "on G. E_mean is swept through zero and negative, and the "
           "prediction uses the REALISED mean of E")
    record("effectiveGeneticEffect", "GeneEnvironmentInterplay.lean",
           "beta_G + beta_GxE * E_mean", cells, regime=reg, control=control)
    record("effectiveGeneticEffect [interaction dropped, competing]",
           "GeneEnvironmentInterplay.lean", "beta_G", c_none, regime=reg,
           control=control)
    record("effectiveGeneticEffect [environment mean dropped, competing]",
           "GeneEnvironmentInterplay.lean", "beta_G + beta_GxE", c_one,
           regime=reg, control=control)


# ---------------------------------------------------------------------------
# D.  MRInstrumentModel.fStat -- StratificationConfounding.lean:801
# ---------------------------------------------------------------------------
def group_d():
    """First-stage F of a Mendelian-randomisation instrument.

    X = beta_inst * dosage + N(0, s2) in each of `reps` independent studies of
    `n` individuals; the observable is the realised mean of the first-stage F
    across studies, MINUS ONE, because E[F] = 1 + ncp under the alternative and
    the Lean body is the noncentrality.  p is swept so the heterozygosity
    factor moves fourfold.
    """
    rng = np.random.default_rng(40004)
    n, reps, s2 = 800, 4000, 1.0
    beta = 0.08
    cells, c_half, c_four, c_one = [], [], [], []
    control = None
    for p in (0.05, 0.15, 0.3, 0.5):
        Fs = np.empty(reps)
        for k in range(reps):
            g = hwe_dosage(rng, p, n)
            x = beta * g + rng.normal(0, math.sqrt(s2), n)
            b, se = ols(g, x)
            Fs[k] = (b / se) ** 2
        ncp_obs = float(Fs.mean()) - 1.0
        sem = float(Fs.std(ddof=1)) / math.sqrt(reps)
        H = 2 * p * (1 - p)
        lab = "p=%.2f (H=%.4f)" % (p, H)
        print("  %-22s ncp = %.4f ± %.4f | body %.4f  half %.4f  four %.4f  "
              "one %.4f" % (lab, ncp_obs, sem, n * beta ** 2 * H / s2,
                            n * beta ** 2 * p * (1 - p) / s2,
                            n * beta ** 2 * 4 * p * (1 - p) / s2,
                            n * beta ** 2 / s2))
        cells.append(dict(design=lab, lean=n * beta ** 2 * H / s2,
                          truth=ncp_obs, sem=sem))
        c_half.append(dict(design=lab, lean=n * beta ** 2 * p * (1 - p) / s2,
                           truth=ncp_obs, sem=sem))
        c_four.append(dict(design=lab,
                           lean=n * beta ** 2 * 4 * p * (1 - p) / s2,
                           truth=ncp_obs, sem=sem))
        c_one.append(dict(design=lab, lean=n * beta ** 2 / s2, truth=ncp_obs,
                          sem=sem))
        if p == 0.3:
            # Control: a null instrument has noncentrality zero, so the mean F
            # must be 1. Measured on the same code path, and it can fail.
            F0 = np.empty(reps)
            for k in range(reps):
                g0 = hwe_dosage(rng, p, n)
                x0 = rng.normal(0, math.sqrt(s2), n)
                b0, se0 = ols(g0, x0)
                F0[k] = (b0 / se0) ** 2
            control = dict(design="p=0.30 beta_inst=0 [null F has mean 1]",
                           lean=1.0, truth=float(F0.mean()),
                           sem=float(F0.std(ddof=1)) / math.sqrt(reps))
    reg = ("Mendelian-randomisation first stage, 4000 independent studies of "
           "800 individuals, exposure X = beta_inst * alt dosage + Gaussian "
           "residual of variance 1; the observable is the realised mean "
           "first-stage F minus one, which is the noncentrality the Lean body "
           "is. p is swept so the heterozygosity factor moves fourfold")
    record("fStat", "StratificationConfounding.lean",
           "n * beta_inst^2 * hweHeterozygosity p / sigma2  (H = 2p(1-p))",
           cells, regime=reg, control=control)
    record("fStat [H = p(1-p), competing]", "StratificationConfounding.lean",
           "n * beta_inst^2 * p*(1-p) / sigma2", c_half, regime=reg,
           control=control)
    record("fStat [H = 4p(1-p), competing]", "StratificationConfounding.lean",
           "n * beta_inst^2 * 4p*(1-p) / sigma2", c_four, regime=reg,
           control=control)
    record("fStat [heterozygosity dropped, competing]",
           "StratificationConfounding.lean", "n * beta_inst^2 / sigma2", c_one,
           regime=reg, control=control)


# ---------------------------------------------------------------------------
# E.  effectiveFisherInformation -- AncestrySpecificPower.lean:178
# ---------------------------------------------------------------------------
def group_e():
    """Information about the CAUSAL effect available through a tag SNP.

    Two linked loci with an explicit haplotype-frequency table, so the
    correlation r between the dosages is constructed rather than assumed, and
    then REMEASURED on the sample.  Y = beta * causal dosage + N(0,1); the
    causal effect is estimated through the tag as
    slope(Y ~ tag) * Var(tag) / Cov(tag, causal), all realised moments, and the
    information is the inverse of that estimator's variance across studies.
    """
    rng = np.random.default_rng(40005)
    n, reps = 600, 4000
    p = q = 0.35
    beta = 0.5
    cells, c_r1, c_r4 = [], [], []
    control = None

    def draw(r_target, n_ind):
        """Two loci with dosage correlation r_target under Hardy-Weinberg."""
        D = r_target * math.sqrt(p * (1 - p) * q * (1 - q))
        h = np.array([p * q + D, p * (1 - q) - D,
                      (1 - p) * q - D, (1 - p) * (1 - q) + D])
        h = np.clip(h, 1e-12, None)
        h /= h.sum()
        idx = rng.choice(4, size=(n_ind, 2), p=h)
        causal = ((idx == 0) | (idx == 1)).sum(axis=1).astype(float)
        tag = ((idx == 0) | (idx == 2)).sum(axis=1).astype(float)
        return causal, tag

    for r in (0.4, 0.6, 0.8, 1.0):
        ests, r2_real = [], []
        for k in range(reps):
            causal, tag = draw(r, n)
            if tag.std() == 0 or causal.std() == 0:
                continue
            y = beta * causal + rng.normal(0, 1.0, n)
            b_tag, _ = ols(tag, y)
            cov = float(np.cov(tag, causal, ddof=1)[0, 1])
            if abs(cov) < 1e-9:
                continue
            ests.append(b_tag * float(tag.var(ddof=1)) / cov)
            r2_real.append(float(np.corrcoef(tag, causal)[0, 1]) ** 2)
        ests = np.asarray(ests)
        r2_hat = float(np.mean(r2_real))
        info = 1.0 / float(ests.var(ddof=1))
        sem = info * math.sqrt(2.0 / (len(ests) - 1))
        lab = "r=%.1f (realised r2=%.4f)" % (r, r2_hat)
        H = 2 * p * (1 - p)
        print("  %-26s I = %.3f ± %.3f | body %.3f  r^1 %.3f  r^4 %.3f"
              % (lab, info, sem, n * H * r2_hat, n * H * math.sqrt(r2_hat),
                 n * H * r2_hat ** 2))
        cells.append(dict(design=lab, lean=n * H * r2_hat, truth=info, sem=sem))
        c_r1.append(dict(design=lab, lean=n * H * math.sqrt(r2_hat),
                         truth=info, sem=sem))
        c_r4.append(dict(design=lab, lean=n * H * r2_hat ** 2, truth=info,
                         sem=sem))
        if r == 1.0:
            # Control: a perfect tag IS the causal variant, so the information
            # must be the full n*2p(1-p). Measured, and it can fail.
            control = dict(design="r=1.0 [perfect tag: I = n 2p(1-p)]",
                           lean=n * H, truth=info, sem=sem)
    reg = ("two linked diploid loci from an explicit haplotype-frequency table "
           "so the dosage correlation is constructed and then REMEASURED, "
           "4000 independent studies of 600 individuals, Y = beta * causal "
           "dosage + unit-variance Gaussian noise; the observable is the "
           "inverse variance across studies of the causal effect estimated "
           "through the tag with realised moments. r is swept so r^2 and r^4 "
           "separate more than fivefold")
    record("effectiveFisherInformation", "AncestrySpecificPower.lean",
           "n * (2*p*(1-p)) * r2_ld", cells, regime=reg, control=control)
    record("effectiveFisherInformation [r^1 attenuation, competing]",
           "AncestrySpecificPower.lean", "n * (2*p*(1-p)) * r", c_r1,
           regime=reg, control=control)
    record("effectiveFisherInformation [r^4 attenuation, competing]",
           "AncestrySpecificPower.lean", "n * (2*p*(1-p)) * r2^2", c_r4,
           regime=reg, control=control)


# ---------------------------------------------------------------------------
# F.  multiAncestryEffectiveN -- BayesianPGSTheory.lean:773
# ---------------------------------------------------------------------------
def group_f():
    """Effective sample size from borrowing an rg-correlated ancestry.

    A genetic correlation below one means the other ancestry's effect is rg
    times the target's PLUS INDEPENDENT SCATTER, and that scatter is an extra
    variance the borrowed estimate carries.  `battery_bulk23` tested the same
    formula with the other trait's effect set to EXACTLY rg times the target's,
    under which `n1 + rg^2 n2` is an algebraic identity for the inverse-variance
    combination and no amount of data could have rejected it.

    N_eff is defined here WITHOUT committing to a convention: it is the
    target-only sample size that attains the same mean squared error as the
    two-ancestry estimator, found by measuring the MSE of the target-only
    estimator on a grid of sample sizes and interpolating.  Both estimators are
    posterior means under the stated Gaussian model, so neither is handed the
    answer.

    The effect prior variance tau2 is swept across the regime boundary
    n2*tau2 = 1, because the scatter term (1-rg^2)*tau2 competes with the
    sampling term 1/n2 and the body can only be right where the second
    dominates.  A polygenic per-SNP tau2 = h2/M is far below 1/n, which is the
    regime the formula comes from; the sweep says whether that is a condition or
    an accident.
    """
    rng = np.random.default_rng(40006)
    reps = 400000
    cells, c_lin, c_sum, c_solo = [], [], [], []
    control = None

    def solo_mse(tau2, n, bt, noise):
        """Measured MSE of the target-only posterior mean at sample size n."""
        b = bt + noise / math.sqrt(n)
        est = b * (tau2 / (tau2 + 1.0 / n))
        return float(np.mean((est - bt) ** 2))

    designs = ((3000, 12000, 0.9, 3e-5), (3000, 12000, 0.6, 3e-5),
               (3000, 12000, 0.9, 3e-4), (6000, 6000, 0.7, 3e-5))
    for n1, n2, rg, tau2 in designs:
        bt = rng.normal(0, math.sqrt(tau2), reps)
        bo = rg * bt + math.sqrt(max(1 - rg ** 2, 0.0) * tau2) * rng.normal(
            0, 1, reps)
        rg_hat = float(np.corrcoef(bt, bo)[0, 1])
        b1 = bt + rng.normal(0, 1 / math.sqrt(n1), reps)
        b2 = bo + rng.normal(0, 1 / math.sqrt(n2), reps)
        v2 = (1 - rg_hat ** 2) * tau2 + 1.0 / n2      # Var(b2 | bt)
        est = ((n1 * b1 + (rg_hat / v2) * b2)
               / (1.0 / tau2 + n1 + rg_hat ** 2 / v2))
        mse = float(np.mean((est - bt) ** 2))
        # measured MSE-equivalent target-only sample size
        noise = rng.normal(0, 1, reps)
        grid = np.unique(np.round(np.geomspace(n1 * 0.8,
                                               (n1 + n2) * 1.5, 40)))
        ms = np.array([solo_mse(tau2, int(g), bt, noise) for g in grid])
        n_eff = float(np.interp(-mse, -ms, grid))   # ms decreasing in n
        # sem on N_eff: propagate the sem of the MSE through the local slope
        sem_mse = mse * math.sqrt(2.0 / (reps - 1))
        j = int(np.clip(np.searchsorted(-ms, -mse), 1, len(grid) - 1))
        dmse_dn = (ms[j] - ms[j - 1]) / (grid[j] - grid[j - 1])
        sem = abs(sem_mse / dmse_dn) if dmse_dn != 0 else float("nan")
        lab = ("n1=%d n2=%d rg=%.1f n2*tau2=%.2f (realised rg %.4f)"
               % (n1, n2, rg, n2 * tau2, rg_hat))
        print("  %-52s N_eff = %.0f ± %.0f | body %.0f  lin %.0f  sum %.0f  "
              "solo %.0f" % (lab, n_eff, sem, n1 + rg_hat ** 2 * n2,
                             n1 + rg_hat * n2, n1 + n2, n1))
        cells.append(dict(design=lab, lean=n1 + rg_hat ** 2 * n2, truth=n_eff,
                          sem=sem))
        c_lin.append(dict(design=lab, lean=n1 + rg_hat * n2, truth=n_eff,
                          sem=sem))
        c_sum.append(dict(design=lab, lean=float(n1 + n2), truth=n_eff,
                          sem=sem))
        c_solo.append(dict(design=lab, lean=float(n1), truth=n_eff, sem=sem))
        if rg == 0.9 and n1 == 3000 and tau2 == 3e-5:
            # Control: at rg = 1 the other ancestry measures the SAME effect,
            # so the two studies simply pool and N_eff must be n1 + n2. Read
            # through the identical MSE-equivalence code path, so it can fail.
            b2p = bt + rng.normal(0, 1 / math.sqrt(n2), reps)
            v2p = 1.0 / n2
            estp = ((n1 * b1 + b2p / v2p) / (1.0 / tau2 + n1 + 1.0 / v2p))
            msep = float(np.mean((estp - bt) ** 2))
            n_effp = float(np.interp(-msep, -ms, grid))
            control = dict(design="rg=1.0 [same effect: N_eff = n1 + n2]",
                           lean=float(n1 + n2), truth=n_effp,
                           sem=abs(msep * math.sqrt(2.0 / (reps - 1))
                                   / dmse_dn))
    reg = ("two ancestries, one locus, effects drawn from a Gaussian prior of "
           "variance tau2; the other ancestry's effect is rg times the "
           "target's PLUS independent scatter, which is what a genetic "
           "correlation below one means. 400000 replicates; N_eff is the "
           "MEASURED target-only sample size attaining the same mean squared "
           "error as the two-ancestry posterior mean, read by interpolation "
           "over a grid of sample sizes, so no convention for 'effective' is "
           "assumed. rg is REMEASURED on the drawn effects and n2*tau2 is "
           "swept across 1, the boundary at which the scatter term "
           "(1-rg^2)tau2 overtakes the sampling term 1/n2")
    record("multiAncestryEffectiveN", "BayesianPGSTheory.lean",
           "n_target + rg^2 * n_other", cells, regime=reg, control=control)
    record("multiAncestryEffectiveN [n_t + rg*n_o, competing]",
           "BayesianPGSTheory.lean", "n_target + rg * n_other", c_lin,
           regime=reg, control=control)
    record("multiAncestryEffectiveN [n_t + n_o, competing]",
           "BayesianPGSTheory.lean", "n_target + n_other", c_sum, regime=reg,
           control=control)
    record("multiAncestryEffectiveN [no borrowing, competing]",
           "BayesianPGSTheory.lean", "n_target", c_solo, regime=reg,
           control=control)


# ---------------------------------------------------------------------------
# G.  screeningBreakEvenPrevalence -- PGSCalibrationTheory.lean:3091
# ---------------------------------------------------------------------------
def group_g():
    """The prevalence at which a screening programme's net benefit crosses zero.

    A population of 4e6 is simulated at a grid of prevalences; each individual
    is tested with the stated sensitivity and specificity, and the realised net
    benefit is benefit per true positive minus harm per false positive.  The
    break-even prevalence is read by linear interpolation of the measured net
    benefit through zero -- a property of the simulated programme, not of the
    formula.  sens, spec, benefit and harm are all REMEASURED from the sample.
    """
    rng = np.random.default_rng(40007)
    n = 4000000
    cells, c_swap, c_nofp, c_ratio = [], [], [], []
    control = None
    designs = ((0.9, 0.95, 1.0, 0.1), (0.8, 0.90, 1.0, 0.05),
               (0.95, 0.80, 1.0, 0.02), (0.7, 0.99, 1.0, 0.2))
    for sens, spec, benefit, harm in designs:
        grid = np.linspace(0.001, 0.4, 60)
        nb = []
        for pi in grid:
            disease = rng.random(n) < pi
            pos = np.where(disease, rng.random(n) < sens,
                           rng.random(n) >= spec)
            tp = float(np.mean(pos & disease))
            fp = float(np.mean(pos & ~disease))
            nb.append(benefit * tp - harm * fp)
        nb = np.asarray(nb)
        sgn = np.where(nb >= 0)[0]
        if len(sgn) == 0 or sgn[0] == 0:
            print("  *** no zero crossing for sens=%.2f spec=%.2f" % (sens, spec))
            continue
        j = sgn[0]
        x0, x1, y0, y1 = grid[j - 1], grid[j], nb[j - 1], nb[j]
        pi_star = x0 + (x1 - x0) * (-y0) / (y1 - y0)
        # sem: the net benefit at one grid point has sem ~ sqrt(var/n); convert
        # to a prevalence sem through the local slope.
        slope = (y1 - y0) / (x1 - x0)
        sem = max(math.sqrt(max(harm, benefit) ** 2 / n) / abs(slope),
                  (x1 - x0) / math.sqrt(12))
        lean = ((1 - spec) * harm) / (sens * benefit + (1 - spec) * harm)
        lab = "sens=%.2f spec=%.2f harm=%.2f" % (sens, spec, harm)
        print("  %-32s pi* = %.5f ± %.5f | body %.5f  swap %.5f  ratio %.5f"
              % (lab, pi_star, sem, lean,
                 (sens * benefit) / (sens * benefit + (1 - spec) * harm),
                 ((1 - spec) * harm) / (sens * benefit)))
        cells.append(dict(design=lab, lean=lean, truth=pi_star, sem=sem))
        c_swap.append(dict(design=lab,
                           lean=(sens * benefit)
                           / (sens * benefit + (1 - spec) * harm),
                           truth=pi_star, sem=sem))
        c_nofp.append(dict(design=lab, lean=((1 - spec) * harm)
                           / (sens * benefit), truth=pi_star, sem=sem))
        c_ratio.append(dict(design=lab, lean=(spec * harm)
                            / (sens * benefit + spec * harm), truth=pi_star,
                            sem=sem))
        if abs(spec - 0.95) < 1e-9:
            # Control: at a FIXED prevalence the programme's net benefit is
            # independently known to be benefit*pi*sens - harm*(1-pi)*(1-spec).
            # That is a different quantity from the break-even prevalence, it
            # is measured on the same simulator, and it fails if the test
            # outcomes are drawn wrongly.
            pi_c = 0.2
            disease = rng.random(n) < pi_c
            pos = np.where(disease, rng.random(n) < sens, rng.random(n) >= spec)
            nb_c = (benefit * float(np.mean(pos & disease))
                    - harm * float(np.mean(pos & ~disease)))
            control = dict(
                design="pi=0.20 [net benefit = b*pi*sens - h*(1-pi)*(1-spec)]",
                lean=benefit * pi_c * sens - harm * (1 - pi_c) * (1 - spec),
                truth=nb_c,
                sem=math.sqrt((benefit ** 2 + harm ** 2) / n))
    reg = ("a simulated screening programme over 4e6 individuals at 60 "
           "prevalences, test outcomes drawn at the stated sensitivity and "
           "specificity, net benefit = benefit per true positive minus harm "
           "per false positive; the observable is the prevalence at which the "
           "MEASURED net benefit crosses zero, read by interpolation")
    record("screeningBreakEvenPrevalence", "PGSCalibrationTheory.lean",
           "(1-spec)*harm / (sens*benefit + (1-spec)*harm)", cells, regime=reg,
           control=control)
    record("screeningBreakEvenPrevalence [numerator swapped, competing]",
           "PGSCalibrationTheory.lean",
           "sens*benefit / (sens*benefit + (1-spec)*harm)", c_swap, regime=reg,
           control=control)
    record("screeningBreakEvenPrevalence [odds form, competing]",
           "PGSCalibrationTheory.lean", "(1-spec)*harm / (sens*benefit)",
           c_nofp, regime=reg, control=control)
    record("screeningBreakEvenPrevalence [spec not complemented, competing]",
           "PGSCalibrationTheory.lean",
           "spec*harm / (sens*benefit + spec*harm)", c_ratio, regime=reg,
           control=control)


# ---------------------------------------------------------------------------
# H.  effectMutualInformation -- MultiAncestryTheory.lean:199
# ---------------------------------------------------------------------------
def group_h():
    """Mutual information as an OPERATIONAL out-of-sample log-loss reduction.

    Evaluating the closed-form Gaussian integral in Python would be the same
    expression twice.  Instead the information is measured as what it buys: a
    predictor of the target effect vector is FIT on a training sample (so the
    correlation it uses is estimated, not handed over), and the observable is
    the realised out-of-sample reduction in negative log-likelihood per effect
    vector, in nats.  rho is swept so the m/2 and m factors separate.
    """
    rng = np.random.default_rng(40008)
    m = 40
    n_train, n_test = 400000, 400000
    cells, c_double, c_nosq = [], [], []
    control = None
    for rho in (0.3, 0.5, 0.7, 0.9):
        bs_tr = rng.normal(0, 1, (n_train, m))
        bt_tr = rho * bs_tr + math.sqrt(1 - rho ** 2) * rng.normal(
            0, 1, (n_train, m))
        # fitted conditional model, per coordinate pooled
        slope = float((bs_tr * bt_tr).sum() / (bs_tr ** 2).sum())
        resid = bt_tr - slope * bs_tr
        s2_cond = float(resid.var())
        s2_marg = float(bt_tr.var())
        bs_te = rng.normal(0, 1, (n_test, m))
        bt_te = rho * bs_te + math.sqrt(1 - rho ** 2) * rng.normal(
            0, 1, (n_test, m))
        ll_cond = -0.5 * (np.log(2 * math.pi * s2_cond)
                          + (bt_te - slope * bs_te) ** 2 / s2_cond)
        ll_marg = -0.5 * (np.log(2 * math.pi * s2_marg)
                          + bt_te ** 2 / s2_marg)
        gain = (ll_cond - ll_marg).sum(axis=1)
        mi = float(gain.mean())
        sem = float(gain.std(ddof=1)) / math.sqrt(n_test)
        rho_hat = float(np.corrcoef(bs_te.ravel(), bt_te.ravel())[0, 1])
        lab = "rho=%.1f (realised %.4f)" % (rho, rho_hat)
        lean = -m / 2.0 * math.log(1 - rho_hat ** 2)
        print("  %-26s MI = %.5f ± %.5f nats | body %.5f  2x %.5f  "
              "log(1-rho) %.5f" % (lab, mi, sem, lean, 2 * lean,
                                   -m / 2.0 * math.log(1 - rho_hat)))
        cells.append(dict(design=lab, lean=lean, truth=mi, sem=sem))
        c_double.append(dict(design=lab, lean=2 * lean, truth=mi, sem=sem))
        c_nosq.append(dict(design=lab, lean=-m / 2.0 * math.log(1 - rho_hat),
                           truth=mi, sem=sem))
        if abs(rho - 0.7) < 1e-9:
            # Control: independent effect vectors carry no information, so the
            # fitted predictor must buy nothing out of sample. Measured on the
            # same code path and capable of failing (an overfit predictor would
            # show a negative gain, a leaked one a positive gain).
            bs0 = rng.normal(0, 1, (n_train, m))
            bt0 = rng.normal(0, 1, (n_train, m))
            sl0 = float((bs0 * bt0).sum() / (bs0 ** 2).sum())
            s2c0 = float((bt0 - sl0 * bs0).var())
            s2m0 = float(bt0.var())
            bs0t = rng.normal(0, 1, (n_test, m))
            bt0t = rng.normal(0, 1, (n_test, m))
            g0 = (-0.5 * (np.log(2 * math.pi * s2c0)
                          + (bt0t - sl0 * bs0t) ** 2 / s2c0)
                  + 0.5 * (np.log(2 * math.pi * s2m0)
                           + bt0t ** 2 / s2m0)).sum(axis=1)
            control = dict(design="rho=0 [independent effects: MI = 0]",
                           lean=0.0, truth=float(g0.mean()),
                           sem=float(g0.std(ddof=1)) / math.sqrt(n_test))
    reg = ("m = 40 coordinate pairs of standardized effects with per-coordinate "
           "correlation rho; a conditional Gaussian predictor is FIT on 400000 "
           "training vectors and scored on 400000 held-out vectors, and the "
           "observable is the realised out-of-sample reduction in negative log "
           "likelihood per vector, in nats. rho is REMEASURED on the test "
           "sample and swept so the m/2 and m factors separate threefold")
    record("effectMutualInformation", "MultiAncestryTheory.lean",
           "-(m/2) * log(1 - rho^2)", cells, regime=reg, control=control)
    record("effectMutualInformation [factor m not m/2, competing]",
           "MultiAncestryTheory.lean", "-m * log(1 - rho^2)", c_double,
           regime=reg, control=control)
    record("effectMutualInformation [rho not squared, competing]",
           "MultiAncestryTheory.lean", "-(m/2) * log(1 - rho)", c_nosq,
           regime=reg, control=control)


GROUPS = (("A averageEffect", group_a),
          ("B variantGeneticVarianceContribution", group_b),
          ("C effectiveGeneticEffect", group_c),
          ("D fStat", group_d),
          ("E effectiveFisherInformation", group_e),
          ("F multiAncestryEffectiveN", group_f),
          ("G screeningBreakEvenPrevalence", group_g),
          ("H effectMutualInformation", group_h))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY40-KESTREL-20260804")
    for label, fn in GROUPS:
        print("\n===== %s =====" % label)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (label, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk40_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-22s %-58s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
