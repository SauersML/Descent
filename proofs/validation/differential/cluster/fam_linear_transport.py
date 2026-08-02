#!/usr/bin/env python3
"""Family simulator: LINEAR PREDICTION TRANSPORT. numpy only.

47 members, the largest unsimulated family in the corpus, and the one carrying
the most "Empirical status: UNTESTED" markers. Every member is matrix algebra
over `CrossPopulationMetricModel` (Calibrator/PortabilityDrift.lean ~1119).
The whole point of this file is that the structure is INSTANTIATED FROM A
SIMULATED TWO-POPULATION GENOTYPE PROCESS, not from hand-chosen matrices --
hand-chosen matrices are what `witnessSigmaObs` / `witnessCross` /
`witnessW_opt` already are, and they can witness existence but never
calibration.

THE PROCESS
  L biallelic loci on a line. Ancestral frequencies U(0.1,0.9); each population
  gets its own frequencies by Balding-Nichols drift at F_ST, and its own LD by
  its own latent AR(1) decay parameter along the chromosome. Haplotypes are a
  Gaussian-copula threshold model (exact marginals, geometric LD decay);
  genotypes are two independent haplotypes, so HWE holds by construction and is
  not assumed anywhere in the measurement. Alternate loci are tags and causals,
  so every tag tags its neighbours by LD and no causal locus is ever observed.

  Phenotype y = g_causal . beta(P) + e, with Var(e) fixed so h^2 = 0.5 in the
  source. Nothing about y is used to build the model matrices except through
  the definitions themselves.

THE INSTANTIATION (this is the contract being tested)
  m.sigmaTag P        := Cov(g_tag) in a REFERENCE sample from P
  m.directCausal P    := Cov(g_tag, g_causal) in the same reference sample
  m.proxyTagging P    := 0            (the direct/proxy split is a partition of
                                       the same matrix; putting it all in one
                                       side tests the sum, which is all any
                                       definition here reads)
  m.novel*            := 0 in the base arms; a target-only causal block with
                         zero source frequency in the NOVEL arm
  m.beta P            := the true effect vector in P
  m.contextCross P    := 0 in the base arms; the finite-sample fitting
                         deviation in the OVERFIT arm (see D)
  m.outcomeVariance P := Var(y) in P

  Weights come from the corpus itself: w = sourceWeightsFromExplicitDrivers m.
  Every closed form is then evaluated on those same matrices, and compared to
  the same quantity MEASURED on an INDEPENDENT evaluation sample of target
  individuals. So the comparison is algebra-against-process, and the residual
  is out-of-sample sampling error, not a tautology.

WHAT EACH ARM SETTLES
  A. scoreVarianceFromSourceWeights, predictiveCovarianceFromSourceWeights,
     calibrationSlopeFromSourceWeights, explainedSignalVarianceFromSourceWeights,
     residualVarianceFromSourceWeights, targetLinearRisk,
     explainedR2FromTransportMoments, sourceERMWeights,
     sourceWeightsFromExplicitDrivers, sourceWeightedTagScore, crossCovariance,
     sigmaTagCausalSourceAt, totalEffect, taggingProjection,
     directCausalProjection, proxyTaggingProjection -- each against its measured
     counterpart in fresh target individuals.
  B. r2FromSourceWeights, effectiveOutcomeVariance, residualBurden,
     irreducibleTargetResidualBurden, and the four residual terms. This is the
     arm with content: r2FromSourceWeights divides the explained signal by
     effectiveOutcomeVariance = outcomeVariance + residualBurden, and the
     burden is a SUM OF SQUARED COVARIANCES added to a variance. The
     phenotype-rescaling probe below is the executable falsifier for that.
  C. targetEffectHeterogeneity and its three projections; ldMismatchFrobenius.
  D. sourceSpecificOverfitResidual across a p/n grid that reaches p/n = 0.75.

CONTROLS -- every one is shown firing on a deliberately broken input
  S1 IDENTICAL POPULATIONS. Target moments are the source moments. Then the
     calibration slope must be exactly 1, target R^2 must equal source R^2, and
     all four residual terms must be exactly 0. Isolates the fitting code from
     the transport. FIRES ON: the same model with the target LD perturbed.
  S2 SAME LD, SHIFTED EFFECTS. brokenTaggingResidual and
     ancestrySpecificLDResidual must be exactly 0 while
     targetEffectHeterogeneity is not. Isolates the effect shift.
     FIRES ON: the LD-shifted arm, where brokenTagging is not 0.
  S3 SHIFTED LD, IDENTICAL EFFECTS. The mirror: targetEffectHeterogeneity must
     be exactly 0 while brokenTagging is not. FIRES ON: the shifted-effect arm.
  P1 POSITIVE CONTROL. A deliberately mis-signed weight vector must drive
     calibrationSlopeFromSourceWeights negative. Proves the slope check can
     fire at all.
  P2 SCALE CONTROL. Genotype coding: g -> c*g with beta -> beta/c. The
     phenotype, the fitted weights' predictions and EVERY measured moment are
     unchanged -- this is the free choice between raw dosages and standardised
     genotypes. Any corpus quantity that moves under it depends on an arbitrary
     unit. FIRES ON: r2FromSourceWeights, and it is exact arithmetic, so the
     control cannot be passed by luck.

CAN-FAIL CLAUSE
  The p/n grid must reach p comparable to n. sourceSpecificOverfitResidual is
  identically zero whenever contextCross is zero, and the finite-sample
  deviation that makes it nonzero is O(p/n); a grid confined to p << n
  validates it vacuously. Arm D goes to p/n = 0.75.
  The F_ST grid must include 0 (control S1) and a value large enough that the
  tag-causal alignment actually moves; at F_ST = 0 every transport term is 0
  by construction and the arm decides nothing.

SPEED
  Vectorised over individuals and loci. The AR(1) latent is built with one
  numpy pass per locus; the batched normal draw is the same draw as a per-
  individual loop because the AR(1) recursion is applied to whole columns.
  No replicate shares random state with another: each population/sample gets
  its own draw from one seeded Generator, consumed in a fixed order.
"""

import json
import math
import sys

import numpy as np

SEED = 20260802

L = 300                 # loci on the chromosome; even index = tag, odd = causal
N_REF = 12000           # reference sample: builds the model matrices
N_EVAL = 12000          # evaluation sample: independent individuals
H2 = 0.5


# ---------------------------------------------------------------------------
# inverse normal CDF (no scipy on the cluster). Acklam, |rel err| < 1.15e-9.
# Its accuracy is checked in main() -- a bad ppf would corrupt every marginal
# allele frequency, so it is a control, not a utility.
# ---------------------------------------------------------------------------
_A = [-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02,
      1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00]
_B = [-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02,
      6.680131188771972e+01, -1.328068155288572e+01]
_C = [-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00,
      -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00]
_D = [7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00,
      3.754408661907416e+00]


def norm_ppf(p):
    p = np.asarray(p, dtype=np.float64)
    out = np.empty_like(p)
    lo = p < 0.02425
    hi = p > 1 - 0.02425
    mid = ~(lo | hi)
    q = np.sqrt(-2 * np.log(np.where(lo, p, 0.5)))
    out = np.where(lo,
                   ((((_C[0] * q + _C[1]) * q + _C[2]) * q + _C[3]) * q + _C[4]) * q + _C[5],
                   0.0)
    out = np.where(lo, out / ((((_D[0] * q + _D[1]) * q + _D[2]) * q + _D[3]) * q + 1), out)
    q2 = np.sqrt(-2 * np.log(np.where(hi, 1 - p, 0.5)))
    hv = ((((_C[0] * q2 + _C[1]) * q2 + _C[2]) * q2 + _C[3]) * q2 + _C[4]) * q2 + _C[5]
    hv = -hv / ((((_D[0] * q2 + _D[1]) * q2 + _D[2]) * q2 + _D[3]) * q2 + 1)
    out = np.where(hi, hv, out)
    r = np.where(mid, p, 0.5) - 0.5
    rr = r * r
    mv = (((((_A[0] * rr + _A[1]) * rr + _A[2]) * rr + _A[3]) * rr + _A[4]) * rr + _A[5]) * r
    mv = mv / (((((_B[0] * rr + _B[1]) * rr + _B[2]) * rr + _B[3]) * rr + _B[4]) * rr + 1)
    return np.where(mid, mv, out)


# ---------------------------------------------------------------------------
# the genotype process
# ---------------------------------------------------------------------------
def draw_haplotypes(n, freqs, ar, rng):
    """n x L haplotypes with exact marginals `freqs` and AR(1) latent decay `ar`."""
    nloc = freqs.shape[0]
    thr = norm_ppf(freqs)
    z = rng.standard_normal(n)
    h = np.empty((n, nloc), dtype=np.int8)
    h[:, 0] = (z < thr[0]).astype(np.int8)
    s = math.sqrt(1.0 - ar * ar)
    for j in range(1, nloc):
        z = ar * z + s * rng.standard_normal(n)
        h[:, j] = (z < thr[j]).astype(np.int8)
    return h


def draw_genotypes(n, freqs, ar, rng):
    a = draw_haplotypes(n, freqs, ar, rng)
    b = draw_haplotypes(n, freqs, ar, rng)
    return (a + b).astype(np.float64)


def balding_nichols(anc, fst, rng):
    if fst <= 0.0:
        return anc.copy()
    a = anc * (1 - fst) / fst
    b = (1 - anc) * (1 - fst) / fst
    p = rng.beta(a, b)
    return np.clip(p, 0.01, 0.99)


def centred_cov(x, y):
    xc = x - x.mean(axis=0, keepdims=True)
    yc = y - y.mean(axis=0, keepdims=True)
    return xc.T.dot(yc) / (x.shape[0] - 1)


# ---------------------------------------------------------------------------
# the corpus definitions, transcribed one-for-one from PortabilityDrift.lean
# and DGP.lean. Names and bodies match; `m` is a dict with the structure fields.
# ---------------------------------------------------------------------------
def sigmaTagCausalSourceAt(m, P):
    return (m["directCausal"][P] + m["novelDirectCausal"][P]
            + m["proxyTagging"][P] + m["novelProxyTagging"][P])


def totalEffect(m, P):
    return m["beta"][P] + m["novelCausalEffect"][P]


def crossCovariance(m, P):
    return sigmaTagCausalSourceAt(m, P).dot(totalEffect(m, P)) + m["contextCross"][P]


def sourceERMWeights(sigmaObsSource, crossSource):
    return np.linalg.solve(sigmaObsSource, crossSource)


def sourceWeightsFromExplicitDrivers(m):
    return sourceERMWeights(m["sigmaTag"]["source"], crossCovariance(m, "source"))


def sourceWeightedTagScore(m, tagState):
    return sourceWeightsFromExplicitDrivers(m).dot(tagState)


def taggingProjection(m, P):
    return sigmaTagCausalSourceAt(m, P).dot(totalEffect(m, P))


def directCausalProjection(m, P):
    return (m["directCausal"][P] + m["novelDirectCausal"][P]).dot(totalEffect(m, P))


def proxyTaggingProjection(m, P):
    return (m["proxyTagging"][P] + m["novelProxyTagging"][P]).dot(totalEffect(m, P))


def targetEffectHeterogeneity(m):
    return totalEffect(m, "target") - m["beta"]["source"]


def targetSourceEffectProjection(m):
    return sigmaTagCausalSourceAt(m, "target").dot(m["beta"]["source"])


def targetEffectHeterogeneityProjection(m):
    return sigmaTagCausalSourceAt(m, "target").dot(targetEffectHeterogeneity(m))


def targetNovelMutationEffectProjection(m):
    return sigmaTagCausalSourceAt(m, "target").dot(m["novelCausalEffect"]["target"])


def targetLinearRisk(sigmaObsTarget, crossTarget, noiseVar, w):
    return noiseVar + w.dot(sigmaObsTarget.dot(w)) - 2 * w.dot(crossTarget)


def scoreVarianceFromSourceWeights(m, P):
    w = sourceWeightsFromExplicitDrivers(m)
    return float(w.dot(m["sigmaTag"][P].dot(w)))


def predictiveCovarianceFromSourceWeights(m, P):
    return float(sourceWeightsFromExplicitDrivers(m).dot(crossCovariance(m, P)))


def calibrationSlopeFromSourceWeights(m, P):
    return (predictiveCovarianceFromSourceWeights(m, P)
            / scoreVarianceFromSourceWeights(m, P))


def brokenTaggingResidual(m):
    d = (sigmaTagCausalSourceAt(m, "source")
         - sigmaTagCausalSourceAt(m, "target")).dot(totalEffect(m, "target"))
    return float(d.dot(d))


def ancestrySpecificLDResidual(m):
    w = sourceWeightsFromExplicitDrivers(m)
    d = (m["sigmaTag"]["source"] - m["sigmaTag"]["target"]).dot(w)
    return float(d.dot(d))


def sourceSpecificOverfitResidual(m):
    d = m["contextCross"]["source"] - m["contextCross"]["target"]
    return float(d.dot(d))


def novelUntaggablePhenotypeResidual(m):
    return float(m["novelUntaggablePhenotypeVarianceTarget"])


def irreducibleTargetResidualBurden(m):
    return (brokenTaggingResidual(m) + ancestrySpecificLDResidual(m)
            + sourceSpecificOverfitResidual(m) + novelUntaggablePhenotypeResidual(m))


def residualBurden(m, P):
    return 0.0 if P == "source" else irreducibleTargetResidualBurden(m)


def effectiveOutcomeVariance(m, P):
    return m["outcomeVariance"][P] + residualBurden(m, P)


def explainedSignalVarianceFromSourceWeights(m, P):
    return (predictiveCovarianceFromSourceWeights(m, P) ** 2
            / scoreVarianceFromSourceWeights(m, P))


def r2FromSourceWeights(m, P):
    return explainedSignalVarianceFromSourceWeights(m, P) / effectiveOutcomeVariance(m, P)


def residualVarianceFromSourceWeights(m, P):
    return effectiveOutcomeVariance(m, P) - explainedSignalVarianceFromSourceWeights(m, P)


def explainedR2FromTransportMoments(scoreOutcomeCov, scoreVariance, outcomeVariance):
    return scoreOutcomeCov ** 2 / (scoreVariance * outcomeVariance)


def ldMismatchFrobenius(Sig_S, Sig_T):
    d = Sig_S - Sig_T
    return float((d * d).sum())


# ---------------------------------------------------------------------------
# building a model from the process
# ---------------------------------------------------------------------------
def build_world(rng, fst, ar_source, ar_target, ntag, effect_shift=0.0,
                novel_frac=0.0, pheno_scale=1.0, overfit_n=0,
                n_ref=N_REF, n_eval=N_EVAL, world_seed=None):
    """Simulate two populations and instantiate CrossPopulationMetricModel.

    `world_seed` pins the POPULATION PARAMETERS (ancestral and drifted allele
    frequencies, effect vectors) to a fixed draw so that two calls differing
    only in n_ref/n_eval are the SAME WORLD observed at two sample sizes. The
    genotypes are still drawn from the caller's stream, so the samples are
    independent draws and no replicate shares random state with another."""
    if world_seed is not None:
        rng_w = np.random.default_rng(world_seed)
    else:
        rng_w = rng
    anc = rng_w.uniform(0.1, 0.9, size=L)
    tag_idx = np.arange(0, L, 2)[:ntag]
    causal_idx = np.arange(1, L, 2)[:ntag]
    q = causal_idx.shape[0]

    fS = balding_nichols(anc, fst, rng_w)
    fT = fS.copy() if fst <= 0.0 else balding_nichols(anc, fst, rng_w)

    beta_s = rng_w.standard_normal(q) * pheno_scale
    beta_t = beta_s + effect_shift * rng_w.standard_normal(q) * pheno_scale

    # novel target-only causal variants: absent in the source (freq clamped to
    # the floor there), segregating in the target.
    novel_t = np.zeros(q)
    if novel_frac > 0.0:
        k = max(1, int(novel_frac * q))
        who = rng_w.choice(q, size=k, replace=False)
        novel_t[who] = rng_w.standard_normal(k) * pheno_scale
        fS[causal_idx[who]] = 0.01

    gS_ref = draw_genotypes(n_ref, fS, ar_source, rng)
    gT_ref = draw_genotypes(n_ref, fT, ar_target, rng)
    gT_ev = draw_genotypes(n_eval, fT, ar_target, rng)
    gS_ev = draw_genotypes(n_eval, fS, ar_source, rng)

    def moments(g):
        t = g[:, tag_idx]
        c = g[:, causal_idx]
        return centred_cov(t, t), centred_cov(t, c), c

    SigS, XcS, cS = moments(gS_ref)
    SigT, XcT, cT = moments(gT_ref)

    # phenotype: sigma_e^2 set from the SOURCE genetic variance so h^2 = 0.5
    vg_s = float(beta_s.dot(np.cov(cS, rowvar=False).dot(beta_s)))
    sig_e = math.sqrt(max(vg_s, 1e-12) * (1 - H2) / H2)

    def pheno(g, beta, novel, n):
        c = g[:, causal_idx]
        return c.dot(beta + novel) + rng.standard_normal(n) * sig_e

    yS_ref = pheno(gS_ref, beta_s, np.zeros(q), n_ref)
    yT_ref = pheno(gT_ref, beta_t, novel_t, n_ref)
    yS_ev = pheno(gS_ev, beta_s, np.zeros(q), n_eval)
    yT_ev = pheno(gT_ev, beta_t, novel_t, n_eval)

    ctxS = np.zeros(ntag)
    ctxT = np.zeros(ntag)
    if overfit_n > 0:
        # contextCross as the finite-sample fitting deviation: the empirical
        # tag-outcome cross-covariance in a sample of `overfit_n` individuals,
        # minus the population-level Sigma_tc . beta. This is what
        # sourceSpecificOverfitResidual is for, and it is O(p/n).
        iS = rng.choice(n_ref, size=overfit_n, replace=False)
        iT = rng.choice(n_ref, size=overfit_n, replace=False)
        empS = centred_cov(gS_ref[iS][:, tag_idx], yS_ref[iS].reshape(-1, 1))[:, 0]
        empT = centred_cov(gT_ref[iT][:, tag_idx], yT_ref[iT].reshape(-1, 1))[:, 0]
        ctxS = empS - XcS.dot(beta_s)
        ctxT = empT - XcT.dot(beta_t + novel_t)

    Z = np.zeros((ntag, q))
    m = {
        "beta": {"source": beta_s, "target": beta_t},
        "sigmaTag": {"source": SigS, "target": SigT},
        "directCausal": {"source": XcS, "target": XcT},
        "proxyTagging": {"source": Z, "target": Z},
        "novelDirectCausal": {"source": Z, "target": Z},
        "novelProxyTagging": {"source": Z, "target": Z},
        "novelCausalEffect": {"source": np.zeros(q), "target": novel_t},
        "contextCross": {"source": ctxS, "target": ctxT},
        "outcomeVariance": {"source": float(np.var(yS_ref, ddof=1)),
                            "target": float(np.var(yT_ref, ddof=1))},
        "novelUntaggablePhenotypeVarianceTarget": 0.0,
        "targetPrevalence": 0.1,
    }
    ev = {"source": (gS_ev[:, tag_idx], yS_ev), "target": (gT_ev[:, tag_idx], yT_ev)}
    return m, ev


def make_identical(m):
    """Control S1: target moments ARE the source moments."""
    m2 = dict(m)
    for k in ("beta", "sigmaTag", "directCausal", "proxyTagging",
              "novelDirectCausal", "novelProxyTagging", "contextCross",
              "outcomeVariance"):
        m2[k] = {"source": m[k]["source"], "target": m[k]["source"]}
    m2["novelCausalEffect"] = {"source": m["novelCausalEffect"]["source"],
                               "target": m["novelCausalEffect"]["source"]}
    return m2


def rescale_genotype_units(m, ev, c):
    """g -> c*g with beta -> beta/c. The PHENOTYPE, the fitted score and every
    measured moment are unchanged bit-for-bit: w picks up a factor 1/c and the
    score w.(c g) is identical. This is exactly the free choice every PGS
    pipeline makes between raw dosages and standardised genotypes.

    Under it the four residual terms are all quadratic in the genotype scale
    while outcomeVariance is invariant, so any definition that ADDS them to a
    variance cannot be scale-covariant. That is the falsifier, and it is exact
    arithmetic -- no sampling enters it."""
    m2 = {}
    for k in m:
        m2[k] = m[k]
    for k in ("sigmaTag",):
        m2[k] = {P: m[k][P] * c * c for P in ("source", "target")}
    for k in ("directCausal", "proxyTagging", "novelDirectCausal", "novelProxyTagging"):
        m2[k] = {P: m[k][P] * c * c for P in ("source", "target")}
    for k in ("beta", "novelCausalEffect"):
        m2[k] = {P: m[k][P] / c for P in ("source", "target")}
    m2["contextCross"] = {P: m["contextCross"][P] * c for P in ("source", "target")}
    ev2 = {P: (ev[P][0] * c, ev[P][1]) for P in ev}
    return m2, ev2


def measure(m, ev, P):
    """Measure the same quantities on INDEPENDENT individuals from P."""
    gt, y = ev[P]
    w = sourceWeightsFromExplicitDrivers(m)
    s = gt.dot(w)
    sc = s - s.mean()
    yc = y - y.mean()
    vs = float(sc.dot(sc) / (len(sc) - 1))
    cov = float(sc.dot(yc) / (len(sc) - 1))
    vy = float(yc.dot(yc) / (len(yc) - 1))
    return {"scoreVariance": vs, "predictiveCovariance": cov, "outcomeVariance": vy,
            "slope": cov / vs, "r2": cov * cov / (vs * vy),
            "explainedSignalVariance": cov * cov / vs,
            "residualVariance": vy - cov * cov / vs,
            "risk": float(((yc - sc) ** 2).mean())}


def rel(a, b):
    d = abs(b) if abs(b) > 1e-12 else 1.0
    return (a - b) / d


# ---------------------------------------------------------------------------
def main():
    rng = np.random.default_rng(SEED)
    out = {}

    # -- ppf accuracy control -------------------------------------------------
    pp = np.array([0.001, 0.025, 0.1, 0.5, 0.9, 0.975, 0.999])
    back = 0.5 * (1 + np.array([math.erf(v / math.sqrt(2)) for v in norm_ppf(pp)]))
    ppf_err = float(np.max(np.abs(back - pp)))
    print("PPF control: max |Phi(Phi^-1(p)) - p| = %.3e -> %s"
          % (ppf_err, "PASS" if ppf_err < 1e-8 else "FAIL"))
    out["ppf_max_err"] = ppf_err

    # =====================================================================
    print("")
    print("S1 CONTROL: IDENTICAL POPULATIONS (target moments = source moments)")
    m0, ev0 = build_world(rng, 0.0, 0.90, 0.90, 60)
    mI = make_identical(m0)
    sl = calibrationSlopeFromSourceWeights(mI, "target")
    r2s = r2FromSourceWeights(mI, "source")
    r2t = r2FromSourceWeights(mI, "target")
    terms = [brokenTaggingResidual(mI), ancestrySpecificLDResidual(mI),
             sourceSpecificOverfitResidual(mI), novelUntaggablePhenotypeResidual(mI)]
    s1 = (abs(sl - 1.0) < 1e-9 and abs(r2t - r2s) < 1e-12
          and all(abs(t) < 1e-18 for t in terms))
    print("  slope = %.12f   r2_source = %.6f  r2_target = %.6f" % (sl, r2s, r2t))
    print("  four residual terms = %s" % (["%.3e" % t for t in terms],))
    print("  S1 -> %s" % ("PASS" if s1 else "FAIL"))
    # S1 FIRING: same criterion on the LD-shifted model must reject
    mX, evX = build_world(rng, 0.15, 0.90, 0.55, 60)
    slX = calibrationSlopeFromSourceWeights(mX, "target")
    termsX = [brokenTaggingResidual(mX), ancestrySpecificLDResidual(mX)]
    s1_fires = not (abs(slX - 1.0) < 1e-9 and all(abs(t) < 1e-18 for t in termsX))
    print("  S1 FIRING on shifted model: slope = %.6f, broken = %.4e -> %s"
          % (slX, termsX[0], "FIRES" if s1_fires else "DEAD CONTROL"))
    out["S1"] = {"slope": sl, "r2_source": r2s, "r2_target": r2t,
                 "terms": terms, "pass": bool(s1), "fires": bool(s1_fires),
                 "fires_slope": slX, "fires_broken": termsX[0]}

    # =====================================================================
    print("")
    print("S2 CONTROL: SAME LD, SHIFTED EFFECTS")
    m2, ev2 = build_world(rng, 0.0, 0.90, 0.90, 60, effect_shift=0.8)
    m2["sigmaTag"]["target"] = m2["sigmaTag"]["source"]
    m2["directCausal"]["target"] = m2["directCausal"]["source"]
    bt, ald = brokenTaggingResidual(m2), ancestrySpecificLDResidual(m2)
    het = float(np.abs(targetEffectHeterogeneity(m2)).max())
    s2 = bt < 1e-18 and ald < 1e-18 and het > 1e-3
    print("  brokenTagging = %.3e  ancestryLD = %.3e  max|effectHeterogeneity| = %.4f"
          % (bt, ald, het))
    print("  S2 -> %s" % ("PASS" if s2 else "FAIL"))
    s2_fires = not (brokenTaggingResidual(mX) < 1e-18)
    print("  S2 FIRING on LD-shifted model: brokenTagging = %.4e -> %s"
          % (brokenTaggingResidual(mX), "FIRES" if s2_fires else "DEAD CONTROL"))
    out["S2"] = {"brokenTagging": bt, "ancestryLD": ald, "max_heterogeneity": het,
                 "pass": bool(s2), "fires": bool(s2_fires)}

    # =====================================================================
    print("")
    print("S3 CONTROL: SHIFTED LD, IDENTICAL EFFECTS (mirror of S2)")
    m3, ev3 = build_world(rng, 0.15, 0.90, 0.55, 60, effect_shift=0.0)
    het3 = float(np.abs(targetEffectHeterogeneity(m3)).max())
    bt3 = brokenTaggingResidual(m3)
    ald3 = ancestrySpecificLDResidual(m3)
    s3 = het3 < 1e-15 and bt3 > 1e-9 and ald3 > 1e-9
    print("  max|effectHeterogeneity| = %.3e  brokenTagging = %.4e  ancestryLD = %.4e"
          % (het3, bt3, ald3))
    print("  S3 -> %s" % ("PASS" if s3 else "FAIL"))
    s3_fires = not (float(np.abs(targetEffectHeterogeneity(m2)).max()) < 1e-15)
    print("  S3 FIRING on shifted-effect model: max|het| = %.4f -> %s"
          % (het, "FIRES" if s3_fires else "DEAD CONTROL"))
    out["S3"] = {"max_heterogeneity": het3, "brokenTagging": bt3, "ancestryLD": ald3,
                 "pass": bool(s3), "fires": bool(s3_fires)}

    # =====================================================================
    print("")
    print("P1 POSITIVE CONTROL: mis-signed weights must give a negative slope")
    mN = dict(m3)
    mN["directCausal"] = {"source": -m3["directCausal"]["source"],
                          "target": m3["directCausal"]["target"]}
    slN = calibrationSlopeFromSourceWeights(mN, "target")
    p1 = slN < 0
    print("  slope with sign-flipped source cross-covariance = %.6f -> %s"
          % (slN, "PASS (fires)" if p1 else "FAIL"))
    out["P1"] = {"slope_missigned": slN, "pass": bool(p1)}

    # =====================================================================
    print("")
    print("A. CLOSED FORMS vs INDEPENDENT TARGET INDIVIDUALS")
    print("   %-8s %-6s %-22s %-13s %-13s %-9s"
          % ("fst", "arLD", "quantity", "corpus", "measured", "rel err"))
    rowsA = []
    for (fst, arS, arT, tagn, tag) in ((0.0, 0.90, 0.90, 60, "null"),
                                       (0.05, 0.90, 0.75, 60, "mild"),
                                       (0.15, 0.90, 0.55, 60, "strong"),
                                       (0.15, 0.90, 0.55, 120, "strong-wide")):
        mm, ee = build_world(rng, fst, arS, arT, tagn)
        me = measure(mm, ee, "target")
        w = sourceWeightsFromExplicitDrivers(mm)
        preds = {
            "scoreVariance": scoreVarianceFromSourceWeights(mm, "target"),
            "predictiveCovariance": predictiveCovarianceFromSourceWeights(mm, "target"),
            "slope": calibrationSlopeFromSourceWeights(mm, "target"),
            "explainedSignalVariance":
                explainedSignalVarianceFromSourceWeights(mm, "target"),
            "risk": targetLinearRisk(mm["sigmaTag"]["target"],
                                     crossCovariance(mm, "target"),
                                     mm["outcomeVariance"]["target"], w),
            "r2_transportMoments": explainedR2FromTransportMoments(
                predictiveCovarianceFromSourceWeights(mm, "target"),
                scoreVarianceFromSourceWeights(mm, "target"),
                mm["outcomeVariance"]["target"]),
            "r2FromSourceWeights": r2FromSourceWeights(mm, "target"),
            "residualVariance": residualVarianceFromSourceWeights(mm, "target"),
        }
        meas = dict(me)
        meas["r2_transportMoments"] = me["r2"]
        meas["r2FromSourceWeights"] = me["r2"]
        for k in ("scoreVariance", "predictiveCovariance", "slope",
                  "explainedSignalVariance", "risk", "r2_transportMoments",
                  "r2FromSourceWeights", "residualVariance"):
            r = rel(preds[k], meas[k])
            rowsA.append({"fst": fst, "ar_target": arT, "ntag": tagn, "arm": tag,
                          "quantity": k, "corpus": preds[k], "measured": meas[k],
                          "rel_err": r})
            print("   %-8.2f %-6.2f %-22s %-13.6g %-13.6g %+9.4f"
                  % (fst, arT, k, preds[k], meas[k], r))
        rowsA.append({"fst": fst, "arm": tag, "quantity": "ldMismatchFrobenius",
                      "corpus": ldMismatchFrobenius(mm["sigmaTag"]["source"],
                                                    mm["sigmaTag"]["target"]),
                      "measured": None, "rel_err": None})
    out["A_closed_forms"] = rowsA

    # =====================================================================
    print("")
    print("P2 SCALE CONTROL: genotype units. g -> c*g, beta -> beta/c.")
    print("   The phenotype, the score and every measured moment are UNCHANGED.")
    rowsP2 = []
    mS, eS = build_world(rng, 0.15, 0.90, 0.55, 60, overfit_n=400)
    for c in (1.0, 2.0, 4.0):
        mc, ec = rescale_genotype_units(mS, eS, c)
        mm = measure(mc, ec, "target")
        rowsP2.append({
            "c": c,
            "measured_r2": mm["r2"],
            "measured_slope": mm["slope"],
            "measured_scoreVariance": mm["scoreVariance"],
            "corpus_r2FromSourceWeights": r2FromSourceWeights(mc, "target"),
            "corpus_residualVariance": residualVarianceFromSourceWeights(mc, "target"),
            "corpus_effectiveOutcomeVariance": effectiveOutcomeVariance(mc, "target"),
            "burden": irreducibleTargetResidualBurden(mc),
            "brokenTagging": brokenTaggingResidual(mc),
            "ancestryLD": ancestrySpecificLDResidual(mc),
            "overfit": sourceSpecificOverfitResidual(mc),
            "outcomeVariance": mc["outcomeVariance"]["target"],
        })
        print("   c=%-4.1f measured r2 = %-12.8g slope = %-10.6g | corpus r2 = %-12.8g "
              "burden = %-12.6g Var(y) = %-10.6g"
              % (c, rowsP2[-1]["measured_r2"], rowsP2[-1]["measured_slope"],
                 rowsP2[-1]["corpus_r2FromSourceWeights"], rowsP2[-1]["burden"],
                 rowsP2[-1]["outcomeVariance"]))
    meas_inv = max(abs(r["measured_r2"] / rowsP2[0]["measured_r2"] - 1.0) for r in rowsP2)
    burden_growth = rowsP2[-1]["burden"] / rowsP2[0]["burden"]
    corpus_move = abs(rowsP2[-1]["corpus_r2FromSourceWeights"]
                      / rowsP2[0]["corpus_r2FromSourceWeights"] - 1.0)
    p2_fires = meas_inv < 1e-12 and corpus_move > 0.01
    print("   measured R^2 max relative move over c=1..4: %.3e  (must be 0)" % meas_inv)
    print("   burden grows %.4g x = c^%.3f   corpus r2 moves %.4f relative"
          % (burden_growth, math.log(burden_growth) / math.log(4.0), corpus_move))
    print("   P2 -> %s"
          % ("FIRES: r2FromSourceWeights / residualVarianceFromSourceWeights / "
             "effectiveOutcomeVariance are NOT invariant to genotype coding"
             if p2_fires else "no scale defect"))
    out["P2_genotype_scale"] = {"rows": rowsP2, "measured_r2_move": meas_inv,
                                "burden_growth_c1_to_c4": burden_growth,
                                "corpus_r2_relative_move": corpus_move,
                                "fires": bool(p2_fires)}

    # =====================================================================
    print("")
    print("B. NOISE OR BIAS?  ONE FIXED WORLD, THREE SAMPLE SIZES.")
    print("   world_seed pins the populations; only N changes. A sampling")
    print("   residual falls as 1/sqrt(N); a bias floor does not.")
    print("   %-8s %-24s %-13s %-13s %-9s"
          % ("N", "quantity", "corpus", "measured", "rel err"))
    rowsB = []
    for n in (6000, 24000, 96000):
        mb, eb = build_world(rng, 0.15, 0.90, 0.55, 60, n_ref=n, n_eval=n,
                             world_seed=777)
        meb = measure(mb, eb, "target")
        w = sourceWeightsFromExplicitDrivers(mb)
        preds = {
            "scoreVariance": scoreVarianceFromSourceWeights(mb, "target"),
            "predictiveCovariance": predictiveCovarianceFromSourceWeights(mb, "target"),
            "slope": calibrationSlopeFromSourceWeights(mb, "target"),
            "risk": targetLinearRisk(mb["sigmaTag"]["target"],
                                     crossCovariance(mb, "target"),
                                     mb["outcomeVariance"]["target"], w),
            "explainedR2FromTransportMoments": explainedR2FromTransportMoments(
                predictiveCovarianceFromSourceWeights(mb, "target"),
                scoreVarianceFromSourceWeights(mb, "target"),
                mb["outcomeVariance"]["target"]),
            "r2FromSourceWeights": r2FromSourceWeights(mb, "target"),
            "residualVarianceFromSourceWeights":
                residualVarianceFromSourceWeights(mb, "target"),
        }
        meas = {"scoreVariance": meb["scoreVariance"],
                "predictiveCovariance": meb["predictiveCovariance"],
                "slope": meb["slope"], "risk": meb["risk"],
                "explainedR2FromTransportMoments": meb["r2"],
                "r2FromSourceWeights": meb["r2"],
                "residualVarianceFromSourceWeights": meb["residualVariance"]}
        bd = irreducibleTargetResidualBurden(mb) / mb["outcomeVariance"]["target"]
        for k in preds:
            rowsB.append({"N": n, "quantity": k, "corpus": preds[k],
                          "measured": meas[k], "rel_err": rel(preds[k], meas[k]),
                          "burden_over_outcomeVariance": bd})
            print("   %-8d %-24s %-13.6g %-13.6g %+9.4f"
                  % (n, k, preds[k], meas[k], rel(preds[k], meas[k])))
        print("      burden/Var(y) = %.5f" % bd)
    def _err(n, q):
        for r in rowsB:
            if r["N"] == n and r["quantity"] == q:
                return abs(r["rel_err"])
        return None
    conv = [q for q in ("scoreVariance", "predictiveCovariance", "slope", "risk",
                        "explainedR2FromTransportMoments")
            if _err(96000, q) < _err(6000, q)]
    b_ok = (len(conv) >= 4 and _err(96000, "r2FromSourceWeights") > 0.05
            and _err(96000, "r2FromSourceWeights") > _err(96000,
                                                          "explainedR2FromTransportMoments"))
    print("   converging with N: %s" % (conv,))
    print("   r2FromSourceWeights rel err at N=96000: %.4f  (bias floor, does not"
          " converge): %s" % (_err(96000, "r2FromSourceWeights"),
                              "CONFIRMED" if b_ok else "not seen"))
    out["B_convergence"] = {"rows": rowsB, "converging": conv,
                            "bias_floor_confirmed": bool(b_ok)}

    # =====================================================================
    print("")
    print("D. sourceSpecificOverfitResidual ACROSS p/n (can-fail: reaches p/n=0.75)")
    rowsD = []
    for (ntag, n) in ((20, 400), (60, 200), (150, 200)):
        md, ed = build_world(rng, 0.15, 0.90, 0.55, ntag, overfit_n=n)
        so = sourceSpecificOverfitResidual(md)
        rowsD.append({"p": ntag, "n": n, "p_over_n": ntag / float(n),
                      "sourceSpecificOverfitResidual": so,
                      "brokenTagging": brokenTaggingResidual(md),
                      "ancestryLD": ancestrySpecificLDResidual(md)})
        print("   p=%-4d n=%-4d p/n=%-5.2f  overfitResidual = %-12.5g" % (ntag, n, ntag / float(n), so))
    # zero-context control: with contextCross = 0 the term must be exactly 0
    mz, _ = build_world(rng, 0.15, 0.90, 0.55, 60, overfit_n=0)
    z = sourceSpecificOverfitResidual(mz)
    d_ok = (z == 0.0) and all(r["sourceSpecificOverfitResidual"] > 0 for r in rowsD)
    print("   CONTROL contextCross=0 -> residual = %.3e (must be exactly 0): %s"
          % (z, "PASS" if d_ok else "FAIL"))
    out["D_overfit"] = {"rows": rowsD, "zero_context_residual": z, "pass": bool(d_ok)}

    # =====================================================================
    print("")
    print("C. NOVEL TARGET-ONLY CAUSAL VARIANTS: the three target projections")
    mc, ec = build_world(rng, 0.15, 0.90, 0.55, 60, effect_shift=0.5, novel_frac=0.25)
    tp = taggingProjection(mc, "target")
    parts = (targetSourceEffectProjection(mc) + targetEffectHeterogeneityProjection(mc))
    c_ok = float(np.abs(tp - parts).max()) < 1e-9
    print("   taggingProjection == targetSourceEffectProjection + "
          "targetEffectHeterogeneityProjection: max diff %.3e -> %s"
          % (float(np.abs(tp - parts).max()), "PASS" if c_ok else "FAIL"))
    novp = targetNovelMutationEffectProjection(mc)
    dcp = directCausalProjection(mc, "target")
    ptp = proxyTaggingProjection(mc, "target")
    c_ok2 = float(np.abs(dcp + ptp - tp).max()) < 1e-9
    print("   directCausalProjection + proxyTaggingProjection == taggingProjection: %s"
          % ("PASS" if c_ok2 else "FAIL"))
    print("   max|targetNovelMutationEffectProjection| = %.5g (must be > 0 here)" % float(np.abs(novp).max()))
    out["C_projections"] = {"decomposition_pass": bool(c_ok),
                            "direct_plus_proxy_pass": bool(c_ok2),
                            "max_novel_projection": float(np.abs(novp).max())}

    # =====================================================================
    ok = bool(ppf_err < 1e-8 and s1 and s1_fires and s2 and s2_fires and s3
              and s3_fires and p1 and d_ok and c_ok and c_ok2 and p2_fires)
    out["READ_THE_TEST"] = ok
    print("")
    print("READ_THE_TEST: %s" % ok)
    fh = open("fam_linear_transport_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_linear_transport_results.json")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
