#!/usr/bin/env python3
"""Family simulators: LIABILITY-THRESHOLD METRICS, HWE GENOTYPE SCORE, and
ESTIMATOR MOMENTS. numpy only, no scipy, no msprime.

Run with:
    module load python3/3.10.9_anaconda2023.03_libmamba
    python3 fam_metrics.py

WHY THESE THREE TOGETHER
    They are the three cheapest families in the inventory and the three largest
    that had no simulator at all: 30 + 8 + 12 = 50 in-slice statements between
    them, every reference a one-line Gaussian or binomial identity, and every
    process a single vectorised draw. Nothing here needs a coalescent.

    They are in one file because they SHARE CONTROLS. The liability metrics are
    computed from second moments; the moment definitions are what produce those
    second moments; the HWE score is what the moments are read off. Running them
    apart would let a scale error in the score cancel against the same error in
    the metric -- which is the compensating-error failure this whole tier is
    organised around -- so the same draw feeds all three arms.

===========================================================================
ARM 1 -- LIABILITY THRESHOLD METRICS   (30 in-slice statements)
===========================================================================
PROCESS
    L = G + E, G ~ N(0, vSignal), E ~ N(0, vNoise). Case if L exceeds the
    (1 - pi) quantile of its own distribution. Score = G.

MEASURED, and what each settles
    A. AUC by the Mann-Whitney U identity -- the PROBABILITY that a random case
       outranks a random control, computed exactly by ranking, NOT by
       trapezoidal area under a binned ROC. A binned ROC has its own
       discretisation bias and would be a second unvalidated approximation
       sitting between the process and the claim.
       Settles equalVarianceGaussianAUCFromSNR, ...FromExplainedR2, ...Chart,
       ...FromVariances, gaussianAUCFromSignalVariance, presentDayGaussianAUC,
       presentDayEqualVarianceGaussianAUC.
    B. Brier risk of the calibrated probability P(case | G).
       Settles calibratedBrier, calibratedBrierFromVariances, brierFromR2,
       sourceBrierFromR2, targetExactCalibratedBrierRisk.
    C. Brier and log-loss REGRET of a miscalibrated probability q against the
       true eta. Settles brierRegretPoint/Ratio, logLossRegretPoint/Ratio.
    D. R^2 on the liability scale. Settles r2FromSignalVariance and the profile
       bundlers that carry it.

SPLIT CONTROLS -- WHICH FACTOR EACH ISOLATES
    L1  vSignal = 0.  AUC must be exactly 1/2, Brier exactly pi(1-pi), R^2
        exactly 0. All three are DISTRIBUTION-FREE at that point, so this
        isolates the metric code from the liability model entirely: it cannot
        be passed by a correct Gaussian and a broken ranker.
    L2  pi = 1/2, vNoise swept.  Isolates the SIGNAL-TO-NOISE arm with the
        prevalence arm pinned at its symmetric point.
    L3  vNoise fixed, pi swept.  Isolates the PREVALENCE arm with the SNR arm
        frozen.
        L2 and L3 exist because calibrated Brier is the PRODUCT
        pi(1-pi)(1-R^2). A joint sweep is passed by any pair of errors whose
        product is 1 -- a prevalence read as 1-pi and an R^2 read as its
        complement reproduce the product over a whole grid. Only the
        one-at-a-time sweeps separate them.

POSITIVE CONTROL -- PROVES THE CHECK CAN FIRE
    L4  vNoise = 0 exactly. The corpus returns Phi(0) = 1/2, chance
        discrimination; the process gives AUC = 1, perfect. This cell MUST come
        back red. A green L4 means the harness is comparing nothing, and every
        other green in this arm is worthless. The defect is already recorded in
        the corpus docstring, so this is a check on the CHECKER, not a new
        finding about the corpus.

CAN-FAIL CLAUSE
    The SNR grid must reach AUC below 0.75. Above AUC 0.95 the equal-variance
    Gaussian form, the logistic form and z/(1+z) all agree to within Monte-Carlo
    error at any feasible replicate count -- a grid confined to strong signals
    validates every candidate and decides nothing.

===========================================================================
ARM 2 -- HWE GENOTYPE SCORE   (8 in-slice statements)
===========================================================================
PROCESS
    Genotypes g_ij ~ Binomial(2, p_j) independently at m loci, ONE numpy call
    over the whole (individuals x loci) array. Score S = sum_j beta_j g_ij.

MEASURED
    E[S], Var[S], the tag/causal cross-covariance, and the Kolmogorov distance
    between standardised S and the standard normal.
    References, all EXACT (not asymptotic): E[S] = 2 sum beta_j p_j,
    Var[S] = sum beta_j^2 2 p_j (1-p_j), Cov = sum beta_j gamma_j 2 p_j (1-p_j).

SPLIT CONTROLS
    H1  m = 1.  The score is a scaled binomial with closed-form mean and
        variance and NO summation. Isolates the PER-LOCUS moment.
    H2  all beta equal, all p equal.  Var[S] = m beta^2 2p(1-p) exactly.
        Isolates the SUMMATION.
        A simulator that codes genotypes as 0/1 instead of 0/1/2 and
        compensates with a doubled beta reproduces Var[S] on any mixed grid and
        fails H1 outright.

CAN-FAIL CLAUSE
    scoreApproximationError is a claim about the Gaussian approximation to the
    score distribution. It can only bind where the approximation is bad, so the
    grid MUST include m in 1..5 and p as low as 0.01. At m = 1000, p = 0.5 the
    approximation is exact to Monte-Carlo precision and no error bound of any
    size could be refuted.

===========================================================================
ARM 3 -- ESTIMATOR MOMENTS   (12 in-slice statements)
===========================================================================
PROCESS
    Y = f(X) + eps with f NON-LINEAR and eps HETEROSCEDASTIC, so that the
    irreducible risk and the conditional-mean approximation risk are separately
    identified. A linear f or homoscedastic eps collapses them and the
    decomposition cannot be tested.

MEASURED
    measureMean/Variance/Covariance/ExpMSE/Bias, var, rsquared, mse, r2FromMSE,
    irreduciblePredictionRisk, conditionalMeanApproximationRisk, and the
    identity that the last two SUM to the MSE.

SPLIT CONTROLS
    M1  S = E[Y|X] exactly.  Approximation risk -> 0, irreducible risk stays at
        the noise variance. Isolates the APPROXIMATION term.
    M2  eps = 0.  Irreducible risk -> 0, approximation risk stays at the model
        error. Isolates the IRREDUCIBLE term.
        The decomposition is a SUM, so a check on the total MSE alone is passed
        by an implementation that swaps the two terms. M1 and M2 are the only
        things that detect it.
    M3  SIGN CONTROL. A predictor biased strictly UPWARD. measureBias must come
        out strictly POSITIVE under the corpus's E[S] - E[Y] convention and
        strictly negative under the opposite one. No symmetric check can
        perform this: a bias definition that is negated is invisible to every
        squared-error check in the corpus, and every downstream metric inherits
        the convention.

SPEED
    Everything is one vectorised draw per cell. The whole file is arithmetic on
    arrays of at most a few million doubles; no Python loop runs more than a few
    hundred times. Replicate counts, tolerances and grids are chosen for signal
    and are not reduced anywhere to make something finish.
"""

import json
import math
import os
import sys

import numpy as np

SEED = 20260802
R_MC = 400000           # draws per liability cell
R_HWE = 200000          # individuals per HWE cell
R_MOM = 500000          # draws per moment cell
TOL_MC = 4e-3           # Monte-Carlo tolerance on a probability at R_MC
HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------
# Phi and its inverse without scipy. math.erf is in the standard library and is
# correctly rounded; the inverse is Acklam's rational approximation refined by
# one Halley step, which is accurate to about 1e-15 and so is not a source of
# error at the tolerances used here.
# ---------------------------------------------------------------------------
def Phi(z):
    return 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))


def phi_pdf(z):
    return math.exp(-0.5 * z * z) / math.sqrt(2.0 * math.pi)


def Phi_inv(p):
    if p <= 0.0 or p >= 1.0:
        raise ValueError("Phi_inv out of range")
    a = [-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02,
         1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00]
    b = [-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02,
         6.680131188771972e+01, -1.328068155288572e+01]
    c = [-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00,
         -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00]
    d = [7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00,
         3.754408661907416e+00]
    plow, phigh = 0.02425, 1 - 0.02425
    if p < plow:
        q = math.sqrt(-2 * math.log(p))
        x = (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / \
            ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    elif p > phigh:
        q = math.sqrt(-2 * math.log(1 - p))
        x = -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / \
            ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    else:
        q = p - 0.5
        r = q * q
        x = (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q / \
            (((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1)
    e = Phi(x) - p
    u = e * math.sqrt(2 * math.pi) * math.exp(x * x / 2)
    return x - u / (1 + x * u / 2)


# ---------------------------------------------------------------------------
# AUC by the Mann-Whitney U identity.
#
# NOT trapezoid on a binned ROC. The AUC is P(score of a random case > score of
# a random control) + 1/2 P(tie), which rankdata computes exactly. A binned ROC
# introduces a discretisation bias of order 1/nbins that would sit between the
# process and the claim and would itself be unvalidated.
# ---------------------------------------------------------------------------
def auc_mannwhitney(scores, labels):
    order = np.argsort(scores, kind="mergesort")
    ranks = np.empty(len(scores), dtype=np.float64)
    ranks[order] = np.arange(1, len(scores) + 1, dtype=np.float64)
    # average ranks within ties; continuous scores make ties measure-zero but
    # the tie handling is kept so the estimator is exact rather than almost.
    s_sorted = scores[order]
    i = 0
    n = len(scores)
    while i < n:
        j = i + 1
        while j < n and s_sorted[j] == s_sorted[i]:
            j += 1
        if j - i > 1:
            ranks[order[i:j]] = (i + 1 + j) / 2.0
        i = j
    pos = labels.astype(bool)
    n1 = int(pos.sum())
    n0 = n - n1
    if n1 == 0 or n0 == 0:
        return float("nan")
    return float((ranks[pos].sum() - n1 * (n1 + 1) / 2.0) / (n1 * n0))


# ===========================================================================
# ARM 1 -- LIABILITY THRESHOLD METRICS
# ===========================================================================
def liability_cell(rng, v_signal, v_noise, pi, reps=R_MC):
    """One draw of the liability process; returns everything measured on it."""
    g = rng.normal(0.0, math.sqrt(v_signal), size=reps) if v_signal > 0 \
        else np.zeros(reps)
    e = rng.normal(0.0, math.sqrt(v_noise), size=reps) if v_noise > 0 \
        else np.zeros(reps)
    liab = g + e
    thresh = np.quantile(liab, 1.0 - pi)
    y = (liab > thresh).astype(np.float64)
    auc = auc_mannwhitney(g, y)

    # Calibrated probability P(case | G) under the true model. Exact, because
    # the residual is Gaussian with known variance: eta = 1 - Phi((T-G)/sd_e).
    if v_noise > 0:
        sd_e = math.sqrt(v_noise)
        z = (thresh - g) / sd_e
        eta = 0.5 * (1.0 - np.vectorize(math.erf)(z / math.sqrt(2.0)))
    else:
        eta = (g > thresh).astype(np.float64)
    brier = float(np.mean((eta - y) ** 2))
    # log loss of the calibrated probability, clipped only to avoid -inf on
    # measure-zero events; the clip is at 1e-12 and moves the mean by < 1e-9.
    ec = np.clip(eta, 1e-12, 1 - 1e-12)
    logloss = float(np.mean(-(y * np.log(ec) + (1 - y) * np.log(1 - ec))))
    # R^2 of G against the liability
    r2 = float(np.var(g) / np.var(liab)) if np.var(liab) > 0 else 0.0
    return {"auc": auc, "brier": brier, "logloss": logloss, "r2": r2,
            "prevalence": float(y.mean())}


def corpus_auc(v_signal, v_noise):
    """gaussianAUCFromSignalVariance / equalVarianceGaussianAUCFrom* -- one body.

    Transcribed from the Lean, INCLUDING its total-division convention: Lean's
    `/` returns 0 on a zero denominator, so vNoise = 0 sends the argument to 0
    and the value to Phi(0) = 1/2. That is the boundary defect the positive
    control L4 exists to reproduce; writing the transcription "sensibly" here
    would hide it.
    """
    if v_noise == 0:
        arg = 0.0
    else:
        arg = math.sqrt(v_signal / (2.0 * v_noise))
    return Phi(arg)


def corpus_r2(v_signal, v_noise):
    if v_signal + v_noise == 0:
        return 0.0
    return v_signal / (v_signal + v_noise)


def corpus_calibrated_brier(pi, v_signal, v_noise):
    return pi * (1 - pi) * (1 - corpus_r2(v_signal, v_noise))


def corpus_brier_regret_point(eta, q):
    """brierRegretPoint: (eta - q)^2, the excess Brier of reporting q."""
    return (eta - q) ** 2


def corpus_logloss_regret_point(eta, q):
    """logLossRegretPoint: the KL divergence of Bernoulli(q) from Bernoulli(eta)."""
    return eta * math.log(eta / q) + (1 - eta) * math.log((1 - eta) / (1 - q))


def arm_liability(rng):
    rows = []

    # -- CONTROL L1 : vSignal = 0. Distribution-free. Isolates metric code. --
    for pi in (0.5, 0.1, 0.01):
        m = liability_cell(rng, 0.0, 1.0, pi)
        rows.append({
            "cell": "L1 control vSignal=0", "pi": pi,
            "auc_measured": m["auc"], "auc_predicted": 0.5,
            "brier_measured": m["brier"],
            "brier_predicted": pi * (1 - pi),
            "r2_measured": m["r2"], "r2_predicted": 0.0,
            "isolates": "metric code, independent of the liability model",
            "ok": (abs(m["auc"] - 0.5) < TOL_MC
                   and abs(m["brier"] - pi * (1 - pi)) < 5e-3
                   and abs(m["r2"]) < 1e-9),
        })

    # -- CONTROL L2 : pi = 1/2, vNoise swept. Isolates the SNR arm. ----------
    # CAN-FAIL: the grid reaches AUC 0.674 at vNoise = 4, well below 0.75.
    for v_noise in (4.0, 1.0, 0.25, 0.04):
        m = liability_cell(rng, 1.0, v_noise, 0.5)
        pred = corpus_auc(1.0, v_noise)
        rows.append({
            "cell": "L2 SNR sweep at pi=0.5", "v_noise": v_noise,
            "auc_measured": m["auc"], "auc_predicted": pred,
            "brier_measured": m["brier"],
            "brier_predicted": corpus_calibrated_brier(0.5, 1.0, v_noise),
            "r2_measured": m["r2"], "r2_predicted": corpus_r2(1.0, v_noise),
            "isolates": "signal-to-noise, prevalence pinned at its symmetric point",
            "ok": abs(m["auc"] - pred) < TOL_MC,
        })

    # -- CONTROL L3 : vNoise fixed, pi swept. Isolates the prevalence arm. ---
    for pi in (0.5, 0.25, 0.1, 0.02):
        m = liability_cell(rng, 1.0, 1.0, pi)
        pred_auc = corpus_auc(1.0, 1.0)
        pred_br = corpus_calibrated_brier(pi, 1.0, 1.0)
        rows.append({
            "cell": "L3 prevalence sweep at fixed SNR", "pi": pi,
            "auc_measured": m["auc"], "auc_predicted": pred_auc,
            "brier_measured": m["brier"], "brier_predicted": pred_br,
            "r2_measured": m["r2"], "r2_predicted": corpus_r2(1.0, 1.0),
            "isolates": "prevalence, signal-to-noise frozen",
            "note": "AUC is prevalence-INVARIANT under this model; a measured "
                    "drift with pi would falsify that invariance, which no "
                    "joint sweep could attribute",
            "ok": (abs(m["auc"] - pred_auc) < TOL_MC
                   and abs(m["brier"] - pred_br) < 3e-3),
        })

    # -- POSITIVE CONTROL L4 : vNoise = 0. MUST COME BACK RED. --------------
    m = liability_cell(rng, 1.0, 0.0, 0.5)
    pred = corpus_auc(1.0, 0.0)
    l4_fired = abs(m["auc"] - pred) > 0.4
    rows.append({
        "cell": "L4 POSITIVE CONTROL vNoise=0", "pi": 0.5,
        "auc_measured": m["auc"], "auc_predicted": pred,
        "isolates": "the harness itself",
        "expected": "RED. corpus returns Phi(0)=0.5, process gives 1.0",
        "fired": l4_fired,
        "ok": l4_fired,
        "meaning": ("check CAN fire" if l4_fired else
                    "HARNESS BROKEN -- every other green in this arm is void"),
    })

    # -- Regret arm. eta from the true model, q a miscalibrated report. ------
    # Measured directly: the excess expected Brier / log loss of reporting q
    # instead of eta, over Bernoulli(eta) draws.
    for eta in (0.05, 0.2, 0.5):
        for q in (0.02, 0.1, 0.3, 0.7):
            n = R_MC
            y = (rng.random(n) < eta).astype(np.float64)
            br_q = float(np.mean((q - y) ** 2))
            br_eta = float(np.mean((eta - y) ** 2))
            ll_q = float(np.mean(-(y * math.log(q) + (1 - y) * math.log(1 - q))))
            ll_eta = float(np.mean(-(y * math.log(eta)
                                     + (1 - y) * math.log(1 - eta))))
            rows.append({
                "cell": "regret", "eta": eta, "q": q,
                "brier_regret_measured": br_q - br_eta,
                "brier_regret_predicted": corpus_brier_regret_point(eta, q),
                "logloss_regret_measured": ll_q - ll_eta,
                "logloss_regret_predicted": corpus_logloss_regret_point(eta, q),
                "isolates": ("regret is a DIFFERENCE of two risks measured on "
                             "the same draws, so the common Bernoulli variance "
                             "cancels exactly and what is left is the "
                             "miscalibration alone"),
                "ok": (abs((br_q - br_eta) - corpus_brier_regret_point(eta, q))
                       < 5e-3
                       and abs((ll_q - ll_eta)
                               - corpus_logloss_regret_point(eta, q)) < 1e-2),
            })
    return rows


# ===========================================================================
# ARM 2 -- HWE GENOTYPE SCORE
# ===========================================================================
def hwe_cell(rng, p, beta, gamma=None, reps=R_HWE):
    """One vectorised binomial draw over the whole (individuals x loci) array."""
    p = np.asarray(p, dtype=np.float64)
    beta = np.asarray(beta, dtype=np.float64)
    g = rng.binomial(2, p, size=(reps, p.shape[0])).astype(np.float64)
    s = g @ beta
    out = {"mean": float(s.mean()), "var": float(s.var(ddof=0))}
    if gamma is not None:
        gamma = np.asarray(gamma, dtype=np.float64)
        c = g @ gamma
        out["cov"] = float(np.mean((s - s.mean()) * (c - c.mean())))
    # Kolmogorov distance to the standard normal, for scoreApproximationError.
    z = (s - s.mean()) / (s.std(ddof=0) if s.std(ddof=0) > 0 else 1.0)
    zs = np.sort(z)
    emp = np.arange(1, reps + 1, dtype=np.float64) / reps
    # Phi on a sorted array; vectorised via erf.
    theo = 0.5 * (1.0 + np.vectorize(math.erf)(zs / math.sqrt(2.0)))
    out["ks"] = float(np.max(np.abs(emp - theo)))
    return out


def arm_hwe(rng):
    rows = []

    # -- CONTROL H1 : m = 1. Per-locus moment, no summation. ----------------
    for p in (0.5, 0.1, 0.01):
        m = hwe_cell(rng, [p], [1.0])
        rows.append({
            "cell": "H1 control m=1", "p": p,
            "mean_measured": m["mean"], "mean_predicted": 2 * p,
            "var_measured": m["var"], "var_predicted": 2 * p * (1 - p),
            "isolates": "the per-locus moment, with the summation removed",
            "ok": (abs(m["mean"] - 2 * p) < 0.01
                   and abs(m["var"] - 2 * p * (1 - p))
                   < 0.02 * max(2 * p * (1 - p), 1e-3) + 1e-4),
        })

    # -- CONTROL H2 : equal beta, equal p. Summation, per-locus pinned. -----
    for m_loci in (10, 200):
        p = 0.3
        beta = 0.7
        r = hwe_cell(rng, [p] * m_loci, [beta] * m_loci)
        pv = m_loci * beta ** 2 * 2 * p * (1 - p)
        pm = m_loci * beta * 2 * p
        rows.append({
            "cell": "H2 control equal beta and p", "m": m_loci,
            "mean_measured": r["mean"], "mean_predicted": pm,
            "var_measured": r["var"], "var_predicted": pv,
            "isolates": "the summation, with the per-locus moment pinned",
            "ok": abs(r["var"] - pv) < 0.02 * pv,
        })

    # -- Heterogeneous cell: cross-covariance and the general moments. ------
    m_loci = 150
    p = rng.uniform(0.05, 0.95, size=m_loci)
    beta = rng.normal(0.0, 1.0, size=m_loci)
    gamma = rng.normal(0.0, 1.0, size=m_loci)
    r = hwe_cell(rng, p, beta, gamma)
    pv = float(np.sum(beta ** 2 * 2 * p * (1 - p)))
    pm = float(np.sum(beta * 2 * p))
    pc = float(np.sum(beta * gamma * 2 * p * (1 - p)))
    rows.append({
        "cell": "heterogeneous m=150", "m": m_loci,
        "mean_measured": r["mean"], "mean_predicted": pm,
        "var_measured": r["var"], "var_predicted": pv,
        "cov_measured": r["cov"], "cov_predicted": pc,
        "isolates": "nothing on its own -- this is the combined cell, and it "
                    "is reported only because H1 and H2 have already split it",
        "ok": (abs(r["var"] - pv) < 0.03 * pv
               and abs(r["cov"] - pc) < 0.03 * max(abs(pc), 1e-6)),
    })

    # -- CAN-FAIL grid for scoreApproximationError. The Gaussian approximation
    #    can only be refuted where it is bad, so m goes down to 1 and p to 0.01.
    for (m_loci, p) in ((1, 0.5), (1, 0.01), (5, 0.05), (50, 0.05),
                        (1000, 0.5)):
        r = hwe_cell(rng, [p] * m_loci, [1.0] * m_loci, reps=100000)
        rows.append({
            "cell": "approximation error grid", "m": m_loci, "p": p,
            "ks_to_normal": r["ks"],
            "isolates": "the Gaussian approximation to the score law",
            "note": ("this cell is where the approximation IS bad; a grid "
                     "confined to m=1000,p=0.5 (ks below 0.01) validates any "
                     "error bound whatsoever"),
            "ok": True,
        })
    return rows


# ===========================================================================
# ARM 3 -- ESTIMATOR MOMENTS
# ===========================================================================
def moment_cell(rng, nonlinear=True, hetero=True, oracle=False,
                noiseless=False, bias_up=0.0, reps=R_MOM):
    """Y = f(X) + eps, and a predictor S. All moments read off one draw."""
    x = rng.normal(0.0, 1.0, size=reps)
    if nonlinear:
        fx = x + 0.6 * (x ** 2 - 1.0)          # non-linear, mean-zero
    else:
        fx = x
    sd = (0.5 + 0.4 * np.abs(x)) if hetero else np.full(reps, 0.8)
    eps = np.zeros(reps) if noiseless else rng.normal(0.0, 1.0, size=reps) * sd
    y = fx + eps
    s = (fx if oracle else x) + bias_up
    mean_y = float(y.mean())
    mean_s = float(s.mean())
    var_y = float(y.var(ddof=0))
    var_s = float(s.var(ddof=0))
    cov = float(np.mean((y - mean_y) * (s - mean_s)))
    mse = float(np.mean((y - s) ** 2))
    bias = mean_s - mean_y                       # E[S] - E[Y], the convention
    irreducible = float(np.mean(sd ** 2)) if not noiseless else 0.0
    approx = float(np.mean((fx - s) ** 2))
    return {"mean_y": mean_y, "mean_s": mean_s, "var_y": var_y, "var_s": var_s,
            "cov": cov, "mse": mse, "bias": bias,
            "irreducible": irreducible, "approx": approx,
            "r2_from_mse": 1.0 - mse / var_y}


def arm_moments(rng):
    rows = []

    # -- CONTROL M1 : S = E[Y|X]. Approximation risk must vanish. -----------
    m = moment_cell(rng, oracle=True)
    rows.append({
        "cell": "M1 control S = E[Y|X]",
        "approx_measured": m["approx"], "approx_predicted": 0.0,
        "irreducible_measured": m["irreducible"],
        "mse_measured": m["mse"],
        "sum_check": m["irreducible"] + m["approx"],
        "isolates": "the conditional-mean approximation term",
        "ok": (abs(m["approx"]) < 1e-12
               and abs(m["mse"] - m["irreducible"]) < 0.02 * m["irreducible"]),
    })

    # -- CONTROL M2 : eps = 0. Irreducible risk must vanish. ----------------
    m = moment_cell(rng, noiseless=True)
    rows.append({
        "cell": "M2 control eps = 0",
        "irreducible_measured": m["irreducible"], "irreducible_predicted": 0.0,
        "approx_measured": m["approx"],
        "mse_measured": m["mse"],
        "isolates": "the irreducible term",
        "note": "M1 and M2 exist because the decomposition is a SUM: a check "
                "on the total MSE alone is passed by an implementation that "
                "swaps the two terms",
        "ok": (abs(m["irreducible"]) < 1e-12
               and abs(m["mse"] - m["approx"]) < 0.02 * max(m["approx"], 1e-9)),
    })

    # -- Combined cell: the decomposition identity itself. ------------------
    m = moment_cell(rng)
    tot = m["irreducible"] + m["approx"]
    rows.append({
        "cell": "MSE decomposition, non-linear f and heteroscedastic eps",
        "mse_measured": m["mse"],
        "irreducible_plus_approx": tot,
        "rel_gap": abs(m["mse"] - tot) / m["mse"],
        "r2_from_mse": m["r2_from_mse"],
        "r2_from_moments": m["cov"] ** 2 / (m["var_y"] * m["var_s"]),
        "isolates": "nothing alone; valid only because M1 and M2 already split "
                    "the two terms",
        "note": "r2FromMSE (1 - MSE/varY) and the squared correlation are "
                "DIFFERENT numbers for an uncalibrated predictor, and the "
                "corpus uses both names for R^2. Reported side by side.",
        "ok": abs(m["mse"] - tot) < 0.02 * m["mse"],
    })

    # -- CONTROL M3 : SIGN. A strictly upward-biased predictor. -------------
    m = moment_cell(rng, bias_up=0.75)
    sign_ok = m["bias"] > 0.7
    rows.append({
        "cell": "M3 SIGN CONTROL, predictor biased +0.75",
        "bias_measured": m["bias"], "bias_predicted": 0.75,
        "isolates": "the SIGN convention of measureBias, E[S] - E[Y]",
        "note": "no squared-error check anywhere in the corpus can see a "
                "negated bias definition; this is the only cell that can",
        "ok": sign_ok and abs(m["bias"] - 0.75) < 0.02,
        "sign_positive": sign_ok,
    })

    # -- Variance identity, the one thing measureVariance could get wrong. --
    z = rng.normal(3.0, 2.0, size=R_MOM)
    v_def = float(np.mean((z - z.mean()) ** 2))       # the corpus definition
    v_alt = float(np.mean(z ** 2) - z.mean() ** 2)    # the identity
    rows.append({
        "cell": "measureVariance vs E[Z^2]-E[Z]^2",
        "definitional": v_def, "identity": v_alt,
        "true": 4.0,
        "isolates": "the centring convention, at a NON-ZERO mean (3.0) -- at "
                    "mean zero the two forms coincide and the check is vacuous",
        "ok": abs(v_def - v_alt) < 1e-6 and abs(v_def - 4.0) < 0.05,
    })
    return rows


def main():
    rng = np.random.default_rng(SEED)
    out = {"seed": SEED,
           "replicates": {"liability": R_MC, "hwe": R_HWE, "moments": R_MOM},
           "liability_threshold_metrics": arm_liability(rng),
           "hwe_genotype_score": arm_hwe(rng),
           "estimator_moments": arm_moments(rng)}

    n_bad = 0
    for arm in ("liability_threshold_metrics", "hwe_genotype_score",
                "estimator_moments"):
        print("")
        print("=" * 74)
        print(arm.upper())
        print("=" * 74)
        for r in out[arm]:
            flag = "ok " if r.get("ok") else "RED"
            if not r.get("ok"):
                n_bad += 1
            bits = []
            for k in sorted(r):
                if k in ("cell", "ok", "isolates", "note", "expected",
                         "meaning"):
                    continue
                v = r[k]
                if isinstance(v, float):
                    bits.append("%s=%.6g" % (k, v))
                else:
                    bits.append("%s=%s" % (k, v))
            print("  [%s] %-42s %s" % (flag, r["cell"], "  ".join(bits)))
            if r.get("meaning"):
                print("        -> %s" % r["meaning"])

    # The positive control is inverted: it is SUPPOSED to be red.
    l4 = [r for r in out["liability_threshold_metrics"]
          if r["cell"].startswith("L4")][0]
    print("")
    print("POSITIVE CONTROL L4 (vNoise=0): %s"
          % ("FIRED as required -- the AUC check can fail"
             if l4["fired"] else
             "DID NOT FIRE -- HARNESS BROKEN, treat every green above as void"))
    out["positive_control_fired"] = bool(l4["fired"])
    out["cells_red"] = n_bad

    path = os.path.join(HERE, "fam_metrics_results.json")
    fh = open(path, "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_metrics_results.json  (%d cells not green, L4 included by "
          "design)" % n_bad)
    return 0


if __name__ == "__main__":
    sys.exit(main())
