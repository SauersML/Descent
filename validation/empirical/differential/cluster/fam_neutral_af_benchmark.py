#!/usr/bin/env python3
"""Family simulator: NEUTRAL ALLELE-FREQUENCY / SHARED-LD BENCHMARK.

The corpus's headline transport law. Target predictive accuracy is obtained
from source accuracy by a single scalar built from F_ST and shared LD:

    covarianceRetention = freqCorrFromFst(fst) * ldOverlapFromSharedLD(shared_ld)
                        = (1 - fst) * shared_ld

WHY THE JOINT SWEEP CANNOT FAIL, WHICH IS WHY THIS FILE IS SHAPED AS IT IS
  The retention is a PRODUCT of a frequency term and an LD term, and the corpus
  defines each by a separate one-line identity. A law wrong by a factor k in one
  term and 1/k in the other reproduces the product EXACTLY at every point of a
  joint sweep -- not approximately, exactly. A joint sweep is therefore not a
  weak test of this family, it is a test that CANNOT FAIL, and reporting
  agreement from one would be the textbook compensating-error result.

  Only two one-at-a-time sweeps can falsify it:

    A1  F_ST swept with SHARED LD PINNED  -- isolates freqCorrFromFst
    A2  SHARED LD swept with F_ST PINNED AT 0 -- isolates ldOverlapFromSharedLD

  C4 does not merely assert this. It CONSTRUCTS the compensating pair (k, 1/k),
  runs it through the joint arm and both split arms, and REQUIRES the joint arm
  to be fooled while both split arms reject. Claiming the joint sweep is
  insufficient without demonstrating it would be asking to be believed.

THE FINDING THIS FILE IS BUILT TO SETTLE: WHICH NORMALISATION IS shared_ld?
  `ldOverlapFromSharedLD` is the identity function, so the corpus never says
  what shared LD is measured in. There are two readings a reader can take, and
  THEY DIFFER BY EXACTLY THE FACTOR THE LAW IS MULTIPLYING BY:

    SLD_D   retention of the absolute LD coefficient D.
    SLD_R   retention of the correlation r = D / sqrt(p(1-p) q(1-q)).

  Under PURE DRIFT with no recombination, E[D_t] = D_0 (1 - 1/(2N_e))^t, so D
  decays at the same rate heterozygosity does. That means SLD_D already CONTAINS
  the drift factor, while SLD_R stays at 1 because numerator and denominator
  fall together. So on the pure-drift arm:

    if shared_ld means SLD_R:  prediction (1-F) * 1     = (1-F)   -- correct
    if shared_ld means SLD_D:  prediction (1-F) * (1-F) = (1-F)^2 -- DRIFT IS
                                                          COUNTED TWICE

  At F_ST = 0.3 those differ by 30%. This is not a stylistic ambiguity: one
  reading makes the headline law right and the other makes it wrong by a factor
  of (1-F_ST), and the corpus's identity function commits to neither. A1
  measures BOTH readings at every cell and C3 reports which one makes the law
  true. Same discipline as labelling the F_ST reading in
  fam_pgs_transport_drift.py, and for the same reason: an unlabelled convention
  that two consumers read differently is a defect with no error message.

BOTH FACTORS ARE DERIVED, NEVER RECEIVED
  Standing practice from the two previous families. The quantity the corpus and
  a reference could disagree about must be an OUTPUT of a process, not an input
  the simulator hands to the formula and reads back.

    F_ST       drift for t generations at N_e; measured off realised
               frequencies as a heterozygosity retention, ratio of sums.
    SHARED LD  recombination for T_LD generations at rate c; measured as the
               realised retention of D and of r. NOT set to (1-c)^t, and not
               read back from a parameter.

  THE TWO ARE MOVED BY PHYSICALLY SEPARATE KNOBS, which is what makes the split
  sweeps real rather than two parameterisations of one axis:
    A1 sets the recombination rate to EXACTLY ZERO -- only drift acts.
    A2 sets N_e very large but FINITE -- recombination dominates and F_ST stays
       at ~1e-4. Finite on purpose: an infinite population makes that arm
       deterministic, every replicate identical and the replicate scatter
       exactly zero, at which point a threshold in standard errors divides by
       nothing and reports the run's precision instead of the law's
       correctness. See NE_FROZEN and `agrees`.

CAN-FAIL
  F_ST must reach 0.15 and beyond, the human continental range. At F_ST = 0.01
  the predicted retention is 0.99 and (1-F), (1-F)^2 and exp(-F) agree to 1e-4,
  so a low-F_ST grid validates every candidate and decides nothing -- including
  the SLD_D versus SLD_R question above, which is invisible below F_ST ~ 0.05.
  The shared-LD axis must fall to ~0.6 or below for the same reason.

WHAT IS COVERED

  freqCorrFromFst                    A1, C3, C4
  ldOverlapFromSharedLD              A2, C3, C4
  covarianceRetention                C3, C4
  covarianceDivergenceFromRetention  C3
  neutralAFSharedLDBenchmarkRatio    C5
  neutralAFBenchmarkMetricProfile    C6
  targetBrierFromNeutralAFBenchmark  C6

  NOT MEASURED HERE, BY DESIGN AND NOT BY OMISSION:
  targetR2FromNeutralAFBenchmark. Its whole body is

      targetR2FromNeutralAFBenchmark V_A V_E fstTarget = presentDayR2 V_A V_E fstTarget

  so it IS presentDayR2 under another name, and presentDayR2 is measured by
  fam_pgs_transport_drift.py check C5. Measuring it again here would be ONE
  MEASUREMENT COUNTED TWICE and the agreement between the two families would
  read as corroboration while being nothing of the kind. This file CITES that
  result. C6 checks only that the FORWARDING still holds, which is a different
  claim from the quantity's correctness.

  NOT FOUND IN THE CORPUS: `targetGaussianAUCFromNeutralAFBenchmark` and
  `targetExactGaussianAUCFromNeutralAFBenchmark`, both listed for this family in
  families.py, have ZERO occurrences anywhere under proofs/ at the revision
  below. No replacement is guessed. THIS FAMILY IS THEREFORE NOT FULLY COVERED
  and this file does not claim it is.

THE AUC IN THIS FAMILY, NAMED
  neutralAFBenchmarkMetricProfile carries an `auc` field, so this family DOES
  touch an AUC and the estimand must be named:

      neutralAFBenchmarkMetricProfile = profileFromSignalVariance π V_E (...)
      profileFromSignalVariance.auc   = equalVarianceGaussianAUCFromSignalVariance

  It is a claim about equalVarianceGaussianAUCFromSignalVariance and NOT about
  liabilityThresholdAUCFromExplainedR2, which is a different estimand carrying a
  prevalence argument. Conflating the two has already cost this project an hour
  and produced a false alarm, so every AUC number here is labelled.

  A STRUCTURAL OBSERVATION C6 MEASURES: the profile TAKES a prevalence π, uses
  it in `brier`, and DOES NOT use it in `auc`. So profiles at π = 0.5 and
  π = 0.02 must return the SAME auc and DIFFERENT brier. DGP.lean states in its
  own text that AUC is not determined by second moments and that it offers this
  chart "as a numerical function only", with no theorem identifying it with a
  process AUC. fam_metrics measured a liability-threshold AUC moving from 0.833
  at π = 0.5 to 0.925 at π = 0.02. So if the deployed quantity does depend on
  prevalence, this field cannot be it at more than one prevalence. That is a
  SCOPE RESULT about where the chart may be used, not a refuted theorem, and C6
  records it as such.

TRANSCRIPTION PROVENANCE
  Bodies quoted beside their transcriptions with file and declaration name and
  NO LINE NUMBER. Transcribed against revision fefbb573, re-read from the
  working tree immediately before commit. PortabilityDrift.lean and DGP.lean are
  under active edit by other sessions; re-read before trusting this later.

RUNNING IT -- NOT ON A LOGIN NODE
  numpy only, single-threaded, no msprime and no build.

      srun --time=45 --mem=8G --cpus-per-task=1 \
        env OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
        python3 validation/empirical/differential/cluster/fam_neutral_af_benchmark.py \
            --profile full \
            --output /projects/standard/hsiehph/sauer354/fam_neutral_af_<stamp>.json \
        > /projects/standard/hsiehph/sauer354/fam_neutral_af_<stamp>.out 2>&1

  CAPTURE BOTH STREAMS: a nonzero exit is a MEASUREMENT OUTCOME, not a crash.
"""

import argparse
import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

import simprov  # noqa: E402

SEED = 20260803

NE = 500                    # diploids, drift arm
# "No drift" for the LD-only arm. DELIBERATELY FINITE. An infinite population
# makes the recombination arm DETERMINISTIC, every replicate identical, and the
# replicate scatter exactly zero -- at which point a threshold in standard
# errors divides by nothing and reports the run's precision rather than the
# law's correctness. That is the same defect fam_coalescent recorded when its
# t=0 control was judged against a fixed constant instead of its own noise. At
# 2e5 diploids, 60 generations of drift give F_ST ~ 1.5e-4, which is pinned at
# zero for every purpose here, while leaving genuine replicate variation.
NE_FROZEN = 200000
T_GRID = (0, 25, 100, 250, 500)     # drift generations; F_ST is measured
C_GRID = (0.0, 0.002, 0.006, 0.02)  # recombination rate, LD arm
T_LD = 60                   # generations of recombination in the LD arm
N_REP = 200                 # replicate populations (the error bar)
M_PAIR = 300                # tag/causal locus pairs
P0 = 0.3                    # ancestral frequency of both loci in a pair
D0_FRAC = 0.9               # initial tag-causal D as a fraction of D_max
IND_REP = 6                 # replicates in the HWE control only
N_IND = 4000                # individuals in the HWE control only
PI_GRID = (0.5, 0.1, 0.02)
V_E = 1.0
CORRUPTION_K = 1.6          # C4 compensating pair is (k, 1/k)

TUNABLES = {
    "NE": "diploids per population in the drift arm",
    "NE_FROZEN": "population size standing in for no drift in the LD arm",
    "T_GRID": "drift generations; F_ST is measured, never set",
    "C_GRID": "recombination rates in the LD arm",
    "T_LD": "generations of recombination in the LD arm",
    "N_REP": "replicate populations (the error bar)",
    "M_PAIR": "tag/causal locus pairs",
    "P0": "ancestral allele frequency of each locus",
    "D0_FRAC": "initial tag-causal D as a fraction of D_max",
    "IND_REP": "replicates in the HWE control",
    "N_IND": "individuals in the HWE control",
    "PI_GRID": "prevalences for the metric-profile arm",
    "V_E": "residual variance",
    "CORRUPTION_K": "C4 compensating pair is (k, 1/k)",
}


def configure_profile(profile):
    """Sampling widths and grid density only. No estimand differs."""
    global N_REP, M_PAIR, T_GRID, C_GRID, IND_REP
    if profile == "full":
        return
    if profile == "deep":
        N_REP, M_PAIR, IND_REP = 600, 600, 12
        T_GRID = (0, 10, 25, 50, 100, 175, 250, 375, 500)
        C_GRID = (0.0, 0.001, 0.002, 0.004, 0.006, 0.012, 0.02, 0.04)
        return
    if profile != "quick":
        raise ValueError("profile must be 'quick', 'full' or 'deep'")
    N_REP, M_PAIR, IND_REP = 40, 60, 2
    T_GRID = (0, 100, 500)
    C_GRID = (0.0, 0.006, 0.02)


def apply_overrides(settings):
    applied = {}
    for s in settings:
        if "=" not in s:
            raise SystemExit("--set expects NAME=VALUE, got %r" % s)
        name, _, raw = s.partition("=")
        name = name.strip().upper()
        if name not in TUNABLES:
            raise SystemExit("--set: unknown knob %r; see --help" % name)
        parts = [p for p in raw.replace(",", " ").split() if p]
        vals = [float(p) if ("." in p or "e" in p.lower()) else int(p)
                for p in parts]
        value = vals[0] if len(vals) == 1 and "," not in raw else tuple(vals)
        globals()[name] = value
        applied[name] = value
    return applied


def resolved_config():
    return {name: (list(globals()[name])
                   if isinstance(globals()[name], tuple)
                   else globals()[name])
            for name in TUNABLES}


# ===========================================================================
# THE CORPUS, TRANSCRIBED. Nothing outside this section predicts anything.
# ===========================================================================

def corpus_freqCorrFromFst(fst):
    """Descent/Portability/PortabilityDrift.lean, decl `freqCorrFromFst`

        noncomputable def freqCorrFromFst (fst : ℝ) : ℝ := 1 - fst
    """
    return 1.0 - fst


def corpus_ldOverlapFromSharedLD(shared_ld):
    """Descent/Portability/PortabilityDrift.lean, decl `ldOverlapFromSharedLD`

        noncomputable def ldOverlapFromSharedLD (shared_ld : ℝ) : ℝ := shared_ld

    The identity function. Transcribed rather than inlined, because the claim
    under test is that THIS is the map from shared LD to covariance overlap,
    and inlining an identity is how a claim stops being visible as a claim.
    It is also where the unstated normalisation lives: nothing here says
    whether shared_ld is measured on D or on r.
    """
    return shared_ld


def corpus_covarianceRetention(freq_corr, ld_overlap):
    """Descent/Portability/PortabilityDrift.lean, decl `covarianceRetention`

        noncomputable def covarianceRetention (freq_corr ld_overlap : ℝ) : ℝ :=
          freq_corr * ld_overlap
    """
    return freq_corr * ld_overlap


def corpus_covarianceDivergenceFromRetention(fst, shared_ld):
    """Descent/Portability/PortabilityDrift.lean, decl `covarianceDivergenceFromRetention`

        noncomputable def covarianceDivergenceFromRetention (fst shared_ld : ℝ) : ℝ :=
          1 - covarianceRetention (freqCorrFromFst fst) (ldOverlapFromSharedLD shared_ld)
    """
    return 1.0 - corpus_covarianceRetention(
        corpus_freqCorrFromFst(fst), corpus_ldOverlapFromSharedLD(shared_ld))


def corpus_neutralAFSharedLDBenchmarkRatio(fstS, fstT, sldS, sldT):
    """Descent/Portability/PortabilityDrift.lean, decl `neutralAFSharedLDBenchmarkRatio`

        noncomputable def neutralAFSharedLDBenchmarkRatio
            (fstSource fstTarget shared_ld_source shared_ld_target : ℝ) : ℝ :=
          ((1 - fstTarget) * shared_ld_target) / ((1 - fstSource) * shared_ld_source)
    """
    return ((1.0 - fstT) * sldT) / ((1.0 - fstS) * sldS)


def corpus_r2FromSignalVariance(vSignal, vNoise):
    """Descent/PopGen/DGP.lean, decl `r2FromSignalVariance`

        noncomputable def r2FromSignalVariance (vSignal vNoise : ℝ) : ℝ :=
          vSignal / (vSignal + vNoise)
    """
    return vSignal / (vSignal + vNoise)


def corpus_calibratedBrier(pi, r2):
    """Descent/PopGen/DGP.lean, decl `calibratedBrier`

        def calibratedBrier (π r2 : ℝ) : ℝ := π * (1 - π) * (1 - r2)
    """
    return pi * (1.0 - pi) * (1.0 - r2)


def corpus_calibratedBrierFromVariances(pi, vSignal, vResidual):
    """Descent/PopGen/DGP.lean, decl `calibratedBrierFromVariances`

        noncomputable def calibratedBrierFromVariances (π vSignal vResidual : ℝ) : ℝ :=
          π * (1 - π) * (1 - vSignal / (vSignal + vResidual))
    """
    return pi * (1.0 - pi) * (1.0 - vSignal / (vSignal + vResidual))


def phi(x):
    """Standard normal CDF; corresponds to the corpus's `Phi`."""
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def corpus_equalVarianceGaussianAUC(vSignal, vNoise):
    """Descent/PopGen/DGP.lean, decl `equalVarianceGaussianAUCFromSignalVariance`

        noncomputable def equalVarianceGaussianAUCFromSignalVariance (vSignal vNoise : ℝ) : ℝ :=
          if vNoise = 0 then if 0 < vSignal then 1 else Phi 0
          else Phi (Real.sqrt (vSignal / (2 * vNoise)))

    THE ZERO-NOISE GUARD IS PART OF THE BODY and is transcribed with it. It was
    not always there: fam_metrics' positive control L4 fired on exactly this
    point, where the unguarded chart returned Phi(0) = 0.5 against a process
    value of 1.0. Transcribing the guarded body is the difference between
    testing the corpus and testing a memory of it.

    ESTIMAND: the equal-variance Gaussian chart. NOT
    liabilityThresholdAUCFromExplainedR2.
    """
    if vNoise == 0:
        return 1.0 if vSignal > 0 else phi(0.0)
    return phi(math.sqrt(vSignal / (2.0 * vNoise)))


def corpus_profileFromSignalVariance(pi, vNoise, vSignal):
    """Descent/PopGen/DGP.lean, decl `profileFromSignalVariance`

        noncomputable def profileFromSignalVariance
            (π vNoise vSignal : ℝ) : Profile where
          r2 := r2FromSignalVariance vSignal vNoise
          auc := equalVarianceGaussianAUCFromSignalVariance vSignal vNoise
          brier := calibratedBrierFromVariances π vSignal vNoise

    NOTE, and C6 measures it: π enters `brier` and does NOT enter `auc`.
    """
    return {"r2": corpus_r2FromSignalVariance(vSignal, vNoise),
            "auc": corpus_equalVarianceGaussianAUC(vSignal, vNoise),
            "brier": corpus_calibratedBrierFromVariances(pi, vSignal, vNoise)}


def corpus_pgsVarianceFromHet(beta_sq_sum, het):
    """Descent/Portability/PortabilityDrift.lean, decl `pgsVarianceFromHet`

        noncomputable def pgsVarianceFromHet (β_sq_sum het : ℝ) : ℝ :=
          β_sq_sum * het
    """
    return beta_sq_sum * het


def corpus_presentDayPGSVariance(V_A, fst):
    """Descent/Portability/PortabilityDrift.lean, decl `presentDayPGSVariance`

        noncomputable def presentDayPGSVariance (V_A fst : ℝ) : ℝ :=
          pgsVarianceFromHet V_A (1 - fst)
    """
    return corpus_pgsVarianceFromHet(V_A, 1.0 - fst)


def corpus_neutralAFBenchmarkMetricProfile(pi, V_A, V_E, fstTarget):
    """Descent/Portability/PortabilityDrift.lean, decl `neutralAFBenchmarkMetricProfile`

        noncomputable def neutralAFBenchmarkMetricProfile
            (π V_A V_E fstTarget : ℝ) : TransportedMetrics.Profile :=
          TransportedMetrics.profileFromSignalVariance π V_E (presentDayPGSVariance V_A fstTarget)
    """
    return corpus_profileFromSignalVariance(
        pi, V_E, corpus_presentDayPGSVariance(V_A, fstTarget))


def corpus_targetR2FromNeutralAFBenchmark(V_A, V_E, fstTarget):
    """Descent/Portability/PortabilityDrift.lean, decl `targetR2FromNeutralAFBenchmark`

        noncomputable def targetR2FromNeutralAFBenchmark
            (V_A V_E fstTarget : ℝ) : ℝ :=
          presentDayR2 V_A V_E fstTarget

    Transcribed as the FORWARD it is, so C6 can check the forwarding still
    holds. The QUANTITY is measured by fam_pgs_transport_drift.py C5 and is NOT
    re-measured here.
    """
    return corpus_r2FromSignalVariance(
        corpus_presentDayPGSVariance(V_A, fstTarget), V_E)


def corpus_targetExactCalibratedBrierRisk(pi, V_A, V_E, fstTarget):
    """Descent/Portability/PortabilityDrift.lean, decl `targetExactCalibratedBrierRisk`

        noncomputable def targetExactCalibratedBrierRisk
            (π V_A V_E fstTarget : ℝ) : ℝ :=
          TransportedMetrics.calibratedBrier π
            (targetR2FromNeutralAFBenchmark V_A V_E fstTarget)
    """
    return corpus_calibratedBrier(
        pi, corpus_targetR2FromNeutralAFBenchmark(V_A, V_E, fstTarget))


def corpus_targetBrierFromNeutralAFBenchmark(pi, V_A, V_E, fstTarget):
    """Descent/Portability/PortabilityDrift.lean, decl `targetBrierFromNeutralAFBenchmark`

        noncomputable def targetBrierFromNeutralAFBenchmark
            (π V_A V_E fstTarget : ℝ) : ℝ :=
          targetExactCalibratedBrierRisk π V_A V_E fstTarget
    """
    return corpus_targetExactCalibratedBrierRisk(pi, V_A, V_E, fstTarget)


# ===========================================================================
# THE PROCESS: two-locus haplotypes, a CAUSAL locus and its TAG.
#
# Haplotype order is [00, 01, 10, 11] with bit 1 = causal allele, bit 0 = tag.
# Per generation: recombination decays D at rate c leaving single-locus
# frequencies alone; drift resamples 2 N_e haplotypes.
# ===========================================================================

def multinomial4_vec(n, p, rng):
    """Vectorised 4-category multinomial by the conditional-binomial chain.

    WHY THIS IS THE SAME DRAW, which the vectorisation rule requires me to be
    able to state: a Multinomial(n, p0..p3) is EXACTLY the chain
        x0 ~ Bin(n, p0)
        x1 ~ Bin(n - x0, p1/(1-p0))
        x2 ~ Bin(n - x0 - x1, p2/(1-p0-p1))
        x3 = n - x0 - x1 - x2
    That is an identity, not an approximation, so each row of the array is drawn
    from its own multinomial independently and nothing is shared between rows.
    numpy's own multinomial does not broadcast over a 2-D pvals array, and the
    loop it would force is 3e7 calls here, which is the difference between a
    minute and an afternoon.
    """
    p = np.clip(p, 0.0, 1.0)
    p = p / p.sum(axis=-1, keepdims=True)
    out = np.empty(p.shape, dtype=np.int64)
    remaining = np.full(p.shape[:-1], int(n), dtype=np.int64)
    left = np.ones(p.shape[:-1])
    for k in range(3):
        frac = np.where(left > 1e-15, p[..., k] / np.maximum(left, 1e-15), 0.0)
        frac = np.clip(frac, 0.0, 1.0)
        draw = rng.binomial(remaining, frac)
        out[..., k] = draw
        remaining = remaining - draw
        left = left - p[..., k]
    out[..., 3] = remaining
    return out


def init_haplotypes(m, p_causal, p_tag, d_frac):
    """Haplotype frequencies at D equal to d_frac of its maximum."""
    d_max = min(p_causal * (1 - p_tag), p_tag * (1 - p_causal))
    d = d_frac * d_max
    h = np.array([(1 - p_causal) * (1 - p_tag) + d,
                  (1 - p_causal) * p_tag - d,
                  p_causal * (1 - p_tag) - d,
                  p_causal * p_tag + d], dtype=float)
    return np.broadcast_to(h, (m, 4)).copy()


def evolve(h, t, c, ne, rng):
    """t generations of recombination at rate c and drift at size ne.

    h has shape (..., m, 4); every row is resampled from its own multinomial.
    """
    h = h.copy()
    two_ne = int(2 * ne)
    for _ in range(int(t)):
        if c > 0:
            d = h[..., 3] * h[..., 0] - h[..., 2] * h[..., 1]
            pc = h[..., 2] + h[..., 3]
            pt = h[..., 1] + h[..., 3]
            dn = (1.0 - c) * d
            h = np.stack([(1 - pc) * (1 - pt) + dn,
                          (1 - pc) * pt - dn,
                          pc * (1 - pt) - dn,
                          pc * pt + dn], axis=-1)
        if ne < 10 ** 8:
            h = multinomial4_vec(two_ne, h, rng) / float(two_ne)
        h = np.clip(h, 0.0, 1.0)
        s = h.sum(axis=-1, keepdims=True)
        h = h / np.where(s > 0, s, 1.0)
    return h


def hap_stats(h):
    """Per-locus causal frequency, tag frequency, D, and r."""
    pc = h[..., 2] + h[..., 3]
    pt = h[..., 1] + h[..., 3]
    d = h[..., 3] * h[..., 0] - h[..., 2] * h[..., 1]
    denom = np.sqrt(np.maximum(pc * (1 - pc) * pt * (1 - pt), 0.0))
    r = np.where(denom > 1e-15, d / np.maximum(denom, 1e-15), 0.0)
    return pc, pt, d, r


def fst_het_ratio_of_sums(pc_t, p0):
    """Heterozygosity-retention F_ST, ratio of sums over loci.

    Same reading and same ratio-of-sums construction as
    fam_pgs_transport_drift.py, deliberately: two families that both report a
    number called F_ST and compute it differently cannot be compared, and
    comparing them is the entire point of a shared benchmark.
    """
    h_t = float(np.mean(np.sum(2.0 * pc_t * (1.0 - pc_t), axis=-1)))
    m = pc_t.shape[-1]
    h_0 = float(m * 2.0 * p0 * (1.0 - p0))
    return 1.0 - h_t / h_0 if h_0 > 0 else float("nan")


def retention_of(x_t, x_0):
    """Ratio of sums over loci, averaged over replicates.

    Ratio of sums rather than mean of per-locus ratios, for the biological
    reason rather than a numerical one: a locus whose D has collapsed carries
    almost no covariance, and a mean of ratios would let it dominate a quantity
    it barely affects.
    """
    num = float(np.mean(np.sum(x_t, axis=-1)))
    den = float(np.sum(x_0))
    return num / den if den != 0 else float("nan")


REL_FLOOR = 0.01


def agrees(meas, se, pred):
    """Agreement in standard errors, WITH A RELATIVE FLOOR.

    Returns (ok, deviation_in_sems).

    A sems threshold alone is wrong on an arm whose replicate scatter is tiny:
    it then measures the run's precision rather than the law's correctness, and
    a 0.2% discrepancy on a very tight arm reads as hundreds of sigma. So an
    agreement inside REL_FLOOR relative error counts as agreement regardless of
    the sems.

    THE FLOOR CANNOT NEUTER THE POSITIVE CONTROL, which is the thing to check
    before adding a tolerance anywhere: C4's corruption is a factor k = 1.6 on
    one arm and 1/k = 0.625 on the other, i.e. 60% and 37.5% errors, which are
    more than an order of magnitude above this floor. A tolerance that could
    swallow the control would make every agreement in the file meaningless.
    """
    dev = abs(meas - pred) / max(se, 1e-12)
    rel = abs(meas - pred) / abs(pred) if pred else float("inf")
    return bool(dev <= 4.0 or rel <= REL_FLOOR), dev


def retention_records(x_t, x_0):
    """One retention per replicate, so the error bar is replicate scatter."""
    den = float(np.sum(x_0))
    if den == 0:
        return []
    return [float(v / den) for v in np.sum(x_t, axis=-1)]


def hwe_covariance_control(h_row, rng):
    """CONTROL: genotype covariance in formed individuals must equal 2 D.

    The predictive covariance is computed from the haplotype state everywhere
    else in this file, which assumes individuals are two independent haplotypes.
    That assumption is checked here rather than trusted, on a handful of
    replicates: it is a property of the INSTRUMENT, not of the corpus, so it
    does not need the replicate count the corpus claims need.
    """
    m = h_row.shape[0]
    cum = np.cumsum(h_row, axis=-1)
    u = rng.random((N_IND, 2, m))
    # Clipped at 3: the last cumulative probability is 1 only up to rounding,
    # so a draw just under 1 can otherwise index a fifth category that does not
    # exist.
    idx = np.clip((u[..., None] > cum[None, None, :, :]).sum(axis=-1), 0, 3)
    causal = (idx >= 2).sum(axis=1).astype(float)
    tag = (idx % 2 == 1).sum(axis=1).astype(float)
    meas = np.array([float(np.cov(tag[:, j], causal[:, j])[0, 1])
                     for j in range(m)])
    _, _, d, _ = hap_stats(h_row)
    return float(np.sum(meas)), float(np.sum(2.0 * d))


# ===========================================================================
# ARMS
# ===========================================================================

def run_arm(t, c, ne, rng, label):
    """One cell: evolve, then measure F_ST, both shared-LD readings, and the
    retention of the predictive covariance (which is proportional to sum D)."""
    h0 = init_haplotypes(M_PAIR, P0, P0, D0_FRAC)
    _, _, d0, r0 = hap_stats(h0)
    h = np.broadcast_to(h0, (N_REP, M_PAIR, 4)).copy()
    h = evolve(h, t, c, ne, rng)
    pc, pt, d, r = hap_stats(h)
    recs = retention_records(d, d0)
    return {
        "label": label, "t": t, "c": c, "Ne": ne,
        "F_ST_measured": fst_het_ratio_of_sums(pc, P0),
        "SLD_D_measured": retention_of(d, d0),
        "SLD_R_measured": retention_of(r, r0),
        "covariance_retention_measured": simprov.summarize(recs),
        "records": recs,
        "_h": h,
    }


def arm_fst_only(rng):
    """A1  F_ST SWEPT, recombination EXACTLY ZERO. Isolates freqCorrFromFst."""
    return [run_arm(t, 0.0, NE, rng, "A1") for t in T_GRID]


def arm_ld_only(rng):
    """A2  SHARED LD SWEPT, N_e frozen. Isolates ldOverlapFromSharedLD."""
    return [run_arm(T_LD, c, NE_FROZEN, rng, "A2") for c in C_GRID]


def arm_joint(rng):
    """THE JOINT SWEEP. Present so C4 can demonstrate it cannot fail."""
    return [run_arm(t, c, NE, rng, "JOINT")
            for t, c in zip(T_GRID[1:], C_GRID[1:])]


# ===========================================================================
# CHECKS
# ===========================================================================

def c1(a1, rng, out):
    """C1  A1 ISOLATES, AND THE TWO shared_ld READINGS SEPARATE HERE.

    An isolation arm that does not isolate is worse than no arm, because its
    conclusion gets quoted as if one factor had been held fixed. So the pinning
    is MEASURED, not assumed. With c = 0:

      SLD_R must stay at 1 -- the correlation is preserved under pure drift;
      SLD_D must FALL like (1 - F_ST) -- D decays with heterozygosity.

    Both are reported at every cell. If SLD_R is pinned and SLD_D is not, then
    the corpus's unstated normalisation is decidable, and C3 decides it.

    Also carries the instrument control that genotype covariance in formed
    individuals equals 2 D, so that computing the predictive covariance from the
    haplotype state everywhere else is checked rather than trusted.
    """
    print("")
    print("=" * 78)
    print("C1  A1 ISOLATION -- and SLD_R vs SLD_D separate here")
    print("=" * 78)
    ok = True
    reach = 0.0
    for r in a1:
        reach = max(reach, r["F_ST_measured"])
        pinned_r = abs(r["SLD_R_measured"] - 1.0) <= 0.05
        ok = ok and pinned_r
        print("  t=%-4d F_ST %.4f | SLD_R %.4f %s | SLD_D %.4f | (1-F_ST) %.4f"
              % (r["t"], r["F_ST_measured"], r["SLD_R_measured"],
                 "pinned" if pinned_r else "NOT PINNED", r["SLD_D_measured"],
                 1.0 - r["F_ST_measured"]))
    can_fail = reach >= 0.15
    print("  F_ST reached %.4f; can-fail needs >= 0.15  %s"
          % (reach, "ok" if can_fail else "FAIL"))

    hwe_rows = []
    hwe_ok = True
    for i in range(min(IND_REP, len(a1[-1]["_h"]))):
        meas, exact = hwe_covariance_control(a1[-1]["_h"][i], rng)
        rel = abs(meas - exact) / abs(exact) if exact else float("nan")
        hwe_rows.append({"measured_genotype_cov": meas, "two_D": exact,
                         "rel": rel})
        hwe_ok = hwe_ok and (rel < 0.05)
    print("  INSTRUMENT CONTROL, genotype covariance vs 2D: %s"
          % ", ".join("%.4f vs %.4f" % (h["measured_genotype_cov"], h["two_D"])
                      for h in hwe_rows))
    out["C1"] = {"rows": [{k: v for k, v in r.items() if k != "_h"}
                          for r in a1],
                 "max_fst": reach, "can_fail_satisfied": can_fail,
                 "hwe_control": hwe_rows, "hwe_control_pass": bool(hwe_ok),
                 "pass": bool(ok and can_fail and hwe_ok)}
    return bool(ok and can_fail and hwe_ok)


def c2(a2, out):
    """C2  A2 ISOLATES: F_ST pinned at 0 while shared LD is swept.

    With N_e frozen no frequency moves, so F_ST must be 0 -- measured, not
    assumed -- and the only thing changing is recombination breaking tag-causal
    LD. Note that here SLD_R and SLD_D coincide, because the single-locus
    frequencies are unchanged and the normalising denominator is constant. That
    coincidence is exactly why A2 alone cannot decide the normalisation and A1
    is needed.
    """
    print("")
    print("=" * 78)
    print("C2  A2 ISOLATION -- F_ST pinned at 0 while shared LD is swept")
    print("=" * 78)
    ok = True
    low = 1.0
    for r in a2:
        pinned = abs(r["F_ST_measured"]) <= 0.005
        low = min(low, r["SLD_D_measured"])
        ok = ok and pinned
        print("  c=%-7g SLD_D %.4f SLD_R %.4f | F_ST %.5f %s"
              % (r["c"], r["SLD_D_measured"], r["SLD_R_measured"],
                 r["F_ST_measured"], "pinned" if pinned else "NOT PINNED"))
    can_fail = low <= 0.6
    print("  shared LD fell to %.4f; can-fail needs <= 0.6  %s"
          % (low, "ok" if can_fail else "FAIL"))
    out["C2"] = {"rows": [{k: v for k, v in r.items() if k != "_h"}
                          for r in a2],
                 "min_shared_ld": low, "can_fail_satisfied": can_fail,
                 "note": "SLD_R and SLD_D coincide on this arm because the "
                         "single-locus frequencies do not move; that is why A2 "
                         "cannot decide the normalisation and A1 must",
                 "pass": bool(ok and can_fail)}
    return bool(ok and can_fail)


def c3(a1, a2, joint, out):
    """C3  THE LAW, arm by arm, UNDER BOTH shared_ld READINGS.

    covarianceRetention (1-fst)*shared_ld against the MEASURED retention of the
    predictive covariance, evaluated with shared_ld = SLD_R and again with
    shared_ld = SLD_D. On A1 the two predictions differ by a factor of
    (1 - F_ST); at F_ST = 0.3 that is 30%.

    The verdict is stated as a sentence in the results file rather than left for
    a reader to derive by differencing two columns.

    covarianceDivergenceFromRetention is the same statement subtracted from 1
    and is reported alongside, being a separate declaration with its own
    consumers.
    """
    print("")
    print("=" * 78)
    print("C3  covarianceRetention under BOTH shared_ld readings")
    print("=" * 78)
    cells = []
    ok = True
    for tag, rows in (("A1 fst-only", a1), ("A2 ld-only", a2),
                      ("JOINT", joint)):
        print("  %s:" % tag)
        for r in rows:
            meas = r["covariance_retention_measured"]["mean"]
            se = r["covariance_retention_measured"]["se"] or 0.0
            f = r["F_ST_measured"]
            pred_r = corpus_covarianceRetention(
                corpus_freqCorrFromFst(f),
                corpus_ldOverlapFromSharedLD(r["SLD_R_measured"]))
            pred_d = corpus_covarianceRetention(
                corpus_freqCorrFromFst(f),
                corpus_ldOverlapFromSharedLD(r["SLD_D_measured"]))
            good, dev_r = agrees(meas, se, pred_r)
            good_d, dev_d = agrees(meas, se, pred_d)
            ok = ok and good
            cells.append({
                "arm": tag, "F_ST": f,
                "SLD_R": r["SLD_R_measured"], "SLD_D": r["SLD_D_measured"],
                "measured_retention": meas, "se": se,
                "covarianceRetention_at_SLD_R": pred_r,
                "covarianceRetention_at_SLD_D": pred_d,
                "sems_SLD_R": dev_r, "sems_SLD_D": dev_d,
                "agrees_SLD_R": bool(good), "agrees_SLD_D": bool(good_d),
                "reading_gap_absolute": pred_d - pred_r,
                "reading_gap_pct": (100.0 * (pred_d - pred_r) / pred_r
                                    if pred_r else float("nan")),
                "covarianceDivergenceFromRetention_at_SLD_R":
                    corpus_covarianceDivergenceFromRetention(
                        f, r["SLD_R_measured"]),
                "measured_divergence": 1.0 - meas,
                "pass": bool(good)})
            print("    F %.4f | measured %.4f +-%.4f | @SLD_R %.4f (%.1f "
                  "sems) | @SLD_D %.4f (%.1f sems) | readings differ %+.1f%%"
                  " %s"
                  % (f, meas, se, pred_r, dev_r, pred_d, dev_d,
                     cells[-1]["reading_gap_pct"], "ok" if good else "FAIL"))
    a1_cells = [c for c in cells if c["arm"] == "A1 fst-only"
                and c["F_ST"] > 0.05]
    if a1_cells:
        r_ok = all(c["agrees_SLD_R"] for c in a1_cells)
        d_ok = all(c["agrees_SLD_D"] for c in a1_cells)
        if r_ok and not d_ok:
            verdict = ("shared_ld MUST be read as the CORRELATION retention "
                       "(SLD_R). Read as the D retention the law counts drift "
                       "TWICE and is wrong by a factor of (1 - F_ST).")
        elif d_ok and not r_ok:
            verdict = ("shared_ld must be read as the D retention (SLD_D); the "
                       "correlation reading is refuted.")
        else:
            verdict = ("UNDECIDED on this grid -- the two readings are not "
                       "separated by the error bars. This is a failure of the "
                       "RUN, not a finding about the corpus.")
    else:
        verdict = "NOT EVALUATED -- no A1 cell reached F_ST > 0.05."
    worst = max([abs(c["reading_gap_pct"]) for c in cells
                 if c["reading_gap_pct"] == c["reading_gap_pct"]] or [0.0])
    print("  NORMALISATION VERDICT: %s" % verdict)
    print("  worst gap between the two readings on this grid: %.2f%%" % worst)
    out["C3"] = {
        "cells": cells, "pass": bool(ok),
        "normalisation_verdict": verdict,
        "worst_reading_gap_pct": worst,
        "why_it_matters":
            "ldOverlapFromSharedLD is the identity function, so the corpus "
            "never states whether shared_ld is measured on D or on r. Under "
            "pure drift D decays like heterozygosity, so the D reading already "
            "contains the frequency factor and multiplying by (1-fst) counts "
            "drift twice. The two readings differ by exactly (1-fst).",
        "pass_note":
            "pass tracks the INSTRUMENT under the reading the measurement "
            "supports. Which reading the DECLARATION should name is the "
            "finding above and does not flip READ_THE_TEST."}
    return ok


def c4(a1, a2, joint, out):
    """C4  THE COMPENSATING PAIR, CONSTRUCTED AND RUN.

    This file's central claim is that a joint sweep cannot falsify a product.
    Asserting it would be asking to be believed, so it is DEMONSTRATED.

        freqCorr'  = k * (1 - fst)
        ldOverlap' = (1/k) * shared_ld

    Their product is IDENTICALLY the corpus product at every point, so:
      (i)   the JOINT arm must NOT reject the corrupted pair;
      (ii)  A1 must reject it -- there shared LD is pinned, so the corruption
            survives undivided as a factor k on the frequency term;
      (iii) A2 must reject it -- there fst is 0, so it survives as 1/k on the
            LD term.

    All three are required. (i) alone shows only that the corruption is
    invisible somewhere; (ii) and (iii) alone show only that something can see
    it. Together they establish the specific claim: the joint sweep is blind to
    an error both split sweeps catch.
    """
    print("")
    print("=" * 78)
    print("C4  COMPENSATING PAIR (k=%.2f, 1/k) -- joint arm must be FOOLED, "
          "split arms must REJECT" % CORRUPTION_K)
    print("=" * 78)
    k = CORRUPTION_K

    def clean(r):
        return corpus_covarianceRetention(
            corpus_freqCorrFromFst(r["F_ST_measured"]),
            corpus_ldOverlapFromSharedLD(r["SLD_R_measured"]))

    def corrupted(r):
        return corpus_covarianceRetention(
            k * corpus_freqCorrFromFst(r["F_ST_measured"]),
            (1.0 / k) * corpus_ldOverlapFromSharedLD(r["SLD_R_measured"]))

    joint_max = max(abs(corrupted(r) - clean(r)) for r in joint)
    joint_fooled = joint_max < 1e-12
    print("  joint arm: max |corrupted - clean| = %.3e  -> %s"
          % (joint_max, "FOOLED, as the design predicts" if joint_fooled
             else "NOT fooled -- the pair is not compensating"))

    def arm_rejects(rows, label, desc):
        worst = 0.0
        fired = False
        for r in rows:
            meas = r["covariance_retention_measured"]["mean"]
            se = r["covariance_retention_measured"]["se"] or 0.0
            # Rejection uses the SAME agreement rule the clean comparison uses,
            # floor included. A control judged by a looser rule than the check
            # it polices proves nothing about that check.
            agreed, dev = agrees(meas, se, corrupted(r))
            worst = max(worst, dev)
            fired = fired or (not agreed)
        print("    %-12s worst deviation %.1f sems (%s) -> %s"
              % (label, worst, desc, "REJECTS" if fired else "DOES NOT REJECT"))
        return fired, worst

    a1_f, a1_w = arm_rejects(a1, "A1 fst-only", "corruption survives as k")
    a2_f, a2_w = arm_rejects(a2, "A2 ld-only", "corruption survives as 1/k")
    ok = bool(joint_fooled and a1_f and a2_f)
    print("  -> %s" % ("ok: the joint sweep is demonstrably blind to an error "
                       "both split sweeps catch" if ok else "FAIL"))
    out["C4"] = {"k": k, "joint_max_abs_difference": joint_max,
                 "joint_fooled": bool(joint_fooled),
                 "A1_rejects": bool(a1_f), "A1_worst_sems": a1_w,
                 "A2_rejects": bool(a2_f), "A2_worst_sems": a2_w,
                 "demonstrates":
                     "the joint sweep cannot falsify a product; only the "
                     "one-at-a-time sweeps can. Measured here, not asserted.",
                 "pass": ok}
    return ok


def c5(a1, a2, out):
    """C5  neutralAFSharedLDBenchmarkRatio -- a RATIO of two retentions.

    ((1-fstT) sldT) / ((1-fstS) sldS). Being a ratio of two products, a common
    factor error in numerator and denominator cancels COMPLETELY, so this
    declaration is even less falsifiable by a joint sweep than
    covarianceRetention. It is therefore evaluated ACROSS arms -- source from
    one, target from the other -- so numerator and denominator do not carry the
    same corrupted factor.
    """
    print("")
    print("=" * 78)
    print("C5  neutralAFSharedLDBenchmarkRatio -- source and target from "
          "DIFFERENT arms")
    print("=" * 78)
    rows = []
    ok = True
    src = a1[0]
    for tgt in (a1[-1], a2[-1]):
        pred = corpus_neutralAFSharedLDBenchmarkRatio(
            src["F_ST_measured"], tgt["F_ST_measured"],
            src["SLD_R_measured"], tgt["SLD_R_measured"])
        ms = src["covariance_retention_measured"]["mean"]
        mt = tgt["covariance_retention_measured"]["mean"]
        ses = src["covariance_retention_measured"]["se"] or 0.0
        set_ = tgt["covariance_retention_measured"]["se"] or 0.0
        meas = mt / ms if ms else float("nan")
        se = (abs(meas) * math.sqrt((set_ / mt) ** 2 + (ses / ms) ** 2)
              if (mt and ms) else 0.0)
        good, dev = agrees(meas, se, pred)
        ok = ok and good
        rows.append({"source_F_ST": src["F_ST_measured"],
                     "source_SLD_R": src["SLD_R_measured"],
                     "target_F_ST": tgt["F_ST_measured"],
                     "target_SLD_R": tgt["SLD_R_measured"],
                     "target_arm": tgt["label"],
                     "measured_ratio": meas, "se": se,
                     "neutralAFSharedLDBenchmarkRatio": pred,
                     "deviation_sems": dev, "pass": bool(good)})
        print("  src(F %.4f sLD %.4f) -> tgt[%s](F %.4f sLD %.4f) | measured "
              "%.4f +-%.4f | corpus %.4f | %.2f sems  %s"
              % (src["F_ST_measured"], src["SLD_R_measured"], tgt["label"],
                 tgt["F_ST_measured"], tgt["SLD_R_measured"], meas, se, pred,
                 dev, "ok" if good else "FAIL"))
    out["C5"] = {"cells": rows, "pass": bool(ok)}
    return ok


def c6(out):
    """C6  THE METRIC PROFILE, AND THE PREVALENCE IT DOES NOT USE.

    neutralAFBenchmarkMetricProfile takes π. Its `brier` field uses π; its `auc`
    field does not, because the equal-variance Gaussian chart is
    prevalence-independent by construction. So:

      (a) the profile's auc must be IDENTICAL across the π grid while its brier
          MOVES -- a structural claim about the declaration, exact, no sampling;
      (b) targetBrierFromNeutralAFBenchmark must equal the profile's brier;
      (c) the forwarding targetR2FromNeutralAFBenchmark = presentDayR2 must
          still hold numerically.

    ESTIMAND, NAMED: equalVarianceGaussianAUCFromSignalVariance, NOT
    liabilityThresholdAUCFromExplainedR2.

    WHAT IS AND IS NOT TESTED. DGP.lean states that AUC is not determined by
    second moments and that it exposes this chart "as a numerical function
    only", with no theorem identifying it with a process AUC. The
    prevalence-independence measured here is a property of the CHART. fam_metrics
    measured a liability-threshold AUC moving 0.833 -> 0.925 across prevalence,
    so if the deployed quantity depends on prevalence this field cannot be it at
    more than one prevalence. SCOPE RESULT, not a refuted theorem.

    targetR2FromNeutralAFBenchmark's QUANTITY is not measured here; only its
    forwarding. See the header.
    """
    print("")
    print("=" * 78)
    print("C6  metric profile -- prevalence enters brier and NOT auc")
    print("=" * 78)
    V_A = 0.4
    rows = []
    ok = True
    by_fst = {}
    for fst in (0.0, 0.05, 0.15, 0.3):
        for pi in PI_GRID:
            prof = corpus_neutralAFBenchmarkMetricProfile(pi, V_A, V_E, fst)
            brier_direct = corpus_targetBrierFromNeutralAFBenchmark(
                pi, V_A, V_E, fst)
            r2_fwd = corpus_targetR2FromNeutralAFBenchmark(V_A, V_E, fst)
            agree_brier = abs(prof["brier"] - brier_direct) < 1e-12
            agree_r2 = abs(prof["r2"] - r2_fwd) < 1e-12
            ok = ok and agree_brier and agree_r2
            by_fst.setdefault(fst, []).append((prof["auc"], prof["brier"]))
            rows.append({"fst": fst, "pi": pi, "profile": prof,
                         "targetBrierFromNeutralAFBenchmark": brier_direct,
                         "targetR2FromNeutralAFBenchmark_forwarded": r2_fwd,
                         "brier_routes_agree": bool(agree_brier),
                         "r2_forwarding_holds": bool(agree_r2),
                         "auc_estimand":
                             "equalVarianceGaussianAUCFromSignalVariance "
                             "(NOT liabilityThresholdAUCFromExplainedR2)"})
            print("  fst %.2f pi %.2f | r2 %.5f | auc %.5f [equal-variance "
                  "Gaussian chart] | brier %.5f | brier routes %s | fwd %s"
                  % (fst, pi, prof["r2"], prof["auc"], prof["brier"],
                     agree_brier, agree_r2))
    auc_flat = all(max(a for a, _ in v) - min(a for a, _ in v) < 1e-12
                   for v in by_fst.values())
    brier_moves = all(max(b for _, b in v) - min(b for _, b in v) > 1e-9
                      for v in by_fst.values())
    print("  auc identical across the prevalence grid: %s   brier moves: %s"
          % (auc_flat, brier_moves))
    ok = ok and auc_flat and brier_moves
    out["C6"] = {"cells": rows,
                 "auc_prevalence_independent": bool(auc_flat),
                 "brier_prevalence_dependent": bool(brier_moves),
                 "auc_estimand":
                     "equalVarianceGaussianAUCFromSignalVariance -- NOT "
                     "liabilityThresholdAUCFromExplainedR2",
                 "scope_note":
                     "DGP.lean states no theorem identifies this chart with a "
                     "process AUC. The prevalence-independence here is a "
                     "property of the CHART. fam_metrics measured a "
                     "liability-threshold AUC moving 0.833 -> 0.925 across "
                     "prevalence, so this field cannot be the deployed quantity "
                     "at more than one prevalence. Scope result, not a refuted "
                     "theorem.",
                 "targetR2_not_measured_here":
                     "targetR2FromNeutralAFBenchmark forwards to presentDayR2, "
                     "measured by fam_pgs_transport_drift.py C5. Only the "
                     "forwarding is checked here, so the quantity is not "
                     "counted twice.",
                 "pass": bool(ok)}
    return bool(ok)


def strip(rows):
    return [{k: v for k, v in r.items() if k != "_h"} for r in rows]


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="tunable knobs for --set NAME=VALUE:\n" +
               "\n".join("  %-14s %s" % (k, v) for k, v in TUNABLES.items()))
    parser.add_argument("--profile", choices=("quick", "full", "deep"),
                        default="quick")
    parser.add_argument("--set", dest="settings", action="append", default=[],
                        metavar="NAME=VALUE")
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--output",
                        default="fam_neutral_af_benchmark_results.json")
    args = parser.parse_args(argv)
    configure_profile(args.profile)
    overrides = apply_overrides(args.settings)
    t0 = time.time()
    rng = np.random.default_rng(args.seed)
    config = resolved_config()
    print("profile %s, seed %d" % (args.profile, args.seed))
    if overrides:
        print("overrides: %s" % ", ".join("%s=%s" % kv
                                          for kv in overrides.items()))
    out = {"_provenance": simprov.stamp(
        "empirical/differential/cluster/fam_neutral_af_benchmark.py", config,
        args.seed,
        {"replicate_populations": N_REP,
         "replicate_unit": "an independent replicate POPULATION; every standard "
                           "error is the scatter across replicate populations, "
                           "never a per-draw formula"}),
        "profile": args.profile, "seed": args.seed,
        "overrides": overrides, "config": config,
        "family": "neutral_af_benchmark_transport",
        "members_covered": [
            "freqCorrFromFst", "ldOverlapFromSharedLD", "covarianceRetention",
            "covarianceDivergenceFromRetention",
            "neutralAFSharedLDBenchmarkRatio",
            "neutralAFBenchmarkMetricProfile",
            "targetBrierFromNeutralAFBenchmark"],
        "members_covered_elsewhere": {
            "targetR2FromNeutralAFBenchmark":
                "body forwards to presentDayR2; the QUANTITY is measured by "
                "fam_pgs_transport_drift.py C5 and is deliberately NOT "
                "re-measured here, because one measurement counted twice would "
                "read as corroboration. Only the forwarding is checked, in C6."},
        "members_not_found_in_corpus": [
            "targetGaussianAUCFromNeutralAFBenchmark",
            "targetExactGaussianAUCFromNeutralAFBenchmark"],
        "members_not_found_note":
            "Both are listed for this family in families.py and neither exists "
            "anywhere under proofs/ at this revision. No replacement is "
            "guessed. THIS FAMILY IS NOT FULLY COVERED.",
        "auc_estimand_in_this_family":
            "equalVarianceGaussianAUCFromSignalVariance, reached through "
            "neutralAFBenchmarkMetricProfile -> profileFromSignalVariance. NOT "
            "liabilityThresholdAUCFromExplainedR2.",
        "transcribed_against_revision": "fefbb573"}

    print("  building A1 (fst-only), A2 (ld-only) and the joint arm ...")
    a1 = arm_fst_only(rng)
    a2 = arm_ld_only(rng)
    joint = arm_joint(rng)

    r1 = c1(a1, rng, out)
    r2 = c2(a2, out)
    r3 = c3(a1, a2, joint, out)
    r4 = c4(a1, a2, joint, out)
    r5 = c5(a1, a2, out)
    r6 = c6(out)

    out["arm_A1_fst_only"] = strip(a1)
    out["arm_A2_ld_only"] = strip(a2)
    out["arm_joint"] = strip(joint)

    print("")
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    checks = (("C1 A1 isolates freqCorr", r1),
              ("C2 A2 isolates ldOverlap", r2),
              ("C3 covarianceRetention", r3),
              ("C4 compensating pair demo", r4),
              ("C5 benchmark ratio across arms", r5),
              ("C6 profile, brier, forwarding", r6))
    for tag, v in checks:
        print("  %-34s %s" % (tag, v))
    print("  NORMALISATION VERDICT: %s" % out["C3"]["normalisation_verdict"])
    ok = bool(r1 and r2 and r3 and r4 and r5 and r6)
    failed = [tag for tag, v in checks if not v]
    out["READ_THE_TEST"] = ok
    out["failed_checks"] = failed
    out["runtime_sec"] = time.time() - t0
    print("  READ_THE_TEST: %s" % ok)
    print("  runtime %.1f s" % out["runtime_sec"])
    fh = open(args.output, "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> %s" % args.output)
    if not ok:
        sys.stderr.write(
            "fam_neutral_af_benchmark: %d of %d checks FAILED under profile "
            "'%s': %s\n" % (len(failed), len(checks), args.profile,
                            ", ".join(failed)))
        sys.stderr.write(
            "fam_neutral_af_benchmark: this is a measurement, not a crash. The "
            "report is on stdout and the results file was written to %s\n"
            % args.output)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
