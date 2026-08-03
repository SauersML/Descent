#!/usr/bin/env python3
"""Family simulator: PGS TRANSPORT UNDER DRIFT.

A polygenic score built from an ancestral additive variance V_A, carried into
populations that have drifted apart; the present-day within-population score
variance, the between-population mean shift, and the R^2 and signal-to-noise
that follow.

WHAT MAKES THIS FAMILY DIFFERENT FROM drift_retention
  That family is about HETEROZYGOSITY. This one is about the VARIANCE OF A
  WEIGHTED SUM under drift, which picks up the between-population component
  2 F_ST V_A that the heterozygosity story does not contain at all.

THE DISPUTED QUANTITY IS F_ST, AND IT IS DERIVED HERE, NEVER RECEIVED
  Every declaration in this family takes `fst` as an argument. A simulator that
  drew frequencies from a Balding-Nichols beta at a NOMINAL F_ST and then fed
  that same nominal number back into the corpus formulas would be testing
  whether its own generator has the variance its own parameter claims. It would
  agree, it would look rigorous, and it would have measured nothing.

  So F_ST is an OUTPUT here. Frequencies drift under an explicit Wright-Fisher
  process from a common ancestor for t generations at N_e, and F_ST is MEASURED
  off the realised frequencies. The primitives are N_e and t; F_ST is derived
  the way M = 4Nm was derived in fam_im_coalescent rather than accepted.

WHICH F_ST, AT EVERY NUMBER
  This corpus contains at least four distinct quantities called F_ST and
  converts freely between them; fam_fst_estimators measured Hudson and Nei
  differing by 75% at the same frequencies. So every number below is LABELLED
  with the reading it uses, and the two readings that matter here are reported
  side by side:

    F_HET      1 - E[2 p_t (1-p_t)] / (2 p_0 (1-p_0)), the heterozygosity-loss
               reading, computed as a RATIO OF SUMS over loci and not a mean of
               per-locus ratios -- a rare locus whose heterozygosity collapses
               dominates a mean of ratios and contributes almost nothing to the
               additive variance.
    F_HUDSON   1 - E[T_ss]/E[T_st] read off the realised frequencies between
               the two daughter demes.

  presentDayPGSVariance is (1 - fst) * V_A with V_A ANCESTRAL. If a reader
  supplies a source-population V_A and a between-population Hudson F_ST -- the
  most natural reading of the two argument names -- the answer is wrong. The
  corpus does not say which. Measuring the size of that gap is a SCOPE
  DECLARATION, not new arithmetic, and it is what C3 reports.

TWO ENGINES, AND THEY ARE EXPECTED TO DISAGREE SOMEWHERE
  ENGINE A  Forward Wright-Fisher: p_{t+1} ~ Binomial(2 N_e, p_t)/(2 N_e).
            Alleles FIX. A fixed locus contributes exactly zero variance
            forever, and the fixation probability is large for a rare allele
            long before F_ST reaches 0.2.
  ENGINE B  Balding-Nichols beta at the F_ST measured from Engine A. The beta
            density has NO ATOMS at 0 and 1, so it cannot represent fixation.

  Engine B is the shortcut used almost everywhere, including by
  fam_fst_estimators. The two must agree at low F_ST and are expected to part
  company at high F_ST on a rare-allele spectrum. Which one the corpus's
  formulas describe is a real question about their scope, and the disagreement
  is reported as a finding rather than averaged away.

SPLIT CONTROLS

  C1 IS LOAD-BEARING AND MUST NOT BE TRIMMED. F_ST = 0 must give within-
     population score variance EXACTLY V_A and mean shift EXACTLY 0.

     WHY IT CANNOT BE REMOVED AS REDUNDANT, since a later reader will be
     tempted: the two quantities this family measures are (1 - F) * V_A and
     2F * V_A -- the SAME V_A in both. A simulator whose V_A is wrong by a
     factor k has BOTH quantities wrong by k, and the error CANCELS EXACTLY in
     their ratio and in every relative comparison between them. C3 and C4 can
     therefore both pass, at every cell of the grid, with the absolute scale
     wrong by any factor whatsoever. C1 is the only check in this file that
     fixes the absolute scale. Delete it and the rest of the file measures
     shape and is blind to scale.

  C2 A SINGLE LOCUS at known drifted frequencies, where both quantities are
     exact binomial moments with no polygenic limit and no summation --
     isolates the DRIFT from the POLYGENIC SUM. A simulator that mis-scales
     genotypes by 2 and compensates with a halved effect passes every
     many-locus check and fails this one.

  C8 POSITIVE CONTROL, REQUIRED TO FIRE IN ONE DIRECTION AND STAY SILENT IN
     THE OTHER. A prediction corrupted by fst -> 1.3 * fst must be REJECTED at
     the high-F_ST cells and must NOT be rejected at the F_ST = 0 cell, where
     1.3 * 0 is still 0. One-directional controls cannot separate "my
     corruption did nothing" from "my check cannot see corruption"; this one
     can, and it also proves the grid reaches a regime where the check has
     power at all.

CAN-FAIL
  F_ST must reach 0.2, where (1-F) and (1-F)^2 differ by 20%. Below F_ST = 0.02
  they agree to 2e-4 and every candidate law validates.
  The locus count m must come DOWN to 5 and the ancestral frequency down to
  0.01, because Expected_Abs_Shift's sqrt(2/pi) is a NORMALITY assumption about
  the mean shift. At m = 1000 common loci the shift is Gaussian to Monte-Carlo
  precision and the factor is validated on a grid where no candidate could
  ever fail.

WHAT IS COVERED, AND WHAT IS NOT IN THE CORPUS

  presentDayPGSVariance            C3
  presentDaySignalToNoise          C5
  presentDayR2                     C5
  Var_Delta_Mu                     C4
  expectedSqMeanPGSDiff_pureSplit  C4
  Expected_Abs_Shift               C4
  realWorldPGSVariance             C6
  causalPortabilityFromLocalFst    C7

  NOT FOUND IN THE CORPUS: `expectedR2`, listed as a member of this family in
  differential/cluster/families.py, DOES NOT EXIST at the revision below. There
  is no `def expectedR2` anywhere under proofs/. The only similar name is
  `expectedR2FromN (n h2 M)` in Calibrator/EquityAndImplementation.lean, which
  takes a sample size and a SNP count and is a different estimand; this file
  does NOT treat it as the replacement, because guessing which declaration
  replaced a deleted one is how an instrument ends up checking a corpus that is
  gone. THIS FAMILY IS THEREFORE NOT FULLY COVERED and this file does not claim
  it is.

THE SHARED R^2 ARM -- READ THIS BEFORE WRITING fam_neutral_af_benchmark.py
  targetR2FromNeutralAFBenchmark in the neutral_af_benchmark_transport family
  is not an independent declaration. Its entire body is

      targetR2FromNeutralAFBenchmark V_A V_E fstTarget = presentDayR2 V_A V_E fstTarget

  so measuring it there would RE-MEASURE C5 of this file under another name,
  and the agreement between the two families would read as corroboration while
  being one measurement counted twice. C5 measures it ONCE, here, and the
  neutral-AF simulator must cite this result rather than repeat it. What that
  simulator has to add is the part this file does not touch: the shared-LD
  factor, and the one-at-a-time sweeps that are the only way to falsify a
  PRODUCT of a frequency term and an LD term.

NO AUC IS TOUCHED BY THIS FILE. neutralAFBenchmarkMetricProfile reaches
  equalVarianceGaussianAUCFromSignalVariance -- NOT
  liabilityThresholdAUCFromExplainedR2, which is a different estimand carrying
  a prevalence argument -- but that profile is a member of the neutral-AF
  family, not this one, and nothing here evaluates either.

TRANSCRIPTION PROVENANCE
  Bodies quoted beside their transcriptions with file and declaration name and
  NO LINE NUMBER. Transcribed against revision 0acbc1d7, re-read from the
  working tree immediately before commit. Calibrator/PortabilityDrift.lean is
  under active edit by other sessions; if you are reading this at a later
  revision, re-read the eight declarations before trusting the transcription.

RUNNING IT -- NOT ON A LOGIN NODE
  numpy only, single-threaded by construction, no msprime and no build.

      srun --time=45 --mem=16G --cpus-per-task=1 \
        env OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
        python3 proofs/validation/empirical/differential/cluster/fam_pgs_transport_drift.py \
            --profile full \
            --output /projects/standard/hsiehph/sauer354/fam_pgs_drift_<stamp>.json \
        > /projects/standard/hsiehph/sauer354/fam_pgs_drift_<stamp>.out 2>&1

  CAPTURE BOTH STREAMS: a nonzero exit here is a MEASUREMENT OUTCOME, not a
  crash. The report is on stdout and the failing check names on stderr, and the
  results file is written either way.

  Output goes outside /tmp, which is node-local, under a unique name, so an
  absent file means not written rather than not written HERE.
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

# --- the drift process -----------------------------------------------------
NE = 500                 # diploids per daughter deme
# Generation grid. With Ne = 500 the heterozygosity-loss F_ST at these times is
# about 0, 0.010, 0.049, 0.141, 0.295 -- the top of the grid is past 0.2, where
# (1-F) and (1-F)^2 differ by 20%, which is the can-fail requirement.
T_GRID = (0, 10, 50, 150, 350)
N_REP = 200              # independent replicate populations per cell
M_LOCI = 400             # causal loci in the polygenic arm
# Ancestral spectrum. Deliberately includes rare variants: a common-only
# spectrum makes fixation negligible, and fixation is exactly where the
# Wright-Fisher and Balding-Nichols engines are expected to part company.
P0_SPECTRUM = (0.01, 0.03, 0.05, 0.1, 0.2, 0.35, 0.5)
# --- the individual-level arm ----------------------------------------------
# Genotypes are drawn for real here rather than assumed to be at HWE, which
# costs n*m draws per deme per replicate, so it runs on fewer replicates. This
# split is itself a control: the frequency arm tests the DRIFT half and the
# individual arm tests the SCORE-CONSTRUCTION half.
IND_REP = 40
IND_N = 4000
IND_M = 300
# --- the small-m arm, where the normal approximation must break -------------
SMALL_M_GRID = (1, 5, 20, 100, 1000)
# --- C6: rho^2 is DERIVED from a finite-n source fit, never fitted ----------
RHO_N_GRID = (500, 2000, 20000)
# --- C8 -------------------------------------------------------------------
CORRUPTION = 1.3
V_E = 1.0                # residual variance for the R^2 arm

TUNABLES = {
    "NE": "diploids per daughter deme",
    "T_GRID": "generations of drift; F_ST is measured, not set",
    "N_REP": "replicate populations per cell (the error bar)",
    "M_LOCI": "causal loci in the polygenic arm",
    "P0_SPECTRUM": "ancestral allele frequencies, rare variants included",
    "IND_REP": "replicates in the individual-genotype arm",
    "IND_N": "individuals per deme in the individual-genotype arm",
    "IND_M": "loci in the individual-genotype arm",
    "SMALL_M_GRID": "locus counts for the normality arm of Expected_Abs_Shift",
    "RHO_N_GRID": "source sample sizes from which rho^2 is DERIVED",
    "CORRUPTION": "C8 multiplier applied to fst in the corrupted prediction",
    "V_E": "residual variance in the R^2 arm",
}


def configure_profile(profile):
    """Sampling widths only. No estimand differs between profiles."""
    global NE, T_GRID, N_REP, M_LOCI, IND_REP, IND_N, IND_M, SMALL_M_GRID
    global RHO_N_GRID
    if profile == "full":
        return
    if profile == "deep":
        N_REP, M_LOCI = 600, 800
        T_GRID = (0, 5, 10, 25, 50, 100, 150, 250, 350, 500)
        IND_REP, IND_N = 120, 8000
        SMALL_M_GRID = (1, 2, 5, 10, 20, 50, 100, 300, 1000)
        RHO_N_GRID = (250, 500, 1000, 2000, 8000, 20000)
        return
    if profile != "quick":
        raise ValueError("profile must be 'quick', 'full' or 'deep'")
    N_REP, M_LOCI = 40, 100
    T_GRID = (0, 50, 350)
    IND_REP, IND_N, IND_M = 8, 800, 60
    SMALL_M_GRID = (1, 20, 1000)
    RHO_N_GRID = (500, 20000)


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

def corpus_pgsVarianceFromHet(beta_sq_sum, het):
    """Calibrator/PortabilityDrift.lean, decl `pgsVarianceFromHet`

        noncomputable def pgsVarianceFromHet (β_sq_sum het : ℝ) : ℝ :=
          β_sq_sum * het
    """
    return beta_sq_sum * het


def corpus_presentDayPGSVariance(V_A, fst):
    """Calibrator/PortabilityDrift.lean, decl `presentDayPGSVariance`

        noncomputable def presentDayPGSVariance (V_A fst : ℝ) : ℝ :=
          pgsVarianceFromHet V_A (1 - fst)

    i.e. (1 - fst) * V_A. NOTE what the composition asserts: the second
    argument of pgsVarianceFromHet is named `het`, so `1 - fst` is being used as
    a HETEROZYGOSITY RETENTION. That is the reading C3 measures against, and it
    is not the same number as a between-population Hudson F_ST.
    """
    return corpus_pgsVarianceFromHet(V_A, 1.0 - fst)


def corpus_realWorldPGSVariance(V_A, fst, rhoSq):
    """Calibrator/PortabilityDrift.lean, decl `realWorldPGSVariance`

        noncomputable def realWorldPGSVariance (V_A fst rhoSq : ℝ) : ℝ :=
          rhoSq * (1 - fst) * V_A
    """
    return rhoSq * (1.0 - fst) * V_A


def corpus_r2FromSignalVariance(vSignal, vNoise):
    """Calibrator/DGP.lean, decl `r2FromSignalVariance`

        noncomputable def r2FromSignalVariance (vSignal vNoise : ℝ) : ℝ :=
          vSignal / (vSignal + vNoise)
    """
    return vSignal / (vSignal + vNoise)


def corpus_presentDayR2(V_A, V_E, fst):
    """Calibrator/PortabilityDrift.lean, decl `presentDayR2`

        noncomputable def presentDayR2 (V_A V_E fst : ℝ) : ℝ :=
          r2FromSignalVariance (presentDayPGSVariance V_A fst) V_E

    THIS IS THE SHARED ARM. targetR2FromNeutralAFBenchmark forwards to this
    body verbatim, so it is measured here and must not be measured again in the
    neutral-AF family.
    """
    return corpus_r2FromSignalVariance(corpus_presentDayPGSVariance(V_A, fst),
                                       V_E)


def corpus_presentDaySignalToNoise(V_A, V_E, fst):
    """Calibrator/PortabilityDrift.lean, decl `presentDaySignalToNoise`

        noncomputable def presentDaySignalToNoise (V_A V_E fst : ℝ) : ℝ :=
          presentDayPGSVariance V_A fst / V_E
    """
    return corpus_presentDayPGSVariance(V_A, fst) / V_E


def corpus_Var_Delta_Mu(V_A, fst):
    """Calibrator/PortabilityDrift.lean, decl `Var_Delta_Mu`

        noncomputable def Var_Delta_Mu (V_A fst : ℝ) : ℝ := 2 * fst * V_A
    """
    return 2.0 * fst * V_A


def corpus_expectedSqMeanPGSDiff_pureSplit(V_A, fstS, fstT):
    """Calibrator/PortabilityDrift.lean, decl `expectedSqMeanPGSDiff_pureSplit`

        noncomputable def expectedSqMeanPGSDiff_pureSplit (V_A fstS fstT : ℝ) : ℝ :=
          Var_Delta_Mu V_A (fstS + fstT)
    """
    return corpus_Var_Delta_Mu(V_A, fstS + fstT)


def corpus_Expected_Abs_Shift(V_A, fstS, fstT):
    """Calibrator/PortabilityDrift.lean, decl `Expected_Abs_Shift`

        noncomputable def Expected_Abs_Shift (V_A fstS fstT : ℝ) : ℝ :=
          Real.sqrt (Var_Delta_Mu V_A (fstS + fstT)) * Real.sqrt (2 / Real.pi)

    The sqrt(2/pi) is the mean absolute deviation of a NORMAL variable. It is
    therefore a distributional assumption about the mean shift, not algebra,
    and it is the only claim in this family that a second moment cannot check.
    """
    return (math.sqrt(corpus_Var_Delta_Mu(V_A, fstS + fstT))
            * math.sqrt(2.0 / math.pi))


def corpus_causalPortabilityFromLocalFst(source_sq_effect, fst_causal):
    """Calibrator/PhenomeWidePortability.lean, decl `causalPortabilityFromLocalFst`

        noncomputable def causalPortabilityFromLocalFst {m : ℕ}
            (sourceSquaredEffect fstCausal : Fin m → ℝ) : ℝ :=
          (∑ i, sourceSquaredEffect i * (1 - fstCausal i)) /
            (∑ i, sourceSquaredEffect i)

    Distinct from presentDayPGSVariance because the per-locus F_ST may differ
    across loci, which is exactly what drift on a spread ancestral spectrum
    produces and what a single scalar F_ST cannot represent.
    """
    num = float(np.sum(np.asarray(source_sq_effect)
                       * (1.0 - np.asarray(fst_causal))))
    den = float(np.sum(np.asarray(source_sq_effect)))
    return num / den


# ===========================================================================
# ENGINE A -- forward Wright-Fisher. F_ST is an output.
# ===========================================================================

def drift(p0, t, n_rep, n_deme, rng, Ne=None):
    """Drift `p0` for `t` generations in `n_deme` independent demes.

    Returns an array (n_rep, n_deme, m). Each element is its own binomial draw
    from its own current frequency -- the batched call is distributionally
    identical to the per-replicate loop it replaces, which is the only
    condition under which vectorising does not correlate replicates and destroy
    the error bars. Alleles FIX and stay fixed, which is the whole point of
    using this engine rather than a beta.
    """
    ne = NE if Ne is None else Ne
    m = len(p0)
    p = np.broadcast_to(np.asarray(p0, dtype=float),
                        (n_rep, n_deme, m)).copy()
    two_ne = 2 * ne
    for _ in range(int(t)):
        p = rng.binomial(two_ne, p) / float(two_ne)
    return p


def fst_het(p_t, p0):
    """F_HET: heterozygosity-loss F_ST, as a RATIO OF SUMS over loci.

    1 - sum_j E[2 p_tj (1-p_tj)] / sum_j 2 p_0j (1-p_0j).

    Deliberately NOT a mean of per-locus ratios. A rare locus that fixes has a
    per-locus ratio of 1 and contributes almost nothing to additive variance;
    averaging the ratios lets it dominate a quantity it barely affects. This is
    the same defect shape as an identifier collision in a membership test: it
    moves the number in a direction that has nothing to do with the effect.
    """
    h_t = float(np.mean(np.sum(2.0 * p_t * (1.0 - p_t), axis=-1)))
    h_0 = float(np.sum(2.0 * np.asarray(p0) * (1.0 - np.asarray(p0))))
    return 1.0 - h_t / h_0 if h_0 > 0 else float("nan")


def fst_het_per_locus(p_t, p0):
    """Per-locus F_HET, for causalPortabilityFromLocalFst. Same reading, no sum."""
    h_t = np.mean(2.0 * p_t * (1.0 - p_t), axis=0)
    h_0 = 2.0 * np.asarray(p0) * (1.0 - np.asarray(p0))
    return 1.0 - h_t / np.where(h_0 > 0, h_0, np.nan)


def fst_hudson(pa, pb):
    """F_HUDSON between two demes from realised frequencies, ratio of sums.

    Numerator (pa-pb)^2 - pa(1-pa)/(2n-1) - ... reduces, at the PARAMETRIC
    frequencies used here (no sampling of individuals), to the uncorrected
    ratio-of-sums form. Labelled as such wherever it is printed: this is the
    BETWEEN-POPULATION reading and it is not the same number as F_HET.
    """
    num = (pa - pb) ** 2
    den = pa * (1 - pb) + pb * (1 - pa)
    return float(np.sum(num) / np.sum(den)) if np.sum(den) > 0 else float("nan")


# ===========================================================================
# ENGINE B -- Balding-Nichols beta at the F_ST Engine A measured.
# Shares no code with Engine A. Cannot represent fixation: the beta density has
# no atoms at 0 or 1, so a locus that Engine A has fixed is, to Engine B, a
# locus at some interior frequency it will never reach.
# ===========================================================================

def balding_nichols(p0, fst, n_rep, n_deme, rng):
    p0 = np.asarray(p0, dtype=float)
    if fst <= 0:
        return np.broadcast_to(p0, (n_rep, n_deme, len(p0))).copy()
    c = (1.0 - fst) / fst
    a = p0 * c
    b = (1.0 - p0) * c
    return rng.beta(np.broadcast_to(a, (n_rep, n_deme, len(p0))),
                    np.broadcast_to(b, (n_rep, n_deme, len(p0))))


# ===========================================================================
# THE SCORE
# ===========================================================================

def make_architecture(m, rng, spectrum=None):
    """Effects and ancestral frequencies. Fixed across replicates so that V_A
    is an exact constant rather than a quantity with its own sampling error."""
    spec = P0_SPECTRUM if spectrum is None else spectrum
    p0 = np.array([spec[i % len(spec)] for i in range(m)], dtype=float)
    beta = rng.normal(size=m)
    V_A = float(np.sum(beta ** 2 * 2.0 * p0 * (1.0 - p0)))
    return p0, beta, V_A


def score_moments_from_freq(p, beta):
    """Within-population score variance and mean under HWE at frequencies `p`.

    Var = sum_j beta_j^2 * 2 p_j (1-p_j),  Mean = sum_j beta_j * 2 p_j.
    Used by the FREQUENCY arm, which tests the drift half. The INDIVIDUAL arm
    below assumes none of this and draws genotypes.
    """
    var = np.sum(beta ** 2 * 2.0 * p * (1.0 - p), axis=-1)
    mean = np.sum(beta * 2.0 * p, axis=-1)
    return var, mean


def score_moments_from_individuals(p, beta, n, rng):
    """Same two quantities, measured on DRAWN GENOTYPES. HWE is not assumed.

    g ~ Binomial(2, p_j) per individual per locus, S = sum_j beta_j g_j.
    """
    g = rng.binomial(2, np.broadcast_to(p, (n, len(p))))
    s = g.dot(beta)
    return float(np.var(s, ddof=1)), float(np.mean(s))


# ===========================================================================
# CHECKS
# ===========================================================================

def c1(rng, out):
    """C1  THE LOAD-BEARING ABSOLUTE-SCALE CONTROL. F_ST = 0.

    DO NOT REMOVE THIS CHECK AS REDUNDANT. Both quantities this file measures
    are multiples of the SAME V_A -- (1-F) V_A and 2F V_A -- so a V_A wrong by
    any factor k leaves every relative comparison between them unchanged, and
    C3 and C4 pass at every cell with the absolute scale arbitrarily wrong.
    This is the only check here that pins the scale.

    At t = 0 the two daughters are identical to the ancestor, so:
      within-population score variance must be EXACTLY V_A;
      the mean shift must be EXACTLY 0, not merely small.
    Both are checked on the frequency arm (exact) and the individual arm
    (sampling error only).
    """
    print("")
    print("=" * 78)
    print("C1  LOAD-BEARING SCALE CONTROL -- F_ST = 0 pins V_A absolutely")
    print("=" * 78)
    p0, beta, V_A = make_architecture(M_LOCI, rng)
    p = drift(p0, 0, N_REP, 2, rng)
    var, mean = score_moments_from_freq(p, beta)
    within = float(np.mean(var))
    shift = float(np.mean(mean[:, 0] - mean[:, 1]))
    exact_var = abs(within - V_A) / V_A
    exact_shift = abs(shift)
    freq_ok = exact_var < 1e-12 and exact_shift < 1e-9

    iv, im_ = score_moments_from_individuals(p[0, 0], beta, IND_N, rng)
    # Sampling error of a variance estimate from n draws is ~ V*sqrt(2/(n-1)).
    se_iv = V_A * math.sqrt(2.0 / (IND_N - 1))
    ind_sems = abs(iv - V_A) / se_iv
    ind_ok = ind_sems <= 4.0

    print("  frequency arm: within-pop variance %.10f vs V_A %.10f "
          "(rel %.2e), mean shift %.2e  %s"
          % (within, V_A, exact_var, exact_shift, "ok" if freq_ok else "FAIL"))
    print("  individual arm (genotypes drawn, HWE not assumed): %.5f vs %.5f, "
          "%.2f sems  %s" % (iv, V_A, ind_sems, "ok" if ind_ok else "FAIL"))
    ok = freq_ok and ind_ok
    out["C1"] = {"V_A": V_A, "within_freq": within, "rel_err_freq": exact_var,
                 "mean_shift_freq": shift,
                 "within_individuals": iv, "individual_sems": ind_sems,
                 "load_bearing": "F_ST=0 is the ONLY absolute-scale control in "
                                 "this file; (1-F) and 2F both multiply the "
                                 "same V_A and a scale error cancels in every "
                                 "ratio between them",
                 "pass": bool(ok)}
    return ok


def c2(rng, out):
    """C2  SINGLE LOCUS -- exact binomial moments, no polygenic limit.

    Isolates the DRIFT from the POLYGENIC SUM. With m = 1 the score is a scaled
    binomial whose mean and variance are known in closed form with no summation
    at all, so a simulator that mis-scales genotypes by 2 and compensates with a
    halved effect -- which passes every many-locus check in this file -- fails
    here.
    """
    print("")
    print("=" * 78)
    print("C2  SINGLE LOCUS -- exact binomial moments (drift split from the sum)")
    print("=" * 78)
    rows = []
    ok = True
    for p0v in (0.05, 0.2, 0.5):
        beta = np.array([1.7])
        p0 = np.array([p0v])
        V_A = float(1.7 ** 2 * 2.0 * p0v * (1.0 - p0v))
        for t in (0, 50):
            p = drift(p0, t, max(N_REP, 400), 2, rng)
            var, _ = score_moments_from_freq(p, beta)
            meas = float(np.mean(var))
            f = fst_het(p, p0)
            pred = corpus_presentDayPGSVariance(V_A, f)
            se = float(np.std(var, ddof=1) / math.sqrt(var.size))
            dev = abs(meas - pred) / max(se, 1e-12)
            good = dev <= 4.0
            ok = ok and good
            rows.append({"p0": p0v, "t": t, "F_HET": f, "V_A": V_A,
                         "measured": meas, "se": se,
                         "presentDayPGSVariance": pred,
                         "deviation_sems": dev, "pass": bool(good)})
            print("  p0=%-5g t=%-4d F_HET %.5f | measured %.6f +-%.6f | "
                  "corpus %.6f | %.2f sems  %s"
                  % (p0v, t, f, meas, se, pred, dev, "ok" if good else "FAIL"))
    out["C2"] = {"cells": rows, "pass": bool(ok)}
    return ok


def base_drift_grid(rng):
    """One Wright-Fisher measurement of the t grid; C3 to C5 and C8 read
    different declarations off it. Four claims on one measurement, not four
    measurements -- stated so nobody quotes them as independent confirmations.
    """
    p0, beta, V_A = make_architecture(M_LOCI, rng)
    cells = []
    for t in T_GRID:
        p = drift(p0, t, N_REP, 2, rng)
        var, mean = score_moments_from_freq(p, beta)
        f_het = fst_het(p, p0)
        # Hudson PER REPLICATE, then averaged. Averaging the frequencies across
        # replicates FIRST would be wrong in a way that always flatters: the
        # replicate mean of p is p0 in both demes, so (pa-pb)^2 collapses to
        # sampling noise and the measured divergence would read as ~0 no matter
        # how far the populations had actually drifted.
        f_hud = float(np.mean([fst_hudson(p[r, 0], p[r, 1])
                               for r in range(p.shape[0])]))
        d_mu = mean[:, 0] - mean[:, 1]
        fixed = float(np.mean((p <= 0.0) | (p >= 1.0)))
        cells.append({
            "t": t,
            "F_HET": f_het,
            "F_HUDSON": f_hud,
            "fixed_locus_fraction": fixed,
            "within_var": simprov.summarize(list(var.reshape(-1))),
            "sq_mean_shift": simprov.summarize(list(d_mu ** 2)),
            "abs_mean_shift": simprov.summarize(list(np.abs(d_mu))),
            "per_locus_F_HET": list(fst_het_per_locus(
                p.reshape(-1, p.shape[-1]), p0)),
        })
    return {"p0": list(p0), "beta": list(beta), "beta_sq": list(beta ** 2),
            "V_A": V_A, "cells": cells}


def c3(base, rng, out):
    """C3  presentDayPGSVariance, against BOTH F_ST readings, labelled.

    The corpus composes pgsVarianceFromHet with `1 - fst`, so its second
    argument is a HETEROZYGOSITY RETENTION. C3 evaluates the same declaration
    under both readings available to a reader of the argument name:

      F_HET     the heterozygosity-loss reading the composition implies;
      F_HUDSON  the between-population reading the name `fst` suggests.

    If they differ materially, the declaration needs a scope note saying which
    it means. That is a SCOPE DECLARATION, not new arithmetic, and it is the
    same defect fam_fst_estimators found in the free conversion between
    estimators.

    ENGINE B is run at the SAME measured F_HET, so any gap between the engines
    is fixation and not parameterisation.
    """
    print("")
    print("=" * 78)
    print("C3  presentDayPGSVariance -- both F_ST readings, both engines")
    print("=" * 78)
    V_A = base["V_A"]
    p0 = np.array(base["p0"])
    beta = np.array(base["beta"])
    rows = []
    ok = True
    for c in base["cells"]:
        meas = c["within_var"]["mean"]
        se = c["within_var"]["se"] or 0.0
        pred_het = corpus_presentDayPGSVariance(V_A, c["F_HET"])
        pred_hud = corpus_presentDayPGSVariance(V_A, c["F_HUDSON"])
        dev_het = abs(meas - pred_het) / max(se, 1e-12)
        dev_hud = abs(meas - pred_hud) / max(se, 1e-12)
        # Engine B at the SAME measured F_HET.
        pb = balding_nichols(p0, max(c["F_HET"], 0.0), N_REP, 2, rng)
        var_b, _ = score_moments_from_freq(pb, beta)
        meas_b = float(np.mean(var_b))
        engine_gap = (meas_b - meas) / meas if meas else float("nan")
        good = dev_het <= 4.0
        ok = ok and good
        rows.append({"t": c["t"], "F_HET": c["F_HET"], "F_HUDSON": c["F_HUDSON"],
                     "measured_WF": meas, "se": se,
                     "presentDayPGSVariance_at_F_HET": pred_het,
                     "presentDayPGSVariance_at_F_HUDSON": pred_hud,
                     "sems_F_HET": dev_het, "sems_F_HUDSON": dev_hud,
                     "measured_BaldingNichols": meas_b,
                     "engine_gap_rel": engine_gap,
                     "fixed_locus_fraction": c["fixed_locus_fraction"],
                     "pass": bool(good)})
        print("  t=%-4d F_HET %.4f F_HUD %.4f | WF %.4f +-%.4f | corpus@HET "
              "%.4f (%.1f sems) | corpus@HUD %.4f (%.1f sems) | BN engine "
              "%+.2f%% | fixed %.1f%%  %s"
              % (c["t"], c["F_HET"], c["F_HUDSON"], meas, se, pred_het,
                 dev_het, pred_hud, dev_hud, 100 * engine_gap,
                 100 * c["fixed_locus_fraction"], "ok" if good else "FAIL"))
    print("  EVERY NUMBER ABOVE IS LABELLED WITH ITS F_ST READING. The corpus "
          "declaration does not say which it means.")
    out["C3"] = {"cells": rows, "pass": bool(ok)}
    return ok


def c4(base, rng, out):
    """C4  THE MEAN SHIFT: Var_Delta_Mu, expectedSqMeanPGSDiff_pureSplit, and
    Expected_Abs_Shift's NORMALITY assumption.

    The first two are second-moment claims and are checked as such. The third
    is not: sqrt(2/pi) is the mean absolute deviation of a NORMAL variable, so
    it is a distributional claim that no second moment can test. It is checked
    against the measured E|shift| on a locus-count grid running down to m = 1,
    where the shift is manifestly not Gaussian.

    CAN-FAIL, and this is why the small-m arm exists: at m = 1000 common loci
    the shift is Gaussian to Monte-Carlo precision and sqrt(2/pi) is validated
    on a grid where no candidate constant could ever fail.
    """
    print("")
    print("=" * 78)
    print("C4  MEAN SHIFT -- second moments, then the normality assumption")
    print("=" * 78)
    V_A = base["V_A"]
    rows = []
    ok = True
    for c in base["cells"]:
        f = c["F_HET"]
        meas = c["sq_mean_shift"]["mean"]
        se = c["sq_mean_shift"]["se"] or 0.0
        # Both daughters drifted the same amount, so fstS = fstT = F_HET.
        pred = corpus_expectedSqMeanPGSDiff_pureSplit(V_A, f, f)
        dev = abs(meas - pred) / max(se, 1e-12)
        good = dev <= 4.0 or c["t"] == 0
        ok = ok and good
        rows.append({"t": c["t"], "F_HET": f, "measured_sq_shift": meas,
                     "se": se, "expectedSqMeanPGSDiff_pureSplit": pred,
                     "Var_Delta_Mu": corpus_Var_Delta_Mu(V_A, 2.0 * f),
                     "deviation_sems": dev, "pass": bool(good)})
        print("  t=%-4d F_HET %.4f | E[shift^2] %.4f +-%.4f | corpus %.4f | "
              "%.2f sems  %s"
              % (c["t"], f, meas, se, pred, dev, "ok" if good else "FAIL"))

    print("  normality arm for Expected_Abs_Shift (sqrt(2/pi) is a "
          "DISTRIBUTIONAL claim):")
    norm_rows = []
    for m in SMALL_M_GRID:
        p0, beta, V_A_m = make_architecture(m, rng)
        p = drift(p0, T_GRID[-1], max(N_REP, 400), 2, rng)
        _, mean = score_moments_from_freq(p, beta)
        d = mean[:, 0] - mean[:, 1]
        f = fst_het(p, p0)
        meas_abs = float(np.mean(np.abs(d)))
        se_abs = float(np.std(np.abs(d), ddof=1) / math.sqrt(d.size))
        pred_abs = corpus_Expected_Abs_Shift(V_A_m, f, f)
        # The ratio E|X| / sqrt(E[X^2]) is sqrt(2/pi) = 0.7979 for a Gaussian
        # and is what the corpus's constant asserts. Measured directly, it is
        # independent of any V_A scale error.
        ratio = meas_abs / math.sqrt(float(np.mean(d ** 2)))
        dev = abs(meas_abs - pred_abs) / max(se_abs, 1e-12)
        norm_rows.append({"m": m, "F_HET": f, "measured_abs_shift": meas_abs,
                          "se": se_abs, "Expected_Abs_Shift": pred_abs,
                          "measured_ratio_absE_over_rmsE": ratio,
                          "gaussian_ratio": math.sqrt(2.0 / math.pi),
                          "deviation_sems": dev})
        print("    m=%-5d F_HET %.4f | E|shift| %.4f +-%.4f | corpus %.4f | "
              "measured E|X|/rms %.4f vs Gaussian %.4f | %.1f sems"
              % (m, f, meas_abs, se_abs, pred_abs, ratio,
                 math.sqrt(2.0 / math.pi), dev))
    print("    REPORTED, NOT SCORED: the small-m cells are where the normal "
          "approximation is EXPECTED to fail, so a failure there is a scope "
          "result about Expected_Abs_Shift, not a broken check.")
    out["C4"] = {"cells": rows, "normality_arm": norm_rows, "pass": bool(ok)}
    return ok


def c5(rng, out):
    """C5  presentDayR2 and presentDaySignalToNoise -- THE SHARED ARM.

    Measured ONCE here. targetR2FromNeutralAFBenchmark in the neutral-AF family
    forwards to presentDayR2 verbatim, so measuring it there too would be one
    measurement counted twice with the agreement reading as corroboration.

    The phenotype is built explicitly: Y = S_true + E with E ~ N(0, V_E), and
    R^2 is the squared correlation between the score and Y in the drifted
    population, measured on DRAWN INDIVIDUALS. The corpus prediction takes the
    ancestral V_A and the measured F_HET.
    """
    print("")
    print("=" * 78)
    print("C5  presentDayR2 / presentDaySignalToNoise -- SHARED with the "
          "neutral-AF family, measured here ONCE")
    print("=" * 78)
    p0, beta, V_A = make_architecture(IND_M, rng)
    rows = []
    ok = True
    for t in T_GRID:
        p = drift(p0, t, IND_REP, 1, rng)
        r2s, snrs = [], []
        for r in range(IND_REP):
            pr = p[r, 0]
            g = rng.binomial(2, np.broadcast_to(pr, (IND_N, len(pr))))
            s = g.dot(beta)
            y = s + rng.normal(scale=math.sqrt(V_E), size=IND_N)
            r2s.append(float(np.corrcoef(s, y)[0, 1] ** 2))
            snrs.append(float(np.var(s, ddof=1) / V_E))
        f = fst_het(p, p0)
        r2 = simprov.summarize(r2s)
        snr = simprov.summarize(snrs)
        pred_r2 = corpus_presentDayR2(V_A, V_E, f)
        pred_snr = corpus_presentDaySignalToNoise(V_A, V_E, f)
        d_r2 = abs(r2["mean"] - pred_r2) / max(r2["se"] or 1e-12, 1e-12)
        d_snr = abs(snr["mean"] - pred_snr) / max(snr["se"] or 1e-12, 1e-12)
        good = d_r2 <= 4.0 and d_snr <= 4.0
        ok = ok and good
        rows.append({"t": t, "F_HET": f, "r2": r2, "snr": snr,
                     "presentDayR2": pred_r2,
                     "presentDaySignalToNoise": pred_snr,
                     "r2_sems": d_r2, "snr_sems": d_snr,
                     "records_r2": r2s, "records_snr": snrs,
                     "pass": bool(good)})
        print("  t=%-4d F_HET %.4f | R2 %.5f +-%.5f vs %.5f (%.1f sems) | "
              "SNR %.4f +-%.4f vs %.4f (%.1f sems)  %s"
              % (t, f, r2["mean"], r2["se"] or 0.0, pred_r2, d_r2,
                 snr["mean"], snr["se"] or 0.0, pred_snr, d_snr,
                 "ok" if good else "FAIL"))
    out["C5"] = {"cells": rows, "pass": bool(ok),
                 "shared_with": "neutral_af_benchmark_transport / "
                                "targetR2FromNeutralAFBenchmark, whose body "
                                "forwards to presentDayR2 verbatim; that "
                                "family must cite this and not re-measure it"}
    return ok


def c6(rng, out):
    """C6  realWorldPGSVariance -- rho^2 DERIVED, never fitted.

    rhoSq is the one free-looking parameter in this family, and a free
    parameter that the simulator chooses is a parameter any measurement can be
    fitted to. selectedDriftFactor was left UNREACHABLE in the selection family
    for exactly that reason.

    So rho^2 is not chosen here. Effects are ESTIMATED from a finite source
    sample of size n, and rho^2 is a realised property of that fit. The corpus
    claim is then testable: the variance of the score built from the ESTIMATED
    effects in the drifted population must be rhoSq (1-fst) V_A.

    WHICH rho^2, declared before the run and not after. There are two readings
    and they are different numbers:

      RHO_UNWEIGHTED  corr(beta_hat, beta)^2, what a reader computes from a
                      table of effect estimates.
      RHO_WEIGHTED    the same correlation in the heterozygosity metric
                      w_j = 2 p0_j (1 - p0_j), i.e.
                      (sum w beta_hat beta)^2 / (sum w beta_hat^2 * sum w beta^2).

    The check is SCORED ON THE WEIGHTED READING and reports both. The reason is
    structural, not empirical: score variance is a heterozygosity-weighted
    quadratic form in the effects, so the only rho^2 that can appear in a
    variance identity at all is the weighted one. Scoring the unweighted
    reading would test a quantity that cannot enter the equation, and picking
    whichever reading agreed after seeing the numbers would be fitting the free
    parameter this check exists to avoid fitting. The gap between the two is
    itself the scope result: the corpus does not say which rhoSq it means.
    """
    print("")
    print("=" * 78)
    print("C6  realWorldPGSVariance -- rho^2 derived from a finite-n fit")
    print("=" * 78)
    p0, beta, V_A = make_architecture(IND_M, rng)
    rows = []
    ok = True
    for n in RHO_N_GRID:
        # Source sample at the ancestral frequencies; per-locus marginal OLS.
        g = rng.binomial(2, np.broadcast_to(p0, (n, len(p0))))
        y = g.dot(beta) + rng.normal(scale=math.sqrt(V_E), size=n)
        gc = g - g.mean(axis=0)
        yc = y - y.mean()
        denom = np.sum(gc ** 2, axis=0)
        beta_hat = np.where(denom > 0, gc.T.dot(yc) / np.where(denom > 0,
                                                              denom, 1.0), 0.0)
        rho_sq_unw = float(np.corrcoef(beta_hat, beta)[0, 1] ** 2)
        w = 2.0 * p0 * (1.0 - p0)
        num = float(np.sum(w * beta_hat * beta)) ** 2
        den = (float(np.sum(w * beta_hat ** 2))
               * float(np.sum(w * beta ** 2)))
        rho_sq = (num / den) if den > 0 else float("nan")
        for t in (0, T_GRID[-1]):
            p = drift(p0, t, IND_REP, 1, rng)
            f = fst_het(p, p0)
            vs = []
            for r in range(IND_REP):
                gt = rng.binomial(2, np.broadcast_to(p[r, 0], (IND_N,
                                                               len(p0))))
                vs.append(float(np.var(gt.dot(beta_hat), ddof=1)))
            meas = simprov.summarize(vs)
            # V_A here is the ancestral variance of the TRUE score; the corpus
            # scales it by rhoSq. Both are on the same footing only because
            # beta_hat is on the beta scale (marginal OLS on genotypes).
            pred = corpus_realWorldPGSVariance(V_A, f, rho_sq)
            dev = abs(meas["mean"] - pred) / max(meas["se"] or 1e-12, 1e-12)
            good = dev <= 4.0
            ok = ok and good
            rows.append({"n_source": n, "t": t, "F_HET": f,
                         "rho_sq_WEIGHTED_scored": rho_sq,
                         "rho_sq_UNWEIGHTED_reported": rho_sq_unw,
                         "realWorldPGSVariance_at_unweighted_rho":
                             corpus_realWorldPGSVariance(V_A, f, rho_sq_unw),
                         "measured": meas, "realWorldPGSVariance": pred,
                         "deviation_sems": dev, "records": vs,
                         "pass": bool(good)})
            print("  n=%-6d t=%-4d rho^2 weighted %.5f (unweighted %.5f) "
                  "F_HET %.4f | measured %.4f +-%.4f | corpus %.4f | "
                  "%.2f sems  %s"
                  % (n, t, rho_sq, rho_sq_unw, f, meas["mean"],
                     meas["se"] or 0.0, pred, dev, "ok" if good else "FAIL"))
    out["C6"] = {"cells": rows, "pass": bool(ok),
                 "rho_sq_provenance": "DERIVED from marginal-OLS effect "
                                      "estimates at finite n, never chosen, so "
                                      "it cannot be fitted to the measurement. "
                                      "SCORED on the heterozygosity-weighted "
                                      "reading because score variance is a "
                                      "heterozygosity-weighted quadratic form "
                                      "and no other reading can enter a "
                                      "variance identity; the unweighted "
                                      "reading is reported alongside and the "
                                      "gap is a scope result about which rhoSq "
                                      "the corpus means"}
    return ok


def c7(base, out):
    """C7  causalPortabilityFromLocalFst -- HETEROGENEOUS per-locus F_ST.

    This declaration is distinct from presentDayPGSVariance precisely because
    it admits a DIFFERENT F_ST at every locus. A grid on which all loci share
    one F_ST validates it by construction and settles nothing, so the ancestral
    spectrum here spans 0.01 to 0.5 and the realised per-locus F_HET spreads
    accordingly.

    Reference: the ratio of drifted to ancestral additive variance,
    sum beta^2 (1-F_j) 2 p0(1-p0) / sum beta^2 2 p0(1-p0). The corpus weights
    by sourceSquaredEffect alone. Whether that weight should carry the
    ancestral heterozygosity too is the question this check can answer, so BOTH
    weightings are reported.
    """
    print("")
    print("=" * 78)
    print("C7  causalPortabilityFromLocalFst -- heterogeneous per-locus F_ST")
    print("=" * 78)
    p0 = np.array(base["p0"])
    beta_sq = np.array(base["beta_sq"])
    rows = []
    ok = True
    for c in base["cells"]:
        f_loc = np.array(c["per_locus_F_HET"], dtype=float)
        spread = float(np.nanmax(f_loc) - np.nanmin(f_loc))
        # The corpus weighting: squared effect alone.
        corpus_val = corpus_causalPortabilityFromLocalFst(beta_sq, f_loc)
        # The variance-ratio reading: squared effect TIMES ancestral het.
        w = beta_sq * 2.0 * p0 * (1.0 - p0)
        var_ratio = float(np.nansum(w * (1.0 - f_loc)) / np.sum(w))
        # What the measurement says, from the same cell's within-pop variance.
        meas = c["within_var"]["mean"] / base["V_A"]
        se = (c["within_var"]["se"] or 0.0) / base["V_A"]
        d_corpus = abs(corpus_val - meas) / max(se, 1e-12)
        d_ratio = abs(var_ratio - meas) / max(se, 1e-12)
        # THE CHECK verifies the INSTRUMENT: the heterozygosity-weighted
        # variance ratio is what the measured variance ratio must equal, and if
        # it does not, this file is broken. Whether the CORPUS weighting also
        # matches is a separate question, reported as a finding rather than
        # folded into the harness verdict -- a corpus disagreement is a result,
        # not a failed run, and burying it in a boolean would hide it.
        good = d_ratio <= 4.0
        ok = ok and good
        rows.append({"t": c["t"], "per_locus_F_spread": spread,
                     "corpus_weighting_agrees": bool(d_corpus <= 4.0),
                     "causalPortabilityFromLocalFst": corpus_val,
                     "het_weighted_variance_ratio": var_ratio,
                     "measured_variance_ratio": meas, "se": se,
                     "sems_corpus_weighting": d_corpus,
                     "sems_het_weighting": d_ratio,
                     "pass": bool(good)})
        print("  t=%-4d per-locus F spread %.4f | corpus weighting %.5f "
              "(%.1f sems) | het-weighted %.5f (%.1f sems) | measured %.5f "
              "+-%.5f  %s"
              % (c["t"], spread, corpus_val, d_corpus, var_ratio, d_ratio,
                 meas, se, "ok" if good else "FAIL"))
    disagreeing = [r["t"] for r in rows if not r["corpus_weighting_agrees"]]
    if disagreeing:
        print("  FINDING, not a harness failure: the corpus weighting "
              "(squared effect alone) disagrees with the measured variance "
              "ratio at t = %s, while the heterozygosity-weighted reading "
              "agrees. causalPortabilityFromLocalFst weights by "
              "sourceSquaredEffect and omits the ancestral heterozygosity."
              % ", ".join(str(t) for t in disagreeing))
    out["C7"] = {"cells": rows, "pass": bool(ok),
                 "corpus_weighting_disagrees_at_t": disagreeing,
                 "finding_vs_harness": "pass reflects the INSTRUMENT (the "
                                       "het-weighted ratio must match the "
                                       "measurement). A corpus-weighting "
                                       "disagreement is reported as a finding "
                                       "and deliberately does NOT flip the "
                                       "harness verdict."}
    return ok


def c8(base, out):
    """C8  POSITIVE CONTROL, TWO-DIRECTIONAL.

    A prediction corrupted by fst -> 1.3 * fst must be

      (i)  REJECTED at the high-F_ST cells -- otherwise C3 cannot see an error
           in the quantity it exists to test, and C3's agreement means nothing;
      (ii) NOT REJECTED at the F_ST = 0 cell, where 1.3 * 0 is still 0 --
           otherwise the check is firing on something other than the
           corruption, and (i) would be uninformative.

    Requiring both separates "my corruption did nothing" from "my check cannot
    see corruption", which a one-sided control cannot do. It also demonstrates
    that the t grid reaches a regime where the check has power at all: if (i)
    failed everywhere, the can-fail requirement would not have been met.
    """
    print("")
    print("=" * 78)
    print("C8  POSITIVE CONTROL -- fst -> %.1f fst must fire at high F_ST and "
          "stay silent at F_ST = 0" % CORRUPTION)
    print("=" * 78)
    V_A = base["V_A"]
    rows = []
    fired_high = False
    silent_at_zero = None
    for c in base["cells"]:
        meas = c["within_var"]["mean"]
        se = c["within_var"]["se"] or 0.0
        bad = corpus_presentDayPGSVariance(V_A, CORRUPTION * c["F_HET"])
        dev = abs(meas - bad) / max(se, 1e-12)
        fires = dev > 4.0
        if c["t"] == 0:
            silent_at_zero = not fires
        elif c["F_HET"] >= 0.1:
            fired_high = fired_high or fires
        rows.append({"t": c["t"], "F_HET": c["F_HET"],
                     "corrupted_prediction": bad, "measured": meas,
                     "deviation_sems": dev, "fired": bool(fires)})
        print("  t=%-4d F_HET %.4f | corrupted %.4f vs measured %.4f | "
              "%.1f sems | %s"
              % (c["t"], c["F_HET"], bad, meas, dev,
                 "FIRED" if fires else "silent"))
    ok = bool(fired_high) and bool(silent_at_zero)
    print("  fired at high F_ST: %s   silent at F_ST=0: %s   -> %s"
          % (fired_high, silent_at_zero, "ok" if ok else "FAIL"))
    out["C8"] = {"cells": rows, "fired_at_high_fst": bool(fired_high),
                 "silent_at_zero_fst": bool(silent_at_zero),
                 "pass": ok}
    return ok


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
    parser.add_argument("--output", default="fam_pgs_transport_drift_results.json")
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
        "empirical/differential/cluster/fam_pgs_transport_drift.py", config,
        args.seed,
        {"replicate_populations_per_cell": N_REP,
         "individual_arm_replicates": IND_REP,
         "replicate_unit": "an independent replicate POPULATION; every "
                           "standard error here is the scatter across "
                           "replicate populations, never a per-draw formula"}),
        "profile": args.profile, "seed": args.seed,
        "overrides": overrides, "config": config,
        "family": "pgs_transport_drift",
        "members_covered": [
            "presentDayPGSVariance", "realWorldPGSVariance", "presentDayR2",
            "presentDaySignalToNoise", "Var_Delta_Mu", "Expected_Abs_Shift",
            "expectedSqMeanPGSDiff_pureSplit", "causalPortabilityFromLocalFst"],
        "members_not_found_in_corpus": ["expectedR2"],
        "members_not_found_note":
            "expectedR2 is listed as a member of this family in families.py "
            "and there is no such declaration under proofs/ at this revision. "
            "expectedR2FromN in EquityAndImplementation.lean takes a sample "
            "size and a SNP count and is a DIFFERENT estimand; it is NOT "
            "treated here as the replacement. This family is therefore NOT "
            "fully covered.",
        "fst_readings_reported": ["F_HET", "F_HUDSON"],
        "transcribed_against_revision": "0acbc1d7"}

    r1 = c1(rng, out)
    r2 = c2(rng, out)
    base = base_drift_grid(rng)
    out["base_grid"] = base
    r3 = c3(base, rng, out)
    r4 = c4(base, rng, out)
    r5 = c5(rng, out)
    r6 = c6(rng, out)
    r7 = c7(base, out)
    r8 = c8(base, out)

    print("")
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    checks = (("C1 F_ST=0 scale (LOAD-BEARING)", r1),
              ("C2 single locus", r2),
              ("C3 presentDayPGSVariance", r3),
              ("C4 mean shift + normality", r4),
              ("C5 presentDayR2 (shared arm)", r5),
              ("C6 realWorldPGSVariance", r6),
              ("C7 causalPortabilityFromLocalFst", r7),
              ("C8 positive control", r8))
    for tag, v in checks:
        print("  %-36s %s" % (tag, v))
    ok = bool(r1 and r2 and r3 and r4 and r5 and r6 and r7 and r8)
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
            "fam_pgs_transport_drift: %d of %d checks FAILED under profile "
            "'%s': %s\n" % (len(failed), len(checks), args.profile,
                            ", ".join(failed)))
        sys.stderr.write(
            "fam_pgs_transport_drift: this is a measurement, not a crash. The "
            "full report is on stdout and the results file was written to %s\n"
            % args.output)
        if args.profile == "quick":
            sys.stderr.write(
                "fam_pgs_transport_drift: profile 'quick' is the bounded "
                "development run; use --profile full before reading a failure "
                "as a finding.\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
