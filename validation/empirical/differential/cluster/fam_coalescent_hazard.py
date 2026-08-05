#!/usr/bin/env python3
"""Family simulator: COALESCENT HAZARD, AND THE HARMONIC-MEAN BRIDGE.

READ THIS FIRST -- THREE OF THE SIX MEMBERS CANNOT BE FALSIFIED.

  integratedCoalescentHazard      Lambda(t) = integral of hazard over [0,t]
  coalescenceSurvivalFromHazard   S(t) = exp(-Lambda(t))
  coalescenceCdfFromHazard        F(t) = 1 - S(t)

  These three are the DEFINITION of a survival function from a hazard. They
  are not claims about a population; they are the chain rule and the
  fundamental theorem of calculus wearing population-genetic names. A
  simulator that draws times by inverse-transform on Lambda and then
  "confirms" S = exp(-Lambda) has measured its own integrator and its own
  inverse-transform sampler, and NOTHING ELSE. It cannot come out any other
  way.

  A prior analysis of this family reached exactly this conclusion, and it is
  written here, beside the checks, and into the results file so that it
  cannot be quietly lost the next time someone reads a green C0 as evidence.

  C0 below does exercise those three declarations. Its verdict is scored into
  the INSTRUMENT health flag and is EXCLUDED BY NAME from the corpus findings.
  Agreement in C0 is a statement about this file's quadrature. It is not
  evidence for the corpus, and the results file says so in a field rather than
  in a comment.

WHAT IS ACTUALLY FALSIFIABLE HERE, AND IT IS THE BRIDGE.

  The corpus expresses a time-varying population size TWICE, in two different
  languages, and never checks that the two readings agree.

    (1) As a PROCESS. Descent/PortabilityDrift.lean defines survival from an
        integrated hazard: with Ne(t) varying, the hazard is 1/(2 Ne(t)) and
        Lambda(t) = integral of it. Nothing is averaged.

    (2) As a NUMBER. Descent/LDDecayTheory.lean defines

            harmonicMeanNe (Ne : Fin T -> R) := T / (sum of 1 / Ne i)

        and the drift-retention work throughout the corpus uses that single
        harmonic mean in place of the trajectory. `bottleneck_dominates_harmonic_mean`
        and `harmonicMeanNe_lt_timeWeightedArithmeticMeanNe` (Descent/DGP.lean)
        are the corpus's own statements that a bottleneck pulls it down.

  THE QUESTION THIS FILE ASKS. Does the constant-size population of size
  Ne_h = harmonicMeanNe(Ne) have the SAME TMRCA DISTRIBUTION as the true
  time-varying history? That is the bridge, and it is the only claim in this
  family that a simulation can contradict.

  WHY THE MEAN CANNOT DECIDE IT. The harmonic mean is constructed so that the
  two integrated hazards MEET at the window endpoint:

        Lambda_true(T_w) = sum over g < T_w of 1/(2 Ne(g))
                         = T_w / (2 Ne_h)
                         = Lambda_surrogate(T_w)

  identically, by the definition of Ne_h. So the two survival curves are
  PINNED TOGETHER at t = T_w whatever the history is, and the total
  coalescence probability over the window is right by construction. A summary
  statistic dominated by that agreement -- and the mean is close to one --
  validates the surrogate on a history where the two curves cross. That is
  why the check below is DISTRIBUTIONAL: pointwise survival with batch error
  bars, and quantiles from the 10th to the 90th percentile.

  THE BLIND POINT IS REPORTED AND NOT SCORED. t = T_w is the one time at which
  the bridge check is CONSTITUTIONALLY INCAPABLE of disagreeing. It is
  computed, printed and stored so a reader can see the pinning happen, and it
  is excluded from the scored grid. A bridge check evaluated only at the
  horizon would decide nothing and would look like a pass.

  THE MEAN IS MEASURED ANYWAY, AND LABELLED. Whether E[T] also agrees is
  itself a measurement -- the pinning argument above pins S(T_w), not the
  integral of S -- so the mean comparison is reported alongside the
  distributional one and explicitly marked as the near-blind statistic. If the
  distribution differs while the mean does not, that is the whole thesis of
  this file, measured rather than asserted.

  DERIVED, NOT ACCEPTED. Ne_h is never an input. The primitives are a CENSUS
  TRAJECTORY of diploid counts. Engine A draws parents from the gene-copy pool
  and lets collisions happen; the per-generation coalescence probability is
  MEASURED from those collisions in a separate census pass with its own error
  bar; the measured probabilities are inverted to Ne_hat(g) = 1/(2 p_hat(g));
  and Ne_h is `harmonicMeanNe` applied to THAT. Nowhere is the number 1/(2N)
  asserted. A simulator handed the harmonic mean it was built to test would
  agree with itself, look rigorous, and measure nothing -- this project spent
  a day on instruments of exactly that shape.

  THE WINDOW IS PART OF THE CLAIM. `harmonicMeanNe` takes `Ne : Fin T -> R`,
  so Ne_h depends on the window T_w over which the trajectory is averaged, and
  for a bottleneck it depends on it strongly. The corpus never says which T_w.
  C3 sweeps T_w and reports the spread as a finding in its own right; the
  SCORED cell is the full history, named in the output.

ALSO FALSIFIABLE, AND CHECKED SEPARATELY.

  C4  discreteRecombinationSurvival (1-r)^tmrca and twoLocusIBDCovariance
      w * (1-r)^tmrca, against a two-locus lineage walked back generation by
      generation with an explicit per-generation recombination event. The
      ibdWeight w is MEASURED at r = 0 and then used to predict the r > 0
      cells, so the formula is not handed its own answer.

  C5  the hard 1 on the diagonal of twoLocusCoalescentCovarianceMatrix, tested
      against SAMPLED GENOTYPES rather than assumed. That entry asserts both
      loci are variance-standardised. Raw diploid dosages have variance
      2p(1-p), which cannot reach 1 at any allele frequency, so the claim is
      decidable against a real genotype sample and the run says which way it
      went. The zeros away from the linked pair are tested too, using two
      unlinked loci in the same block.

WHAT THE FAMILY LISTING NAMES THAT THIS FILE DOES NOT COVER AS A MEMBER.
  differential/cluster/families.py lists `twoLocusIdx0` and `twoLocusIdx1`
  alongside the six. Both are `private def` in Descent/DGP.lean and return
  `Fin t`, not a number. They are exercised only through the matrix: C5's
  off-block zeros are what would fail if those indices named the wrong
  positions. They are reported as COVERED INDIRECTLY, not as scored members,
  because a private index constructor has no independent empirical content.

  ALL SIX MEMBERS NAMED FOR THIS FAMILY ARE LIVE IN THE CORPUS. Nothing was
  missing and nothing was guessed at. The three that are live but
  unfalsifiable are unfalsifiable by their content, not by their absence.

TWO ENGINES THAT SHARE NO CODE, AND WHERE THEY MUST DISAGREE.
  ENGINE A, WRIGHT-FISHER. Discrete generations. Each surviving lineage pair
    draws two parent indices uniformly from the 2N gene copies of that
    generation and coalesces on a collision. No hazard, no exponential, no
    integral appears in it. It is the primitive process.
  ENGINE B, INTEGRATED HAZARD. Continuous time. Builds Lambda by accumulating
    the piecewise-constant hazard and inverts it on an Exp(1) draw. It is the
    corpus's own reading, and it draws nothing that Engine A draws.

  THEY ARE EXPECTED TO DISAGREE, and by a stated amount: Engine A's waiting
  time is geometric, Engine B's is exponential, and the two differ at
  O(1/(2N)) in relative terms plus a half-generation offset in the survival
  curve. At N = 500 that is 0.1 percent. A check that demanded equality to
  many digits would be measuring the discretisation, so the A-vs-B comparison
  in C0b quotes the expected gap 1/(2N) BEFORE the measurement and fails only
  outside a stated multiple of it.

  THE BRIDGE IS MEASURED WITHIN EACH ENGINE, never across them. True history
  and harmonic surrogate are both drawn by Engine A, and both by Engine B, so
  the discretisation cancels out of the difference. The two engines must agree
  on the FINDING; they are not required to agree on the numbers to a precision
  the discretisation forbids.

POSITIVE CONTROL THAT MUST FAIL IN TWO DIRECTIONS.
  C6 displaces the population history by C6_SHIFT generations, through the
  IDENTICAL code path both engines already use (`shift_history`, whose shift
  is 0 in every other arm). That is an endpoint-convention error in the
  integration of a step function, which is the failure the family's own spec
  names.

    (i)  C1 MUST STAY BLIND. A constant history is invariant under the shift,
         so the constant-hazard mean is unchanged. This is not a courtesy: it
         demonstrates that an arm resting on the textbook constant-hazard
         result would certify a sampler whose step function is fifty
         generations out of place.
    (ii) C2 MUST FIRE. The zero-hazard window lands C6_SHIFT generations away
         from where the history declares it, so coalescence events appear
         inside an interval where the hazard is zero. C2 counts them; the
         count is an integer and must be zero uncorrupted and nonzero here.

  BOTH ARE REQUIRED. If (i) moves, the corruption was not the one described
  and the control has proved nothing. If (ii) does not fire, C2 is blind to
  the exact error it exists to catch and nothing in this file should be
  believed. C3's response to the same corruption is reported as a third
  direction and is NOT scored, because C3 is expected to move under the
  uncorrupted history too.

INSTRUMENT VERDICT AND CORPUS FINDINGS ARE SEPARATE, AND THE EXIT CODE
FOLLOWS THE INSTRUMENT.
  READ_THE_TEST is the INSTRUMENT health flag: C0, C1, C2 and C6. Those are
  the checks that can only fail because this file is broken.
  CORPUS_FINDINGS carries C3, C4 and C5 as verdict STRINGS naming which side
  lost. A corpus disagreement is a RESULT. It must not flip the harness pass
  flag, because a harness that goes red when the corpus is wrong trains its
  reader to fix the harness.

REPLICATE UNIT: THE BATCH. One record per batch, and every standard error in
  this file is the scatter ACROSS batches. A per-draw error bar would be an
  analytic claim about the estimator rather than a measurement of it.

EVERY NUMBER IS LABELLED WITH ITS ESTIMAND. Confusing two similar quantities
  cost this project an hour today. `E[T]` here is always TMRCA IN GENERATIONS
  for a pair of lineages under the named history; it is never in coalescent
  units, never a per-locus quantity, and never the between-population
  divergence time. `Ne_h` is always harmonicMeanNe over the named window T_w,
  never a census size and never an equilibrium Ne.

TRANSCRIPTION PROVENANCE
  Bodies are quoted beside their transcriptions with file and DECLARATION
  NAME and NO LINE NUMBER. Line numbers in this corpus drifted measurably
  inside one hour today and have already sent one instrument chasing
  declarations that had moved.

  Declarations read from Descent/PortabilityDrift.lean
  (integratedCoalescentHazard, coalescenceSurvivalFromHazard,
  coalescenceCdfFromHazard), Descent/DGP.lean
  (discreteRecombinationSurvival, twoLocusIBDCovariance,
  twoLocusCoalescentCovarianceMatrix, twoLocusIdx0, twoLocusIdx1) and
  Descent/LDDecayTheory.lean (harmonicMeanNe). Three of those files carried
  uncommitted edits from other sessions at transcription time; re-read them
  before trusting this transcription at a later revision.

RUNNING IT -- NOT ON A LOGIN NODE
  numpy only, Python 3.6 compatible, single-threaded by construction. The
  thread pins are set because numpy will otherwise take every core and one
  agent's contention gets misdiagnosed as another's deadlock.

      srun --time=60 --mem=8G --cpus-per-task=1 \
        env OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
        python3 validation/empirical/differential/cluster/fam_coalescent_hazard.py \
            --profile full \
            --output /projects/standard/hsiehph/sauer354/fam_coalescent_hazard_<stamp>.json \
        > /projects/standard/hsiehph/sauer354/fam_coalescent_hazard_<stamp>.out 2>&1

  CAPTURE BOTH STREAMS. A nonzero exit is a MEASUREMENT OUTCOME, not a crash:
  the report goes to stdout and the failing check names go to stderr. A probe
  harness that collected only stderr has already recorded a family of this
  shape as crashing.

  Output goes OUTSIDE /tmp, which is node-local and invisible to the next
  relay call, and carries a unique name so an absent file means not written
  rather than not written here.

  README rule, compare do not overwrite: this family has no stored result yet,
  so the first run creates one. Every run after that goes to a fresh path and
  gets diffed. A disagreement between two runs is a finding and needs both
  numbers and both revisions.
"""

import argparse
import json
import math
import os
import sys
import time

import numpy as np


def _bootstrap_simprov_path():
    """Find the directory holding `simprov.py` by WALKING UP, not by counting.

    `parents[2]`, or a fixed stack of `dirname()` calls, is a hidden dependency
    on where this file currently sits. The repository README records two
    instances of that bug in provenance and data-location code, both of which
    survived a move by returning a real but wrong path rather than raising, and
    records that four sibling scripts here bootstrap `simprov` with a fixed
    number of `dirname()` calls and survive only by moving together with it.
    This tree was reorganised today. So: ask for the thing actually wanted.
    """
    here = os.path.dirname(os.path.abspath(__file__))
    while True:
        if os.path.exists(os.path.join(here, "simprov.py")):
            return here
        parent = os.path.dirname(here)
        if parent == here:
            raise SystemExit(
                "fam_coalescent_hazard: simprov.py not found in any ancestor "
                "of %s; refusing to run without provenance stamping"
                % os.path.dirname(os.path.abspath(__file__)))
        here = parent


sys.path.insert(0, _bootstrap_simprov_path())

import simprov  # noqa: E402

SEED = 20260803

# ---------------------------------------------------------------------------
# PRIMITIVES. Census sizes and generation counts only. No hazard, no Ne_h, no
# coalescent time unit appears among the tunables: every one of those is
# DERIVED below from these.
# ---------------------------------------------------------------------------
N_LARGE = 500          # diploid census size outside the bottleneck
N_SMALL = 50           # diploid census size inside it -- a 10x bottleneck, the
                       # depth the family spec names as the CAN-FAIL condition
BOTTLENECK_START = 200  # generations before present, inclusive
BOTTLENECK_END = 300    # generations before present, exclusive
#
# WHY THE BOTTLENECK IS 100 GENERATIONS AND NOT LONGER. A deeper or longer
# bottleneck makes the bridge effect larger but drives the integrated hazard
# through the bottleneck above 1, so almost every pair coalesces inside it and
# the TAIL -- which is where the harmonic-mean surrogate and the true history
# are supposed to part company -- has too few survivors left to measure. At
# 100 generations at N_SMALL the bottleneck contributes Lambda = 1.0, which
# separates the curves by a factor of two in the median while leaving of order
# 5 percent of pairs alive at the scored window. The depth, 10x, is the spec's
# stated CAN-FAIL condition and is unchanged.
FREEZE_START = 300      # zero-hazard window for C2, inclusive
FREEZE_END = 700        # exclusive
MAX_GEN = 10000        # history length and event-loop cap; unresolved pairs
                       # are COUNTED and reported, never dropped

N_BATCH = 100          # THE REPLICATE UNIT. Every SE here is scatter across
                       # these, never a per-draw formula.
BATCH_REPS = 2000      # lineage pairs inside one batch

CENSUS_BATCHES = 40    # batches of the census pass that MEASURES 1/(2N)
CENSUS_PAIRS_LARGE = 1000000   # pairs per batch at N_LARGE
CENSUS_PAIRS_SMALL = 100000    # pairs per batch at N_SMALL

# Windows over which harmonicMeanNe is taken. The corpus never says which one,
# so the spread across this grid is itself reported.
TW_GRID = (500, 1000, 2000, 4000)
# The SCORED window, named rather than inferred from the grid's last entry.
# It is chosen so that the BLIND POINT is observable: at t = SCORED_TW the two
# integrated hazards coincide by construction, and a reader can only watch that
# happen if a measurable fraction of pairs is still uncoalesced there. At these
# sizes Lambda(2000) is about 2.9, leaving of order 5 percent alive -- enough
# to resolve the pinning. A window out at MAX_GEN would pin the curves at a
# survival of 1e-5, where the agreement is unobservable and the demonstration
# would be an assertion again.
SCORED_TW = 2000

QUANTILE_LEVELS = (0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9)

# Two-locus recombination cells, for C4.
R_GRID = (0.0, 0.001, 0.005, 0.02, 0.05)
TMRCA_GRID = (10, 50, 200)
LOCUS_BATCHES = 100
LOCUS_REPS = 20000

# Genotype sampling for C5. The allele-frequency grid spans the range where
# 2p(1-p) is largest, so the diagonal claim is tested where it comes closest
# to being satisfiable.
GENO_P_GRID = (0.1, 0.3, 0.5)
GENO_BATCHES = 100
GENO_INDIVIDUALS = 2000
GENO_W = 0.8           # ancestral two-locus association; MEASURED at r=0 and
                       # the measured value is what predicts the r>0 cells
GENO_R = 0.01
GENO_TMRCA = 50

C6_SHIFT = 50          # generations of history displacement in the positive
                       # control; large enough that C2 fires unambiguously

SEMS = 4.0             # rejection threshold, in standard errors of the batch mean

TUNABLES = {
    "N_LARGE": "diploid census size outside the bottleneck",
    "N_SMALL": "diploid census size inside the bottleneck",
    "BOTTLENECK_START": "first bottleneck generation, inclusive",
    "BOTTLENECK_END": "last bottleneck generation, exclusive",
    "FREEZE_START": "first zero-hazard generation for C2, inclusive",
    "FREEZE_END": "last zero-hazard generation for C2, exclusive",
    "MAX_GEN": "history length and event-loop cap",
    "N_BATCH": "batches per cell; the replicate unit and the error bar",
    "BATCH_REPS": "lineage pairs inside one batch",
    "CENSUS_BATCHES": "batches of the census pass that measures 1/(2N)",
    "CENSUS_PAIRS_LARGE": "parent-pair draws per census batch at N_LARGE",
    "CENSUS_PAIRS_SMALL": "parent-pair draws per census batch at N_SMALL",
    "TW_GRID": "windows T_w over which harmonicMeanNe is taken",
    "SCORED_TW": "the T_w whose bridge comparison is scored",
    "R_GRID": "per-generation recombination rates for C4",
    "TMRCA_GRID": "lineage ages for C4",
    "LOCUS_BATCHES": "batches for the two-locus recombination sim",
    "LOCUS_REPS": "lineages inside one two-locus batch",
    "GENO_P_GRID": "allele frequencies for the sampled-genotype test C5",
    "GENO_BATCHES": "batches for C5",
    "GENO_INDIVIDUALS": "diploid individuals inside one C5 batch",
    "GENO_W": "ancestral two-locus association used to build the sample",
    "GENO_R": "recombination rate for the C5 genotype sample",
    "GENO_TMRCA": "lineage age for the C5 genotype sample",
    "C6_SHIFT": "generations of history displacement in the positive control",
    "SEMS": "rejection threshold in standard errors",
}


def configure_profile(profile):
    """`full` is the registered experiment; `quick` is a bounded development run.

    Only sampling widths change. NO ESTIMAND, NO HISTORY AND NO CONVENTION
    differs between the profiles. A profile that changed what is being measured
    would make two runs of this file incomparable, which is exactly what the
    compare-do-not-overwrite rule exists to protect.
    """
    global N_BATCH, BATCH_REPS, CENSUS_BATCHES, CENSUS_PAIRS_LARGE
    global CENSUS_PAIRS_SMALL, LOCUS_BATCHES, LOCUS_REPS
    global GENO_BATCHES, GENO_INDIVIDUALS
    if profile == "full":
        return
    if profile == "deep":
        N_BATCH, BATCH_REPS = 200, 5000
        CENSUS_BATCHES = 80
        CENSUS_PAIRS_LARGE, CENSUS_PAIRS_SMALL = 2000000, 200000
        LOCUS_BATCHES, LOCUS_REPS = 200, 50000
        GENO_BATCHES, GENO_INDIVIDUALS = 200, 5000
        return
    if profile != "quick":
        raise ValueError("profile must be 'quick', 'full' or 'deep'")
    N_BATCH, BATCH_REPS = 20, 400
    CENSUS_BATCHES = 10
    CENSUS_PAIRS_LARGE, CENSUS_PAIRS_SMALL = 200000, 20000
    LOCUS_BATCHES, LOCUS_REPS = 20, 4000
    GENO_BATCHES, GENO_INDIVIDUALS = 20, 500


def apply_overrides(settings):
    """`--set NAME=VALUE` after the profile, so a profile stays a baseline."""
    applied = {}
    for s in settings:
        if "=" not in s:
            raise SystemExit("--set expects NAME=VALUE, got %r" % s)
        name, _, raw = s.partition("=")
        name = name.strip().upper()
        if name not in TUNABLES:
            raise SystemExit("--set: unknown knob %r; see --help for the list"
                             % name)
        parts = [p for p in raw.replace(",", " ").split() if p]
        vals = [float(p) if ("." in p or "e" in p.lower()) else int(p)
                for p in parts]
        value = vals[0] if len(vals) == 1 and "," not in raw else tuple(vals)
        globals()[name] = value
        applied[name] = value
    return applied


def resolved_config():
    """Every tunable as it stands, so the run is reproducible from its output."""
    out = {}
    for name in TUNABLES:
        v = globals()[name]
        out[name] = list(v) if isinstance(v, tuple) else v
    return out


# ===========================================================================
# THE CORPUS, TRANSCRIBED.
#
# Each function below is one declaration, quoted above its transcription.
# Nothing in this section computes anything the corpus does not, and nothing
# in the measurement sections calls anything but these.
# ===========================================================================

def corpus_integrated_hazard(hazard_values, dt):
    """Descent/PortabilityDrift.lean, decl `integratedCoalescentHazard`

        noncomputable def integratedCoalescentHazard (hazard : R -> R) (t : R) : R :=
          integral of s in (0)..t, hazard s

    NOT FALSIFIABLE. This is the definition of an integral. `hazard_values` is
    the step function's value on each sub-interval of width `dt`, so the
    Riemann sum below is exact for a piecewise-constant hazard, which is what
    every history in this file is. Returns the CUMULATIVE array, so
    result[k] = Lambda(k*dt), with result[0] = 0.
    """
    lam = np.asarray(hazard_values, dtype=float) * float(dt)
    return np.concatenate(([0.0], np.cumsum(lam)))


def corpus_survival(integrated):
    """Descent/PortabilityDrift.lean, decl `coalescenceSurvivalFromHazard`

        noncomputable def coalescenceSurvivalFromHazard (hazard : R -> R) (t : R) : R :=
          Real.exp (-(integratedCoalescentHazard hazard t))

    NOT FALSIFIABLE. Applying exp to a number this file computed.
    """
    return np.exp(-np.asarray(integrated, dtype=float))


def corpus_cdf(integrated):
    """Descent/PortabilityDrift.lean, decl `coalescenceCdfFromHazard`

        noncomputable def coalescenceCdfFromHazard (hazard : R -> R) (t : R) : R :=
          1 - coalescenceSurvivalFromHazard hazard t

    NOT FALSIFIABLE. Subtracting from one.
    """
    return 1.0 - corpus_survival(integrated)


def corpus_harmonic_mean_ne(ne_values):
    """Descent/LDDecayTheory.lean, decl `harmonicMeanNe`

        noncomputable def harmonicMeanNe {T : N} (Ne : Fin T -> R) : R :=
          (T : R) / sum i, (1 / Ne i)

    THIS IS THE OTHER SIDE OF THE BRIDGE. It is applied here to MEASURED Ne,
    never to the census sizes that were fed to the sampler. A frozen
    generation has infinite Ne and contributes 0 to the sum, which is what
    `1 / Ne i` gives in the limit and what the reciprocal form below computes
    directly without ever forming the infinity.
    """
    recips = np.asarray(ne_values, dtype=float)
    T = float(recips.size)
    return T / float(np.sum(recips))


def corpus_harmonic_mean_ne_from_reciprocals(recip_ne):
    """`harmonicMeanNe` with the sum of 1/Ne supplied directly.

    Used because the MEASURED reciprocal 1/Ne_hat(g) = 2 * p_hat(g) is an
    UNBIASED estimator of 1/Ne, while 1/(2 * p_hat) is not an unbiased
    estimator of Ne and is undefined when a batch records no collision. The
    corpus formula only ever reads the reciprocals, so nothing is lost and a
    division by an estimated zero is avoided. Same body, same T / sum(1/Ne).
    """
    recips = np.asarray(recip_ne, dtype=float)
    return float(recips.size) / float(np.sum(recips))


def corpus_discrete_recombination_survival(recomb_rate, tmrca):
    """Descent/DGP.lean, decl `discreteRecombinationSurvival`

        noncomputable def discreteRecombinationSurvival (recombRate : R) (tmrca : N) : R :=
          (1 - recombRate) ^ tmrca

    FALSIFIABLE. C4 walks a two-locus lineage back `tmrca` generations with an
    explicit recombination event each generation and counts survivors.
    """
    return (1.0 - float(recomb_rate)) ** int(tmrca)


def corpus_two_locus_ibd_covariance(ibd_weight, recomb_rate, tmrca):
    """Descent/DGP.lean, decl `twoLocusIBDCovariance`

        noncomputable def twoLocusIBDCovariance (ibdWeight recombRate : R) (tmrca : N) : R :=
          ibdWeight * discreteRecombinationSurvival recombRate tmrca

    FALSIFIABLE. C4 and C5. `ibdWeight` is MEASURED at recombRate = 0, where
    the survival factor is exactly 1, and the measured value is then used to
    predict every recombRate > 0 cell. Handing this formula its own ibdWeight
    would leave nothing to test but the exponent.
    """
    return (float(ibd_weight)
            * corpus_discrete_recombination_survival(recomb_rate, tmrca))


def corpus_two_locus_covariance_matrix(t, ibd_weight, recomb_rate, tmrca):
    """Descent/DGP.lean, decl `twoLocusCoalescentCovarianceMatrix`

        noncomputable def twoLocusCoalescentCovarianceMatrix {t : N} (ht : 2 <= t)
            (ibdWeight recombRate : R) (tmrca : N) : Matrix (Fin t) (Fin t) R :=
          fun i j =>
            if i = twoLocusIdx0 ht and j = twoLocusIdx1 ht then
              twoLocusIBDCovariance ibdWeight recombRate tmrca
            else if i = twoLocusIdx1 ht and j = twoLocusIdx0 ht then
              twoLocusIBDCovariance ibdWeight recombRate tmrca
            else if i = j then 1 else 0

    with `twoLocusIdx0 ht = <0, _>` and `twoLocusIdx1 ht = <1, _>` (both
    `private def` in the same file).

    FALSIFIABLE IN THREE PLACES, and C5 tests all three against a genotype
    sample rather than against the formula's own arithmetic:
      the hard 1 on the diagonal, which asserts variance standardisation;
      the (0,1) and (1,0) entries, which assert the IBD covariance;
      the zeros everywhere else, which assert the OTHER loci in the block are
        uncorrelated with each other and with the linked pair -- and that is
        where twoLocusIdx0/twoLocusIdx1 would show up if they named the wrong
        positions.
    """
    t = int(t)
    if t < 2:
        raise ValueError("twoLocusCoalescentCovarianceMatrix needs 2 <= t")
    cov = corpus_two_locus_ibd_covariance(ibd_weight, recomb_rate, tmrca)
    M = np.zeros((t, t), dtype=float)
    for i in range(t):
        M[i, i] = 1.0
    M[0, 1] = cov
    M[1, 0] = cov
    return M


# ===========================================================================
# HISTORIES. The primitives: a census size and an "can these two lineages find
# a common parent at all" flag, per generation.
#
# `active[g] = False` is an INFINITE population at generation g, so the hazard
# there is EXACTLY zero rather than merely small. C2 needs exactly zero: a
# very large finite N would make "survival is flat across the window" a
# statement about a small number, and the check would pass on a sampler that
# was slightly wrong in the same direction.
# ===========================================================================

def history_constant(n_gen=None):
    """Constant census size N_LARGE. The C1 control history."""
    T = MAX_GEN if n_gen is None else n_gen
    return {"name": "constant",
            "sizes": np.full(T, N_LARGE, dtype=np.int64),
            "active": np.ones(T, dtype=bool)}


def history_frozen_window(n_gen=None):
    """N_LARGE everywhere, with coalescence IMPOSSIBLE on [FREEZE_START, FREEZE_END).

    The C2 control history. Its content is an interval on which the corpus's
    integrated hazard must be exactly flat and on which the sampler must
    produce exactly zero events.
    """
    T = MAX_GEN if n_gen is None else n_gen
    active = np.ones(T, dtype=bool)
    active[FREEZE_START:FREEZE_END] = False
    return {"name": "frozen_window",
            "sizes": np.full(T, N_LARGE, dtype=np.int64),
            "active": active}


def history_bottleneck(n_gen=None):
    """N_LARGE outside, N_SMALL on [BOTTLENECK_START, BOTTLENECK_END).

    THE DISCRIMINATING HISTORY. The depth is 10x, which the family spec names
    as the CAN-FAIL condition: shallower and the harmonic-mean surrogate and
    the true integrated hazard would not separate in the tail by more than the
    error bars, and the run would decide nothing while looking like a pass.
    """
    T = MAX_GEN if n_gen is None else n_gen
    sizes = np.full(T, N_LARGE, dtype=np.int64)
    sizes[BOTTLENECK_START:BOTTLENECK_END] = N_SMALL
    return {"name": "bottleneck",
            "sizes": sizes,
            "active": np.ones(T, dtype=bool)}


def history_constant_at(ne_h):
    """The HARMONIC-MEAN SURROGATE: a constant population of size Ne_h.

    Ne_h is a MEASURED real number, not an integer census count, so the
    gene-copy pool 2*Ne_h is not an integer either. Engine A draws parent
    INDICES, and an index draw needs an integer pool. Rounding would shift the
    per-generation coalescence probability by up to 0.5/(2 Ne_h) -- 0.1 percent
    at these sizes, which is the same order as the bridge effect in the body
    of the distribution and would contaminate exactly the comparison this file
    exists to make.

    So the pool size is RANDOMISED per generation between k = floor(2 Ne_h)
    and k+1, with the probability q chosen so that the per-generation
    collision probability is EXACTLY 1/(2 Ne_h):

        q/(k+1) + (1-q)/k = 1/(2 Ne_h)
        =>  q = (1/k - 1/(2 Ne_h)) / (1/k - 1/(k+1))

    and 1/(k+1) <= 1/(2 Ne_h) <= 1/k puts q in [0,1]. The surrogate therefore
    goes through Engine A's IDENTICAL parent-draw path as the true history --
    no Bernoulli shortcut, no formula substituted for the process -- which is
    the only way the true-minus-surrogate difference is free of a code-path
    difference.

    The sizes array is filled at draw time by `wf_sample`, which is why this
    returns a marker rather than a fixed size vector.
    """
    two_ne = 2.0 * float(ne_h)
    k = int(math.floor(two_ne))
    if k < 2:
        raise ValueError("harmonic-mean surrogate needs 2*Ne_h >= 2, got %r"
                         % two_ne)
    denom = (1.0 / k) - (1.0 / (k + 1))
    q = ((1.0 / k) - (1.0 / two_ne)) / denom if denom > 0 else 0.0
    q = min(1.0, max(0.0, q))
    return {"name": "harmonic_surrogate",
            "sizes": None,
            "active": np.ones(MAX_GEN, dtype=bool),
            "randomized_pool": (k, k + 1, q),
            "two_ne": two_ne}


def shift_history(hist, shift):
    """Displace a history by `shift` generations. THE CORRUPTION PATH.

    `shift` is 0 in every arm except C6, and BOTH engines read the history
    through this function, so the corrupted run differs from the clean run in
    the value of one integer and in nothing else. A positive control that
    reached its corruption by a second code path would be testing the second
    code path.

    A constant history is invariant under this, which is the blindness C6
    requires C1 to exhibit.
    """
    if not shift:
        return hist
    if hist["sizes"] is None:
        # The surrogate is constant, hence invariant. Returned unchanged and
        # recorded as such rather than silently.
        out = dict(hist)
        out["shift_applied"] = int(shift)
        out["shift_is_identity"] = True
        return out
    out = dict(hist)
    out["sizes"] = np.roll(hist["sizes"], shift)
    out["active"] = np.roll(hist["active"], shift)
    out["shift_applied"] = int(shift)
    out["shift_is_identity"] = bool(
        np.array_equal(out["sizes"], hist["sizes"])
        and np.array_equal(out["active"], hist["active"]))
    return out


# ===========================================================================
# THE CENSUS PASS -- where 1/(2N) is MEASURED rather than asserted.
#
# For each distinct census size in the histories, draw pairs of parent indices
# from the gene-copy pool and count collisions. p_hat is the measured
# per-generation coalescence probability, one value per BATCH, so the error
# bar is batch scatter.
#
# This is the step that makes the bridge a measurement. If this file took
# Ne(g) = the census size it had just written into the history, the harmonic
# mean would be an input and C3 would be checking that a formula reproduces a
# number it was handed.
# ===========================================================================

def measure_recip_two_ne(census_size, pairs_per_batch, batches, rng):
    """Measured 1/Ne for a population of `census_size` diploids, per batch.

    Returns a list of per-batch estimates of 1/Ne = 2 * p_hat, where p_hat is
    the measured probability that two lineages drawn independently from the
    gene-copy pool have the same parent.

    THE RECIPROCAL IS WHAT IS ESTIMATED, and deliberately: 2*p_hat is unbiased
    for 1/Ne, whereas 1/(2*p_hat) is biased for Ne and undefined for a batch
    that happened to record no collision. `harmonicMeanNe` reads only the
    reciprocals, so this loses nothing.
    """
    two_n = 2 * int(census_size)
    out = []
    for _ in range(int(batches)):
        a = rng.integers(0, two_n, int(pairs_per_batch))
        b = rng.integers(0, two_n, int(pairs_per_batch))
        p_hat = float(np.count_nonzero(a == b)) / float(pairs_per_batch)
        out.append(2.0 * p_hat)
    return out


def measured_recip_ne_trajectory(hist, recip_by_size):
    """1/Ne_hat for every generation of a history, from the census pass.

    A frozen generation gets 1/Ne = 0 exactly -- the reciprocal of an infinite
    population -- which is what `harmonicMeanNe` needs and what the sampler
    actually does there.
    """
    sizes = hist["sizes"]
    recips = np.zeros(sizes.size, dtype=float)
    for size, val in recip_by_size.items():
        recips[sizes == size] = val
    recips[~hist["active"]] = 0.0
    return recips


# ===========================================================================
# ENGINE A -- WRIGHT-FISHER. Discrete generations, parent indices, collisions.
#
# Contains no hazard, no exponential and no integral. It is the primitive
# process this family's other reading is supposed to describe.
# ===========================================================================

def wf_sample(hist, n, rng):
    """TMRCA IN GENERATIONS for `n` independent lineage pairs under `hist`.

    Returns (tmrca, resolved). Pairs still alive at MAX_GEN are returned with
    resolved = False and are COUNTED by the caller; they are never set to the
    cap, because a cell with censoring is a different measurement from a cell
    without and a bare mean cannot tell them apart.

    THE SAMPLER CANNOT PRODUCE AN EVENT IN ITS OWN INACTIVE GENERATIONS, by
    construction: it makes no draw there. So the zero-hazard count that C2
    needs is NOT taken from here. C2 recounts the returned times against the
    window the HISTORY FILE DECLARES, which is what makes the C6 displacement
    visible: the sampler faithfully follows the history it was given, and the
    check compares that against the window that was declared. A count taken
    inside the sampler would be zero under the corruption too, and the positive
    control would silently prove nothing.
    """
    T = hist["active"].size
    tmrca = np.zeros(n, dtype=np.int64)
    resolved = np.zeros(n, dtype=bool)
    idx = np.arange(n)
    pool = hist.get("randomized_pool")
    sizes = hist["sizes"]
    active = hist["active"]
    for g in range(min(T, MAX_GEN)):
        if idx.size == 0:
            break
        if not active[g]:
            # Infinite population: the two lineages cannot share a parent. No
            # draw is made, which is what makes the hazard EXACTLY zero rather
            # than a very small number.
            continue
        if pool is not None:
            k_lo, k_hi, q = pool
            two_n = k_hi if rng.random() < q else k_lo
        else:
            two_n = 2 * int(sizes[g])
        a = rng.integers(0, two_n, idx.size)
        b = rng.integers(0, two_n, idx.size)
        hit = (a == b)
        if hit.any():
            sel = idx[hit]
            tmrca[sel] = g + 1
            resolved[sel] = True
            idx = idx[~hit]
    return tmrca, resolved


def wf_batches(hist, rng, n_batch=None, batch_reps=None):
    """One record per BATCH. The batch is the replicate unit and the error bar.

    Returns a list of per-batch dicts, each carrying that batch's resolved
    TMRCA array. Per-batch rather than per-draw records: several hundred
    thousand rows per cell is not a measurement anyone can diff, and the
    scatter the error bar has to describe is carried entirely by the batch
    summaries.
    """
    nb = N_BATCH if n_batch is None else int(n_batch)
    br = BATCH_REPS if batch_reps is None else int(batch_reps)
    out = []
    for _ in range(nb):
        tm, res = wf_sample(hist, br, rng)
        out.append({"tmrca": tm[res].astype(float),
                    "n_drawn": br,
                    "n_resolved": int(res.sum())})
    return out


# ===========================================================================
# ENGINE B -- INTEGRATED HAZARD. Continuous time, inverse transform on Lambda.
#
# SHARES NO CODE WITH ENGINE A. It draws Exp(1) variates and inverts the
# corpus's own integrated hazard; Engine A draws integer parent indices and
# never forms Lambda. Nothing but the measured 1/Ne trajectory passes between
# them.
#
# EXPECTED DISAGREEMENT WITH ENGINE A: Engine A's waiting time is geometric
# with mean exactly 2N generations; Engine B's is exponential with mean
# exactly 2N. The MEANS agree exactly. The SURVIVAL CURVES differ by the
# within-generation offset, at relative order 1/(2N) -- 0.1 percent at
# N_LARGE. C0b states that expected gap before measuring it.
# ===========================================================================

def hazard_from_recip(recip_ne):
    """Per-generation hazard 1/(2 Ne(g)) from the MEASURED reciprocal 1/Ne(g).

    The factor of two is the diploid gene-copy count and is the only piece of
    population-genetic convention Engine B carries; it is the same factor
    Engine A realises by drawing from a pool of 2N copies, arrived at
    independently in each engine.
    """
    return 0.5 * np.asarray(recip_ne, dtype=float)


def hazard_sample(recip_ne, n, rng):
    """TMRCA in GENERATIONS by inverse transform on the integrated hazard.

    Lambda is piecewise linear because the hazard is piecewise constant, so
    the inversion inside the crossing generation is EXACT and not an
    approximation. Draws that exceed Lambda(MAX_GEN) are unresolved and are
    returned as such.
    """
    lam = hazard_from_recip(recip_ne)
    Lam = corpus_integrated_hazard(lam, 1.0)   # Lam[g] = Lambda(g)
    E = rng.exponential(1.0, int(n))
    j = np.searchsorted(Lam, E, side="right") - 1
    resolved = j < lam.size
    jj = np.clip(j, 0, lam.size - 1)
    rate = lam[jj]
    frac = np.where(rate > 0.0, (E - Lam[jj]) / np.where(rate > 0.0, rate, 1.0),
                    0.0)
    t = jj.astype(float) + frac
    return t, resolved


def hazard_batches(recip_ne, rng, n_batch=None, batch_reps=None):
    """One record per batch, same replicate unit as Engine A."""
    nb = N_BATCH if n_batch is None else int(n_batch)
    br = BATCH_REPS if batch_reps is None else int(batch_reps)
    out = []
    for _ in range(nb):
        t, res = hazard_sample(recip_ne, br, rng)
        out.append({"tmrca": t[res], "n_drawn": br,
                    "n_resolved": int(res.sum())})
    return out


# ===========================================================================
# BATCH STATISTICS. Every one of these returns a per-batch list; the SE is
# always simprov.summarize's scatter across those, never a per-draw formula.
# ===========================================================================

def batch_means(batches):
    return [float(b["tmrca"].mean()) if b["tmrca"].size else float("nan")
            for b in batches]


def batch_quantiles(batches, level):
    return [float(np.quantile(b["tmrca"], level)) if b["tmrca"].size
            else float("nan") for b in batches]


def batch_survival(batches, t):
    """Per-batch S(t) = fraction of DRAWN pairs with TMRCA > t.

    The denominator is n_drawn, not n_resolved, so an unresolved pair counts
    as still surviving -- which it is. Using the resolved count would silently
    renormalise the tail away, and the tail is the whole subject of C3.
    """
    return [float(np.count_nonzero(b["tmrca"] > t) + (b["n_drawn"]
                                                     - b["n_resolved"]))
            / float(b["n_drawn"]) for b in batches]


def unresolved_fraction(batches):
    drawn = sum(b["n_drawn"] for b in batches)
    res = sum(b["n_resolved"] for b in batches)
    return float(drawn - res) / float(drawn) if drawn else 1.0


def events_in_window(batches, lo, hi):
    """COUNT of coalescences with lo < TMRCA <= hi, summed over batches.

    An INTEGER, deliberately. C2's claim is that a zero-hazard interval
    contains exactly zero events; "flat within the error bars" would pass a
    sampler that put a handful of events in the window.
    """
    return int(sum(np.count_nonzero((b["tmrca"] > lo) & (b["tmrca"] <= hi))
                   for b in batches))


def diff_sems(sa, sb):
    """|mean_a - mean_b| in standard errors of the DIFFERENCE.

    The two arms are drawn independently, so the SEs add in quadrature.
    """
    if sa["mean"] is None or sb["mean"] is None:
        return float("inf")
    se = math.sqrt((sa["se"] or 0.0) ** 2 + (sb["se"] or 0.0) ** 2)
    return abs(sa["mean"] - sb["mean"]) / max(se, 1e-12)


# ===========================================================================
# CHECKS
# ===========================================================================

def c0(recip_by_size, out):
    """C0  THE THREE UNFALSIFIABLE MEMBERS, AND AN A-vs-B ENGINE CROSS-CHECK.

    C0a  integratedCoalescentHazard, coalescenceSurvivalFromHazard and
         coalescenceCdfFromHazard, exercised on the bottleneck history.

         THIS CANNOT FALSIFY THE CORPUS AND IS NOT REPORTED AS EVIDENCE FOR
         IT. S = exp(-Lambda) and F = 1 - S are the definitions of those two
         declarations; a simulator that "confirms" them has measured its own
         quadrature. C0a is retained because it CAN fail -- if this file's
         cumulative sum, its endpoint convention or its step-function indexing
         is wrong, C0a goes red -- and a failure there means the INSTRUMENT is
         broken, which is exactly what the instrument flag is for.

         The comparison is against an independent dense Riemann sum of the
         same step function on a 10x finer grid. That is a check of this
         file's arithmetic against this file's other arithmetic. It is not a
         check of the corpus.

    C0b  ENGINE A vs ENGINE B on the constant history, with the expected
         disagreement STATED FIRST. Geometric and exponential waiting times
         have the same mean 2N exactly, so the means must agree within the
         batch error bars; the survival curves differ at relative order
         1/(2 N_LARGE), quoted below before the numbers are printed. A check
         that demanded curve equality would be measuring the discretisation
         and would fail a correct pair of engines.
    """
    print("")
    print("=" * 78)
    print("C0  INSTRUMENT SELF-TEST -- three members that CANNOT be falsified")
    print("=" * 78)
    print("  S = exp(-Lambda) and F = 1 - S are DEFINITIONS. Agreement below is")
    print("  a statement about this file's integrator. It is NOT evidence for")
    print("  the corpus and is excluded by name from CORPUS_FINDINGS.")

    hist = history_bottleneck()
    recip = measured_recip_ne_trajectory(hist, recip_by_size)
    lam = hazard_from_recip(recip)
    Lam = corpus_integrated_hazard(lam, 1.0)
    S = corpus_survival(Lam)
    F = corpus_cdf(Lam)

    # Independent dense Riemann sum of the same step function.
    sub = 10
    dense = np.repeat(lam, sub)
    Lam_dense = corpus_integrated_hazard(dense, 1.0 / sub)[::sub]
    lam_err = float(np.max(np.abs(Lam - Lam_dense)))
    comp_err = float(np.max(np.abs(S + F - 1.0)))
    exp_err = float(np.max(np.abs(S - np.exp(-Lam))))
    a_ok = lam_err < 1e-10 and comp_err < 1e-12 and exp_err < 1e-15
    print("  C0a  max |Lambda - dense Riemann| = %.3e   max |S + F - 1| = %.3e"
          % (lam_err, comp_err))
    print("       integrator %s -- INSTRUMENT ONLY" % ("ok" if a_ok else "FAIL"))

    out["C0"] = {
        "integrator_max_abs_error": lam_err,
        "cdf_complement_max_abs_error": comp_err,
        "survival_exp_max_abs_error": exp_err,
        "falsifiable": False,
        "why_not_falsifiable":
            "integratedCoalescentHazard, coalescenceSurvivalFromHazard and "
            "coalescenceCdfFromHazard are the definition of survival from a "
            "hazard. A simulator that confirms them has measured its own "
            "integrator. Scored into the INSTRUMENT flag only; excluded from "
            "CORPUS_FINDINGS by name.",
        "pass": bool(a_ok)}
    return a_ok


def c0b(rng, recip_by_size, out):
    """C0b  ENGINE A vs ENGINE B, with the expected gap declared in advance."""
    print("")
    print("=" * 78)
    print("C0b ENGINE A (Wright-Fisher) vs ENGINE B (integrated hazard)")
    print("=" * 78)
    expected_rel_gap = 1.0 / (2.0 * N_LARGE)
    print("  DECLARED BEFORE MEASURING: geometric and exponential waiting times")
    print("  share the mean 2N exactly, so E[TMRCA] must agree; the survival")
    print("  curves differ at relative order 1/(2N) = %.4f. A check demanding"
          % expected_rel_gap)
    print("  curve equality would be measuring the discretisation.")

    hist = history_constant()
    recip = measured_recip_ne_trajectory(hist, recip_by_size)
    a = wf_batches(hist, rng)
    b = hazard_batches(recip, rng)
    sa = simprov.summarize(batch_means(a))
    sb = simprov.summarize(batch_means(b))
    sems = diff_sems(sa, sb)
    ok = sems <= SEMS
    print("  E[TMRCA] generations: engine A %.3f +-%.3f | engine B %.3f +-%.3f"
          "  (%.2f sems)  %s"
          % (sa["mean"], sa["se"] or 0.0, sb["mean"], sb["se"] or 0.0, sems,
             "ok" if ok else "FAIL"))
    out["C0b"] = {"engine_a_ETMRCA_generations": sa,
                  "engine_b_ETMRCA_generations": sb,
                  "difference_sems": sems,
                  "expected_relative_gap_in_survival_curve": expected_rel_gap,
                  "estimand": "E[TMRCA] in GENERATIONS for a lineage pair "
                              "under the constant history at N_LARGE",
                  "pass": bool(ok)}
    return ok


def c1(rng, recip_by_size, out, shift=0, label="C1"):
    """C1  CONSTANT-HAZARD CONTROL -- isolates the sampler from the integration.

    From the family's own spec: a constant hazard must give the textbook mean
    2*N_LARGE generations. Both engines must return it.

    THIS CONTROL IS BLIND TO AN ENDPOINT-CONVENTION ERROR, and that is the
    point. A constant history is invariant under `shift_history`, so a sampler
    whose step function is fifty generations out of place passes C1 unharmed.
    C6 runs exactly that sampler and requires C2 to catch what C1 cannot. A
    control that could catch it would not be isolating the sampler.

    The predicted 2*N_LARGE is NOT taken from the census input: it is
    2 / (measured 1/Ne), the measured value inverted, so a census pass that
    was systematically wrong would move the prediction with the measurement
    and this check would still be comparing like with like. The census input
    is printed beside it so a divergence is visible.
    """
    print("")
    print("=" * 78)
    print("%s  CONSTANT-HAZARD CONTROL -- E[TMRCA] = 2*Ne generations" % label)
    if shift:
        print("     (history displaced by %d generations; a CONSTANT history is"
              % shift)
        print("      invariant under that, so this check MUST NOT MOVE)")
    print("=" * 78)
    hist = shift_history(history_constant(), shift)
    recip = measured_recip_ne_trajectory(hist, recip_by_size)
    ne_measured = 1.0 / float(recip[0]) if recip[0] > 0 else float("inf")
    pred = 2.0 * ne_measured

    a = wf_batches(hist, rng)
    b = hazard_batches(recip, rng)
    sa = simprov.summarize(batch_means(a))
    sb = simprov.summarize(batch_means(b))
    ua, ub = unresolved_fraction(a), unresolved_fraction(b)
    da = abs(sa["mean"] - pred) / max(sa["se"] or 0.0, 1e-12)
    db = abs(sb["mean"] - pred) / max(sb["se"] or 0.0, 1e-12)
    ok = da <= SEMS and db <= SEMS and ua < 0.01 and ub < 0.01
    print("  measured Ne from the census pass = %.3f (census input %d)"
          % (ne_measured, N_LARGE))
    print("  predicted E[TMRCA] = 2*Ne_measured = %.3f generations" % pred)
    print("  engine A %.3f +-%.3f (%.2f sems) | engine B %.3f +-%.3f (%.2f sems)"
          "  %s" % (sa["mean"], sa["se"] or 0.0, da,
                    sb["mean"], sb["se"] or 0.0, db, "ok" if ok else "FAIL"))
    print("  unresolved at %d generations: A %.5f  B %.5f  (COUNTED, not dropped)"
          % (MAX_GEN, ua, ub))
    res = {"shift": int(shift),
           "shift_is_identity": bool(hist.get("shift_is_identity", True)),
           "measured_Ne": ne_measured,
           "census_input_N": N_LARGE,
           "predicted_ETMRCA_generations": pred,
           "engine_a": sa, "engine_b": sb,
           "engine_a_sems": da, "engine_b_sems": db,
           "unresolved_fraction_a": ua, "unresolved_fraction_b": ub,
           "batch_means_a": batch_means(a), "batch_means_b": batch_means(b),
           "estimand": "E[TMRCA] in GENERATIONS, constant history",
           "pass": bool(ok)}
    out[label] = res
    return ok, res


def c2(rng, recip_by_size, out, shift=0, label="C2"):
    """C2  ZERO-HAZARD CONTROL -- isolates the integration from the sampler.

    From the family's own spec: survival across an interval of zero hazard
    must be EXACTLY flat. The statistic is an INTEGER COUNT of coalescence
    events that landed inside [FREEZE_START, FREEZE_END). It must be exactly
    zero. An integer count is used rather than a difference of two estimated
    survival probabilities because "flat within the error bars" would pass a
    sampler that put a handful of events in the window.

    WHY THIS AND C1 ARE BOTH NEEDED. A sampler that integrates a step function
    with the wrong endpoint convention still reproduces the constant-hazard
    mean. C1 cannot see it; C2 is the check that can. The two together pin the
    draw and the integral separately, which is the point of the split.

    C2 also reports the integrated hazard's own flatness across the window --
    Lambda(FREEZE_END) - Lambda(FREEZE_START), which must be exactly 0 -- so
    that a discrepancy can be attributed to the sampler or to the integration
    rather than to the pair.
    """
    print("")
    print("=" * 78)
    print("%s  ZERO-HAZARD CONTROL -- exactly zero events on [%d, %d)"
          % (label, FREEZE_START, FREEZE_END))
    if shift:
        print("     (history displaced by %d generations; this check MUST FIRE)"
              % shift)
    print("=" * 78)
    declared = history_frozen_window()
    hist = shift_history(declared, shift)
    recip_actual = measured_recip_ne_trajectory(hist, recip_by_size)

    # The sampler follows the history it was given; the window the check reads
    # is the one the history file DECLARES. That is what makes the C6 shift
    # visible. Counting inside the sampler would report zero under the
    # corruption too, because the sampler makes no draw in its own inactive
    # generations, and the positive control would prove nothing.
    batches = wf_batches(hist, rng)
    events = events_in_window(batches, FREEZE_START, FREEZE_END)
    lam = hazard_from_recip(recip_actual)
    Lam = corpus_integrated_hazard(lam, 1.0)
    lam_gap = float(Lam[FREEZE_END] - Lam[FREEZE_START])

    # Engine B, same declared window, same reasoning.
    tb, resb = hazard_sample(recip_actual, N_BATCH * BATCH_REPS, rng)
    events_b = int(np.count_nonzero(resb & (tb > FREEZE_START)
                                    & (tb <= FREEZE_END)))

    fired = events > 0 or events_b > 0 or lam_gap > 0.0
    ok = (not fired) if not shift else fired
    print("  engine A coalescences inside the declared window: %d" % events)
    print("  engine B coalescences inside the declared window: %d" % events_b)
    print("  Lambda(%d) - Lambda(%d) = %.6e  (must be exactly 0 uncorrupted)"
          % (FREEZE_END, FREEZE_START, lam_gap))
    if shift:
        print("  positive control: %s"
              % ("FIRED as required" if fired else "DID NOT FIRE -- C2 is blind "
                 "to the error it exists to catch"))
    else:
        print("  %s" % ("ok" if ok else "FAIL -- events in a zero-hazard window"))
    res = {"shift": int(shift),
           "declared_window": [FREEZE_START, FREEZE_END],
           "engine_a_events_in_window": events,
           "engine_b_events_in_window": events_b,
           "integrated_hazard_gap_across_window": lam_gap,
           "fired": bool(fired),
           "estimand": "COUNT of pair coalescences landing in the declared "
                       "zero-hazard window; an integer, not a rate",
           "pass": bool(ok)}
    out[label] = res
    return ok, res


def c3(rng, recip_by_size, out, shift=0, label="C3"):
    """C3  THE BRIDGE. The one falsifiable claim in this family.

    THE CLAIM UNDER TEST, stated so it can lose: the constant-size population
    of size Ne_h = harmonicMeanNe(measured Ne trajectory) has the SAME TMRCA
    DISTRIBUTION as the true bottleneck history.

    THE STATISTIC IS DISTRIBUTIONAL AND IT HAS TO BE. The harmonic mean pins
    Lambda_true(T_w) = Lambda_surrogate(T_w) identically, so the survival
    curves CROSS at the window endpoint by construction and a summary
    statistic dominated by that agreement cannot separate them. Scored:
      quantiles from the 10th to the 90th percentile, per batch;
      the survival curve compared POINTWISE at a grid of times, per batch.
    Reported and NOT scored:
      t = T_w, the constitutionally blind point, printed so the pinning is
        visible rather than argued;
      E[TMRCA], the near-blind statistic, so a reader can see for themselves
        whether a mean-only comparison would have decided anything.

    Ne_h IS DERIVED. It comes from `corpus_harmonic_mean_ne_from_reciprocals`
    applied to the MEASURED 1/Ne trajectory, whose per-generation values came
    out of the census pass's parent-collision counts. The census sizes that
    built the history are printed beside it, and if the two disagree that is a
    fact about the census pass, not an input to the check.

    THE WINDOW IS SWEPT. `harmonicMeanNe` takes Ne over Fin T and the corpus
    never says which T. Ne_h is reported at every T_w in TW_GRID; the SCORED
    cell is the full history, named in the output. That the surrogate's answer
    depends on the window is a finding in its own right and is recorded as
    one.

    BOTH ENGINES RUN THE COMPARISON, each against its own surrogate, so the
    Wright-Fisher discretisation cancels out of the difference. The engines
    must agree on the FINDING; they are not required to agree on the numbers
    to a precision the discretisation forbids.

    THIS IS A CORPUS FINDING, NOT AN INSTRUMENT CHECK. Its verdict does not
    touch READ_THE_TEST.
    """
    print("")
    print("=" * 78)
    print("%s  THE BRIDGE -- does harmonicMeanNe reproduce the TMRCA "
          "DISTRIBUTION?" % label)
    if shift:
        print("     (history displaced by %d generations; reported, NOT scored)"
              % shift)
    print("=" * 78)

    hist = shift_history(history_bottleneck(), shift)
    recip = measured_recip_ne_trajectory(hist, recip_by_size)

    # Ne_h at every window, derived from the MEASURED trajectory.
    window_rows = []
    for tw in TW_GRID:
        tw = int(tw)
        if tw > recip.size:
            continue
        ne_h = corpus_harmonic_mean_ne_from_reciprocals(recip[:tw])
        window_rows.append({"T_w": tw, "Ne_h_measured": ne_h})
        print("  harmonicMeanNe over T_w=%-6d -> Ne_h = %.3f generations-worth "
              "of drift" % (tw, ne_h))
    scored_tw = int(SCORED_TW)
    if scored_tw > recip.size:
        raise SystemExit("SCORED_TW exceeds MAX_GEN; the scored window must lie "
                         "inside the simulated history")
    ne_h = corpus_harmonic_mean_ne_from_reciprocals(recip[:scored_tw])
    # The corpus body, T / sum(1/Ne), evaluated on the inverted reciprocals as
    # literally written. The bottleneck history has no frozen generations, so
    # every Ne is finite and the two spellings must agree exactly; this is a
    # transcription check on the reciprocal shortcut and nothing more.
    ne_h_literal = corpus_harmonic_mean_ne(1.0 / recip[:scored_tw])
    literal_gap = abs(ne_h - ne_h_literal) / max(abs(ne_h), 1e-12)
    print("  SCORED WINDOW: T_w = %d, Ne_h = %.4f  (literal harmonicMeanNe "
          "body gives %.4f, relative gap %.2e)"
          % (scored_tw, ne_h, ne_h_literal, literal_gap))
    print("  census inputs were N_LARGE=%d, N_SMALL=%d on [%d,%d) -- printed for"
          % (N_LARGE, N_SMALL, BOTTLENECK_START, BOTTLENECK_END))
    print("  comparison only; Ne_h above came from the MEASURED trajectory.")
    spread = (max(w["Ne_h_measured"] for w in window_rows)
              / min(w["Ne_h_measured"] for w in window_rows)) \
        if window_rows else float("nan")
    print("  WINDOW DEPENDENCE: Ne_h varies by a factor %.3f across TW_GRID. "
          % spread)
    print("  The corpus does not say which T_w harmonicMeanNe is taken over.")

    surrogate = history_constant_at(ne_h)
    recip_surr = np.full(recip.size, 1.0 / ne_h)

    a_true = wf_batches(hist, rng)
    a_surr = wf_batches(surrogate, rng)
    b_true = hazard_batches(recip, rng)
    b_surr = hazard_batches(recip_surr, rng)

    u = max(unresolved_fraction(a_true), unresolved_fraction(a_surr),
            unresolved_fraction(b_true), unresolved_fraction(b_surr))
    max_level = max(QUANTILE_LEVELS)
    censoring_ok = u < (1.0 - max_level) / 4.0
    if not censoring_ok:
        print("  RUN FAILURE: unresolved fraction %.4f is too large for the "
              "%.2f quantile to be defined; raise MAX_GEN." % (u, max_level))

    arms = (("engine_A_wright_fisher", a_true, a_surr),
            ("engine_B_integrated_hazard", b_true, b_surr))
    engine_out = {}
    fired_any = {}
    for eng, tr, su in arms:
        print("  --- %s ---" % eng)
        qrows = []
        fired = False
        for lev in QUANTILE_LEVELS:
            st = simprov.summarize(batch_quantiles(tr, lev))
            ss = simprov.summarize(batch_quantiles(su, lev))
            sems = diff_sems(st, ss)
            rel = ((st["mean"] - ss["mean"]) / ss["mean"]
                   if ss["mean"] else float("nan"))
            fired = fired or sems > SEMS
            qrows.append({"level": lev,
                          "true_history_quantile_generations": st,
                          "harmonic_surrogate_quantile_generations": ss,
                          "difference_sems": sems,
                          "relative_difference": rel})
            print("    q%.2f  true %9.2f +-%6.2f | surrogate %9.2f +-%6.2f | "
                  "%+7.2f%%  %6.2f sems"
                  % (lev, st["mean"], st["se"] or 0.0, ss["mean"],
                     ss["se"] or 0.0, 100.0 * rel, sems))

        # Pointwise survival. The blind point t = T_w is included in the grid,
        # marked, and EXCLUDED from the scoring.
        grid = sorted(set([50, 100, BOTTLENECK_START, BOTTLENECK_END,
                           BOTTLENECK_END + 200, 800, 1200,
                           scored_tw // 2, scored_tw]))
        srows = []
        for t in grid:
            st = simprov.summarize(batch_survival(tr, t))
            ss = simprov.summarize(batch_survival(su, t))
            sems = diff_sems(st, ss)
            blind = (t == scored_tw)
            if not blind:
                fired = fired or sems > SEMS
            srows.append({"t_generations": t,
                          "true_history_survival": st,
                          "harmonic_surrogate_survival": ss,
                          "difference_sems": sems,
                          "blind_by_construction": bool(blind),
                          "scored": not blind})
            print("    S(%-5d) true %.5f +-%.5f | surrogate %.5f +-%.5f | "
                  "%6.2f sems%s"
                  % (t, st["mean"], st["se"] or 0.0, ss["mean"],
                     ss["se"] or 0.0, sems,
                     "   <- BLIND BY CONSTRUCTION, NOT SCORED" if blind else ""))

        mt = simprov.summarize(batch_means(tr))
        ms = simprov.summarize(batch_means(su))
        mean_sems = diff_sems(mt, ms)
        print("    E[TMRCA] true %.2f +-%.2f | surrogate %.2f +-%.2f | %.2f "
              "sems   <- NEAR-BLIND STATISTIC, REPORTED NOT SCORED"
              % (mt["mean"], mt["se"] or 0.0, ms["mean"], ms["se"] or 0.0,
                 mean_sems))
        engine_out[eng] = {
            "quantiles": qrows, "survival": srows,
            "mean_true_generations": mt,
            "mean_surrogate_generations": ms,
            "mean_difference_sems": mean_sems,
            "mean_is_scored": False,
            "distribution_differs": bool(fired)}
        fired_any[eng] = fired

    engines_agree = (fired_any["engine_A_wright_fisher"]
                     == fired_any["engine_B_integrated_hazard"])
    differs = all(fired_any.values())
    same = not any(fired_any.values())
    if not engines_agree:
        verdict = ("UNDECIDED -- the two engines disagree on whether the "
                   "distributions differ. This is a failure of the RUN, not a "
                   "finding about the corpus.")
    elif differs:
        verdict = ("THE HARMONIC-MEAN Ne DOES NOT REPRODUCE THE TMRCA "
                   "DISTRIBUTION of the integrated hazard under a %dx "
                   "bottleneck. harmonicMeanNe LOSES as a distributional "
                   "surrogate; the corpus's drift-retention work that "
                   "substitutes Ne_h for a trajectory is making a claim about "
                   "the mean, not about the distribution."
                   % (N_LARGE // N_SMALL))
    elif same:
        verdict = ("THE HARMONIC-MEAN Ne REPRODUCES THE TMRCA DISTRIBUTION to "
                   "within %.0f standard errors at every scored quantile and "
                   "time point. harmonicMeanNe SURVIVES as a distributional "
                   "surrogate at this bottleneck depth." % SEMS)
    else:
        verdict = "UNDECIDED"
    print("  VERDICT: %s" % verdict)

    res = {"shift": int(shift),
           "scored_T_w": scored_tw,
           "Ne_h_measured_at_scored_window": ne_h,
           "Ne_h_from_literal_harmonicMeanNe_body": ne_h_literal,
           "Ne_h_transcription_relative_gap": literal_gap,
           "Ne_h_by_window": window_rows,
           "Ne_h_window_dependence_ratio": spread,
           "census_inputs": {"N_LARGE": N_LARGE, "N_SMALL": N_SMALL,
                             "bottleneck": [BOTTLENECK_START, BOTTLENECK_END]},
           "surrogate_randomized_pool": list(surrogate["randomized_pool"]),
           "max_unresolved_fraction": u,
           "censoring_ok": bool(censoring_ok),
           "engines": engine_out,
           "engines_agree_on_finding": bool(engines_agree),
           "verdict": verdict,
           "estimand": "TMRCA DISTRIBUTION in GENERATIONS for a lineage pair, "
                       "true bottleneck history vs a constant population at "
                       "harmonicMeanNe of the MEASURED Ne trajectory",
           "is_corpus_finding": True,
           "run_ok": bool(censoring_ok and engines_agree)}
    out[label] = res
    return res


def c4(rng, out):
    """C4  discreteRecombinationSurvival AND twoLocusIBDCovariance.

    FALSIFIABLE. A two-locus lineage is walked back generation by generation.
    Each generation the two loci are separated onto different parental
    chromosomes with probability r, independently; once separated they stay
    separated. The measured survival probability after tmrca generations is
    compared to (1-r)^tmrca.

    THE ibdWeight IS MEASURED, NOT SUPPLIED. twoLocusIBDCovariance is
    w * (1-r)^tmrca, and handing it w would leave only the exponent under
    test. So w is measured in the r = 0 cell -- where the survival factor is
    exactly 1, so the measured covariance IS w -- and the measured w then
    predicts every r > 0 cell.

    r = 0 IS THEREFORE A CALIBRATION CELL AND NOT A TEST. It is marked as such
    in the output. Reporting it as a passing check would be reporting that a
    number equals itself.
    """
    print("")
    print("=" * 78)
    print("C4  discreteRecombinationSurvival AND twoLocusIBDCovariance")
    print("=" * 78)
    print("  ibdWeight is MEASURED in the r=0 cell and then PREDICTS r>0.")
    print("  The r=0 cell is a CALIBRATION, not a test, and is marked so.")

    def survival_batches(r, tmrca, rng):
        vals = []
        for _ in range(LOCUS_BATCHES):
            intact = np.ones(LOCUS_REPS, dtype=bool)
            for _g in range(int(tmrca)):
                if r > 0.0:
                    intact &= (rng.random(LOCUS_REPS) >= r)
            vals.append(float(np.count_nonzero(intact)) / float(LOCUS_REPS))
        return vals

    # ibdWeight, measured. The IBD weight is the covariance carried by an
    # unrecombined pair, which this construction fixes at GENO_W; it is
    # RECOVERED here from an r=0 genotype sample rather than reused.
    w_batches = []
    for _ in range(LOCUS_BATCHES):
        g0, g1 = sample_two_locus_genotypes(0.5, GENO_W, 0.0, GENO_TMRCA,
                                            GENO_INDIVIDUALS, rng)
        w_batches.append(standardised_covariance(g0, g1))
    w_s = simprov.summarize(w_batches)
    w_measured = w_s["mean"]
    print("  MEASURED ibdWeight at r=0: %.5f +-%.5f  (construction used %.3f)"
          % (w_measured, w_s["se"] or 0.0, GENO_W))

    rows = []
    ok = True
    for r in R_GRID:
        for tm in TMRCA_GRID:
            s = simprov.summarize(survival_batches(r, tm, rng))
            pred = corpus_discrete_recombination_survival(r, tm)
            # At r = 0 every batch returns exactly 1.0, so the batch scatter is
            # exactly 0 and the sems ratio is 0/0. That cell is a calibration
            # rather than a test and is excluded from scoring below, so the
            # floored denominator only ever affects a line that is printed and
            # not judged.
            sems = abs(s["mean"] - pred) / max(s["se"] or 0.0, 1e-12)
            calib = (r == 0.0)
            good = calib or sems <= SEMS
            ok = ok and good
            cov_pred = corpus_two_locus_ibd_covariance(w_measured, r, tm)
            rows.append({"recombRate": r, "tmrca": tm,
                         "measured_survival": s,
                         "discreteRecombinationSurvival": pred,
                         "deviation_sems": sems,
                         "measured_ibdWeight": w_measured,
                         "twoLocusIBDCovariance_predicted": cov_pred,
                         "is_calibration_not_test": bool(calib),
                         "pass": bool(good)})
            print("  r=%-6g tmrca=%-4d  measured %.5f +-%.5f | (1-r)^t %.5f "
                  "(%.2f sems) | w*(1-r)^t = %.5f  %s"
                  % (r, tm, s["mean"], s["se"] or 0.0, pred, sems, cov_pred,
                     "CALIBRATION" if calib else ("ok" if good else "FAIL")))

    verdict = ("discreteRecombinationSurvival and twoLocusIBDCovariance "
               "SURVIVE the two-locus lineage sim at every tested (r, tmrca)"
               if ok else
               "discreteRecombinationSurvival IS CONTRADICTED by the two-locus "
               "lineage sim; see the failing (r, tmrca) cells")
    print("  VERDICT: %s" % verdict)
    out["C4"] = {"measured_ibdWeight": w_s, "cells": rows,
                 "verdict": verdict, "is_corpus_finding": True,
                 "estimand": "P(no recombination between two loci over tmrca "
                             "generations), and the covariance it induces",
                 "agrees": bool(ok)}
    return ok


def sample_two_locus_genotypes(p, w, r, tmrca, n_ind, rng):
    """Diploid dosages at two linked loci, from an explicit IBD mechanism.

    Each haplotype either carries both loci co-inherited from one ancestral
    two-locus haplotype -- which happens with probability (1-r)^tmrca, realised
    here by an explicit per-generation recombination draw and NOT by evaluating
    the formula -- or draws its second locus from an independent ancestral
    haplotype. The ancestral pool carries association `w` between the two loci.

    Returns two arrays of diploid dosages in {0,1,2}, one per locus.
    """
    n_hap = 2 * int(n_ind)
    # Explicit per-generation recombination. No (1-r)^t is evaluated here.
    intact = np.ones(n_hap, dtype=bool)
    for _g in range(int(tmrca)):
        if r > 0.0:
            intact &= (rng.random(n_hap) >= r)
    a0 = (rng.random(n_hap) < p)
    # Ancestral association: locus 1 copies locus 0 with probability w, else
    # draws independently at the same frequency.
    copy = rng.random(n_hap) < w
    a1_anc = np.where(copy, a0, rng.random(n_hap) < p)
    a1_ind = (rng.random(n_hap) < p)
    a1 = np.where(intact, a1_anc, a1_ind)
    g0 = a0[0::2].astype(np.int64) + a0[1::2].astype(np.int64)
    g1 = a1[0::2].astype(np.int64) + a1[1::2].astype(np.int64)
    return g0, g1


def standardised_covariance(x, y):
    """Covariance of x and y AFTER dividing each by its own sample sd.

    This is the correlation. It is written out rather than called `corrcoef`
    so that the standardisation the corpus's diagonal-1 asserts is visible at
    the point where it is applied.
    """
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    sx, sy = x.std(ddof=1), y.std(ddof=1)
    if sx <= 0 or sy <= 0:
        return float("nan")
    return float(np.mean((x - x.mean()) * (y - y.mean()))
                 * len(x) / (len(x) - 1.0) / (sx * sy))


def raw_variance(x):
    x = np.asarray(x, dtype=float)
    return float(x.var(ddof=1))


def c5(rng, out):
    """C5  THE HARD 1 ON THE DIAGONAL, AGAINST SAMPLED GENOTYPES.

    twoLocusCoalescentCovarianceMatrix writes 1 on every diagonal entry. That
    is not a free choice: it ASSERTS that both loci are variance-standardised.
    A real genotype sample can contradict it, so this check builds one rather
    than assuming the assertion.

    THREE THINGS ARE MEASURED, and they are not the same claim:

      (a) RAW DIPLOID DOSAGES. Var(g) = 2p(1-p), which is at most 0.5 and
          reaches it only at p = 0.5. So the diagonal of the raw sample
          covariance CANNOT be 1 at any allele frequency. This is FALSIFIABLE
          and is expected to REFUTE the diagonal for raw dosages; the run says
          which way it went and by how much, across an allele-frequency grid.

      (b) STANDARDISED DOSAGES. The diagonal is then 1 BY CONSTRUCTION. This
          is measured and reported, and it is EXPLICITLY MARKED AS BLIND: a
          quantity divided by its own standard deviation has unit variance
          whatever the corpus says. Reporting (b) as a pass for the corpus
          would be the exact error this file's header warns about, so it is
          scored as an instrument sanity line and named as non-falsifiable.

      (c) THE OFF-DIAGONAL, on standardised dosages, against
          twoLocusIBDCovariance with the ibdWeight MEASURED in C4. This is
          falsifiable and is the entry that carries content.

      (d) THE ZEROS AWAY FROM THE LINKED PAIR. Two extra unlinked loci are
          sampled into the same block and their entries are compared to 0.
          This is where twoLocusIdx0 and twoLocusIdx1 would show up if they
          named the wrong positions: a matrix whose linked pair sat at (2,3)
          would put the measured covariance where this check demands a zero.

    THE READING OF (a) IS A CORPUS FINDING, NOT AN INSTRUMENT FAILURE. It does
    not touch READ_THE_TEST.
    """
    print("")
    print("=" * 78)
    print("C5  twoLocusCoalescentCovarianceMatrix AGAINST SAMPLED GENOTYPES")
    print("=" * 78)

    w_meas = out.get("C4", {}).get("measured_ibdWeight", {}).get("mean")
    w_se = out.get("C4", {}).get("measured_ibdWeight", {}).get("se") or 0.0
    if w_meas is None:
        raise SystemExit("C5 requires C4's measured ibdWeight; run C4 first")
    print("  ibdWeight = %.5f +-%.5f, MEASURED in C4's r=0 cell. Its error bar"
          % (w_meas, w_se))
    print("  is propagated into the (c) prediction below: the prediction is an")
    print("  ESTIMATE, and comparing a measurement to an estimate without its")
    print("  error bar manufactures significance out of the calibration noise.")

    rows = []
    raw_refuted_everywhere = True
    offdiag_ok = True
    zeros_ok = True
    for p in GENO_P_GRID:
        raw_var0, raw_var1, std_var0, off, z01, z02 = [], [], [], [], [], []
        for _ in range(GENO_BATCHES):
            g0, g1 = sample_two_locus_genotypes(p, GENO_W, GENO_R, GENO_TMRCA,
                                                GENO_INDIVIDUALS, rng)
            # Two UNLINKED loci in the same block, at the same frequency.
            u2 = ((rng.random(GENO_INDIVIDUALS) < p).astype(np.int64)
                  + (rng.random(GENO_INDIVIDUALS) < p).astype(np.int64))
            u3 = ((rng.random(GENO_INDIVIDUALS) < p).astype(np.int64)
                  + (rng.random(GENO_INDIVIDUALS) < p).astype(np.int64))
            raw_var0.append(raw_variance(g0))
            raw_var1.append(raw_variance(g1))
            s0 = (g0 - g0.mean()) / g0.std(ddof=1)
            std_var0.append(raw_variance(s0))
            off.append(standardised_covariance(g0, g1))
            z01.append(standardised_covariance(g0, u2))
            z02.append(standardised_covariance(u2, u3))

        s_raw0 = simprov.summarize(raw_var0)
        s_raw1 = simprov.summarize(raw_var1)
        s_std0 = simprov.summarize(std_var0)
        s_off = simprov.summarize(off)
        s_z01 = simprov.summarize(z01)
        s_z02 = simprov.summarize(z02)

        raw_sems = abs(s_raw0["mean"] - 1.0) / max(s_raw0["se"] or 0.0, 1e-12)
        raw_refutes = raw_sems > SEMS
        raw_refuted_everywhere = raw_refuted_everywhere and raw_refutes

        std_sems = abs(s_std0["mean"] - 1.0) / max(s_std0["se"] or 0.0, 1e-12)

        pred_off = corpus_two_locus_ibd_covariance(w_meas, GENO_R, GENO_TMRCA)
        # twoLocusIBDCovariance is LINEAR in ibdWeight, so the prediction's own
        # standard error is w_se times the survival factor, and it adds in
        # quadrature with the measurement's.
        pred_off_se = w_se * corpus_discrete_recombination_survival(GENO_R,
                                                                    GENO_TMRCA)
        off_se = math.sqrt((s_off["se"] or 0.0) ** 2 + pred_off_se ** 2)
        off_sems = abs(s_off["mean"] - pred_off) / max(off_se, 1e-12)
        offdiag_ok = offdiag_ok and off_sems <= SEMS

        z_sems = max(abs(s_z01["mean"]) / max(s_z01["se"] or 0.0, 1e-12),
                     abs(s_z02["mean"]) / max(s_z02["se"] or 0.0, 1e-12))
        zeros_ok = zeros_ok and z_sems <= SEMS

        print("  p=%.2f" % p)
        print("    (a) RAW dosage variance  %.5f +-%.5f vs corpus diagonal 1 "
              "-> %.1f sems  %s   [2p(1-p) = %.4f]"
              % (s_raw0["mean"], s_raw0["se"] or 0.0, raw_sems,
                 "REFUTES the hard 1" if raw_refutes else "does not refute",
                 2 * p * (1 - p)))
        print("    (b) STANDARDISED dosage variance %.5f +-%.5f (%.1f sems from "
              "1)  <- BLIND BY CONSTRUCTION, NOT EVIDENCE"
              % (s_std0["mean"], s_std0["se"] or 0.0, std_sems))
        print("    (c) off-diagonal (0,1) standardised %.5f +-%.5f | "
              "twoLocusIBDCovariance %.5f +-%.5f  (%.2f sems)  %s"
              % (s_off["mean"], s_off["se"] or 0.0, pred_off, pred_off_se,
                 off_sems, "ok" if off_sems <= SEMS else "FAIL"))
        print("    (d) off-block entries vs 0: max %.2f sems  %s"
              % (z_sems, "ok" if z_sems <= SEMS else "FAIL"))

        rows.append({
            "p": p,
            "raw_dosage_variance_locus0": s_raw0,
            "raw_dosage_variance_locus1": s_raw1,
            "raw_diagonal_sems_from_1": raw_sems,
            "raw_diagonal_refutes_corpus_1": bool(raw_refutes),
            "analytic_2p1mp": 2 * p * (1 - p),
            "standardised_dosage_variance": s_std0,
            "standardised_diagonal_is_blind_by_construction": True,
            "offdiagonal_standardised_measured": s_off,
            "twoLocusIBDCovariance_with_measured_ibdWeight": pred_off,
            "twoLocusIBDCovariance_prediction_se": pred_off_se,
            "offdiagonal_sems": off_sems,
            "offblock_max_sems_from_zero": z_sems,
            "corpus_matrix_at_t4":
                corpus_two_locus_covariance_matrix(4, w_meas, GENO_R,
                                                   GENO_TMRCA).tolist()})

    if raw_refuted_everywhere:
        verdict = ("THE HARD 1 ON THE DIAGONAL OF "
                   "twoLocusCoalescentCovarianceMatrix IS REFUTED FOR RAW "
                   "DIPLOID DOSAGES at every tested allele frequency: the "
                   "measured variance is 2p(1-p), which cannot reach 1. The "
                   "matrix is therefore a claim about VARIANCE-STANDARDISED "
                   "genotypes and its declaration does not say so. Under "
                   "standardisation the diagonal is 1 by construction and the "
                   "entry carries no empirical content.")
    else:
        verdict = ("The diagonal 1 was NOT refuted on raw dosages at every "
                   "tested frequency, which is unexpected -- check the "
                   "genotype sampler before reading this as a corpus result.")
    if not offdiag_ok:
        verdict += (" SEPARATELY: the off-diagonal entry DISAGREES with "
                    "twoLocusIBDCovariance at the measured ibdWeight.")
    if not zeros_ok:
        verdict += (" SEPARATELY: entries the matrix declares zero are "
                    "NONZERO in the sample; twoLocusIdx0/twoLocusIdx1 may not "
                    "name the positions this matrix is being read at.")
    print("  VERDICT: %s" % verdict)

    out["C5"] = {"cells": rows, "verdict": verdict,
                 "raw_diagonal_refuted_at_every_frequency":
                     bool(raw_refuted_everywhere),
                 "offdiagonal_agrees": bool(offdiag_ok),
                 "declared_zeros_agree": bool(zeros_ok),
                 "standardised_diagonal_scored": False,
                 "why_standardised_diagonal_not_scored":
                     "a quantity divided by its own sample sd has unit "
                     "variance whatever the corpus says; scoring it would "
                     "report that a number equals itself",
                 "is_corpus_finding": True,
                 "estimand": "entries of the sample covariance matrix of "
                             "diploid dosages at four loci, two linked and "
                             "two unlinked",
                 "agrees": bool(offdiag_ok and zeros_ok)}
    return offdiag_ok and zeros_ok


def c6(rng, recip_by_size, out, clean_c1, clean_c2):
    """C6  POSITIVE CONTROL -- ONE CORRUPTION, TWO REQUIRED RESPONSES.

    The history is displaced by C6_SHIFT generations through `shift_history`,
    the SAME function every other arm calls with shift 0. Nothing else
    differs: not the sampler, not the integrator, not the seeds' structure.

      (i)  C1 MUST STAY BLIND. A constant history is invariant under a shift,
           so the constant-hazard mean must be statistically unchanged from
           the clean run. If it moves, THE CORRUPTION WAS NOT THE ONE
           DESCRIBED and this control has proved nothing -- the run says so
           rather than reporting a pass.
      (ii) C2 MUST FIRE. The zero-hazard window is displaced away from where
           the history declares it, so coalescences appear inside a declared
           zero-hazard interval. The statistic is an integer count.

    BOTH ARE REQUIRED. A corruption that only fires proves the check is
    sensitive but not that the control is the one claimed; a corruption that
    only stays blind proves nothing at all.

    C3's response is measured and REPORTED AS A THIRD DIRECTION, NOT SCORED:
    C3 is expected to separate the two distributions under the uncorrupted
    history too, so "C3 moved" carries no information about the corruption.
    """
    print("")
    print("=" * 78)
    print("C6  POSITIVE CONTROL -- history displaced by %d generations"
          % C6_SHIFT)
    print("      C1 MUST STAY BLIND (constant history is shift-invariant)")
    print("      C2 MUST FIRE (zero-hazard window lands where it is not "
          "declared)")
    print("=" * 78)

    ok1, corrupt_c1 = c1(rng, recip_by_size, out, shift=C6_SHIFT,
                         label="C6_C1_blind_arm")
    blind_sems = diff_sems(clean_c1["engine_a"], corrupt_c1["engine_a"])
    stayed_blind = blind_sems <= SEMS
    print("  (i)  C1 clean %.3f vs corrupted %.3f -> %.2f sems: C1 %s"
          % (clean_c1["engine_a"]["mean"], corrupt_c1["engine_a"]["mean"],
             blind_sems,
             "STAYED BLIND as designed" if stayed_blind
             else "MOVED -- the corruption was not the one described"))

    ok2, corrupt_c2 = c2(rng, recip_by_size, out, shift=C6_SHIFT,
                         label="C6_C2_firing_arm")
    fired = corrupt_c2["fired"]
    clean_quiet = not clean_c2["fired"]
    print("  (ii) C2 clean events %d -> corrupted events %d: C2 %s"
          % (clean_c2["engine_a_events_in_window"],
             corrupt_c2["engine_a_events_in_window"],
             "FIRED as required" if fired
             else "DID NOT FIRE -- C2 is blind to the error it exists to catch"))

    c3_corrupt = c3(rng, recip_by_size, out, shift=C6_SHIFT,
                    label="C6_C3_reported_arm")
    print("  (iii) C3 under the same corruption: %s"
          "   <- REPORTED, NOT SCORED (C3 separates under the clean history too)"
          % c3_corrupt["verdict"][:60])

    ok = bool(stayed_blind and fired and clean_quiet)
    if not clean_quiet:
        print("  NOTE: the CLEAN C2 already reported events in the window, so "
              "the firing above is not attributable to the corruption.")
    out["C6"] = {"shift": C6_SHIFT,
                 "c1_blind_arm_sems_from_clean": blind_sems,
                 "c1_stayed_blind": bool(stayed_blind),
                 "c2_clean_events": clean_c2["engine_a_events_in_window"],
                 "c2_corrupted_events":
                     corrupt_c2["engine_a_events_in_window"],
                 "c2_fired": bool(fired),
                 "clean_c2_was_quiet": bool(clean_quiet),
                 "c3_verdict_under_corruption": c3_corrupt["verdict"],
                 "c3_scored": False,
                 "both_directions_required": True,
                 "pass": ok}
    print("  C6 %s" % ("ok -- both directions behaved as required" if ok
                       else "FAIL -- a positive control that does not behave "
                            "as described has proved nothing"))
    _ = (ok1, ok2)
    return ok


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="tunable knobs for --set NAME=VALUE:\n" +
               "\n".join("  %-20s %s" % (k, v)
                         for k, v in sorted(TUNABLES.items())))
    parser.add_argument("--profile", choices=("quick", "full", "deep"),
                        default="quick",
                        help="bounded development signal, the registered full "
                             "experiment, or the same experiment with the "
                             "sampling widened (deep)")
    parser.add_argument("--set", dest="settings", action="append", default=[],
                        metavar="NAME=VALUE",
                        help="override one knob after the profile; repeatable")
    parser.add_argument("--seed", type=int, default=SEED,
                        help="master seed (default %d)" % SEED)
    parser.add_argument("--output", default="fam_coalescent_hazard_results.json")
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
        "empirical/differential/cluster/fam_coalescent_hazard.py", config,
        args.seed,
        {"batches_per_cell": N_BATCH, "replicates_per_batch": BATCH_REPS,
         "replicate_unit": "batch; every standard error in this file is the "
                           "scatter across batches, never a per-draw formula"}),
        "profile": args.profile, "seed": args.seed,
        "overrides": overrides, "config": config,
        "family": "coalescent_hazard",
        "members_covered": [
            "integratedCoalescentHazard",
            "coalescenceSurvivalFromHazard",
            "coalescenceCdfFromHazard",
            "discreteRecombinationSurvival",
            "twoLocusIBDCovariance",
            "twoLocusCoalescentCovarianceMatrix"],
        "members_not_found_in_corpus": [],
        "members_covered_indirectly": ["twoLocusIdx0", "twoLocusIdx1"],
        "members_that_cannot_be_falsified": [
            "integratedCoalescentHazard",
            "coalescenceSurvivalFromHazard",
            "coalescenceCdfFromHazard"],
        "why_they_cannot_be_falsified":
            "S(t) = exp(-Lambda(t)) and F = 1 - S are the DEFINITION of "
            "survival from a hazard, and Lambda is the definition of an "
            "integral. A simulator that draws by inverse transform on Lambda "
            "and then confirms S = exp(-Lambda) has measured its own "
            "integrator and nothing else. C0 exercises them, is scored into "
            "the INSTRUMENT flag, and is excluded from CORPUS_FINDINGS. "
            "Agreement in C0 is NOT evidence for the corpus.",
        "the_falsifiable_claim":
            "C3: whether harmonicMeanNe (Descent/LDDecayTheory.lean), the "
            "single number the corpus's drift-retention work substitutes for a "
            "time-varying Ne, yields the same TMRCA DISTRIBUTION as the "
            "integrated hazard of the true trajectory. The two are pinned "
            "together at the window endpoint by the definition of the "
            "harmonic mean, so only a distributional statistic can separate "
            "them; the mean is reported and explicitly not scored.",
        "external_declarations_used": {
            "harmonicMeanNe": "Descent/LDDecayTheory.lean -- the other side "
                              "of the bridge; not a member of this family"},
        "transcription_note":
            "Bodies transcribed by declaration name, never by line number. "
            "Descent/DGP.lean and Descent/PortabilityDrift.lean carried "
            "uncommitted edits from other sessions at transcription time; "
            "re-read the declarations before trusting this at a later "
            "revision."}

    # ------------------------------------------------------------------
    # THE CENSUS PASS. This is where 1/(2N) stops being an assumption.
    # ------------------------------------------------------------------
    print("")
    print("=" * 78)
    print("CENSUS PASS -- MEASURING 1/Ne from parent collisions, not asserting it")
    print("=" * 78)
    recip_batches = {
        N_LARGE: measure_recip_two_ne(N_LARGE, CENSUS_PAIRS_LARGE,
                                      CENSUS_BATCHES, rng),
        N_SMALL: measure_recip_two_ne(N_SMALL, CENSUS_PAIRS_SMALL,
                                      CENSUS_BATCHES, rng)}
    census = {}
    recip_by_size = {}
    for size, vals in recip_batches.items():
        s = simprov.summarize(vals)
        recip_by_size[size] = s["mean"]
        ne_hat = 1.0 / s["mean"] if s["mean"] else float("inf")
        rel = (s["se"] or 0.0) / s["mean"] if s["mean"] else float("nan")
        census[str(size)] = {"census_input_N": size,
                             "measured_recip_Ne": s,
                             "measured_Ne": ne_hat,
                             "relative_se_of_recip": rel,
                             "batches": CENSUS_BATCHES}
        print("  census N=%-5d  measured 1/Ne = %.6e +-%.2e (%.3f%% rel) -> "
              "Ne_hat = %.3f"
              % (size, s["mean"], s["se"] or 0.0, 100.0 * rel, ne_hat))
    print("  These measured reciprocals, and NOT the census inputs, are what")
    print("  harmonicMeanNe is applied to in C3.")
    out["census_pass"] = census

    r0 = c0(recip_by_size, out)
    r0b = c0b(rng, recip_by_size, out)
    ok1, clean_c1 = c1(rng, recip_by_size, out)
    ok2, clean_c2 = c2(rng, recip_by_size, out)
    c3_res = c3(rng, recip_by_size, out)
    c4_ok = c4(rng, out)
    c5_ok = c5(rng, out)
    r6 = c6(rng, recip_by_size, out, clean_c1, clean_c2)

    # ------------------------------------------------------------------
    # INSTRUMENT VERDICT AND CORPUS FINDINGS, KEPT APART.
    # ------------------------------------------------------------------
    print("")
    print("=" * 78)
    print("INSTRUMENT HEALTH -- these fail only if THIS FILE is broken")
    print("=" * 78)
    instrument = (("C0  integrator self-test (NOT corpus evidence)", r0),
                  ("C0b engine A vs engine B", r0b),
                  ("C1  constant-hazard control", ok1),
                  ("C2  zero-hazard control", ok2),
                  ("C3  run validity (censoring, engines agree)",
                   c3_res["run_ok"]),
                  ("C6  positive control, both directions", r6))
    for tag, v in instrument:
        print("  %-46s %s" % (tag, v))
    ok = all(v for _, v in instrument)
    failed = [tag for tag, v in instrument if not v]

    print("")
    print("=" * 78)
    print("CORPUS FINDINGS -- results, NOT harness failures")
    print("=" * 78)
    print("  C3 BRIDGE : %s" % c3_res["verdict"])
    print("  C4 RECOMB : %s" % out["C4"]["verdict"])
    print("  C5 MATRIX : %s" % out["C5"]["verdict"])
    print("  A corpus disagreement above does NOT flip READ_THE_TEST. A harness")
    print("  that goes red when the corpus is wrong trains its reader to fix")
    print("  the harness.")

    out["CORPUS_FINDINGS"] = {
        "C3_harmonic_mean_bridge": c3_res["verdict"],
        "C4_recombination_survival": out["C4"]["verdict"],
        "C5_covariance_matrix_diagonal": out["C5"]["verdict"],
        "C3_corpus_agrees": bool(
            c3_res["run_ok"]
            and not c3_res["engines"]["engine_A_wright_fisher"][
                "distribution_differs"]),
        "C4_corpus_agrees": bool(c4_ok),
        "C5_corpus_agrees": bool(c5_ok),
        "excluded_because_unfalsifiable": [
            "integratedCoalescentHazard", "coalescenceSurvivalFromHazard",
            "coalescenceCdfFromHazard"],
        "note": "C0's agreement is a property of this file's integrator and is "
                "not listed above as a corpus finding."}
    out["READ_THE_TEST"] = bool(ok)
    out["READ_THE_TEST_means"] = ("INSTRUMENT HEALTH ONLY: C0, C0b, C1, C2, "
                                  "C3 run validity and C6. Corpus "
                                  "disagreements live in CORPUS_FINDINGS and "
                                  "do not appear here.")
    out["failed_checks"] = failed
    out["runtime_sec"] = time.time() - t0
    print("")
    print("  READ_THE_TEST (INSTRUMENT ONLY): %s" % ok)
    print("  runtime %.1f s" % out["runtime_sec"])

    fh = open(args.output, "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> %s" % args.output)

    if not ok:
        sys.stderr.write(
            "fam_coalescent_hazard: %d of %d INSTRUMENT checks FAILED under "
            "profile '%s': %s\n"
            % (len(failed), len(instrument), args.profile, ", ".join(failed)))
        sys.stderr.write(
            "fam_coalescent_hazard: this is a measurement, not a crash. The "
            "full report is on stdout and the results file was written to %s\n"
            % args.output)
        if args.profile == "quick":
            sys.stderr.write(
                "fam_coalescent_hazard: profile 'quick' is the bounded "
                "development run; its batch counts are too small for the C3 "
                "bridge verdict to be read as a finding. Use --profile full.\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
