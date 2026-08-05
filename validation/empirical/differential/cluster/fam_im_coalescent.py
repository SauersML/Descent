#!/usr/bin/env python3
"""Family simulator: ISOLATION WITH MIGRATION, TWO-DEME STRUCTURED COALESCENT.

WHY THIS FAMILY WAS WRITTEN FIRST
  It is the cheapest of the five unsimulated families AND the one most likely
  to return a result rather than a green tick. Those are not independent
  virtues: a first simulator that can only agree teaches us nothing about
  whether the harness works, and this repository has already shipped
  instruments that returned credible numbers while measuring nothing. This one
  has a disagreement waiting for it before a single replicate is drawn.

THE DISAGREEMENT THAT MAKES IT WORTH THE NODE TIME
  The corpus says the equilibrium mean coalescence time for two lineages in
  DIFFERENT demes is

      twoDemeIMEquilibriumETst M = (2M + 1)/M   =  2 + 1/M

  The specification for this family in differential/cluster/families.py cites
  Wakeley and states the reference as 2 + 2/M. Those differ by a factor of two
  in the migration arm, which is the signature of a per-lineage versus total
  migration-rate convention, and NOTHING IN THE REPOSITORY CHECKS IT. One of
  the two is wrong.

  So this simulator is built so that ONE NUMBER DECIDES. Define

      kappa(M) := (E[T_st] - 2) * M          [T in units of 2N generations]

  The corpus predicts kappa = 1 at every M. The Wakeley form as quoted in
  families.py predicts kappa = 2 at every M. C2 measures kappa. Whichever side
  loses is named in the output as a string, not left as "a discrepancy" for a
  reader to adjudicate.

  THE CONVENTION IS TAKEN OUT OF MY HANDS ON PURPOSE. Neither M nor a
  coalescent time unit is a primitive here. The primitives are PHYSICAL: N
  diploids per deme and a per-lineage per-generation migration probability m.
  M = 4*N*m and the time unit 2N generations are DERIVED from those. A
  simulator that took M as an input would be assuming exactly the convention
  the run is supposed to settle, and would return whichever answer its author
  had already assumed.

  THE CORPUS STATES ITS CONVENTION EXPLICITLY, which is why this is decidable
  rather than a matter of taste. The docstring on twoDemeIMFirstStepSame says:

      "Time is in units of 2 Nₑ generations, so two lineages sitting in one
       deme coalesce at rate 1 and each lineage leaves its deme at rate M/2."

  and the docstring on twoDemeIMFirstStepDiff says the only event from the
  different-deme state is "a migration, at total rate M". So the corpus has
  written down exactly the rates this sampler derives from N and m. If the
  measurement lands on kappa = 1, the corpus is right and the families.py spec
  is quoting a reference that does not describe these rates. If it lands on
  kappa = 2, the corpus's stated rates do not follow from its own primitives.
  Neither outcome is a matter of naming.

  EVERY DECLARATION IN THIS FAMILY CARRIES "Empirical status: UNTESTED" in the
  corpus. This is the first instrument to touch any of them.

TWO ENGINES THAT SHARE NO CODE
  ENGINE A, sampler. Continuous-time competing exponential clocks on the
    two-lineage state space {SAME deme, DIFFERENT demes}, vectorised over
    replicates. Draws times.
  ENGINE B, exact solve. The DISCRETE-generation ancestral chain written as a
    2x2 linear system in (E[T_S], E[T_D]) and solved with numpy.linalg.solve.
    Draws nothing.
  They agree only if both are right. Two engines that disagree is the most
  productive thing that can happen here, so they are kept separate rather than
  refactored into a shared helper.

THE CONTROL THAT PINS THE CLOCK WITHOUT TOUCHING THE DISPUTE
  E[T_ss] = 2 holds at EVERY M, and -- this is the point -- it holds under
  BOTH candidate migration conventions. The corpus names this Strobeck's
  invariance and calls its M-freedom "the content of the model", so C1 is
  simultaneously a control on my sampler and a corpus claim under test; both
  readings are reported. Substituting the corpus's own
  first-step equations gives E[T_ss] = 2 whether the per-lineage migration rate
  is M/2 or M; the migration terms cancel. So C1 is a genuine control: it
  proves the coalescence clock and the sampler are right, and it is
  CONSTITUTIONALLY INCAPABLE of deciding C2. A control that could decide the
  test would not be a control.

  This is also why C6 exists. A sampler whose migration rate is wrong by a
  factor of two passes C1 unharmed. C6 runs exactly that corrupted sampler and
  requires C2 to reject it. A check never shown failing is not a check.

CAN-FAIL
  The M grid runs from 0.1 to 8. At M = 8 the two candidate forms are 2.125
  and 2.25, six percent apart and inside reach of the error bars; at M = 0.1
  they are 12 and 22. A grid confined to large M would leave the two candidates
  within a few percent of each other and would decide nothing, which is the
  failure mode this family has survived in so far.

WHAT IS COVERED
  All eight members of the family are LIVE in the corpus at the revision below
  and every one is exercised:

      twoDemeIMFirstStepSame          C3
      twoDemeIMFirstStepDiff          C3
      twoDemeIMEquilibriumETss        C1
      twoDemeIMEquilibriumETst        C2   <- the deciding one
      twoDemeIMEquilibriumScalars     C4
      twoDemeIMEquilibriumDelta       C4
      DemographicCoalescenceScalars.delta   C4
      expectedSqMeanPGSDiff_IMEquilibrium   C4, REPORTED NOT SCORED (below)

  NO MEMBER OF THIS FAMILY IS MISSING FROM THE CORPUS. That is worth saying
  explicitly, because it is not true of the neighbouring families: eleven
  members listed for the other five unsimulated families could not be found in
  the corpus at any name, and this one is clean.

  `delta` is a SHORT NAME and short names collide in this corpus. The
  declaration transcribed here is `DemographicCoalescenceScalars.delta` in
  Descent/PortabilityDrift.lean, reached through
  `twoDemeIMEquilibriumScalars`. If a `delta` elsewhere in the corpus is meant,
  this simulator does not cover it.

WHAT IS REPORTED AND NOT SCORED, AND WHY
  expectedSqMeanPGSDiff_IMEquilibrium feeds `2 * delta` into `Var_Delta_Mu` as
  an F_ST. C4 measures that the coalescent delta is Hudson's F_ST between the
  two demes and reports the doubling, because `Var_Delta_Mu V_A fst` is scored
  against a simulated polygenic score in the pgs_transport_drift family, not
  here. Scoring it here would mean this file quietly re-measuring another
  family's estimand and the agreement reading as corroboration. It is left as
  a measured input to that family with its error bar attached.

NO AUC IS TOUCHED BY THIS FAMILY. Recorded because two AUC estimands in this
  corpus -- liabilityThresholdAUCFromExplainedR2 and
  equalVarianceGaussianAUCFromSignalVariance -- look alike, are different, and
  conflating them has already cost an hour and produced a false alarm. Neither
  appears anywhere downstream of the eight members above.

TRANSCRIPTION PROVENANCE
  Every corpus body below is quoted beside its Python transcription with its
  file and declaration name and NO LINE NUMBER, because line numbers here go
  stale and have already sent one instrument chasing declarations that no
  longer existed.

  Transcribed against revision a4bc5385. The eight bodies were re-read from
  the working tree at three successive revisions while this file was being
  written -- 48ff8c05, 9eee6e05, a4bc5385 -- and were byte-identical at all
  three. Descent/PortabilityDrift.lean was being edited by other sessions
  throughout, and one read of it failed outright because the file was mid-write
  at that instant, so the agreement across three revisions is the evidence
  here, not any single read. If this file is being read at a later revision,
  re-read the eight declarations before trusting the transcription.

RUNNING IT -- NOT ON A LOGIN NODE
  Nothing here needs msprime, scipy or a build. numpy only, Python 3.6
  compatible, single-threaded by construction. The thread pins are still set,
  because numpy will otherwise take every core and one agent's contention gets
  misdiagnosed as another's deadlock.

      srun --time=30 --mem=8G --cpus-per-task=1 \
        env OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
        python3 validation/empirical/differential/cluster/fam_im_coalescent.py \
            --profile full \
            --output /projects/standard/hsiehph/sauer354/fam_im_coalescent_<stamp>.json \
        > /projects/standard/hsiehph/sauer354/fam_im_<stamp>.out 2>&1

  CAPTURE BOTH STREAMS. A nonzero exit from this script is a MEASUREMENT
  OUTCOME, not a crash: the report goes to stdout and the failing check names
  go to stderr. A harness that collects only stderr has already recorded a
  family of this shape as crashing.

  Output goes OUTSIDE /tmp, which is node-local and invisible to the next relay
  call, and carries a unique name so an absent file means not written rather
  than not written here.

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

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

import simprov  # noqa: E402

SEED = 20260803

# The M grid. Spans below 1, where the two candidate ETst forms differ by a
# factor approaching two, up to 8, where they differ by six percent.
M_GRID = (0.1, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0)
# Sampler replicate structure. The REPLICATE UNIT IS THE BATCH: one record is
# written per batch, and every standard error in this file is the scatter
# ACROSS batches, never a per-draw formula. A per-draw standard error would be
# an analytic claim about the estimator rather than a measurement of it.
N_BATCH = 200
BATCH_REPS = 5000
# Physical primitives for the sampler's discrete companion and for C5.
NE_GRID = (50, 500, 5000)
# Panmixia and isolation limits for the two split controls in C2. M=50 is far
# enough into panmixia that the corpus gap E[T_st]-E[T_ss] = 1/M is 0.02, well
# inside the batch error bar, without the ~M events per replicate that a much
# larger M would cost.
M_PANMICTIC = 50.0
M_ISOLATED = 0.02
# Safety cap on the event loop. A replicate that has not resolved by here is
# COUNTED and reported, never dropped silently.
MAX_EVENTS = 20000

TUNABLES = {
    "M_GRID": "scaled migration rates M = 4 N m swept by C1-C4",
    "N_BATCH": "batches per cell; the replicate unit and the error bar",
    "BATCH_REPS": "replicates inside one batch",
    "NE_GRID": "deme sizes for the discrete-generation ordering test C5",
    "M_PANMICTIC": "large-M cell for the panmixia split control",
    "M_ISOLATED": "small-M cell for the isolation split control",
    "MAX_EVENTS": "event-loop cap; unresolved replicates are counted",
}


def configure_profile(profile):
    """`full` is the registered experiment; `quick` is a bounded development run.

    Only sampling widths and grid density change. No estimand, no rate, no
    convention differs between the profiles -- a profile that changed what is
    being measured would make two runs of this file incomparable, which is the
    thing the compare-do-not-overwrite rule exists to protect.
    """
    global M_GRID, N_BATCH, BATCH_REPS, NE_GRID
    if profile == "full":
        return
    if profile == "deep":
        N_BATCH, BATCH_REPS = 400, 20000
        M_GRID = (0.1, 0.2, 0.4, 0.8, 1.6, 3.2, 6.4, 8.0)
        NE_GRID = (25, 50, 100, 500, 1000, 5000)
        return
    if profile != "quick":
        raise ValueError("profile must be 'quick', 'full' or 'deep'")
    N_BATCH, BATCH_REPS = 40, 400
    M_GRID = (0.25, 1.0, 4.0)
    NE_GRID = (50, 500)


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
    return {name: (list(globals()[name])
                   if isinstance(globals()[name], tuple)
                   else globals()[name])
            for name in TUNABLES}


# ===========================================================================
# THE CORPUS, TRANSCRIBED.
#
# Each function below is one declaration from Descent/PortabilityDrift.lean,
# quoted above its transcription. Nothing in this section computes anything the
# corpus does not; nothing in the measurement sections calls anything but these.
# ===========================================================================

def corpus_ETss(M):
    """Descent/PortabilityDrift.lean, decl `twoDemeIMEquilibriumETss`

        noncomputable def twoDemeIMEquilibriumETss (_M : ℝ) : ℝ := 2

    The argument is discarded in the Lean body -- the underscore is the
    corpus's own claim that E[T_ss] does not depend on M, and C1 is what makes
    that claim face a measurement.
    """
    return 2.0


def corpus_ETst(M):
    """Descent/PortabilityDrift.lean, decl `twoDemeIMEquilibriumETst`

        noncomputable def twoDemeIMEquilibriumETst (M : ℝ) : ℝ :=
          (2 * M + 1) / M

    Equivalently 2 + 1/M. THIS IS THE DECLARATION UNDER TEST.
    """
    return (2.0 * M + 1.0) / M


def families_spec_ETst(M):
    """NOT a corpus declaration. The competing reference, quoted from the
    `isolation_with_migration_coalescent` spec in
    differential/cluster/families.py:

        "the exact equilibrium E[T_ss] = 2, E[T_st] = 2 + 2/M (Wakeley)"

    Carried here so the run adjudicates between two named candidates rather
    than reporting that the corpus deviates from something unnamed.
    """
    return 2.0 + 2.0 / M


def corpus_first_step_same(M, ETss, ETst):
    """Descent/PortabilityDrift.lean, decl `twoDemeIMFirstStepSame`

        noncomputable def twoDemeIMFirstStepSame (M _ETss ETst : ℝ) : ℝ :=
          1 / (1 + M) + (M / (1 + M)) * ETst

    Note the corpus discards its own ETss argument here. The recurrence is
    therefore a map that must have the MEASURED ETss as a fixed point, which is
    what C3 checks.
    """
    return 1.0 / (1.0 + M) + (M / (1.0 + M)) * ETst


def corpus_first_step_diff(M, ETss, ETst):
    """Descent/PortabilityDrift.lean, decl `twoDemeIMFirstStepDiff`

        noncomputable def twoDemeIMFirstStepDiff (M ETss _ETst : ℝ) : ℝ :=
          1 / M + ETss
    """
    return 1.0 / M + ETss


def corpus_delta_from_scalars(ETss, ETst):
    """Descent/PortabilityDrift.lean, decls `DemographicCoalescenceScalars.delta`
    and `hudsonFstFromCoalescenceTimes`

        noncomputable def DemographicCoalescenceScalars.delta
            (d : DemographicCoalescenceScalars) : ℝ :=
          hudsonFstFromCoalescenceTimes d.ETss d.ETst

        noncomputable def hudsonFstFromCoalescenceTimes (ETss ETst : ℝ) : ℝ :=
          1 - ETss / ETst

    `twoDemeIMEquilibriumScalars M` is the structure literal
    { ETss := twoDemeIMEquilibriumETss M, ETst := twoDemeIMEquilibriumETst M },
    so composing it with delta is exactly this function applied to the two
    closed forms -- which is how C4 reaches `twoDemeIMEquilibriumScalars`.
    """
    return 1.0 - ETss / ETst


def corpus_delta_closed(M):
    """Descent/PortabilityDrift.lean, decl `twoDemeIMEquilibriumDelta`

        noncomputable def twoDemeIMEquilibriumDelta (M : ℝ) : ℝ :=
          1 / (2 * M + 1)
    """
    return 1.0 / (2.0 * M + 1.0)


def corpus_var_delta_mu(V_A, fst):
    """Descent/PortabilityDrift.lean, decl `Var_Delta_Mu`

        noncomputable def Var_Delta_Mu (V_A fst : ℝ) : ℝ := 2 * fst * V_A

    Reached only through `expectedSqMeanPGSDiff_IMEquilibrium`, which is

        noncomputable def expectedSqMeanPGSDiff_IMEquilibrium (V_A M : ℝ) : ℝ :=
          Var_Delta_Mu V_A (2 * twoDemeIMEquilibriumDelta M)

    REPORTED, NOT SCORED. See the header: the polygenic-score side of this is
    pgs_transport_drift's estimand and belongs to its simulator.
    """
    return 2.0 * fst * V_A


def corpus_expected_sq_mean_pgs_diff_im(V_A, M):
    """Descent/PortabilityDrift.lean, decl `expectedSqMeanPGSDiff_IMEquilibrium`
    (body quoted above). The doubling of delta is the corpus's, not mine."""
    return corpus_var_delta_mu(V_A, 2.0 * corpus_delta_closed(M))


# ===========================================================================
# ENGINE A -- continuous-time sampler.
#
# STATE SPACE for two lineages: SAME deme or DIFFERENT demes, two demes total.
#
# RATES, DECLARED FROM PHYSICAL PRIMITIVES AND NOT FROM M:
#   deme size N diploids, so 2N gene copies and coalescence probability 1/(2N)
#   per generation when co-resident; per-lineage migration probability m per
#   generation. Time is measured in units of 2N generations, so
#       coalescence rate when SAME            = 1
#       per-lineage migration rate            = 2 N m = M/2,  M := 4 N m
#       total migration rate, either state    = M
#   From SAME: competing clocks, total rate 1 + M, coalescing with probability
#   1/(1 + M). From DIFFERENT: no coalescence is possible, and with two demes
#   ANY migration by either lineage reunites them, so the wait is Exp(M).
#
# `mig_scale` multiplies the per-lineage migration rate and is 1.0 everywhere
# except in C6, where it is deliberately wrong.
#
# WHY THE VECTORISED DRAW IS THE SAME DRAW: `rng.exponential(1.0/rate)` with a
# rate ARRAY draws each element from its own exponential independently, and
# `rng.random(k)` likewise. No random state is shared across replicates, so the
# batch is distributionally identical to the loop it replaces -- which is the
# only condition under which vectorising does not silently correlate the
# replicates and destroy the error bars.
# ===========================================================================

def sample_times(M, start_same, n, rng, mig_scale=1.0):
    """Coalescence times for `n` independent lineage pairs, in 2N-generation units.

    Returns (times, n_unresolved, resolved_mask). Unresolved replicates are
    those still alive at MAX_EVENTS; they are returned as a COUNT and masked
    out of the times, never quietly set to the cap. A cell with censoring is a
    different measurement from a cell without, and a bare mean cannot tell them
    apart.
    """
    mu_total = mig_scale * M          # both lineages, either state
    same = np.full(n, bool(start_same))
    t = np.zeros(n)
    resolved = np.zeros(n, dtype=bool)
    idx = np.arange(n)
    events = 0
    while idx.size and events < MAX_EVENTS:
        events += 1
        s = same[idx]
        # total event rate: coalescence (1) competes with migration only in SAME
        rate = np.where(s, 1.0 + mu_total, mu_total)
        t[idx] = t[idx] + rng.exponential(1.0 / rate)
        u = rng.random(idx.size)
        coalesced = s & (u < 1.0 / (1.0 + mu_total))
        resolved[idx[coalesced]] = True
        moved = idx[~coalesced]
        same[moved] = ~same[moved]
        idx = moved
    return t, int(idx.size), resolved


def batch_means(M, start_same, rng, mig_scale=1.0, n_batch=None):
    """One mean per batch. The batch is the replicate unit and the error bar.

    All n_batch * BATCH_REPS pairs are drawn in ONE pass and then reshaped into
    batches. That is the same experiment as drawing batch by batch -- every
    replicate is an independent element of the arrays, and no random state is
    shared between them -- and it replaces a few hundred thousand small numpy
    calls with a few hundred large ones. Reshaping AFTER the draw cannot
    correlate replicates; only sharing a variate could, and nothing here does.

    Records are written per batch rather than per drawn lineage pair: a million
    rows per cell is not a measurement anyone can diff, and the scatter the
    error bar has to describe is carried entirely by the batch means.
    """
    nb = N_BATCH if n_batch is None else n_batch
    t, n_un, resolved = sample_times(M, start_same, nb * BATCH_REPS, rng,
                                     mig_scale)
    tb = t.reshape(nb, BATCH_REPS)
    rb = resolved.reshape(nb, BATCH_REPS)
    counts = rb.sum(axis=1)
    sums = np.where(rb, tb, 0.0).sum(axis=1)
    # A batch with no resolved replicate contributes no mean; summarize()
    # counts the drop rather than averaging around it.
    means = [float(s / c) if c else float("nan")
             for s, c in zip(sums, counts)]
    return means, n_un


def cell(M, rng, mig_scale=1.0, n_batch=None):
    """Both starting states at one M, with per-batch records and batch SEs."""
    ss, un_s = batch_means(M, True, rng, mig_scale, n_batch)
    st, un_d = batch_means(M, False, rng, mig_scale, n_batch)
    return {
        "M": M,
        "mig_scale": mig_scale,
        "batches": N_BATCH if n_batch is None else n_batch,
        "reps_per_batch": BATCH_REPS,
        "ETss": simprov.summarize(ss),
        "ETst": simprov.summarize(st),
        "batch_means_ETss": ss,
        "batch_means_ETst": st,
        "unresolved_ss": un_s,
        "unresolved_st": un_d,
    }


# ===========================================================================
# ENGINE B -- exact discrete-generation solve. Shares no code with Engine A.
#
# Per generation, two lineages, two demes, N diploids each:
#   migration: each lineage moves with probability m.
#     From SAME:  neither moves (1-m)^2 -> SAME; both move -> SAME (they swap
#                 into the same other deme); exactly one moves -> DIFFERENT.
#                 P(SAME->SAME) = (1-m)^2 + m^2,  P(SAME->DIFF) = 2m(1-m)
#     From DIFF:  neither moves -> DIFF; both move -> DIFF (they swap); exactly
#                 one moves -> SAME.  P(DIFF->SAME) = 2m(1-m)
#   coalescence: probability c = 1/(2N) when co-resident.
#
# THE ORDERING IS THE TEST. The corpus's docstring states the composition
# convention is continuous time, where ordering is immaterial, and names the
# discrete-generation alternative as differing at O(1/Ne). That is a testable
# claim that has never been tested, so both orderings are solved exactly and
# both are compared to the continuous answer.
# ===========================================================================

def discrete_expected_times(N, m, order):
    """Exact (E[T_S], E[T_D]) in GENERATIONS, by linear solve. No sampling.

    order = "mig_first": migrate, then attempt coalescence.
        E_S = 1 + Pss (1-c) E_S + Psd E_D
        E_D = 1 + Pds (1-c) E_S + Pdd E_D
      (from DIFF, a pair that lands together may coalesce in the same generation)
    order = "coal_first": attempt coalescence, then migrate.
        E_S = 1 + (1-c) (Pss E_S + Psd E_D)
        E_D = 1 + Pds E_S + Pdd E_D
    """
    c = 1.0 / (2.0 * N)
    pss = (1.0 - m) ** 2 + m ** 2
    psd = 2.0 * m * (1.0 - m)
    pds = psd
    pdd = 1.0 - pds
    if order == "mig_first":
        A = np.array([[1.0 - pss * (1.0 - c), -psd],
                      [-pds * (1.0 - c), 1.0 - pdd]])
    elif order == "coal_first":
        A = np.array([[1.0 - (1.0 - c) * pss, -(1.0 - c) * psd],
                      [-pds, 1.0 - pdd]])
    else:
        raise ValueError("order must be 'mig_first' or 'coal_first'")
    b = np.array([1.0, 1.0])
    x = np.linalg.solve(A, b)
    return float(x[0]), float(x[1])


def discrete_in_coalescent_units(N, M, order):
    """Engine B's answer on Engine A's scale: divide generations by 2N.

    m is recovered from M and N by the SAME definition M = 4 N m the sampler
    uses, so the two engines are being asked the same question in the same
    units without sharing a line of code.
    """
    m = M / (4.0 * N)
    ts, td = discrete_expected_times(N, m, order)
    return ts / (2.0 * N), td / (2.0 * N)


# ===========================================================================
# CHECKS
# ===========================================================================

def base_grid(rng, mig_scale=1.0):
    """Simulate every M cell ONCE. C1 to C4 are four different CLAIMS read off
    the same measurement, not four measurements.

    Said explicitly because it matters for how the results are read: C1 to C4
    are not independent confirmations of each other and must not be quoted as
    if they were. What makes them separate tests is that they interrogate
    different declarations -- the invariant, the closed form, the step map, the
    F_ST -- and each can fail while the others pass. C6 draws its own cells,
    because a positive control that shared draws with the arm it is policing
    could not show that arm failing.
    """
    return dict((M, cell(M, rng, mig_scale)) for M in M_GRID)


def c1(base, out):
    """C1  THE CLOCK CONTROL: E[T_ss] = 2 at every M.

    twoDemeIMEquilibriumETss discards its M argument. This measures whether it
    is entitled to.

    THIS CONTROL CANNOT DECIDE C2 AND THAT IS WHY IT IS A CONTROL. Solving the
    corpus's own first-step pair gives E[T_ss] = 2 whether the per-lineage
    migration rate is M/2 or M -- the migration terms cancel -- so C1 pins the
    coalescence clock and the sampler while remaining blind to the very
    convention under dispute. C6 exercises exactly that blindness.
    """
    print("")
    print("=" * 78)
    print("C1  CLOCK CONTROL -- E[T_ss] = 2 at every M (blind to C2 by design)")
    print("=" * 78)
    rows = []
    ok = True
    for M in M_GRID:
        r = base[M]
        mean = r["ETss"]["mean"]
        se = r["ETss"]["se"] or 0.0
        pred = corpus_ETss(M)
        dev = abs(mean - pred) / max(se, 1e-12)
        good = dev <= 4.0
        ok = ok and good and r["unresolved_ss"] == 0
        # A fresh row per check rather than mutating the shared cell: four
        # checks writing keys into one dict would make the results file report
        # whichever check ran last.
        rows.append({"M": M, "measured": mean, "se": se,
                     "twoDemeIMEquilibriumETss": pred,
                     "deviation_sems": dev,
                     "unresolved_ss": r["unresolved_ss"],
                     "pass": bool(good)})
        print("  M=%-6g  measured %.5f +-%.5f   corpus %.5f   %.2f sems  %s"
              % (M, mean, se, pred, dev, "ok" if good else "FAIL"))
        if r["unresolved_ss"]:
            print("      %d replicates unresolved at the event cap -- COUNTED, "
                  "not dropped" % r["unresolved_ss"])
    # Engine B on the same claim, at the largest Ne, where the discrete chain
    # should have converged onto the continuous one.
    N = max(NE_GRID)
    eng_b = []
    for M in M_GRID:
        ts, _ = discrete_in_coalescent_units(N, M, "mig_first")
        eng_b.append({"M": M, "Ne": N, "ETss_exact": ts})
    print("  ENGINE B (exact solve, Ne=%d): E[T_ss] = %s"
          % (N, ", ".join("%.5f" % e["ETss_exact"] for e in eng_b)))
    out["C1"] = {"cells": rows, "engine_b": eng_b, "pass": bool(ok)}
    return ok


def c2(base, rng, out):
    """C2  THE DECIDING NUMBER.

        kappa(M) = (E[T_st] - 2) * M

    corpus twoDemeIMEquilibriumETst = 2 + 1/M          =>  kappa = 1
    families.py spec, citing Wakeley = 2 + 2/M         =>  kappa = 2

    One number, measured at every M, and the loser is named in the output.

    SPLIT CONTROLS, run in the same arm because each isolates one clock:
      (a) M large: the demes panmict and E[T_st] must fall to E[T_ss] = 2 --
          isolates the coalescence clock with the migration clock switched off
          by saturation.
      (b) M small: E[T_st] must diverge like 1/M (corpus) or 2/M (Wakeley)
          while E[T_ss] stays pinned at 2 -- isolates the migration clock. This
          is the cell where the two candidates are furthest apart.
    """
    print("")
    print("=" * 78)
    print("C2  THE DECIDING NUMBER -- kappa = (E[T_st] - 2) * M")
    print("      corpus twoDemeIMEquilibriumETst -> kappa = 1")
    print("      families.py spec (Wakeley 2 + 2/M) -> kappa = 2")
    print("=" * 78)
    rows = []
    kappas = []
    for M in M_GRID:
        r = base[M]
        mean = r["ETst"]["mean"]
        se = r["ETst"]["se"] or 0.0
        kappa = (mean - 2.0) * M
        kappa_se = se * M
        row = {"M": M, "measured": mean, "se": se,
               "kappa": kappa, "kappa_se": kappa_se,
               "twoDemeIMEquilibriumETst": corpus_ETst(M),
               "families_spec_ETst": families_spec_ETst(M),
               "sems_from_corpus": abs(mean - corpus_ETst(M)) / max(se, 1e-12),
               "sems_from_families_spec": (abs(mean - families_spec_ETst(M))
                                           / max(se, 1e-12)),
               "unresolved_st": r["unresolved_st"]}
        rows.append(row)
        kappas.append((kappa, kappa_se))
        print("  M=%-6g measured %9.5f +-%.5f | corpus %9.5f (%.1f sems) | "
              "spec %9.5f (%.1f sems) | kappa %.4f +-%.4f"
              % (M, mean, se, corpus_ETst(M), row["sems_from_corpus"],
                 families_spec_ETst(M), row["sems_from_families_spec"],
                 kappa, kappa_se))

    # Pooled verdict. Inverse-variance weighted kappa over the grid.
    w = [1.0 / max(s, 1e-12) ** 2 for _, s in kappas]
    kbar = sum(k * wi for (k, _), wi in zip(kappas, w)) / sum(w)
    kbar_se = math.sqrt(1.0 / sum(w))
    d_corpus = abs(kbar - 1.0) / kbar_se
    d_spec = abs(kbar - 2.0) / kbar_se
    if d_corpus <= 4.0 < d_spec:
        verdict = ("CORPUS twoDemeIMEquilibriumETst = (2M+1)/M IS CONFIRMED; "
                   "the families.py spec's cited 2 + 2/M IS REFUTED")
        ok = True
    elif d_spec <= 4.0 < d_corpus:
        verdict = ("families.py spec's 2 + 2/M IS CONFIRMED; the CORPUS "
                   "declaration twoDemeIMEquilibriumETst IS REFUTED")
        ok = True
    else:
        verdict = ("UNDECIDED -- kappa is not within 4 sems of exactly one "
                   "candidate; this is a failure of the RUN, not a finding "
                   "about the corpus")
        ok = False
    print("  pooled kappa = %.5f +-%.5f  (%.1f sems from 1, %.1f sems from 2)"
          % (kbar, kbar_se, d_corpus, d_spec))
    print("  VERDICT: %s" % verdict)

    print("  split controls:")
    # The panmictic cell costs ~M events per replicate, so it runs on a
    # quarter of the batches. It is a limit control on a gap that shrinks like
    # 1/M, not a precision measurement, and its error bar is reported.
    pan = cell(M_PANMICTIC, rng, n_batch=max(4, N_BATCH // 4))
    iso = cell(M_ISOLATED, rng, n_batch=max(4, N_BATCH // 4))
    pan_gap = abs(pan["ETst"]["mean"] - pan["ETss"]["mean"])
    pan_se = math.sqrt((pan["ETst"]["se"] or 0) ** 2
                       + (pan["ETss"]["se"] or 0) ** 2)
    pan_ok = pan_gap <= max(4.0 * pan_se, 0.02)
    print("    (a) panmixia M=%g: E[T_st]-E[T_ss] = %.5f +-%.5f  %s"
          % (M_PANMICTIC, pan_gap, pan_se, "ok" if pan_ok else "FAIL"))
    iso_k = (iso["ETst"]["mean"] - 2.0) * M_ISOLATED
    iso_ss = abs(iso["ETss"]["mean"] - 2.0) / max(iso["ETss"]["se"] or 1e-12, 1e-12)
    iso_ok = iso_ss <= 4.0
    print("    (b) isolation M=%g: E[T_st] = %.3f, kappa %.4f, and E[T_ss] "
          "still 2 to %.1f sems  %s"
          % (M_ISOLATED, iso["ETst"]["mean"], iso_k, iso_ss,
             "ok" if iso_ok else "FAIL"))

    out["C2"] = {"cells": rows, "pooled_kappa": kbar, "pooled_kappa_se": kbar_se,
                 "sems_from_corpus": d_corpus, "sems_from_families_spec": d_spec,
                 "verdict": verdict,
                 "control_panmixia": pan, "control_isolation": iso,
                 "control_panmixia_pass": bool(pan_ok),
                 "control_isolation_pass": bool(iso_ok),
                 "pass": bool(ok and pan_ok and iso_ok)}
    return bool(ok and pan_ok and iso_ok)


def c3(base, out):
    """C3  THE RECURRENCE, SEPARATELY FROM ITS CLOSED FORM.

    twoDemeIMFirstStepSame and twoDemeIMFirstStepDiff are fed the MEASURED
    times and must return them. This splits "the closed form solves the
    recurrence" -- which is algebra and cannot fail -- from "the recurrence
    describes the process", which can. A check that only compared the closed
    forms to the measurement would fuse the two, and a compensating pair of
    errors in the step map and its solution would pass it.
    """
    print("")
    print("=" * 78)
    print("C3  FIRST-STEP RECURRENCE on MEASURED times (algebra split from process)")
    print("=" * 78)
    rows = []
    ok = True
    for M in M_GRID:
        r = base[M]
        ss, st = r["ETss"]["mean"], r["ETst"]["mean"]
        se_s = r["ETss"]["se"] or 0.0
        se_d = r["ETst"]["se"] or 0.0
        back_s = corpus_first_step_same(M, ss, st)
        back_d = corpus_first_step_diff(M, ss, st)
        # Propagate the measurement error through each step map.
        se_back_s = (M / (1.0 + M)) * se_d
        se_back_d = se_s
        d_s = abs(back_s - ss) / max(math.sqrt(se_s ** 2 + se_back_s ** 2), 1e-12)
        d_d = abs(back_d - st) / max(math.sqrt(se_d ** 2 + se_back_d ** 2), 1e-12)
        good = d_s <= 4.0 and d_d <= 4.0
        ok = ok and good
        rows.append({"M": M, "measured_ETss": ss, "measured_ETst": st,
                     "firstStepSame_of_measured": back_s,
                     "firstStepDiff_of_measured": back_d,
                     "same_residual_sems": d_s, "diff_residual_sems": d_d,
                     "pass": bool(good)})
        print("  M=%-6g  same: %.5f -> %.5f (%.2f sems) | diff: %.5f -> %.5f "
              "(%.2f sems)  %s"
              % (M, ss, back_s, d_s, st, back_d, d_d, "ok" if good else "FAIL"))
    out["C3"] = {"cells": rows, "pass": bool(ok)}
    return ok


def c4(base, out):
    """C4  DELTA IS HUDSON'S F_ST, and what it feeds.

    twoDemeIMEquilibriumScalars M is the structure carrying the two closed
    forms; DemographicCoalescenceScalars.delta reads 1 - ETss/ETst off it, and
    twoDemeIMEquilibriumDelta claims that equals 1/(2M+1). Measured delta comes
    from the SAMPLED times, so this compares a corpus identity to a process.

    REPORTED AND NOT SCORED: expectedSqMeanPGSDiff_IMEquilibrium feeds
    2*delta into Var_Delta_Mu as an F_ST. The doubling is the corpus's own and
    is coherent -- expectedSqMeanPGSDiff_pureSplit feeds (fstS + fstT), which
    for two symmetric demes is delta + delta -- but whether Var_Delta_Mu itself
    describes a polygenic score is pgs_transport_drift's estimand. Measuring it
    here would have this file silently re-measure another family and the
    agreement would read as corroboration.
    """
    print("")
    print("=" * 78)
    print("C4  delta = Hudson F_ST, measured; and the F_ST it hands downstream")
    print("=" * 78)
    rows = []
    ok = True
    for M in M_GRID:
        r = base[M]
        ss, st = r["ETss"]["mean"], r["ETst"]["mean"]
        se_s = r["ETss"]["se"] or 0.0
        se_d = r["ETst"]["se"] or 0.0
        d_meas = corpus_delta_from_scalars(ss, st)
        # delta = 1 - ss/st; first-order propagation in both measured means.
        se_delta = math.sqrt((se_s / st) ** 2 + (ss * se_d / st ** 2) ** 2)
        d_pred = corpus_delta_closed(M)
        dev = abs(d_meas - d_pred) / max(se_delta, 1e-12)
        # The same delta read off the corpus's OWN scalars, which is the
        # composition twoDemeIMEquilibriumScalars -> delta.
        d_scalars = corpus_delta_from_scalars(corpus_ETss(M), corpus_ETst(M))
        good = dev <= 4.0
        ok = ok and good
        rows.append({"M": M,
                     "delta_measured": d_meas, "delta_se": se_delta,
                     "twoDemeIMEquilibriumDelta": d_pred,
                     "delta_of_twoDemeIMEquilibriumScalars": d_scalars,
                     "deviation_sems": dev,
                     "fst_handed_to_Var_Delta_Mu": 2.0 * d_pred,
                     "expectedSqMeanPGSDiff_IMEquilibrium_at_V_A_1":
                         corpus_expected_sq_mean_pgs_diff_im(1.0, M),
                     "expectedSqMeanPGSDiff_scored": False,
                     "pass": bool(good)})
        print("  M=%-6g  delta measured %.5f +-%.5f | closed form %.5f "
              "(%.2f sems) | via scalars %.5f | hands 2*delta=%.5f downstream  %s"
              % (M, d_meas, se_delta, d_pred, dev, d_scalars, 2.0 * d_pred,
                 "ok" if good else "FAIL"))
    print("  expectedSqMeanPGSDiff_IMEquilibrium is REPORTED, NOT SCORED: its "
          "polygenic half belongs to pgs_transport_drift.")
    out["C4"] = {"cells": rows, "pass": bool(ok),
                 "expectedSqMeanPGSDiff_IMEquilibrium":
                     "REPORTED NOT SCORED -- polygenic half is "
                     "pgs_transport_drift's estimand"}
    return ok


def c5(out):
    """C5  THE CONVENTION TEST -- the claim that has never been tested.

    The corpus states its composition convention in a docstring: continuous
    time, where the ordering of migration and coalescence within a generation
    is immaterial, with the discrete-generation alternative named as differing
    at O(1/Ne). Engine B solves BOTH orderings exactly at several Ne, so the
    gap and its SCALING are both measured. Exactness matters here: the gap at
    Ne = 5000 is order 1e-4 and no affordable sampler would resolve it.

    The claim is O(1/Ne), so the diagnostic is the RATIO of the gap between
    consecutive Ne, which must track the ratio of 1/Ne. A gap that merely
    "looks small" at one Ne is consistent with O(1/Ne), O(1/Ne^2) and a
    constant alike.
    """
    print("")
    print("=" * 78)
    print("C5  DISCRETE-GENERATION ORDERING -- the O(1/Ne) claim, exact solve")
    print("=" * 78)
    rows = []
    ok = True
    for M in M_GRID:
        prev = None
        for N in NE_GRID:
            ss_m, st_m = discrete_in_coalescent_units(N, M, "mig_first")
            ss_c, st_c = discrete_in_coalescent_units(N, M, "coal_first")
            cont_ss, cont_st = corpus_ETss(M), corpus_ETst(M)
            gap_order = abs(st_m - st_c) / cont_st
            gap_cont = abs(0.5 * (st_m + st_c) - cont_st) / cont_st
            row = {"M": M, "Ne": N,
                   "ETst_mig_first": st_m, "ETst_coal_first": st_c,
                   "ETss_mig_first": ss_m, "ETss_coal_first": ss_c,
                   "continuous_ETst": cont_st,
                   "ordering_gap_rel": gap_order,
                   "discrete_vs_continuous_rel": gap_cont,
                   "times_Ne": gap_order * N}
            if prev is not None:
                # O(1/Ne) means gap*Ne is flat across the Ne axis.
                row["gapNe_ratio_to_previous"] = (
                    (gap_order * N) / prev if prev else None)
            prev = gap_order * N
            rows.append(row)
        # The O(1/Ne) claim, judged on the product gap*Ne being flat.
        #
        # JUDGED ON THE TWO LARGEST Ne ONLY, and the whole series REPORTED.
        # O(1/Ne) is an asymptotic statement, so the small-Ne cells carry
        # higher-order terms that are not evidence against it; scoring the
        # spread across the entire axis would fail the claim for being true
        # only asymptotically, which is what it says.
        prods = [r["times_Ne"] for r in rows if r["M"] == M]
        tail = prods[-2:]
        ratio = (max(tail) / min(tail)) if min(tail) > 0 else float("inf")
        good = ratio <= 1.1
        ok = ok and good
        print("  M=%-6g  ordering gap * Ne = %s  (two largest Ne differ by "
              "%.4f; O(1/Ne) needs 1)  %s"
              % (M, ", ".join("%.4g" % p for p in prods), ratio,
                 "ok" if good else "FAIL"))
    out["C5"] = {"rows": rows, "pass": bool(ok)}
    return ok


def c6(rng, out):
    """C6  POSITIVE CONTROL -- C2 must reject a sampler it should reject.

    The corrupted sampler has its per-lineage migration rate DOUBLED and is
    otherwise the identical code path. Two things must both happen:

      (i)  C1's invariant must STILL HOLD on the corrupted sampler, E[T_ss] = 2.
           This demonstrates the blindness the header claims: the control
           cannot see the error, so an arm resting on C1 alone would pass a
           sampler whose migration rate is wrong by a factor of two.
      (ii) C2's kappa must MOVE to 0.5 and away from 1. This demonstrates that
           C2 can fail, which is the only thing that makes C2's agreement in
           the uncorrupted arm mean anything.

    If (i) fails the corruption was not the one described. If (ii) fails, C2 is
    insensitive to exactly the quantity it was built to measure and NOTHING
    ELSE IN THIS FILE SHOULD BE BELIEVED.
    """
    print("")
    print("=" * 78)
    print("C6  POSITIVE CONTROL -- migration rate doubled; C1 must stay blind, "
          "C2 must fire")
    print("=" * 78)
    rows = []
    ok = True
    for M in M_GRID:
        r = cell(M, rng, mig_scale=2.0)
        ss, st = r["ETss"]["mean"], r["ETst"]["mean"]
        se_s = r["ETss"]["se"] or 0.0
        se_d = r["ETst"]["se"] or 0.0
        blind = abs(ss - 2.0) / max(se_s, 1e-12)
        kappa = (st - 2.0) * M
        kappa_se = se_d * M
        fires = abs(kappa - 1.0) / max(kappa_se, 1e-12) > 4.0
        stays = blind <= 4.0
        good = fires and stays
        ok = ok and good
        r.update({"C1_invariant_sems": blind, "C1_stayed_blind": bool(stays),
                  "kappa": kappa, "kappa_se": kappa_se,
                  "C2_fired": bool(fires), "pass": bool(good)})
        rows.append(r)
        print("  M=%-6g  E[T_ss] %.5f (%.2f sems from 2: C1 %s) | kappa %.4f "
              "+-%.4f (C2 %s)  %s"
              % (M, ss, blind, "blind as designed" if stays else "BROKE",
                 kappa, kappa_se, "FIRED" if fires else "DID NOT FIRE",
                 "ok" if good else "FAIL"))
    out["C6"] = {"cells": rows, "pass": bool(ok)}
    return ok


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="tunable knobs for --set NAME=VALUE:\n" +
               "\n".join("  %-14s %s" % (k, v) for k, v in TUNABLES.items()))
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
    parser.add_argument("--output", default="fam_im_coalescent_results.json")
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
        "empirical/differential/cluster/fam_im_coalescent.py", config, args.seed,
        {"batches_per_cell": N_BATCH, "replicates_per_batch": BATCH_REPS,
         "replicate_unit": "batch; every standard error here is the scatter "
                           "across batches, never a per-draw formula"}),
        "profile": args.profile, "seed": args.seed,
        "overrides": overrides, "config": config,
        "family": "isolation_with_migration_coalescent",
        "members_covered": [
            "twoDemeIMFirstStepSame", "twoDemeIMFirstStepDiff",
            "twoDemeIMEquilibriumETss", "twoDemeIMEquilibriumETst",
            "twoDemeIMEquilibriumScalars", "twoDemeIMEquilibriumDelta",
            "DemographicCoalescenceScalars.delta",
            "expectedSqMeanPGSDiff_IMEquilibrium"],
        "members_not_found_in_corpus": [],
        "members_reported_not_scored": ["expectedSqMeanPGSDiff_IMEquilibrium"],
        "transcribed_against_revision": "a4bc5385",
        "transcription_caveat":
            "Descent/PortabilityDrift.lean differed from origin/main by "
            "uncommitted edits from other sessions at transcription time; the "
            "eight bodies were re-read from the working tree immediately "
            "before commit"}

    # One measurement of the M grid; four checks read different declarations
    # off it. The per-batch records live here, once, rather than being copied
    # into each check's rows.
    base = base_grid(rng)
    out["base_grid"] = [base[M] for M in M_GRID]

    r1 = c1(base, out)
    r2 = c2(base, rng, out)
    r3 = c3(base, out)
    r4 = c4(base, out)
    r5 = c5(out)
    r6 = c6(rng, out)

    print("")
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    checks = (("C1 clock control E[T_ss]=2", r1),
              ("C2 the deciding number kappa", r2),
              ("C3 first-step recurrence", r3),
              ("C4 delta is Hudson F_ST", r4),
              ("C5 discrete ordering O(1/Ne)", r5),
              ("C6 positive control fires", r6))
    for tag, v in checks:
        print("  %-32s %s" % (tag, v))
    print("  VERDICT ON THE DISPUTE: %s" % out["C2"]["verdict"])
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
        # A nonzero exit here is a MEASUREMENT, not a crash, and a harness that
        # collects stderr and finds it empty will read it as one.
        sys.stderr.write(
            "fam_im_coalescent: %d of %d checks FAILED under profile '%s': "
            "%s\n" % (len(failed), len(checks), args.profile,
                      ", ".join(failed)))
        sys.stderr.write(
            "fam_im_coalescent: this is a measurement, not a crash. The full "
            "report is on stdout and the results file was written to %s\n"
            % args.output)
        if args.profile == "quick":
            sys.stderr.write(
                "fam_im_coalescent: profile 'quick' is the bounded "
                "development run; its batch counts are too small for the C2 "
                "verdict to be read as a finding. Use --profile full.\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
