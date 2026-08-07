/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TransferLearningPGS.PGSPortabilityDerivation
-- `sharedLDFromMigration`, `sharedLDFromMigration_lt_one` and `targetLinearRisk` are
-- named below and are declared in the `PortabilityDrift` subsystem.  They used to
-- arrive through the head of this directory, which no longer carries that subsystem
-- because it does not use it.  The module that does use it names it.
import Descent.Portability.PortabilityDrift

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Program`:
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.Portability

open MeasureTheory Finset

/-!
# `TransferLearningPGS.FineTuning`

Part of the split of `Descent/Portability/TransferLearningPGS.lean`, which was 3,558 lines.

The parts are a FAN: each imports the parts that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against its siblings'
declarations, and the imports above are the answer, so what a part rests on is readable
from its header instead of inherited from its position in a file that no longer exists.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



/-!
## Fine-Tuning and Few-Shot Adaptation

Adapting a source-population PGS to a target population with limited target-population data.
-/

section FineTuning

/-- Fine-tuned target `R²` in a simple additive penalty model. -/
def fineTunedTargetR2 (r2_source divergence_penalty adaptation_gain : ℝ) : ℝ :=
  r2_source - divergence_penalty + adaptation_gain

/-- **Divergence and adaptation enter with opposite signs and equal weight.**

The three-term budget is additive, so a divergence penalty is cancelled exactly by an equal
adaptation gain and the fine-tuned accuracy returns to the source's. That symmetry is the content
of the model -- it says the two effects are commensurable and trade one for one -- and a body
weighting them differently would still be monotone in each argument, which is all the surrounding
comparisons require. -/
theorem fineTunedTargetR2_cancels (r2_source d : ℝ) :
    fineTunedTargetR2 r2_source d d = r2_source := by
  unfold fineTunedTargetR2
  ring

/-- Target-trained `R²` in a simple additive estimation-penalty model. -/
noncomputable def scratchTargetR2 (oracle_target_r2 estimation_penalty : ℝ) : ℝ :=
  Descent.Core.difference oracle_target_r2 estimation_penalty

/-- Canonical deployed target `R²` for transfer/adaptation methods: start from
    an explicit transported target baseline, add any target-specific adaptation
    gain, and subtract any finite-sample estimation penalty. This is the shared
    target-metric surface that both fine-tuning and scratch training reduce to. -/
def deployedTransferTargetR2
    (transported_r2 adaptation_gain estimation_penalty : ℝ) : ℝ :=
  transported_r2 + adaptation_gain - estimation_penalty

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem deployedTransferTargetR2_at_reference_point :
    deployedTransferTargetR2 (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  unfold deployedTransferTargetR2
  norm_num

/-- The target-only oracle gap above an explicit transported target baseline. This
    is the amount of target-specific gain available beyond that transported
    `R²` before any estimation penalty is paid. -/
def oracleTransportAdaptationGain
    (transported_r2 oracle_target_r2 : ℝ) : ℝ :=
  oracle_target_r2 - transported_r2

/-- **The adaptation gain's orientation, pinned.** This definition carries no result of its own,
and its entire content is the direction of the subtraction. The gain is what refitting in the
target would buy over transporting the source score, so it is positive when the oracle beats the
transported score. -/
theorem oracleTransportAdaptationGain_positive_when_oracle_wins :
    oracleTransportAdaptationGain 1 3 = 2 := by
  unfold oracleTransportAdaptationGain
  norm_num

/-- Portability penalty as the literal gap between a source baseline and an
    explicitly supplied transported target baseline. -/
noncomputable def transportPenalty
    (source_r2 transported_r2 : ℝ) : ℝ :=
  Descent.Core.difference source_r2 transported_r2

/-- **The transport penalty's orientation, pinned.** This definition carries no result of its
own. The penalty is what transporting COSTS relative to performance in the source population, so
it is positive when the score does worse after transport. -/
theorem transportPenalty_positive_when_transport_costs :
    transportPenalty 3 1 = 2 := by
  unfold transportPenalty Descent.Core.difference
  norm_num

/-- The additive fine-tuning model is exactly the transported target baseline
    plus any additional target-specific adaptation gain once the portability
    penalty is instantiated by the literal source-minus-transported gap. -/
theorem fineTunedTargetR2_eq_transportedR2_plus_adaptation
    (source_r2 transported_r2 adaptationGain : ℝ) :
    fineTunedTargetR2 source_r2
        (transportPenalty source_r2 transported_r2)
        adaptationGain =
      transported_r2 + adaptationGain := by
  unfold fineTunedTargetR2 transportPenalty Descent.Core.difference
  ring

/-- Fine-tuning is exactly the canonical deployed-transfer target `R²` with an
    explicit transported baseline, target-specific adaptation gain, and zero
    estimation penalty. -/
theorem fineTunedTargetR2_eq_deployedTransferTargetR2
    (source_r2 transported_r2 adaptationGain : ℝ) :
    fineTunedTargetR2 source_r2
        (transportPenalty source_r2 transported_r2)
        adaptationGain =
      deployedTransferTargetR2 transported_r2 adaptationGain 0 := by
  rw [fineTunedTargetR2_eq_transportedR2_plus_adaptation]
  unfold deployedTransferTargetR2
  ring

/-- Target-only oracle `R²` in the diagonal-LD architecture model. This is the
    target self-prediction ceiling, i.e. target additive heritability.

    Regime: independent standardized variants; the score is built from the
    TARGET's own effects, which is what makes it a ceiling rather than a
    transported score.

    Empirical status: **VALIDATED** (`simcov/battery_bulk27.py`). Measured as
    the realised squared correlation between the target's own true score and
    the target phenotype, over 300 variants and 300000 individuals; worst cell
    2.63 sems at 0.67% relative. It exceeds `transportedTargetR2DiagonalLD` in
    every cell, which is the ceiling property the name claims, and the gap
    closes as `rg → 1` exactly as effect turnover predicts.

    Power: the shared `pgsR2` shape is discriminated on the same runs -- see
    `transportedTargetR2DiagonalLD`, where the unsquared-covariance and
    omitted-variance forms are rejected at 1364 and 212 sems. -/
noncomputable def targetOracleR2DiagonalLD {m : ℕ}
    (β_target : Fin m → ℝ) (var_y : ℝ) : ℝ :=
  sourceSelfR2DiagonalLD β_target var_y

/-- The scratch-training scalar model becomes the exact target heritability
    ceiling minus the chosen estimation penalty once the oracle target `R²` is
    instantiated by the target architecture. -/
theorem scratchTargetR2_eq_targetHeritability_minus_estimationPenalty_diagonalLD
    {m : ℕ}
    (β_target : Fin m → ℝ) (var_y estimation_penalty : ℝ)
    (h_var_y : 0 < var_y)
    (h_beta_nonzero : 0 < additiveGeneticVariance β_target) :
    scratchTargetR2 (targetOracleR2DiagonalLD β_target var_y) estimation_penalty =
      additiveHeritability β_target var_y - estimation_penalty := by
  unfold scratchTargetR2 targetOracleR2DiagonalLD Descent.Core.difference
  rw [sourceOptimalR2_eq_additiveHeritability β_target var_y h_var_y h_beta_nonzero]

/-- Scratch training is also exactly the canonical deployed-transfer target
    `R²`: the baseline is the chosen transported target `R²`, the adaptation
    gain is the oracle gap above that transported baseline, and the estimator
    pays the explicit estimation penalty. -/
theorem scratchTargetR2_eq_deployedTransferTargetR2
    (transported_r2 oracle_target_r2 estimation_penalty : ℝ) :
    scratchTargetR2 oracle_target_r2 estimation_penalty =
      deployedTransferTargetR2 transported_r2
        (oracleTransportAdaptationGain transported_r2 oracle_target_r2)
        estimation_penalty := by
  unfold scratchTargetR2 deployedTransferTargetR2 oracleTransportAdaptationGain
    Descent.Core.difference
  ring

/-- The canonical deployed-transfer target `R²` can always be rewritten as the
    target oracle ceiling minus any residual post-transfer gap and minus any
    explicit estimation penalty. This is the common algebraic form behind the
    scratch, fine-tuning, and meta-learning specializations below. -/
theorem deployedTransferTargetR2_eq_oracle_minus_residualGap_minus_estimationPenalty
    (transported_r2 oracle_target_r2 residual_gap estimation_penalty : ℝ) :
    deployedTransferTargetR2 transported_r2
        (oracleTransportAdaptationGain transported_r2 oracle_target_r2 - residual_gap)
        estimation_penalty =
      oracle_target_r2 - residual_gap - estimation_penalty := by
  unfold deployedTransferTargetR2 oracleTransportAdaptationGain
  ring

/-- **Fine-tuning wins in the explicit additive penalty model.**
    This theorem does not claim a universal fine-tuning advantage. It works in
    the two formal score models above:

    - `fineTunedTargetR2` starts from source `R²`, pays a portability penalty,
      and gains target-specific adaptation;
    - `scratchTargetR2` starts from an oracle target ceiling and pays a
      finite-sample estimation penalty.

    If the fine-tuned baseline `r2_source + adaptation_gain` weakly exceeds the
    scratch oracle ceiling, and the scratch estimator pays a larger penalty than
    the fine-tuning portability cost, then the modeled fine-tuned target `R²`
    exceeds the modeled scratch target `R²`. -/
theorem fine_tuned_target_r2_exceeds_scratch_of_penalty_gap
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 estimation_penalty : ℝ)
    (h_baseline : oracle_target_r2 ≤ r2_source + adaptation_gain)
    (h_penalty : divergence_penalty < estimation_penalty) :
    scratchTargetR2 oracle_target_r2 estimation_penalty <
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain := by
  unfold scratchTargetR2 fineTunedTargetR2 Descent.Core.difference
  linarith

/-- Scratch-trained target `R²` with finite-sample estimation noise
    `noiseVar / nTarget`.

    Regime: `noiseVar / nTarget ≤ oracle_target_r2`. The subtraction is a
    first-order estimation penalty and is only a model of `R²` while it stays
    below the ceiling it is subtracted from. Outside that regime it returns
    values no `R²` can take: at `oracle_target_r2 = 1e-4`, `noiseVar = 1000`,
    `nTarget = 1` it is `-1000`.
    `sampleLimitedScratchTargetR2_negative_of_small_sample` exhibits the escape
    and `sampleLimitedScratchTargetR2_nonneg` states the condition that
    excludes it. `usableScratchTargetR2` is the clamped variant for callers who
    cannot discharge the regime; it is offered rather than substituted here
    because clamping would assert that the estimator still attains `0` at
    sample sizes where this model has simply left its domain, and that is a
    modelling claim the development has no evidence for.

    Empirical status: UNTESTED inside the regime; FALSIFIED outside it, where
    the value is not an `R²`. -/
noncomputable def sampleLimitedScratchTargetR2
    (oracle_target_r2 noiseVar nTarget : ℝ) : ℝ :=
  scratchTargetR2 oracle_target_r2 (noiseVar / nTarget)

/-- **The range escape, exhibited.**  Once the estimation penalty exceeds the
oracle ceiling the modelled `R²` goes negative, without bound. -/
theorem sampleLimitedScratchTargetR2_negative_of_small_sample
    (oracle_target_r2 noiseVar nTarget : ℝ)
    (h : oracle_target_r2 < noiseVar / nTarget) :
    sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget < 0 := by
  unfold sampleLimitedScratchTargetR2 scratchTargetR2 Descent.Core.difference
  linarith

/-- **The condition that keeps it an `R²`.**  This is the regime declared on the
definition, stated as a hypothesis a caller can discharge. -/
theorem sampleLimitedScratchTargetR2_nonneg
    (oracle_target_r2 noiseVar nTarget : ℝ)
    (h : noiseVar / nTarget ≤ oracle_target_r2) :
    0 ≤ sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget := by
  unfold sampleLimitedScratchTargetR2 scratchTargetR2 Descent.Core.difference
  linarith

/-- **Clamped scratch-trained target `R²`.**

The same model, floored at `0`: a predictor is never worse than the population
mean in the `R²` a deployment would report, because the mean is always
available. Use this where the sample size is not known to satisfy the regime on
`sampleLimitedScratchTargetR2`; the two agree inside it
(`usableScratchTargetR2_eq_of_nonneg`), and `0` is attained rather than
approached, which is the correct behaviour at sample sizes carrying no usable
signal.

    Empirical status: UNTESTED. -/
noncomputable def usableScratchTargetR2
    (oracle_target_r2 noiseVar nTarget : ℝ) : ℝ :=
  max 0 (sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget)

/-- Inside the regime the clamp does nothing, so no downstream result changes
meaning. -/
theorem usableScratchTargetR2_eq_of_nonneg
    (oracle_target_r2 noiseVar nTarget : ℝ)
    (h : noiseVar / nTarget ≤ oracle_target_r2) :
    usableScratchTargetR2 oracle_target_r2 noiseVar nTarget =
      sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget :=
  max_eq_right (sampleLimitedScratchTargetR2_nonneg oracle_target_r2 noiseVar nTarget h)

/-- The clamped variant never leaves `[0, ∞)`, which is the range property the
unclamped model lacks. -/
theorem usableScratchTargetR2_nonneg
    (oracle_target_r2 noiseVar nTarget : ℝ) :
    0 ≤ usableScratchTargetR2 oracle_target_r2 noiseVar nTarget :=
  le_max_left _ _

/-- **The zero floor is attained**, at any sample size where the estimation
penalty reaches the oracle ceiling: no usable signal, and the model says so
rather than reporting a negative number. -/
theorem usableScratchTargetR2_eq_zero_of_exhausted
    (oracle_target_r2 noiseVar nTarget : ℝ)
    (h : oracle_target_r2 ≤ noiseVar / nTarget) :
    usableScratchTargetR2 oracle_target_r2 noiseVar nTarget = 0 := by
  unfold usableScratchTargetR2
  apply max_eq_left
  unfold sampleLimitedScratchTargetR2 scratchTargetR2 Descent.Core.difference
  linarith

/-- Sample-limited scratch training is the exact target heritability ceiling
    minus the explicit finite-sample estimation penalty `noiseVar / nTarget`. -/
theorem sampleLimitedScratchTargetR2_eq_targetHeritability_minus_noise_over_n_diagonalLD
    {m : ℕ}
    (β_target : Fin m → ℝ) (var_y noiseVar nTarget : ℝ)
    (h_var_y : 0 < var_y)
    (h_beta_nonzero : 0 < additiveGeneticVariance β_target) :
    sampleLimitedScratchTargetR2 (targetOracleR2DiagonalLD β_target var_y) noiseVar nTarget =
      additiveHeritability β_target var_y - noiseVar / nTarget := by
  unfold sampleLimitedScratchTargetR2 scratchTargetR2 targetOracleR2DiagonalLD
    Descent.Core.difference
  rw [sourceOptimalR2_eq_additiveHeritability β_target var_y h_var_y h_beta_nonzero]

/-- Sample-limited scratch training is the canonical deployed-transfer target
    `R²` with an explicit transported baseline, the oracle target gap above
    that baseline, and the explicit finite-sample penalty `noiseVar / nTarget`. -/
theorem sampleLimitedScratchTargetR2_eq_deployedTransferTargetR2
    {m : ℕ}
    (β_target : Fin m → ℝ)
    (var_y transported_r2 noiseVar nTarget : ℝ) :
    sampleLimitedScratchTargetR2 (targetOracleR2DiagonalLD β_target var_y) noiseVar nTarget =
      deployedTransferTargetR2
        transported_r2
        (oracleTransportAdaptationGain
          transported_r2
          (targetOracleR2DiagonalLD β_target var_y))
        (noiseVar / nTarget) := by
  unfold sampleLimitedScratchTargetR2
  simpa using scratchTargetR2_eq_deployedTransferTargetR2
    transported_r2
    (targetOracleR2DiagonalLD β_target var_y)
    (noiseVar / nTarget)

/-- In the diagonal-LD target architecture model, sample-limited scratch
    training is exactly an explicit transported target baseline plus the target
    heritability gap above that transported baseline, minus the finite-sample
    estimation penalty. -/
theorem sampleLimitedScratchTargetR2_eq_coreTransport_plus_targetHeritabilityGap_minus_noise
    {m : ℕ}
    (β_target : Fin m → ℝ)
    (var_y transported_r2 noiseVar nTarget : ℝ)
    (h_var_y : 0 < var_y)
    (h_beta_nonzero : 0 < additiveGeneticVariance β_target) :
    sampleLimitedScratchTargetR2 (targetOracleR2DiagonalLD β_target var_y) noiseVar nTarget =
      deployedTransferTargetR2
        transported_r2
        (additiveHeritability β_target var_y -
          transported_r2)
        (noiseVar / nTarget) := by
  rw [sampleLimitedScratchTargetR2_eq_targetHeritability_minus_noise_over_n_diagonalLD
    β_target var_y noiseVar nTarget h_var_y h_beta_nonzero]
  unfold deployedTransferTargetR2
  ring

/-- Exact target sample size at which scratch training matches fine-tuning in
    the explicit additive `R²` model above. -/
noncomputable def scratchVsFineTuningCriticalSampleSize
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar : ℝ) : ℝ :=
  noiseVar /
    (oracle_target_r2 -
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain)

/-- **Scratch training matches fine-tuning at the derived critical sample size.**
    In the explicit model
    `scratchTargetR2 = oracle_target_r2 - noiseVar / nTarget`,
    the crossover point is solved exactly rather than assumed. -/
theorem scratchTargetR2_eq_fineTunedTargetR2_at_critical_sample_size
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar : ℝ)
    (h_gap :
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain <
        oracle_target_r2)
    (h_noise : 0 < noiseVar) :
    sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar
        (scratchVsFineTuningCriticalSampleSize
          r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar) =
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain := by
  unfold sampleLimitedScratchTargetR2 scratchVsFineTuningCriticalSampleSize
    scratchTargetR2 fineTunedTargetR2 Descent.Core.difference
  have h_gap_pos :
      0 < oracle_target_r2 - (r2_source - divergence_penalty + adaptation_gain) := by
    unfold fineTunedTargetR2 at h_gap
    linarith
  field_simp [ne_of_gt h_gap_pos, ne_of_gt h_noise]
  ring_nf

/-- **Scratch training beats fine-tuning exactly above a derived sample threshold.**
    In the explicit additive `R²` model, the target-only estimator overtakes
    fine-tuning if and only if the target sample size exceeds the exact
    crossover `noiseVar / (oracle_target_r2 - fineTunedTargetR2)`. -/
theorem scratch_beats_fine_tuning_iff_target_sample_exceeds_critical
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar nTarget : ℝ)
    (h_gap :
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain <
        oracle_target_r2)
    (h_n : 0 < nTarget) :
    fineTunedTargetR2 r2_source divergence_penalty adaptation_gain <
      sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget ↔
    scratchVsFineTuningCriticalSampleSize
        r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar <
      nTarget := by
  have h_gap_pos :
      0 < oracle_target_r2 -
        fineTunedTargetR2 r2_source divergence_penalty adaptation_gain :=
    sub_pos.mpr h_gap
  constructor
  · intro h
    unfold sampleLimitedScratchTargetR2 scratchVsFineTuningCriticalSampleSize
      scratchTargetR2 Descent.Core.difference at *
    have hineq :
        noiseVar / nTarget <
          oracle_target_r2 -
            fineTunedTargetR2 r2_source divergence_penalty adaptation_gain := by
      linarith
    have hcross :
        noiseVar <
          nTarget *
            (oracle_target_r2 -
              fineTunedTargetR2 r2_source divergence_penalty adaptation_gain) := by
      rw [div_lt_iff₀ h_n] at hineq
      simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
    rw [div_lt_iff₀ h_gap_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
  · intro h
    unfold sampleLimitedScratchTargetR2 scratchVsFineTuningCriticalSampleSize
      scratchTargetR2 Descent.Core.difference at *
    have hcross :
        noiseVar <
          nTarget *
            (oracle_target_r2 -
              fineTunedTargetR2 r2_source divergence_penalty adaptation_gain) := by
      rw [div_lt_iff₀ h_gap_pos] at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hineq :
        noiseVar / nTarget <
          oracle_target_r2 -
            fineTunedTargetR2 r2_source divergence_penalty adaptation_gain := by
      rw [div_lt_iff₀ h_n]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
    linarith

/-- **Target fine-tuning shrinkage MSE.**
    We model the fine-tuned estimator as a convex combination of the unbiased
    target-only estimator and the source estimator, with source weight `λ`.

    - `gapSq` is the squared source-target effect mismatch.
    - `noiseVar` is the per-sample target estimation variance scale.
    - `noiseVar / nTarget` is the variance of the target-only estimator.

    The resulting MSE decomposes into:
    - squared transfer bias: `gapSq * λ^2`
    - residual target-estimation variance: `(noiseVar / nTarget) * (1 - λ)^2`. -/
noncomputable def sourceShrinkageMSE (gapSq noiseVar nTarget lam : ℝ) : ℝ :=
  gapSq * lam^2 + (noiseVar / nTarget) * (1 - lam)^2

/-- **sourceShrinkageMSE at its junk point, named.** With no target samples the estimation term
`noiseVar / nTarget` is unbounded and no shrinkage weight is safe. The divisor is zero, that
term vanishes, and the mean squared error reduces to the bias term alone -- so the optimiser is
free to take `lam` toward one and is told it costs nothing. Consumers must exclude the argument
that makes the guard vanish. -/
theorem sourceShrinkageMSE_zero_target_samples_is_junk (gapSq noiseVar lam : ℝ) :
    sourceShrinkageMSE gapSq noiseVar 0 lam = gapSq * lam ^ 2 := by
  unfold sourceShrinkageMSE
  simp

/-- **Exact optimizer of the source-shrinkage MSE.**
    In the explicit bias-variance model above, the unique minimizer is
    `(noiseVar / nTarget) / (gapSq + noiseVar / nTarget)`. This is derived from the
    quadratic objective, not assumed. -/
noncomputable def optimalSourceShrinkageWeight (gapSq noiseVar nTarget : ℝ) : ℝ :=
  (noiseVar / nTarget) / (gapSq + noiseVar / nTarget)

/-- **optimalSourceShrinkageWeight where its denominator vanishes, named.** The guard `gapSq +
noiseVar / nTarget` is zero at `gapSq = 0`, `noiseVar = 0`, `nTarget = 1`. Lean returns `0`
there rather than the value the modelled quantity takes, and no type error marks the point.
Consumers must require `gapSq + noiseVar / nTarget ≠ 0`. -/
theorem optimalSourceShrinkageWeight_at_gapsq0noisevar0ntarget1_is_junk :
    optimalSourceShrinkageWeight 0 0 1 = 0 := by
  unfold optimalSourceShrinkageWeight
  norm_num

/-- **With no transfer gap the optimal weight is one: keep the source entirely.** The quadratic
decomposition below holds around whatever the optimum is and does not say where it sits; this
does, and it is the endpoint that distinguishes a shrinkage rule from its complement. -/
theorem optimalSourceShrinkageWeight_no_gap (noiseVar nTarget : ℝ)
    (h : noiseVar / nTarget ≠ 0) :
    optimalSourceShrinkageWeight 0 noiseVar nTarget = 1 := by
  unfold optimalSourceShrinkageWeight
  rw [zero_add, div_self h]

/-- Exact quadratic decomposition around the optimal source weight. -/
theorem sourceShrinkageMSE_eq_optimal_plus_square
    (gapSq noiseVar nTarget lam : ℝ)
    (h_curv : gapSq + noiseVar / nTarget ≠ 0) :
    sourceShrinkageMSE gapSq noiseVar nTarget lam =
      gapSq * (noiseVar / nTarget) / (gapSq + noiseVar / nTarget) +
        (gapSq + noiseVar / nTarget) *
          (lam - optimalSourceShrinkageWeight gapSq noiseVar nTarget)^2 := by
  set b : ℝ := noiseVar / nTarget
  have h_curv' : gapSq + b ≠ 0 := by simpa [b] using h_curv
  have hquad :
      gapSq * lam ^ 2 + b * (1 - lam)^2 =
        gapSq * b / (gapSq + b) +
          (gapSq + b) * (lam - b / (gapSq + b))^2 := by
    field_simp [h_curv']
    ring_nf
  simpa [sourceShrinkageMSE, optimalSourceShrinkageWeight, b] using hquad

/-- Closed-form optimizer rewritten with the original denominator. -/
theorem optimalSourceShrinkageWeight_eq_closed_form
    (gapSq noiseVar nTarget : ℝ)
    (h_n : 0 < nTarget)
    (h_curv : gapSq + noiseVar / nTarget ≠ 0) :
    optimalSourceShrinkageWeight gapSq noiseVar nTarget =
      noiseVar / (nTarget * gapSq + noiseVar) := by
  have hn_ne : nTarget ≠ 0 := ne_of_gt h_n
  have h_denom : nTarget * gapSq + noiseVar ≠ 0 := by
    intro h_zero
    apply h_curv
    have hmul : nTarget * (gapSq + noiseVar / nTarget) = 0 := by
      calc
        nTarget * (gapSq + noiseVar / nTarget) = nTarget * gapSq + noiseVar := by
          field_simp [hn_ne]
        _ = 0 := h_zero
    rcases mul_eq_zero.mp hmul with h0 | h0
    · exact False.elim (hn_ne h0)
    · exact h0
  unfold optimalSourceShrinkageWeight
  field_simp [hn_ne, h_curv, h_denom]

/-- **The explicit source-shrinkage weight minimizes the fine-tuning MSE.**
    This is a true optimization theorem for the quadratic transfer-bias /
    target-variance objective above. -/
theorem optimalSourceShrinkageWeight_minimizes_mse
    (gapSq noiseVar nTarget lam : ℝ)
    (h_gapSq : 0 ≤ gapSq)
    (h_noise : 0 ≤ noiseVar)
    (h_n : 0 < nTarget) :
    sourceShrinkageMSE gapSq noiseVar nTarget
        (optimalSourceShrinkageWeight gapSq noiseVar nTarget) ≤
      sourceShrinkageMSE gapSq noiseVar nTarget lam := by
  have hcoeff_nonneg : 0 ≤ gapSq + noiseVar / nTarget := by
    have hdiv_nonneg : 0 ≤ noiseVar / nTarget :=
      div_nonneg h_noise (le_of_lt h_n)
    linarith
  by_cases h_curv : gapSq + noiseVar / nTarget = 0
  · have hdiv_zero : noiseVar / nTarget = 0 := by
      have hdiv_nonneg : 0 ≤ noiseVar / nTarget :=
        div_nonneg h_noise (le_of_lt h_n)
      linarith
    have h_gap_zero : gapSq = 0 := by
      have hdiv_nonneg : 0 ≤ noiseVar / nTarget :=
        div_nonneg h_noise (le_of_lt h_n)
      linarith
    have h_noise_zero : noiseVar = 0 := by
      have hn_ne : nTarget ≠ 0 := ne_of_gt h_n
      have hmul : (noiseVar / nTarget) * nTarget = 0 := by
        simpa using congrArg (fun x : ℝ ↦ x * nTarget) hdiv_zero
      calc
        noiseVar = (noiseVar / nTarget) * nTarget := by
          field_simp [hn_ne]
        _ = 0 := hmul
    simp [sourceShrinkageMSE, optimalSourceShrinkageWeight, h_gap_zero, h_noise_zero]
  · rw [sourceShrinkageMSE_eq_optimal_plus_square gapSq noiseVar nTarget lam h_curv]
    have hsquare_nonneg :
        0 ≤ (gapSq + noiseVar / nTarget) *
          (lam - optimalSourceShrinkageWeight gapSq noiseVar nTarget)^2 :=
      mul_nonneg hcoeff_nonneg (sq_nonneg _)
    have h_at_opt :
        sourceShrinkageMSE gapSq noiseVar nTarget
            (optimalSourceShrinkageWeight gapSq noiseVar nTarget) =
          gapSq * (noiseVar / nTarget) / (gapSq + noiseVar / nTarget) := by
      rw [sourceShrinkageMSE_eq_optimal_plus_square gapSq noiseVar nTarget
        (optimalSourceShrinkageWeight gapSq noiseVar nTarget) h_curv]
      ring
    rw [h_at_opt]
    linarith

/-- **Optimal regularization decreases with target sample size.**
    In the explicit shrinkage-MSE model above, the source weight solving the
    optimization problem is
    `noiseVar / (nTarget * gapSq + noiseVar)`. Hence, with a fixed transfer gap
    and fixed per-sample target noise, more target data strictly decreases the
    optimal amount of shrinkage toward the source PGS. -/
theorem optimal_lambda_decreases_with_n
    (gapSq noiseVar : ℝ) (n₁ n₂ : ℕ)
    (h_gapSq : 0 < gapSq)
    (h_noise : 0 < noiseVar)
    (h_n₁ : 0 < n₁)
    (h_more_data : n₁ < n₂) :
    optimalSourceShrinkageWeight gapSq noiseVar n₂ <
      optimalSourceShrinkageWeight gapSq noiseVar n₁ := by
  have h_n₂ : 0 < n₂ := lt_trans h_n₁ h_more_data
  have h_curv₁ : gapSq + noiseVar / (n₁ : ℝ) ≠ 0 := by
    have h_pos : 0 < gapSq + noiseVar / (n₁ : ℝ) := by
      have hn₁_real : 0 < (n₁ : ℝ) := Nat.cast_pos.mpr h_n₁
      have hdiv_pos : 0 < noiseVar / (n₁ : ℝ) :=
        div_pos h_noise hn₁_real
      linarith
    linarith
  have h_curv₂ : gapSq + noiseVar / (n₂ : ℝ) ≠ 0 := by
    have hn₂_real : 0 < (n₂ : ℝ) := Nat.cast_pos.mpr h_n₂
    have h_pos : 0 < gapSq + noiseVar / (n₂ : ℝ) := by
      have hdiv_pos : 0 < noiseVar / (n₂ : ℝ) :=
        div_pos h_noise hn₂_real
      linarith
    linarith
  rw [optimalSourceShrinkageWeight_eq_closed_form gapSq noiseVar (n₂ : ℝ)
      (Nat.cast_pos.mpr h_n₂) h_curv₂,
    optimalSourceShrinkageWeight_eq_closed_form gapSq noiseVar (n₁ : ℝ)
      (Nat.cast_pos.mpr h_n₁) h_curv₁]
  apply div_lt_div_of_pos_left h_noise
  · have hn₁_real : 0 < (n₁ : ℝ) := Nat.cast_pos.mpr h_n₁
    nlinarith
  · have hcast : (n₁ : ℝ) < (n₂ : ℝ) := by
      exact_mod_cast h_more_data
    nlinarith

/-- **The optimal source weight drops below one-half exactly past a target
    sample threshold.**
    In the explicit shrinkage-MSE model, this gives an interpretable
    sample-complexity criterion for when the target data should dominate the
    source PGS in the optimal convex combination. -/
theorem optimalSourceShrinkageWeight_le_half_iff_target_samples_dominate_gap
    (gapSq noiseVar nTarget : ℝ)
    (h_gapSq : 0 < gapSq)
    (h_noise : 0 < noiseVar)
    (h_n : 0 < nTarget) :
    optimalSourceShrinkageWeight gapSq noiseVar nTarget ≤ 1 / 2 ↔
      noiseVar ≤ nTarget * gapSq := by
  have h_curv : gapSq + noiseVar / nTarget ≠ 0 := by
    have h_pos : 0 < gapSq + noiseVar / nTarget :=
      add_pos h_gapSq (div_pos h_noise h_n)
    linarith
  have h_denom_pos : 0 < nTarget * gapSq + noiseVar := by
    nlinarith
  rw [optimalSourceShrinkageWeight_eq_closed_form gapSq noiseVar nTarget h_n h_curv]
  constructor
  · intro h
    have h_cross : noiseVar ≤ (1 / 2 : ℝ) * (nTarget * gapSq + noiseVar) :=
      (div_le_iff₀ h_denom_pos).1 h
    nlinarith
  · intro h
    exact (div_le_iff₀ h_denom_pos).2 (by nlinarith)

/-- Squared coefficient mismatch between a transported source predictor and the
    target-optimal linear predictor. This is the exact bias term appearing in
    the source-shrinkage fine-tuning MSE. -/
noncomputable def coefficientGapSq {p : ℕ}
    (wSource wTarget : Fin p → ℝ) : ℝ :=
  dotProduct (fun i ↦ wSource i - wTarget i) (fun i ↦ wSource i - wTarget i)

/-- The squared coefficient gap is a sum of squares, so it is never negative.
    Proved here rather than assumed, so no downstream theorem has to receive
    `0 ≤ irreducibleGap` as a gift. -/
theorem coefficientGapSq_nonneg {p : ℕ} (wSource wTarget : Fin p → ℝ) :
    0 ≤ coefficientGapSq wSource wTarget := by
  have h :
      coefficientGapSq wSource wTarget =
        ∑ i : Fin p, (wSource i - wTarget i) * (wSource i - wTarget i) := rfl
  rw [h]
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _

/-- Sum of the first `k` population-specific deviations around a shared
    representation center. -/
noncomputable def populationDeviationSum {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i ↦ Finset.sum (Finset.range k) (fun j ↦ deviation j i)

/-- Mean population-specific deviation after training on the first `k`
    source populations. -/
noncomputable def meanPopulationDeviation {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i ↦ (k : ℝ)⁻¹ * populationDeviationSum deviation k i

/-- Meta-learned source weights: a shared center plus the average
    source-population-specific deviation. -/
noncomputable def metaLearnedSourceWeights {p : ℕ}
    (wShared : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i ↦ wShared i + meanPopulationDeviation deviation k i

/-- Population-specific effect deviation around a shared ancestral-effect
    center. This is the closed-form effect-architecture object whose average is used
    by the meta-learning block below.

    The population index is left general. This was two definitions with identical
    bodies, one indexed by `ℕ` and one by `Fin k`; nothing in the deviation depends on
    which, so the index is a parameter rather than a reason for a second definition.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is what "deviation around a
    center" MEANS. Both arguments are supplied by the caller and the body is
    their difference; no population can exhibit a `wSource` and a `wShared`
    whose deviation is something other than `wSource - wShared`, so there is
    nothing a measurement could agree or disagree with. It has no free
    parameter and relates no two measurable quantities.

    The empirical content is in what is built ON it and is claimed there:
    `metaLearnedSourceWeights` asserts that averaging these deviations recovers
    the mean source effect vector (`metaLearnedSourceWeights_eq_sourcePopulationMeanWeights`),
    and `weightedMetaTransferGapSq` asserts a transfer gap. Those are the
    objects a simulation can contradict.

    That this definition was screened at all is an artefact of the word
    "Effect" in its name: its structurally identical siblings
    `populationDeviationSum`, `meanPopulationDeviation` and
    `weightedPopulationDeviation` -- the same subtraction and the same sums --
    are not screened, and nothing distinguishes them. A marker owing a
    measurement here would record a debt that can never be paid. -/
noncomputable def centeredPopulationEffectDeviation {p : ℕ} {ι : Type*}
    (wShared : Fin p → ℝ)
    (wSource : ι → Fin p → ℝ) : ι → Fin p → ℝ :=
  fun j i ↦ wSource j i - wShared i

/-- Exact mean effect vector over the first `k` source populations. -/
noncomputable def sourcePopulationMeanWeights {p : ℕ}
    (wSource : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i ↦ (k : ℝ)⁻¹ * (Finset.sum (Finset.range k) (fun j ↦ wSource j i))

/-- The meta-learned source weights are exactly the mean source-population
    effect vector once the deviations are instantiated as centered effect
    differences around the shared center. -/
theorem metaLearnedSourceWeights_eq_sourcePopulationMeanWeights
    {p : ℕ}
    (wShared : Fin p → ℝ)
    (wSource : ℕ → Fin p → ℝ)
    (k : ℕ)
    (h_k : 0 < k) :
    metaLearnedSourceWeights wShared
        (centeredPopulationEffectDeviation wShared wSource) k =
      sourcePopulationMeanWeights wSource k := by
  funext i
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h_k)
  unfold metaLearnedSourceWeights meanPopulationDeviation populationDeviationSum
    centeredPopulationEffectDeviation sourcePopulationMeanWeights
  have hsum_const : Finset.sum (Finset.range k) (fun _ ↦ wShared i) = (k : ℝ) * wShared i := by
    simp
  calc
    wShared i + (k : ℝ)⁻¹ * (Finset.sum (Finset.range k) (fun j ↦ wSource j i - wShared i))
        = wShared i + (k : ℝ)⁻¹ *
            (Finset.sum (Finset.range k) (fun j ↦ wSource j i) -
              Finset.sum (Finset.range k) (fun _ ↦ wShared i)) := by
              rw [Finset.sum_sub_distrib]
    _ = wShared i + (k : ℝ)⁻¹ *
            (Finset.sum (Finset.range k) (fun j ↦ wSource j i) - (k : ℝ) * wShared i) := by
              rw [hsum_const]
    _ = (k : ℝ)⁻¹ * (Finset.sum (Finset.range k) (fun j ↦ wSource j i)) := by
          field_simp [hk_ne]
          ring

/-- Exact squared transfer gap of the meta-learned source weights. -/
noncomputable def metaLearnedTransferGapSq {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : ℝ :=
  coefficientGapSq (metaLearnedSourceWeights wShared deviation k) wTarget

/-- The meta-learned exact transfer gap is literally the squared mismatch
    between the mean source-population effect vector and the target-optimal
    effect vector. -/
theorem metaLearnedTransferGapSq_eq_sourcePopulationMeanEffectGapSq
    {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (wSource : ℕ → Fin p → ℝ)
    (k : ℕ)
    (h_k : 0 < k) :
    metaLearnedTransferGapSq wShared wTarget
        (centeredPopulationEffectDeviation wShared wSource) k =
      coefficientGapSq (sourcePopulationMeanWeights wSource k) wTarget := by
  unfold metaLearnedTransferGapSq
  rw [metaLearnedSourceWeights_eq_sourcePopulationMeanWeights wShared wSource k h_k]

/-- Dot product distributes over addition in the left argument. -/
theorem dotProduct_add_left {p : ℕ}
    (u v w : Fin p → ℝ) :
    dotProduct (fun i ↦ u i + v i) w = dotProduct u w + dotProduct v w :=
  add_dotProduct u v w

/-- Dot product distributes over addition in the right argument. -/
theorem dotProduct_add_right {p : ℕ}
    (u v w : Fin p → ℝ) :
    dotProduct u (fun i ↦ v i + w i) = dotProduct u v + dotProduct u w :=
  dotProduct_add u v w

/-- Pulling a scalar out of the left dot-product argument. -/
theorem dotProduct_smul_left {p : ℕ}
    (c : ℝ) (u v : Fin p → ℝ) :
    dotProduct (fun i ↦ c * u i) v = c * dotProduct u v :=
  smul_dotProduct c u v

/-- Pulling a scalar out of the right dot-product argument. -/
theorem dotProduct_smul_right {p : ℕ}
    (u v : Fin p → ℝ) (c : ℝ) :
    dotProduct u (fun i ↦ c * v i) = c * dotProduct u v :=
  dotProduct_smul c u v

/-- Dot product of a finite sum of vectors with a fixed vector. -/
theorem dotProduct_sum_left {α : Type*} [DecidableEq α] {p : ℕ}
    (s : Finset α)
    (f : α → Fin p → ℝ)
    (v : Fin p → ℝ) :
    dotProduct (fun i ↦ Finset.sum s (fun j ↦ f j i)) v =
      Finset.sum s (fun j ↦ dotProduct (f j) v) := by
  unfold dotProduct
  rw [show (∑ i, (Finset.sum s (fun j ↦ f j i)) * v i) =
      ∑ i, Finset.sum s (fun j ↦ f j i * v i) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]]
  rw [Finset.sum_comm]

/-- Dot product of a fixed vector with a finite sum of vectors. -/
theorem dotProduct_sum_right {α : Type*} [DecidableEq α] {p : ℕ}
    (s : Finset α)
    (u : Fin p → ℝ)
    (f : α → Fin p → ℝ) :
    dotProduct u (fun i ↦ Finset.sum s (fun j ↦ f j i)) =
      Finset.sum s (fun j ↦ dotProduct u (f j)) := by
  unfold dotProduct
  rw [show (∑ i, u i * (Finset.sum s (fun j ↦ f j i))) =
      ∑ i, Finset.sum s (fun j ↦ u i * f j i) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]]
  rw [Finset.sum_comm]

/-- Prefix-sum recursion for population-specific deviations. -/
theorem populationDeviationSum_succ {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) :
    populationDeviationSum deviation (k + 1) =
      fun i ↦ populationDeviationSum deviation k i + deviation k i := by
  funext i
  simp [populationDeviationSum, Finset.sum_range_succ]

/-- If the new population-specific deviation is orthogonal to each earlier
    deviation, then it is orthogonal to their sum. -/
theorem dotProduct_populationDeviationSum_last_eq_zero {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ)
    (h_pair : ∀ j < k, dotProduct (deviation j) (deviation k) = 0) :
    dotProduct (populationDeviationSum deviation k) (deviation k) = 0 := by
  rw [show dotProduct (populationDeviationSum deviation k) (deviation k) =
      Finset.sum (Finset.range k) (fun j ↦ dotProduct (deviation j) (deviation k)) by
      simpa [populationDeviationSum] using
        dotProduct_sum_left (Finset.range k) deviation (deviation k)]
  apply Finset.sum_eq_zero
  intro j hj
  exact h_pair j (Finset.mem_range.mp hj)

/-- Exact norm growth of the summed population-specific deviations.
    Under pairwise orthogonality and equal per-population squared norm, the
    squared norm of the sum over `k` populations is exactly `k * gap`. -/
theorem populationDeviationSum_squaredNorm_eq_mul {p : ℕ}
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ) :
    ∀ k : ℕ,
      (∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap) →
      (∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0) →
      dotProduct (populationDeviationSum deviation k) (populationDeviationSum deviation k) =
        k * populationSpecificGap
  | 0, _, _ => by
      simp [populationDeviationSum, dotProduct]
  | k + 1, h_norm, h_pair => by
      have h_norm_prev :
          ∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap := by
        intro j hj
        exact h_norm j (lt_trans hj (Nat.lt_succ_self k))
      have h_pair_prev :
          ∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0 := by
        intro j hj l hl hneq
        exact h_pair j (lt_trans hj (Nat.lt_succ_self k))
          l (lt_trans hl (Nat.lt_succ_self k)) hneq
      have ih :=
        populationDeviationSum_squaredNorm_eq_mul deviation populationSpecificGap k
          h_norm_prev h_pair_prev
      have h_last_norm :
          dotProduct (deviation k) (deviation k) = populationSpecificGap :=
        h_norm k (Nat.lt_succ_self k)
      have h_cross_left :
          dotProduct (populationDeviationSum deviation k) (deviation k) = 0 := by
        apply dotProduct_populationDeviationSum_last_eq_zero
        intro j hj
        exact h_pair j (lt_trans hj (Nat.lt_succ_self k))
          k (Nat.lt_succ_self k) (Nat.ne_of_lt hj)
      calc
        dotProduct (populationDeviationSum deviation (k + 1))
            (populationDeviationSum deviation (k + 1))
            =
              dotProduct (populationDeviationSum deviation k) (populationDeviationSum deviation k) +
                dotProduct (populationDeviationSum deviation k) (deviation k) +
                (dotProduct (deviation k) (populationDeviationSum deviation k) +
                  dotProduct (deviation k) (deviation k)) := by
                rw [populationDeviationSum_succ, dotProduct_add_left,
                  dotProduct_add_right, dotProduct_add_right]
        _ = k * populationSpecificGap + 0 + (0 + populationSpecificGap) := by
              rw [ih, h_cross_left, dotProduct_comm, h_cross_left, h_last_norm]
        _ = (((k + 1 : ℕ) : ℝ) * populationSpecificGap) := by
              rw [Nat.cast_add, Nat.cast_one]
              ring_nf

/-- Exact squared norm of the averaged population-specific deviation.
    Under pairwise orthogonality and equal per-population squared norm, the
    average deviation has squared norm exactly `gap / k`. -/
theorem meanPopulationDeviation_squaredNorm_eq_populationSpecificGap_div_k {p : ℕ}
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k : ℕ)
    (h_k : 0 < k)
    (h_norm : ∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    dotProduct (meanPopulationDeviation deviation k) (meanPopulationDeviation deviation k) =
      populationSpecificGap / k := by
  have h_sumnorm :=
    populationDeviationSum_squaredNorm_eq_mul deviation populationSpecificGap k h_norm h_pair
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h_k)
  unfold meanPopulationDeviation
  calc
    dotProduct (fun i ↦ (k : ℝ)⁻¹ * populationDeviationSum deviation k i)
        (fun i ↦ (k : ℝ)⁻¹ * populationDeviationSum deviation k i)
        =
          ((k : ℝ)⁻¹)^2 *
            dotProduct (populationDeviationSum deviation k)
              (populationDeviationSum deviation k) := by
              unfold dotProduct
              rw [show (∑ i,
                    ((k : ℝ)⁻¹ * populationDeviationSum deviation k i) *
                      ((k : ℝ)⁻¹ * populationDeviationSum deviation k i))
                  = ∑ i, ((k : ℝ)⁻¹)^2 *
                      (populationDeviationSum deviation k i *
                        populationDeviationSum deviation k i) by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring]
              rw [← Finset.mul_sum]
    _ = ((k : ℝ)⁻¹)^2 * (k * populationSpecificGap) := by
          rw [h_sumnorm]
    _ = populationSpecificGap / k := by
          field_simp [hk_ne]

/-- If the shared representation residual is orthogonal to each population-
    specific deviation, then it is orthogonal to their average. -/
theorem dotProduct_meanPopulationDeviation_eq_zero {p : ℕ}
    (u : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (k : ℕ)
    (h_orth : ∀ j < k, dotProduct u (deviation j) = 0) :
    dotProduct u (meanPopulationDeviation deviation k) = 0 := by
  unfold meanPopulationDeviation
  rw [dotProduct_smul_right]
  rw [show dotProduct u (populationDeviationSum deviation k) =
      Finset.sum (Finset.range k) (fun j ↦ dotProduct u (deviation j)) by
      simpa [populationDeviationSum] using
        dotProduct_sum_right (Finset.range k) u deviation]
  have hsum :
      Finset.sum (Finset.range k) (fun j ↦ dotProduct u (deviation j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact h_orth j (Finset.mem_range.mp hj)
  rw [hsum]
  ring

/-- **The meta-learning deviation geometry, named once.**

Five statements below are conditioned on the same three facts about the population-specific
deviations: each is orthogonal to the shared residual, each has the same squared norm, and
distinct ones are orthogonal.  Written out at each theorem that block was five identical
lines repeated five times, and restricting it to a smaller task count was another nine.
It is one geometry, so it is one structure, with its own restriction lemma. -/
structure MetaLearningDeviations {p : ℕ} (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ) (populationSpecificGap : ℝ) (k : ℕ) : Prop where
  /-- Every deviation is orthogonal to the shared residual. -/
  shared_orth : ∀ j < k, dotProduct (fun i ↦ wShared i - wTarget i) (deviation j) = 0
  /-- Every deviation has the same squared norm. -/
  norm_eq : ∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap
  /-- Distinct deviations are orthogonal. -/
  pairwise : ∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0

/-- **The geometry is inhabited.**  A theorem conditioned on a bundle nothing satisfies is
true and empty.  One source population with zero deviation from the shared centre satisfies
all three conditions, so the statements below are statements about something. -/
theorem metaLearningDeviations_witness {p : ℕ} (wShared wTarget : Fin p → ℝ) :
    MetaLearningDeviations wShared wTarget (fun _ _ ↦ 0) 0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j _
    simp [dotProduct]
  · intro j _
    simp [dotProduct]
  · intro j hj l hl hne
    exact absurd (show j = l by omega) hne

/-- The geometry at `k₂` populations restricts to any smaller task count. -/
theorem MetaLearningDeviations.mono {p : ℕ} {wShared wTarget : Fin p → ℝ}
    {deviation : ℕ → Fin p → ℝ} {populationSpecificGap : ℝ} {k₁ k₂ : ℕ}
    (h : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₂)
    (hle : k₁ ≤ k₂) :
    MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₁ :=
  ⟨fun j hj ↦ h.shared_orth j (lt_of_lt_of_le hj hle),
    fun j hj ↦ h.norm_eq j (lt_of_lt_of_le hj hle),
    fun j hj l hl hne ↦
      h.pairwise j (lt_of_lt_of_le hj hle) l (lt_of_lt_of_le hl hle) hne⟩

/-- Exact transfer-gap formula for the shared-feature meta-learning model.
    The shared center's own residual gap is `coefficientGapSq wShared wTarget`
    — computed, not assumed. If in addition each population-specific deviation
    has squared norm `populationSpecificGap`, those deviations are pairwise
    orthogonal, and each is orthogonal to the shared residual, then averaging
    over `k` source populations yields the exact residual gap
    `coefficientGapSq wShared wTarget + populationSpecificGap / k`. -/
theorem metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k : ℕ)
    (h_k : 0 < k)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k) :
    metaLearnedTransferGapSq wShared wTarget deviation k =
      coefficientGapSq wShared wTarget + populationSpecificGap / k := by
  obtain ⟨h_shared_orth, h_norm, h_pair⟩ := hdev
  obtain ⟨irreducibleGap, h_shared⟩ :
      ∃ g : ℝ, coefficientGapSq wShared wTarget = g := ⟨_, rfl⟩
  rw [h_shared]
  let sharedResidual : Fin p → ℝ := fun i ↦ wShared i - wTarget i
  have h_shared_norm : dotProduct sharedResidual sharedResidual = irreducibleGap := by
    simpa [sharedResidual, coefficientGapSq] using h_shared
  have h_mean_norm :
      dotProduct (meanPopulationDeviation deviation k) (meanPopulationDeviation deviation k) =
        populationSpecificGap / k :=
    meanPopulationDeviation_squaredNorm_eq_populationSpecificGap_div_k
      deviation populationSpecificGap k h_k h_norm h_pair
  have h_cross :
      dotProduct sharedResidual (meanPopulationDeviation deviation k) = 0 :=
    dotProduct_meanPopulationDeviation_eq_zero
      sharedResidual deviation k h_shared_orth
  have h_sub :
      (fun i ↦
        (metaLearnedSourceWeights wShared deviation k i) - wTarget i) =
        fun i ↦ sharedResidual i + meanPopulationDeviation deviation k i := by
    funext i
    unfold metaLearnedSourceWeights sharedResidual
    ring
  unfold metaLearnedTransferGapSq coefficientGapSq
  rw [h_sub]
  calc
    dotProduct
        (fun i ↦ sharedResidual i + meanPopulationDeviation deviation k i)
        (fun i ↦ sharedResidual i + meanPopulationDeviation deviation k i)
        =
          dotProduct sharedResidual sharedResidual +
            dotProduct sharedResidual (meanPopulationDeviation deviation k) +
            (dotProduct (meanPopulationDeviation deviation k) sharedResidual +
              dotProduct (meanPopulationDeviation deviation k)
                (meanPopulationDeviation deviation k)) := by
              rw [dotProduct_add_left, dotProduct_add_right, dotProduct_add_right]
    _ = irreducibleGap + 0 + (0 + populationSpecificGap / k) := by
          rw [h_shared_norm, h_cross, dotProduct_comm, h_cross, h_mean_norm]
    _ = irreducibleGap + populationSpecificGap / k := by
          ring

/-- Exact population-genetic bridge for meta-learning: if the source
    population effect vectors decompose into a shared center plus orthogonal
    centered deviations, then the mean source effect vector itself has exact
    transfer gap `coefficientGapSq wShared wTarget + populationSpecificGap / k`
    to the target optimum. -/
theorem sourcePopulationMeanEffectGapSq_eq_irreducible_plus_populationSpecificGap_div_k
    {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (wSource : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k : ℕ)
    (h_k : 0 < k)
    (hdev : MetaLearningDeviations wShared wTarget
      (centeredPopulationEffectDeviation wShared wSource) populationSpecificGap k) :
    coefficientGapSq (sourcePopulationMeanWeights wSource k) wTarget =
      coefficientGapSq wShared wTarget + populationSpecificGap / k := by
  rw [← metaLearnedTransferGapSq_eq_sourcePopulationMeanEffectGapSq
    wShared wTarget wSource k h_k]
  exact metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
    wShared wTarget (centeredPopulationEffectDeviation wShared wSource)
    populationSpecificGap k h_k hdev

/-- More source populations strictly reduce the exact residual transfer gap in
    the shared-feature meta-learning model, because the averaged population-
    specific deviation has exact squared norm `gap / k`. -/
theorem metaLearnedTransferGapSq_strictMono {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k₁ k₂ : ℕ)
    (h_pop : 0 < populationSpecificGap)
    (h_k₁ : 0 < k₁)
    (h_more : k₁ < k₂)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₂) :
    metaLearnedTransferGapSq wShared wTarget deviation k₂ <
      metaLearnedTransferGapSq wShared wTarget deviation k₁ := by
  have h_k₂ : 0 < k₂ := lt_trans h_k₁ h_more
  have h_formula₂ :
      metaLearnedTransferGapSq wShared wTarget deviation k₂ =
        coefficientGapSq wShared wTarget + populationSpecificGap / k₂ :=
    metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
      wShared wTarget deviation populationSpecificGap
      k₂ h_k₂ hdev
  have h_formula₁ :
      metaLearnedTransferGapSq wShared wTarget deviation k₁ =
        coefficientGapSq wShared wTarget + populationSpecificGap / k₁ :=
    metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
      wShared wTarget deviation populationSpecificGap
      k₁ h_k₁ (hdev.mono (le_of_lt h_more))
  rw [h_formula₂, h_formula₁]
  have hk₁ : 0 < (k₁ : ℝ) := Nat.cast_pos.mpr h_k₁
  have hcast : (k₁ : ℝ) < (k₂ : ℝ) := by
    exact_mod_cast h_more
  have hdiv : populationSpecificGap / (k₂ : ℝ) < populationSpecificGap / (k₁ : ℝ) :=
    div_lt_div_of_pos_left h_pop hk₁ hcast
  linarith

/-- Positivity of the exact shared-feature meta-learning transfer gap. -/
theorem metaLearnedTransferGapSq_pos {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k : ℕ)
    (h_pop : 0 < populationSpecificGap)
    (h_k : 0 < k)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k) :
    0 < metaLearnedTransferGapSq wShared wTarget deviation k := by
  rw [metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
    wShared wTarget deviation populationSpecificGap
    k h_k hdev]
  have h_irred : 0 ≤ coefficientGapSq wShared wTarget :=
    coefficientGapSq_nonneg wShared wTarget
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr h_k
  have hdiv : 0 < populationSpecificGap / (k : ℝ) :=
    div_pos h_pop hk
  linarith

/-- Weighted population-specific deviation around the shared representation
    center. This lets us compare the usual equal-weight meta average against
    arbitrary affine aggregation of the first `k` source populations. -/
noncomputable def weightedPopulationDeviation {p k : ℕ}
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : Fin p → ℝ :=
  fun i ↦ ∑ j : Fin k, weight j * deviation j i

/-- Weighted meta-learned source weights built from an affine combination of
    source-population-specific deviations around a shared center. -/
noncomputable def weightedMetaSourceWeights {p k : ℕ}
    (wShared : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : Fin p → ℝ :=
  fun i ↦ wShared i + weightedPopulationDeviation deviation weight i

/-- Exact transfer gap of a weighted affine meta-aggregator. -/
noncomputable def weightedMetaTransferGapSq {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : ℝ :=
  coefficientGapSq (weightedMetaSourceWeights wShared deviation weight) wTarget

/-- Uniform affine weights on `k` source populations. -/
noncomputable def uniformMetaWeight (k : ℕ) : Fin k → ℝ :=
  fun _ ↦ (k : ℝ)⁻¹

/-- Weighted average of source-population effect vectors: the same weighted combination
    as `weightedPopulationDeviation`, applied to the source effect vectors themselves
    rather than to their deviations around a shared center.

    Empirical status: NOT AN EMPIRICAL CLAIM -- the body is literally
    `weightedPopulationDeviation wSource weight`, an application of another
    definition to different arguments, and it introduces no constant, no
    exponent and no relation of its own. A weighted average of supplied vectors
    at supplied weights is what the caller asked for; no measured population can
    make `Σⱼ wⱼ · vⱼ` come out otherwise.

    What is claimed, and could fail, is
    `weightedMetaSourceWeights_eq_weightedPopulationEffectAverage`: that ANY
    affine meta-aggregator over centred deviations equals this average, which
    needs `Σⱼ wⱼ = 1` and is false without it. That is a theorem about the
    aggregator, proved rather than measured, and it is where the content sits.

    As with `centeredPopulationEffectDeviation`, the screen fired on the word
    "Effect" in the name: the definition this one calls is not screened, and the
    two have the same body. -/
noncomputable def weightedPopulationEffectAverage {p k : ℕ}
    (wSource : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : Fin p → ℝ :=
  weightedPopulationDeviation wSource weight

/-- Any affine meta-aggregator is exactly the weighted average of the source
    effect vectors once deviations are instantiated as centered source effects. -/
theorem weightedMetaSourceWeights_eq_weightedPopulationEffectAverage
    {p k : ℕ}
    (wShared : Fin p → ℝ)
    (wSource : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (h_sum : ∑ j : Fin k, weight j = 1) :
    weightedMetaSourceWeights wShared
        (centeredPopulationEffectDeviation wShared wSource) weight =
      weightedPopulationEffectAverage wSource weight := by
  funext i
  unfold weightedMetaSourceWeights weightedPopulationEffectAverage
    centeredPopulationEffectDeviation weightedPopulationDeviation
  calc
    wShared i + ∑ j : Fin k, weight j * (wSource j i - wShared i)
        = wShared i + ((∑ j : Fin k, weight j * wSource j i) -
            (∑ j : Fin k, weight j) * wShared i) := by
              have hsplit :
                  (∑ j : Fin k, weight j * (wSource j i - wShared i)) =
                    (∑ j : Fin k, weight j * wSource j i) -
                      ∑ j : Fin k, weight j * wShared i := by
                    calc
                      (∑ j : Fin k, weight j * (wSource j i - wShared i))
                          = ∑ j : Fin k, (weight j * wSource j i - weight j * wShared i) := by
                              apply Finset.sum_congr rfl
                              intro j hj
                              ring
                      _ = (∑ j : Fin k, weight j * wSource j i) -
                            ∑ j : Fin k, weight j * wShared i := by
                              rw [Finset.sum_sub_distrib]
              have hconst :
                  (∑ j : Fin k, weight j * wShared i) =
                    (∑ j : Fin k, weight j) * wShared i := by
                    calc
                      (∑ j : Fin k, weight j * wShared i)
                          = ∑ j : Fin k, wShared i * weight j := by
                              apply Finset.sum_congr rfl
                              intro j hj
                              ring
                      _ = wShared i * ∑ j : Fin k, weight j := by
                            rw [Finset.mul_sum]
                      _ = (∑ j : Fin k, weight j) * wShared i := by
                            ring
              rw [hsplit, hconst]
    _ = ∑ j : Fin k, weight j * wSource j i := by
          rw [h_sum]
          ring

/-- The weighted meta-learning transfer gap is literally the squared mismatch
    between the weighted average source effect vector and the target-optimal
    effect vector. -/
theorem weightedMetaTransferGapSq_eq_weightedPopulationEffectAverageGapSq
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (wSource : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (h_sum : ∑ j : Fin k, weight j = 1) :
    weightedMetaTransferGapSq wShared wTarget
        (centeredPopulationEffectDeviation wShared wSource) weight =
      coefficientGapSq (weightedPopulationEffectAverage wSource weight) wTarget := by
  unfold weightedMetaTransferGapSq
  rw [weightedMetaSourceWeights_eq_weightedPopulationEffectAverage
    wShared wSource weight h_sum]

/-- Exact squared norm of a weighted population-specific deviation. Under
    pairwise orthogonality and equal per-population squared norm, the weighted
    combination has squared norm `gap × Σ_j w_j²`. -/
theorem weightedPopulationDeviation_squaredNorm_eq_populationSpecificGap_mul_sum_sq
    {p k : ℕ}
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (populationSpecificGap : ℝ)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    dotProduct (weightedPopulationDeviation deviation weight)
      (weightedPopulationDeviation deviation weight) =
        populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
  unfold weightedPopulationDeviation
  rw [show
      dotProduct
          (fun i ↦ ∑ j : Fin k, weight j * deviation j i)
          (fun i ↦ ∑ j : Fin k, weight j * deviation j i) =
        ∑ j : Fin k,
          dotProduct (fun i ↦ weight j * deviation j i)
            (fun i ↦ ∑ l : Fin k, weight l * deviation l i) by
      simpa using
        dotProduct_sum_left (Finset.univ)
          (fun j : Fin k ↦ fun i ↦ weight j * deviation j i)
          (fun i ↦ ∑ l : Fin k, weight l * deviation l i)]
  calc
    ∑ j : Fin k,
        dotProduct (fun i ↦ weight j * deviation j i)
          (fun i ↦ ∑ l : Fin k, weight l * deviation l i)
      =
        ∑ j : Fin k,
          weight j *
            dotProduct (deviation j)
              (fun i ↦ ∑ l : Fin k, weight l * deviation l i) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [dotProduct_smul_left]
    _ =
        ∑ j : Fin k,
          weight j *
            (∑ l : Fin k, weight l * dotProduct (deviation j) (deviation l)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [show
              dotProduct (deviation j)
                (fun i ↦ ∑ l : Fin k, weight l * deviation l i) =
              ∑ l : Fin k,
                dotProduct (deviation j) (fun i ↦ weight l * deviation l i) by
                simpa using
                  dotProduct_sum_right (Finset.univ) (deviation j)
                    (fun l : Fin k ↦ fun i ↦ weight l * deviation l i)]
          congr 1
          apply Finset.sum_congr rfl
          intro l hl
          rw [dotProduct_smul_right]
    _ = ∑ j : Fin k, weight j * (weight j * populationSpecificGap) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_eq_single j]
          · rw [h_norm]
          · intro l hl hlj
            rw [h_pair j l (Ne.symm hlj), mul_zero]
          · intro hj_not_mem
            exact (hj_not_mem (Finset.mem_univ j)).elim
    _ = populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
          rw [show
              (∑ j : Fin k, weight j * (weight j * populationSpecificGap)) =
                ∑ j : Fin k, populationSpecificGap * weight j ^ 2 by
                apply Finset.sum_congr rfl
                intro j hj
                ring]
          rw [Finset.mul_sum]

/-- Exact transfer-gap formula for an affine weighted meta-aggregator. -/
theorem weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_mul_sum_sq
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (populationSpecificGap : ℝ)
    (h_shared_orth :
      ∀ j, dotProduct (fun i ↦ wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    weightedMetaTransferGapSq wShared wTarget deviation weight =
      coefficientGapSq wShared wTarget +
        populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
  obtain ⟨irreducibleGap, h_shared⟩ :
      ∃ g : ℝ, coefficientGapSq wShared wTarget = g := ⟨_, rfl⟩
  rw [h_shared]
  let sharedResidual : Fin p → ℝ := fun i ↦ wShared i - wTarget i
  have h_shared_norm : dotProduct sharedResidual sharedResidual = irreducibleGap := by
    simpa [sharedResidual, coefficientGapSq] using h_shared
  have h_weighted_norm :
      dotProduct (weightedPopulationDeviation deviation weight)
        (weightedPopulationDeviation deviation weight) =
          populationSpecificGap * ∑ j : Fin k, weight j ^ 2 :=
    weightedPopulationDeviation_squaredNorm_eq_populationSpecificGap_mul_sum_sq
      deviation weight populationSpecificGap h_norm h_pair
  have h_cross :
      dotProduct sharedResidual (weightedPopulationDeviation deviation weight) = 0 := by
    unfold weightedPopulationDeviation
    rw [show
        dotProduct sharedResidual
          (fun i ↦ ∑ j : Fin k, weight j * deviation j i) =
          ∑ j : Fin k,
            dotProduct sharedResidual (fun i ↦ weight j * deviation j i) by
          simpa using
            dotProduct_sum_right (Finset.univ) sharedResidual
              (fun j : Fin k ↦ fun i ↦ weight j * deviation j i)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [dotProduct_smul_right, h_shared_orth j, mul_zero]
  have h_sub :
      (fun i ↦
        weightedMetaSourceWeights wShared deviation weight i - wTarget i) =
      fun i ↦ sharedResidual i + weightedPopulationDeviation deviation weight i := by
    funext i
    unfold weightedMetaSourceWeights sharedResidual weightedPopulationDeviation
    ring
  unfold weightedMetaTransferGapSq coefficientGapSq
  rw [h_sub]
  calc
    dotProduct
        (fun i ↦ sharedResidual i + weightedPopulationDeviation deviation weight i)
        (fun i ↦ sharedResidual i + weightedPopulationDeviation deviation weight i)
        =
          dotProduct sharedResidual sharedResidual +
            dotProduct sharedResidual (weightedPopulationDeviation deviation weight) +
            (dotProduct (weightedPopulationDeviation deviation weight) sharedResidual +
              dotProduct (weightedPopulationDeviation deviation weight)
                (weightedPopulationDeviation deviation weight)) := by
              rw [dotProduct_add_left, dotProduct_add_right, dotProduct_add_right]
    _ = irreducibleGap + 0 + (0 + populationSpecificGap * ∑ j : Fin k, weight j ^ 2) := by
          rw [h_shared_norm, h_cross, dotProduct_comm, h_cross, h_weighted_norm]
    _ = irreducibleGap + populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
          ring

/-- Among affine weights summing to one, the squared weight mass is minimized
    by the uniform average. This is the exact Cauchy-Schwarz step behind the
    `1 / k` decay of the shared-feature meta-learning transfer gap. -/
theorem one_div_card_le_sum_sq_of_affine_weights
    {k : ℕ}
    (weight : Fin k → ℝ)
    (h_k : 0 < k)
    (h_sum : ∑ j : Fin k, weight j = 1) :
    1 / (k : ℝ) ≤ ∑ j : Fin k, weight j ^ 2 := by
  have h_sq :=
    sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k))) (f := weight)
  have h_card : ((#(Finset.univ : Finset (Fin k)) : ℕ) : ℝ) = k := by
    simp
  have h_key : 1 ≤ (k : ℝ) * ∑ j : Fin k, weight j ^ 2 := by
    simpa [h_sum, h_card] using h_sq
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr h_k
  by_contra h_contra
  have hlt : ∑ j : Fin k, weight j ^ 2 < 1 / (k : ℝ) :=
    not_le.mp h_contra
  have hmul_lt : (k : ℝ) * ∑ j : Fin k, weight j ^ 2 < 1 := by
    have := mul_lt_mul_of_pos_left hlt hk
    simpa [div_eq_mul_inv, one_div, hk.ne'] using this
  linarith

/-- Exact uniform affine weighting formula. -/
theorem weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k_of_uniform
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (h_k : 0 < k)
    (h_shared_orth :
      ∀ j, dotProduct (fun i ↦ wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    weightedMetaTransferGapSq wShared wTarget deviation (uniformMetaWeight k) =
      coefficientGapSq wShared wTarget + populationSpecificGap / k := by
  rw [weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_mul_sum_sq
    wShared wTarget deviation (uniformMetaWeight k)
    populationSpecificGap h_shared_orth h_norm h_pair]
  have hcard : (∑ j : Fin k, ((uniformMetaWeight k) j) ^ 2) = k * ((k : ℝ)⁻¹ ^ 2) := by
    simp [uniformMetaWeight]
  rw [hcard]
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h_k)
  field_simp [hk_ne]

/-- **Equal-weight meta-averaging is exactly optimal among affine source-model
    aggregators under the shared-feature geometry.**
    Under orthogonal population-specific deviations of equal squared norm,
    every affine combination of the `k` source-specific models has exact
    transfer gap `coefficientGapSq wShared wTarget + gap × Σ_j w_j²`, so the
    uniform average minimizes the exact transfer gap because `Σ_j w_j² ≥ 1 / k`. -/
theorem weightedMetaTransferGapSq_ge_uniform_of_affine_weights
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (populationSpecificGap : ℝ)
    (h_k : 0 < k)
    (h_sum : ∑ j : Fin k, weight j = 1)
    (h_shared_orth :
      ∀ j, dotProduct (fun i ↦ wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0)
    (h_pop : 0 ≤ populationSpecificGap) :
    weightedMetaTransferGapSq wShared wTarget deviation (uniformMetaWeight k) ≤
      weightedMetaTransferGapSq wShared wTarget deviation weight := by
  rw [weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k_of_uniform
      wShared wTarget deviation populationSpecificGap
      h_k h_shared_orth h_norm h_pair,
    weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_mul_sum_sq
      wShared wTarget deviation weight populationSpecificGap
      h_shared_orth h_norm h_pair]
  have h_sq_lb : 1 / (k : ℝ) ≤ ∑ j : Fin k, weight j ^ 2 :=
    one_div_card_le_sum_sq_of_affine_weights weight h_k h_sum
  have hmul :
      populationSpecificGap / k ≤
        populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left h_sq_lb h_pop
  linarith

/-- Optimal fine-tuning MSE after choosing the source-shrinkage weight
    optimally. -/
noncomputable def optimalFineTuningMSE (gapSq noiseVar nTarget : ℝ) : ℝ :=
  sourceShrinkageMSE gapSq noiseVar nTarget
    (optimalSourceShrinkageWeight gapSq noiseVar nTarget)

/-- Closed form of the optimal fine-tuning MSE. -/
theorem optimalFineTuningMSE_eq_closed_form
    (gapSq noiseVar nTarget : ℝ)
    (h_curv : gapSq + noiseVar / nTarget ≠ 0) :
    optimalFineTuningMSE gapSq noiseVar nTarget =
      gapSq * (noiseVar / nTarget) / (gapSq + noiseVar / nTarget) := by
  unfold optimalFineTuningMSE
  rw [sourceShrinkageMSE_eq_optimal_plus_square gapSq noiseVar nTarget
    (optimalSourceShrinkageWeight gapSq noiseVar nTarget) h_curv]
  ring

/-- Closed form with target sample size cleared from the nested quotient.  This is the form in
which the exact sample-complexity threshold is transparent. -/
theorem optimalFineTuningMSE_eq_gap_mul_noise_div
    (gapSq noiseVar nTarget : ℝ)
    (h_n : 0 < nTarget)
    (h_curv : gapSq + noiseVar / nTarget ≠ 0) :
    optimalFineTuningMSE gapSq noiseVar nTarget =
      gapSq * noiseVar / (nTarget * gapSq + noiseVar) := by
  rw [optimalFineTuningMSE_eq_closed_form gapSq noiseVar nTarget h_curv]
  field_simp [h_n.ne']

/-- For fixed target sample size and noise level, the optimal fine-tuning MSE
    is strictly increasing in the residual source-target mismatch. -/
theorem optimalFineTuningMSE_strictMono_in_gapSq
    (gap₁ gap₂ noiseVar nTarget : ℝ)
    (h_gap₁ : 0 ≤ gap₁)
    (h_gap : gap₁ < gap₂)
    (h_noise : 0 < noiseVar)
    (h_n : 0 < nTarget) :
    optimalFineTuningMSE gap₁ noiseVar nTarget <
      optimalFineTuningMSE gap₂ noiseVar nTarget := by
  have h_curv₁ : gap₁ + noiseVar / nTarget ≠ 0 := by
    have h_pos : 0 < gap₁ + noiseVar / nTarget := by
      have hdiv : 0 < noiseVar / nTarget := div_pos h_noise h_n
      linarith
    linarith
  have h_curv₂ : gap₂ + noiseVar / nTarget ≠ 0 := by
    have h_pos : 0 < gap₂ + noiseVar / nTarget := by
      have hdiv : 0 < noiseVar / nTarget := div_pos h_noise h_n
      linarith
    linarith
  rw [optimalFineTuningMSE_eq_closed_form gap₁ noiseVar nTarget h_curv₁,
    optimalFineTuningMSE_eq_closed_form gap₂ noiseVar nTarget h_curv₂]
  set b : ℝ := noiseVar / nTarget
  have hb_pos : 0 < b := by
    unfold b
    exact div_pos h_noise h_n
  change gap₁ * b / (gap₁ + b) < gap₂ * b / (gap₂ + b)
  apply (div_lt_div_iff₀ (by linarith) (by linarith)).2
  have h_sq_term : gap₁ * (b * b) < gap₂ * (b * b) :=
    mul_lt_mul_of_pos_right h_gap (mul_pos hb_pos hb_pos)
  nlinarith

/-- Target sample size needed for the optimal fine-tuning MSE to reach a target
    tolerance `τ`. This is the exact threshold obtained by solving the
    closed-form optimal-MSE equation for `nTarget`. -/
noncomputable def requiredTargetSamplesForOptimalFineTuningMSE
    (gapSq noiseVar tau : ℝ) : ℝ :=
  noiseVar * (gapSq - tau) / (tau * gapSq)

/-- **requiredTargetSamplesForOptimalFineTuningMSE at zero gapSq, named.** A zero squared gap means
source and target coincide and no target samples are needed -- but the formula reaches that answer
through a division by zero rather than through the model, so it returns `0` for the wrong reason
and returns it just as readily when `tau` is zero and the requirement diverges. Consumers must
require `gapSq ≠ 0`. -/
theorem requiredTargetSamplesForOptimalFineTuningMSE_zero_gapsq_is_junk (noiseVar : ℝ) (tau : ℝ) :
    requiredTargetSamplesForOptimalFineTuningMSE 0 noiseVar tau = 0 := by
  unfold requiredTargetSamplesForOptimalFineTuningMSE
  simp

/-- The required target sample size is positive whenever the desired MSE target
    lies strictly below the transfer gap. -/
theorem requiredTargetSamplesForOptimalFineTuningMSE_pos
    (gapSq noiseVar tau : ℝ)
    (h_noise : 0 < noiseVar)
    (h_tau : 0 < tau)
    (h_gap : tau < gapSq) :
    0 < requiredTargetSamplesForOptimalFineTuningMSE gapSq noiseVar tau := by
  unfold requiredTargetSamplesForOptimalFineTuningMSE
  have h_gap_pos : 0 < gapSq := by linarith
  have h_num : 0 < noiseVar * (gapSq - tau) := by
    have : 0 < gapSq - tau := by linarith
    exact mul_pos h_noise this
  have h_den : 0 < tau * gapSq :=
    mul_pos h_tau h_gap_pos
  exact div_pos h_num h_den

/-- **Exact target-sample requirement for a desired fine-tuning accuracy.**  When the requested
tolerance lies strictly between zero and the residual transfer gap, optimal fine-tuning reaches
that tolerance if and only if the target sample size meets the derived threshold.  This turns the
sample formula into a necessary-and-sufficient design law. -/
theorem optimalFineTuningMSE_le_iff_requiredTargetSamples_le
    (gapSq noiseVar nTarget tau : ℝ)
    (h_noise : 0 < noiseVar)
    (h_n : 0 < nTarget)
    (h_tau : 0 < tau)
    (h_gap : tau < gapSq) :
    optimalFineTuningMSE gapSq noiseVar nTarget ≤ tau ↔
      requiredTargetSamplesForOptimalFineTuningMSE gapSq noiseVar tau ≤ nTarget := by
  have h_gap_pos : 0 < gapSq := lt_trans h_tau h_gap
  have h_curv : gapSq + noiseVar / nTarget ≠ 0 := by
    exact ne_of_gt (add_pos h_gap_pos (div_pos h_noise h_n))
  have h_mse_denom : 0 < nTarget * gapSq + noiseVar := by
    exact add_pos (mul_pos h_n h_gap_pos) h_noise
  have h_req_denom : 0 < tau * gapSq := mul_pos h_tau h_gap_pos
  rw [optimalFineTuningMSE_eq_gap_mul_noise_div gapSq noiseVar nTarget h_n h_curv]
  unfold requiredTargetSamplesForOptimalFineTuningMSE
  rw [div_le_iff₀ h_mse_denom, div_le_iff₀ h_req_denom]
  constructor <;> intro h <;> nlinarith

/-- For a fixed MSE tolerance, reducing the transfer gap strictly lowers the
    target sample size required to hit that tolerance under optimal fine-tuning. -/
theorem requiredTargetSamplesForOptimalFineTuningMSE_strictMono_in_gapSq
    (gap₁ gap₂ noiseVar tau : ℝ)
    (h_gap₁ : 0 < gap₁)
    (h_gap : gap₁ < gap₂)
    (h_noise : 0 < noiseVar)
    (h_tau : 0 < tau) :
    requiredTargetSamplesForOptimalFineTuningMSE gap₁ noiseVar tau <
      requiredTargetSamplesForOptimalFineTuningMSE gap₂ noiseVar tau := by
  have h_gap₂ : 0 < gap₂ := lt_trans h_gap₁ h_gap
  have h_rewrite₁ :
      requiredTargetSamplesForOptimalFineTuningMSE gap₁ noiseVar tau =
        noiseVar / tau - noiseVar / gap₁ := by
    unfold requiredTargetSamplesForOptimalFineTuningMSE
    field_simp [ne_of_gt h_tau, ne_of_gt h_gap₁]
  have h_rewrite₂ :
      requiredTargetSamplesForOptimalFineTuningMSE gap₂ noiseVar tau =
        noiseVar / tau - noiseVar / gap₂ := by
    unfold requiredTargetSamplesForOptimalFineTuningMSE
    field_simp [ne_of_gt h_tau, ne_of_gt h_gap₂]
  rw [h_rewrite₁, h_rewrite₂]
  have hdiv : noiseVar / gap₂ < noiseVar / gap₁ :=
    div_lt_div_of_pos_left h_noise h_gap₁ h_gap
  nlinarith

/-- Exact target excess quadratic risk of using `w` instead of the
    target-optimal predictor `wStar`. -/
noncomputable def targetLinearExcessRisk {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (w wStar : Fin p → ℝ) : ℝ :=
  targetLinearRisk sigmaObsTarget crossTarget noiseVar w -
    targetLinearRisk sigmaObsTarget crossTarget noiseVar wStar

/-- Symmetric target covariance swaps the bilinear cross-term exactly:
    `uᵀΣv = vᵀΣu`. -/
theorem dotProduct_mulVec_swap_of_isSymm
    {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A.IsSymm)
    (u v : Fin p → ℝ) :
    dotProduct u (A.mulVec v) = dotProduct v (A.mulVec u) := by
  have h := Foundations.sum_mulVec_mul_eq_sum_mul_transpose_mulVec A v u
  simpa [dotProduct, hA.eq, mul_comm] using h

/-- Exact excess-risk decomposition for target quadratic risk.
    If `wStar` solves the target normal equations, then the target excess risk
    of any transported weight vector `w` is exactly the quadratic form of the
    coefficient error under the target covariance geometry. -/
theorem targetLinearExcessRisk_eq_quadratic_gap
    {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (w wStar : Fin p → ℝ)
    (h_symm : sigmaObsTarget.IsSymm)
    (h_opt : sigmaObsTarget.mulVec wStar = crossTarget) :
    targetLinearExcessRisk sigmaObsTarget crossTarget noiseVar w wStar =
      dotProduct (fun i ↦ w i - wStar i)
        (sigmaObsTarget.mulVec (fun i ↦ w i - wStar i)) := by
  let u : Fin p → ℝ := fun i ↦ w i - wStar i
  have hw : w = fun i ↦ wStar i + u i := by
    funext i
    simp [u]
  have hmul :
      sigmaObsTarget.mulVec (fun i ↦ wStar i + u i) =
        sigmaObsTarget.mulVec wStar + sigmaObsTarget.mulVec u := by
    simpa [u] using Foundations.matrix_mulVec_add sigmaObsTarget wStar u
  have hswap :
      dotProduct wStar (sigmaObsTarget.mulVec u) =
        dotProduct u crossTarget := by
    calc
      dotProduct wStar (sigmaObsTarget.mulVec u) =
          dotProduct u (sigmaObsTarget.mulVec wStar) :=
            dotProduct_mulVec_swap_of_isSymm sigmaObsTarget h_symm wStar u
      _ = dotProduct u crossTarget := by simp [h_opt]
  let a : ℝ := dotProduct wStar crossTarget
  let b : ℝ := dotProduct wStar (sigmaObsTarget.mulVec u)
  let c : ℝ := dotProduct u crossTarget
  let d : ℝ := dotProduct u (sigmaObsTarget.mulVec u)
  have hexpand1 :
      dotProduct (fun i ↦ wStar i + u i) (crossTarget + sigmaObsTarget.mulVec u) =
        a + b + c + d := by
    simp [a, b, c, d, dotProduct, Finset.sum_add_distrib, add_mul, mul_add]
    ring
  have hexpand2 :
      dotProduct (fun i ↦ wStar i + u i) crossTarget = a + c := by
    simp [a, c, dotProduct, Finset.sum_add_distrib, add_mul]
  have h_gap_rhs :
      dotProduct (fun i ↦ (fun j ↦ wStar j + u j) i - wStar i)
        (sigmaObsTarget.mulVec (fun i ↦ (fun j ↦ wStar j + u j) i - wStar i)) = d := by
    simp [d]
  unfold targetLinearExcessRisk targetLinearRisk
  rw [hw, hmul, h_opt, hexpand1, hexpand2]
  rw [h_gap_rhs]
  rw [show b = c by
    simpa [b, c] using hswap]
  linarith

/-- In the isotropic target-feature model (`Σ_T = I`), the exact target excess
    quadratic risk is literally the squared coefficient mismatch. -/
  theorem isotropic_targetLinearExcessRisk_eq_coefficientGapSq
      {p : ℕ}
      (crossTarget : Fin p → ℝ)
      (noiseVar : ℝ)
      (w wStar : Fin p → ℝ)
      (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
      targetLinearExcessRisk (1 : Matrix (Fin p) (Fin p) ℝ) crossTarget noiseVar w wStar =
        coefficientGapSq w wStar := by
    have h_one_symm : (1 : Matrix (Fin p) (Fin p) ℝ).IsSymm :=
      Matrix.isSymm_one
    have h_excess :=
      targetLinearExcessRisk_eq_quadratic_gap
        (1 : Matrix (Fin p) (Fin p) ℝ) crossTarget noiseVar w wStar
        h_one_symm h_opt
    simpa using h_excess

/-- Any upper bound on exact isotropic target excess risk is automatically an
    upper bound on the fine-tuning bias term `coefficientGapSq`. -/
theorem coefficientGapSq_le_of_targetLinearExcessRisk_le
    {p : ℕ}
    (crossTarget : Fin p → ℝ)
    (noiseVar errCap : ℝ)
    (w wStar : Fin p → ℝ)
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget)
    (h_excess :
      targetLinearExcessRisk (1 : Matrix (Fin p) (Fin p) ℝ)
        crossTarget noiseVar w wStar ≤ errCap) :
    coefficientGapSq w wStar ≤ errCap := by
  rw [← isotropic_targetLinearExcessRisk_eq_coefficientGapSq
    crossTarget noiseVar w wStar h_opt]
  exact h_excess

/-- Exact target-specific adaptation gain: the reduction in literal target
    excess quadratic risk achieved by moving from `wBefore` to `wAfter`. -/
noncomputable def exactAdaptationGain {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (wBefore wAfter wStar : Fin p → ℝ) : ℝ :=
  targetLinearExcessRisk sigmaObsTarget crossTarget noiseVar wBefore wStar -
    targetLinearExcessRisk sigmaObsTarget crossTarget noiseVar wAfter wStar

/-- In the isotropic target design, exact adaptation gain is literally the drop
    in squared coefficient mismatch to the target-optimal effect vector. -/
theorem exactAdaptationGain_eq_coefficientGapDrop_isotropic
    {p : ℕ}
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (wBefore wAfter wStar : Fin p → ℝ)
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
    exactAdaptationGain (1 : Matrix (Fin p) (Fin p) ℝ)
        crossTarget noiseVar wBefore wAfter wStar =
      coefficientGapSq wBefore wStar - coefficientGapSq wAfter wStar := by
  unfold exactAdaptationGain
  rw [isotropic_targetLinearExcessRisk_eq_coefficientGapSq crossTarget noiseVar
      wBefore wStar h_opt]
  rw [isotropic_targetLinearExcessRisk_eq_coefficientGapSq crossTarget noiseVar
      wAfter wStar h_opt]

section ExactGainFineTuning

/-! Every declaration in this section is about one score at one design, and each of them
repeated the same seven-line binder block to say so.  The block is a `variable` line now,
which is what Lean has for this; only the hypothesis `h_opt`, which the isotropic
statements need and the general ones do not, stays where it is used. -/

variable {p : ℕ}
  (source_r2 transported_r2 : ℝ)
  (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
  (crossTarget : Fin p → ℝ)
  (noiseVar : ℝ)
  (wBefore wAfter wStar : Fin p → ℝ)

/-- The fine-tuned target `R²` credited with the EXACT adaptation gain: the transported
baseline, penalised by the portability loss, and credited with the literal drop in target
excess risk rather than a scalar parameter.

Every theorem about this score wrote it out in full -- four lines of it, on top of the
binder block they share -- so the score and its readings could drift apart in a proof that
still typechecks.  The isotropic score below is this one at `Σ = 1`. -/
noncomputable def fineTunedTargetR2OfExactGain : ℝ :=
  fineTunedTargetR2 source_r2
    (transportPenalty source_r2 transported_r2)
    (exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar)

/-- The scalar fine-tuning `adaptation_gain` parameter is exactly the gain in
    target `R²` obtained by reducing literal target excess risk, once the
    baseline portability loss is instantiated by an explicit transported
    baseline. -/
theorem fineTunedTargetR2_eq_transportedBaseline_plus_exact_excessRisk_reduction :
    fineTunedTargetR2OfExactGain source_r2 transported_r2 sigmaObsTarget
        crossTarget noiseVar wBefore wAfter wStar =
      transported_r2 +
        exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar := by
  unfold fineTunedTargetR2OfExactGain
  rw [fineTunedTargetR2_eq_transportedR2_plus_adaptation]

/-- The exact excess-risk fine-tuning theorem is an instance of the canonical
    deployed-transfer target `R²` surface with an explicit transported baseline,
    exact target-specific adaptation gain, and zero estimation penalty. -/
theorem fineTunedTargetR2_eq_deployedTransferTargetR2_exactAdaptationGain :
    fineTunedTargetR2OfExactGain source_r2 transported_r2 sigmaObsTarget
        crossTarget noiseVar wBefore wAfter wStar =
      deployedTransferTargetR2 transported_r2
        (exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar) 0 := by
  unfold fineTunedTargetR2OfExactGain
  simpa using fineTunedTargetR2_eq_deployedTransferTargetR2
    source_r2 transported_r2
    (exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar)

/-- The fine-tuned target `R²` of the isotropic design: the transported baseline penalised
by the portability loss and credited with the exact adaptation gain at `Σ = 1`.

The two theorems below evaluate this same score against two different right-hand sides, and
each wrote the score out in full -- four lines of it, on top of the seven binder lines they
share.  Named once, the pair reads as two readings of one quantity, which is what it is. -/
noncomputable def isotropicFineTunedTargetR2 : ℝ :=
  fineTunedTargetR2OfExactGain source_r2 transported_r2
    (1 : Matrix (Fin p) (Fin p) ℝ) crossTarget noiseVar wBefore wAfter wStar

/-- In the isotropic target design, the scalar fine-tuning model is exactly the
    transported baseline plus the drop in squared effect mismatch
    from target adaptation. -/
theorem fineTunedTargetR2_eq_transportedBaseline_plus_gap_drop_isotropic
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
    isotropicFineTunedTargetR2 source_r2 transported_r2 crossTarget noiseVar
        wBefore wAfter wStar =
      transported_r2 +
        (coefficientGapSq wBefore wStar - coefficientGapSq wAfter wStar) := by
  unfold isotropicFineTunedTargetR2
  rw [fineTunedTargetR2_eq_transportedBaseline_plus_exact_excessRisk_reduction]
  rw [exactAdaptationGain_eq_coefficientGapDrop_isotropic crossTarget noiseVar
    wBefore wAfter wStar h_opt]

/-- In the isotropic target design, the deployed fine-tuning target `R²`
    reduces to the canonical transported baseline plus the exact drop in
    squared coefficient mismatch, with zero estimation penalty. -/
theorem fineTunedTargetR2_eq_deployedTransferTargetR2_gapDrop_isotropic
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
    isotropicFineTunedTargetR2 source_r2 transported_r2 crossTarget noiseVar
        wBefore wAfter wStar =
      deployedTransferTargetR2 transported_r2
        (coefficientGapSq wBefore wStar - coefficientGapSq wAfter wStar) 0 := by
  rw [fineTunedTargetR2_eq_transportedBaseline_plus_gap_drop_isotropic
    source_r2 transported_r2 crossTarget noiseVar wBefore wAfter wStar h_opt]
  unfold deployedTransferTargetR2
  ring

end ExactGainFineTuning

/-- Taking the transported baseline to be the target oracle ceiling minus the
    pre-adaptation coefficient gap — written out in the statement rather than
    assumed of a free variable — isotropic fine-tuning reduces the deployed
    target `R²` exactly to the oracle ceiling minus the residual
    post-adaptation gap. This is the clean residual-gap form of the canonical
    deployed-transfer theorem. -/
theorem fineTunedTargetR2_eq_oracle_minus_postGap_isotropic
    {p : ℕ}
    (source_r2 oracle_target_r2 : ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (wBefore wAfter wStar : Fin p → ℝ)
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
    fineTunedTargetR2 source_r2
        (transportPenalty source_r2
          (oracle_target_r2 - coefficientGapSq wBefore wStar))
        (exactAdaptationGain (1 : Matrix (Fin p) (Fin p) ℝ)
          crossTarget noiseVar wBefore wAfter wStar) =
      oracle_target_r2 - coefficientGapSq wAfter wStar := by
  -- The goal is `isotropicFineTunedTargetR2` unfolded. `rw` matches syntactically,
  -- so fold it back before rewriting with the lemma stated about that name.
  show isotropicFineTunedTargetR2 source_r2
      (oracle_target_r2 - coefficientGapSq wBefore wStar)
      crossTarget noiseVar wBefore wAfter wStar =
    oracle_target_r2 - coefficientGapSq wAfter wStar
  rw [fineTunedTargetR2_eq_deployedTransferTargetR2_gapDrop_isotropic
    source_r2 (oracle_target_r2 - coefficientGapSq wBefore wStar)
    crossTarget noiseVar wBefore wAfter wStar h_opt]
  have h_oracle_gap :
      oracleTransportAdaptationGain
          (oracle_target_r2 - coefficientGapSq wBefore wStar)
          oracle_target_r2 =
        coefficientGapSq wBefore wStar := by
    unfold oracleTransportAdaptationGain
    ring
  calc
    deployedTransferTargetR2
        (oracle_target_r2 - coefficientGapSq wBefore wStar)
        (coefficientGapSq wBefore wStar - coefficientGapSq wAfter wStar)
        0
      =
        deployedTransferTargetR2
          (oracle_target_r2 - coefficientGapSq wBefore wStar)
          (oracleTransportAdaptationGain
              (oracle_target_r2 - coefficientGapSq wBefore wStar)
              oracle_target_r2 -
            coefficientGapSq wAfter wStar)
          0 := by rw [h_oracle_gap]
    _ = oracle_target_r2 - coefficientGapSq wAfter wStar - 0 :=
      deployedTransferTargetR2_eq_oracle_minus_residualGap_minus_estimationPenalty
        (oracle_target_r2 - coefficientGapSq wBefore wStar)
        oracle_target_r2
        (coefficientGapSq wAfter wStar)
        0
    _ = oracle_target_r2 - coefficientGapSq wAfter wStar := by ring

/-- **More source populations reduce the target fine-tuning burden.**
    This is an explicit shared-feature meta-learning theorem, not a hard-coded
    `1 / k` law. We model the transported source weights learned from the first
    `k` populations as

    - a shared center `wShared`,
    - plus the average of `k` population-specific deviations.

    The `1 / k` decay is then derived, not assumed: if the population-specific
    deviations are pairwise orthogonal, each has the same squared norm
    `populationSpecificGap`, and each is orthogonal to the shared residual
    `wShared - wTarget`, then averaging over more source populations strictly
    lowers the exact squared coefficient gap to the target optimum. Because the
    optimal shrinkage fine-tuning MSE and the required target sample size are
    already solved exactly as functions of that gap, they strictly decrease as
    well. -/
theorem amortized_per_population_adaptation_cost_falls_with_task_count
    {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap noiseVar nTarget tau : ℝ)
    (k₁ k₂ : ℕ)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₂)
    (h_pop : 0 < populationSpecificGap)
    (h_noise : 0 < noiseVar)
    (h_n : 0 < nTarget)
    (h_tau : 0 < tau)
    (h_k₁ : 0 < k₁)
    (h_more_tasks : k₁ < k₂)
    (h_tau_small :
      tau < metaLearnedTransferGapSq wShared wTarget deviation k₂) :
    metaLearnedTransferGapSq wShared wTarget deviation k₂ <
      metaLearnedTransferGapSq wShared wTarget deviation k₁ ∧
    optimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₂)
        noiseVar nTarget <
      optimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₁)
        noiseVar nTarget ∧
    0 <
      requiredTargetSamplesForOptimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₂)
        noiseVar tau ∧
    requiredTargetSamplesForOptimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₂)
        noiseVar tau <
      requiredTargetSamplesForOptimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₁)
        noiseVar tau := by
  have h_k₂ : 0 < k₂ := lt_trans h_k₁ h_more_tasks
  have h_gap_order :
      metaLearnedTransferGapSq wShared wTarget deviation k₂ <
        metaLearnedTransferGapSq wShared wTarget deviation k₁ :=
    metaLearnedTransferGapSq_strictMono
      wShared wTarget deviation populationSpecificGap
      k₁ k₂ h_pop h_k₁ h_more_tasks hdev
  have h_gap₂_pos :
      0 < metaLearnedTransferGapSq wShared wTarget deviation k₂ :=
    metaLearnedTransferGapSq_pos
      wShared wTarget deviation populationSpecificGap
      k₂ h_pop h_k₂ hdev
  have h_mse_order :
      optimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₂)
          noiseVar nTarget <
        optimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₁)
          noiseVar nTarget :=
    optimalFineTuningMSE_strictMono_in_gapSq
      (metaLearnedTransferGapSq wShared wTarget deviation k₂)
      (metaLearnedTransferGapSq wShared wTarget deviation k₁)
      noiseVar nTarget (le_of_lt h_gap₂_pos) h_gap_order h_noise h_n
  have h_req_pos :
      0 <
        requiredTargetSamplesForOptimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₂)
          noiseVar tau :=
    requiredTargetSamplesForOptimalFineTuningMSE_pos
      (metaLearnedTransferGapSq wShared wTarget deviation k₂)
      noiseVar tau h_noise h_tau h_tau_small
  have h_req_order :
      requiredTargetSamplesForOptimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₂)
          noiseVar tau <
        requiredTargetSamplesForOptimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₁)
          noiseVar tau :=
    requiredTargetSamplesForOptimalFineTuningMSE_strictMono_in_gapSq
      (metaLearnedTransferGapSq wShared wTarget deviation k₂)
      (metaLearnedTransferGapSq wShared wTarget deviation k₁)
      noiseVar tau h_gap₂_pos h_gap_order h_noise h_tau
  exact ⟨h_gap_order, h_mse_order, h_req_pos, h_req_order⟩

/-- More source populations strictly improve the canonical deployed-transfer
    target `R²` when the only remaining adaptation burden is the exact
    meta-learned residual coefficient gap. This expresses the meta-learning
    block directly on the shared deployed metric surface rather than only on
    gap or MSE surrogates. -/
theorem metaLearned_deployedTransferTargetR2_strictMono
    {p : ℕ}
    (transported_r2 oracle_target_r2 estimation_penalty : ℝ)
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k₁ k₂ : ℕ)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₂)
    (h_pop : 0 < populationSpecificGap)
    (h_k₁ : 0 < k₁)
    (h_more_tasks : k₁ < k₂) :
    deployedTransferTargetR2 transported_r2
        (oracleTransportAdaptationGain transported_r2 oracle_target_r2 -
          metaLearnedTransferGapSq wShared wTarget deviation k₁)
        estimation_penalty <
      deployedTransferTargetR2 transported_r2
        (oracleTransportAdaptationGain transported_r2 oracle_target_r2 -
          metaLearnedTransferGapSq wShared wTarget deviation k₂)
        estimation_penalty := by
  have h_gap_order :
      metaLearnedTransferGapSq wShared wTarget deviation k₂ <
        metaLearnedTransferGapSq wShared wTarget deviation k₁ :=
    metaLearnedTransferGapSq_strictMono
      wShared wTarget deviation populationSpecificGap
      k₁ k₂ h_pop h_k₁ h_more_tasks hdev
  unfold deployedTransferTargetR2 oracleTransportAdaptationGain
  linarith

end FineTuning


/-!
## Theoretical Limits of Transfer

Even with optimal transfer learning, there are fundamental limits
on cross-population PGS performance.
-/

section TransferLimits

/-- **Subunit cross-pop effect correlation prevents attaining target heritability.**
    If a transported score is certified to satisfy the ceiling
    `R²_target ≤ rg_sq × h²_target` and the cross-pop effect-correlation factor
    satisfies `rg_sq < 1`, then the score falls strictly below the target
    heritability ceiling. This is the actual transfer-limit consequence used in
    this file. -/
theorem subunit_effect_correlation_prevents_attaining_target_heritability
    (r2_target rg_sq h2_target : ℝ)
    (h_bound : r2_target ≤ rg_sq * h2_target)
    (h_rg_lt : rg_sq < 1)
    (h_h2_pos : 0 < h2_target) :
    r2_target < h2_target := by
  have h_ceiling_lt : rg_sq * h2_target < h2_target := by
    nlinarith
  exact lt_of_le_of_lt h_bound h_ceiling_lt

/-- **Transfer ceiling from private architecture and migration-limited LD sharing.**
    Even with perfect transport on the shared loci, only the shared causal
    fraction `1 - f_private` can contribute across populations, and only the
    migration-drift shared-LD fraction `sharedLDFromMigration M` can be tagged
    coherently in the target. This gives the architecture-aware ceiling

    `h²_target × (1 - f_private) × sharedLDFromMigration M`.

    The ceiling is stated in terms of target heritability rather than source
    `R²`, so it is directly comparable to the theoretical transport limits above
    and to the migration-drift LD machinery in `PortabilityDrift`. -/
noncomputable def privateArchitectureTransferCeiling
    (h2_target f_private M : ℝ) : ℝ :=
  h2_target * (1 - f_private) * sharedLDFromMigration M

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem privateArchitectureTransferCeiling_at_reference_point :
    privateArchitectureTransferCeiling 1 (1 / 2) 1 = 1 / 4 := by
  norm_num [privateArchitectureTransferCeiling, sharedLDFromMigration,
      Descent.Core.saturation]



/-- **A positive private causal fraction lowers the transferable `R²` ceiling.**
    In the architecture-aware transfer model above, compare a trait with private causal fraction
    `f_private` to the same trait with no private
    architecture (`f_private = 0`) at the same migration-drift LD sharing level
    `sharedLDFromMigration M`.

    If a transported score is certified to satisfy the private-architecture
    ceiling, then any strictly positive private fraction pushes the achievable
    target `R²` strictly below the no-private benchmark, and therefore strictly
    below target heritability as well. This is a real transport-limit statement,
    not just the algebraic identity `f_shared = 1 - f_private`. -/
theorem private_causal_fraction_lowers_transfer_ceiling
    (r2_target h2_target f_private M : ℝ)
    (h_bound : r2_target ≤ privateArchitectureTransferCeiling h2_target f_private M)
    (h_h2 : 0 < h2_target)
    (h_private : 0 < f_private)
    (hM : 0 < M) :
    privateArchitectureTransferCeiling h2_target f_private M <
      privateArchitectureTransferCeiling h2_target 0 M ∧
    r2_target < privateArchitectureTransferCeiling h2_target 0 M ∧
    r2_target < h2_target := by
  have h_shared_pos : 0 < sharedLDFromMigration M := by
    unfold sharedLDFromMigration Descent.Core.saturation
    have h_den_pos : 0 < 1 + M := by linarith
    exact div_pos hM h_den_pos
  have h_shared_lt_one : sharedLDFromMigration M < 1 :=
    sharedLDFromMigration_lt_one M (le_of_lt hM)
  have h_one_minus_lt_one : 1 - f_private < 1 := by linarith
  have h_ceiling_lt_no_private :
      privateArchitectureTransferCeiling h2_target f_private M <
        privateArchitectureTransferCeiling h2_target 0 M := by
    unfold privateArchitectureTransferCeiling
    have h_base_pos : 0 < h2_target * sharedLDFromMigration M :=
      mul_pos h_h2 h_shared_pos
    calc
      h2_target * (1 - f_private) * sharedLDFromMigration M
          = (h2_target * sharedLDFromMigration M) * (1 - f_private) := by ring
      _ < h2_target * sharedLDFromMigration M :=
        mul_lt_of_lt_one_right h_base_pos h_one_minus_lt_one
      _ = h2_target * (1 - (0 : ℝ)) * sharedLDFromMigration M := by ring
  have h_no_private_lt_h2 :
      privateArchitectureTransferCeiling h2_target 0 M < h2_target := by
    unfold privateArchitectureTransferCeiling
    calc
      h2_target * (1 - (0 : ℝ)) * sharedLDFromMigration M
          = h2_target * sharedLDFromMigration M := by ring
      _ < h2_target :=
        mul_lt_of_lt_one_right h_h2 h_shared_lt_one
  have h_r2_lt_no_private :
      r2_target < privateArchitectureTransferCeiling h2_target 0 M :=
    lt_of_le_of_lt h_bound h_ceiling_lt_no_private
  have h_r2_lt_h2 : r2_target < h2_target :=
    lt_trans h_r2_lt_no_private h_no_private_lt_h2
  exact ⟨h_ceiling_lt_no_private, h_r2_lt_no_private, h_r2_lt_h2⟩

end TransferLimits

/-! ## What it costs to have fitted against the wrong linkage-disequilibrium operator

Every bound above takes the operator as given. In practice the panel is optimised against an
estimated reference linkage structure and deployed against the target's true one, and what decides
whether that is tolerable is not the error in the estimated objective — which moves at first order
and always will — but the loss from transplanting the optimizer.

`Descent.Portability.TransplantationStability` answers with one number the fit already contains:
`γ`, the
margin by which the selected panel beats the runner-up in the fitted objective. With `δ` an error
budget for the operator, the deployment loss is `min(2δ, 8δ²/γ)`, and the quadratic branch binds
exactly when `4δ < γ`.

The degenerate branch is not hypothetical. Near-ties between candidate panels, shrinkage levels
and ancestry-weighting schemes are the normal case, and there the standard argument — the
objective is stationary at the optimum, so small model error costs second order — fails: the
transplanted choice lands on the wrong branch and pays the full `δ`.

So a transferred score should be reported with its margin. Without `γ` there is no route from an
operator error budget to a deployment-loss bound, and optimality under one estimated operator is a
different claim from robustness to having estimated it. -/

section OperatorError

open Matrix

/-- From linkage-disequilibrium model error to deployment loss. Instance of
    `transplant_excess_le`, in the eigenbasis of the true operator: `spectrum` carries its
    eigenvalues with the deployed design at the ground direction, `weights` the fitted panel's
    coefficients, `E` the operator error with quadratic form bounded by `modelError`, and
    `margin` the gap between the selected panel and the runner-up. The excess loss is quadratic
    in the model error with constant `8/margin`.

    The spectral gap bound and the perturbation estimate used by `transplant_excess_le` are both
    proved in `Descent.Portability.TransplantationStability`.

    Empirical status: DERIVED; `margin` is a quantity a fit already produces and this result asks
    to be reported. -/
theorem ldModelError_to_deploymentLoss {n : ℕ}
    (spectrum weights : Fin (n + 1) → ℝ)
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (margin modelError : ℝ)
    (hmargin : 0 < margin) (herr : 0 ≤ modelError) (hEsymm : E.IsSymm)
    (hEbound : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 →
      |v ⬝ᵥ (E *ᵥ v)| ≤ modelError)
    (hunit : ∑ i, weights i ^ 2 = 1)
    (hgap : ∀ i ∈ Finset.univ.erase (0 : Fin (n + 1)),
      spectrum 0 + margin ≤ spectrum i)
    (hmin : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 →
      perturbedEnergy spectrum E weights ≤ perturbedEnergy spectrum E v) :
    spectralEnergy spectrum weights - spectrum 0 ≤ 8 * modelError ^ 2 / margin :=
  transplant_excess_le spectrum weights E margin modelError hmargin herr hEsymm hEbound
    hunit hgap hmin

/-- The quadratic branch applies only while the model error is small against the margin.

    Empirical status: DERIVED. -/
theorem quadraticLoss_binds_iff_error_small (margin modelError : ℝ)
    (hmargin : 0 < margin) (herr : 0 < modelError) :
    8 * modelError ^ 2 / margin < 2 * modelError ↔ 4 * modelError < margin :=
  quadratic_beats_linear_iff margin modelError hmargin herr

/-- At a tie between candidate panels the loss is the full model error.

    Empirical status: DERIVED. -/
theorem tiedPanels_lose_the_whole_error (modelError : ℝ) (herr : 0 < modelError) :
    trueDesignValue modelError 0 - trueDesignValue modelError 1 = modelError :=
  (crossing_loss_linear modelError herr).2.2

/-! ### Junk-value boundaries

Four bodies here divide, and one takes a square root that Mathlib sends to `0` on negative
arguments.  Each branch is named so a consumer cannot read the returned `0` as a measurement. -/

/-- A nonpositive product of shared-LD genetic variances sends the square root to Mathlib's
junk `0`, and the correlation with it.  Zero correlation is a meaningful value, so this branch
has to be named rather than detected. -/
theorem ldEffectGeneticCorrelation_at_nonpositive_variance_is_junk
    {m : ℕ} (β_source β_target : Fin m → ℝ) (ld : Fin m → Fin m → ℝ)
    (hnonpos : sharedLDGeneticVariance β_source ld * sharedLDGeneticVariance β_target ld ≤ 0) :
    ldEffectGeneticCorrelation β_source β_target ld = 0 := by
  unfold ldEffectGeneticCorrelation
  rw [Real.sqrt_eq_zero_of_nonpos hnonpos, div_zero]

/-- With no target sample the noise-per-sample term is Mathlib's junk `0`, so the body reports
the noiseless oracle rather than the correct limit of no information. -/
theorem sampleLimitedScratchTargetR2_at_zero_sample_is_junk
    (oracle_target_r2 noiseVar : ℝ) :
    sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar 0
      = scratchTargetR2 oracle_target_r2 0 := by
  unfold sampleLimitedScratchTargetR2
  rw [div_zero]

/-- When fine-tuning already matches the oracle there is no crossing sample size, and the
quotient reports `0` -- the value that would mean "no samples needed", the opposite reading. -/
theorem scratchVsFineTuningCriticalSampleSize_at_no_gap_is_junk
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar : ℝ)
    (hgap : oracle_target_r2
      = fineTunedTargetR2 r2_source divergence_penalty adaptation_gain) :
    scratchVsFineTuningCriticalSampleSize r2_source divergence_penalty adaptation_gain
        oracle_target_r2 noiseVar = 0 := by
  unfold scratchVsFineTuningCriticalSampleSize
  rw [hgap, sub_self, div_zero]

/-- Averaging over no populations divides by zero, and the mean deviation reports `0` rather
than being undefined. -/
theorem meanPopulationDeviation_at_zero_count_is_junk
    {p : ℕ} (deviation : ℕ → Fin p → ℝ) (i : Fin p) :
    meanPopulationDeviation deviation 0 i = 0 := by
  unfold meanPopulationDeviation
  simp

/-- The same boundary for the averaged source weights. -/
theorem sourcePopulationMeanWeights_at_zero_count_is_junk
    {p : ℕ} (wSource : ℕ → Fin p → ℝ) (i : Fin p) :
    sourcePopulationMeanWeights wSource 0 i = 0 := by
  unfold sourcePopulationMeanWeights
  simp

end OperatorError

end Descent.Portability
