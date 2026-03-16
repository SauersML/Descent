import Calibrator.PortabilityDrift

namespace Calibrator

open Matrix
open scoped Matrix

/-!
# Simulation Theory and Mechanistic Validation of Portability Models

This file records only simulation-validation objects that remain honest under
the explicit SNP/LD-aware portability surface in `PortabilityDrift`.

The deleted source-`R²` attenuation law is intentionally absent. Target metrics
are evaluated directly from explicit source/target biological state:

- source and target LD among scored SNPs
- source and target tag-to-causal alignment
- source and target effect vectors
- source and target context/environment cross-covariances
- additive target-side residual losses from broken tagging,
  ancestry-specific LD distortion, and source-specific overfit
- target prevalence for deployed calibration metrics
-/

section MechanisticValidation

/-- Exact target/source portability ratio from the explicit mechanistic state. -/
noncomputable def mechanisticPortabilityRatio {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  targetR2FromSourceWeights m / sourceR2FromSourceWeights m

/-- Baseline single-locus mechanistic witness with identical source and target
state where the scored SNP is itself the causal variant. -/
noncomputable def baselineMetricModel : CrossPopulationMetricModel 1 1 := {
  betaSource := ![1]
  betaTarget := ![1]
  sigmaTagSource := !![1]
  sigmaTagTarget := !![1]
  directCausalSource := !![1]
  directCausalTarget := !![1]
  proxyTaggingSource := !![0]
  proxyTaggingTarget := !![0]
  contextCrossSource := ![0]
  contextCrossTarget := ![0]
  sourceOutcomeVariance := 2
  targetOutcomeVariance := 2
  targetPrevalence := 1 / 2
  sourceOutcomeVariance_pos := by norm_num
  targetOutcomeVariance_pos := by norm_num
  targetPrevalence_pos := by norm_num
  targetPrevalence_lt_one := by norm_num
}

/-- Target-LD-shift witness: only the target LD among scored SNPs changes. -/
noncomputable def targetLDShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      sigmaTagTarget := !![2] }

/-- Proxy-tag baseline witness: the scored SNP is not itself causal, but is a
perfect source and target proxy for the unscored causal variant. -/
noncomputable def baselineProxyTagMetricModel : CrossPopulationMetricModel 1 1 := {
  baselineMetricModel with
    directCausalSource := !![0]
    directCausalTarget := !![0]
    proxyTaggingSource := !![1]
    proxyTaggingTarget := !![1] }

/-- Target tagging-shift witness: only the target proxy-tagging alignment
changes. -/
noncomputable def targetTaggingShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineProxyTagMetricModel with
      proxyTaggingTarget := !![1 / 2] }

/-- Target effect-shift witness: only the target causal effect size changes. -/
noncomputable def targetEffectShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      betaTarget := ![1 / 2] }

/-- Target context-shift witness: only the target context/environment
cross-covariance changes. -/
noncomputable def targetContextShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      contextCrossTarget := ![-(1 / 2)] }

/-- Irreducible target mismatch witness. -/
noncomputable def targetPrevalenceShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      targetPrevalence := 1 / 4
      targetPrevalence_pos := by norm_num
      targetPrevalence_lt_one := by norm_num }

/-- The baseline witness has exact source and target metrics that can be read
off from the explicit state. -/
theorem baseline_mechanistic_metrics :
    brokenTaggingResidual baselineMetricModel = 0 ∧
    ancestrySpecificLDResidual baselineMetricModel = 0 ∧
    sourceSpecificOverfitResidual baselineMetricModel = 0 ∧
    sourceR2FromSourceWeights baselineMetricModel = 1 / 2 ∧
    targetR2FromSourceWeights baselineMetricModel = 1 / 2 ∧
    mechanisticPortabilityRatio baselineMetricModel = 1 ∧
    targetCalibratedBrierFromSourceWeights baselineMetricModel = 1 / 8 := by
  simp [baselineMetricModel, mechanisticPortabilityRatio,
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    irreducibleTargetResidualBurden,
    sourceR2FromSourceWeights, targetR2FromSourceWeights,
    sourceExplainedSignalVarianceFromSourceWeights,
    targetExplainedSignalVarianceFromSourceWeights,
    sourcePredictiveCovarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights,
    sourceScoreVarianceFromExplicitDrivers,
    targetScoreVarianceFromSourceWeights,
    sigmaTagCausalSource, sigmaTagCausalTarget,
    sourceTaggingProjection, targetTaggingProjection,
    sourceDirectCausalProjection, sourceProxyTaggingProjection,
    targetDirectCausalProjection, targetProxyTaggingProjection,
    sourceWeightsFromExplicitDrivers, sourceERMWeights,
    sourceCrossCovariance, targetCrossCovariance,
    effectiveTargetOutcomeVariance,
    targetCalibratedBrierFromSourceWeights,
    Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- A score built on the directly causal SNP and a score built on a perfect
proxy tag can have the same source `R²`, but once proxy tagging degrades in the
target population the tag-based score loses portability while the direct-causal
score does not. This is the explicit direct-vs-tag witness missing from the old
abstraction. -/
theorem direct_causal_vs_proxy_tag_same_source_r2_different_portability :
    sourceDirectCausalProjection baselineMetricModel 0 = 1 ∧
    sourceProxyTaggingProjection baselineMetricModel 0 = 0 ∧
    sourceDirectCausalProjection baselineProxyTagMetricModel 0 = 0 ∧
    sourceProxyTaggingProjection baselineProxyTagMetricModel 0 = 1 ∧
    sourceR2FromSourceWeights baselineMetricModel =
      sourceR2FromSourceWeights baselineProxyTagMetricModel ∧
    targetR2FromSourceWeights targetTaggingShiftMetricModel <
      targetR2FromSourceWeights baselineMetricModel := by
  simp [baselineMetricModel, baselineProxyTagMetricModel, targetTaggingShiftMetricModel,
    sourceDirectCausalProjection, sourceProxyTaggingProjection,
    sourceR2FromSourceWeights, targetR2FromSourceWeights,
    sourceExplainedSignalVarianceFromSourceWeights,
    targetExplainedSignalVarianceFromSourceWeights,
    sourcePredictiveCovarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights,
    sourceScoreVarianceFromExplicitDrivers,
    targetScoreVarianceFromSourceWeights,
    sourceWeightsFromExplicitDrivers, sourceERMWeights,
    sourceCrossCovariance, targetCrossCovariance,
    sigmaTagCausalSource, sigmaTagCausalTarget,
    sourceTaggingProjection, targetTaggingProjection,
    sourceDirectCausalProjection, sourceProxyTaggingProjection,
    targetDirectCausalProjection, targetProxyTaggingProjection,
    effectiveTargetOutcomeVariance, brokenTaggingResidual,
    ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    irreducibleTargetResidualBurden,
    Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- Target LD among scored SNPs changes target `R²` and portability even when
the source state, and therefore the source `R²`, are unchanged. -/
theorem target_ld_shift_changes_portability_without_changing_source_r2 :
    ancestrySpecificLDResidual targetLDShiftMetricModel = 1 ∧
    sourceR2FromSourceWeights targetLDShiftMetricModel =
      sourceR2FromSourceWeights baselineMetricModel ∧
    targetR2FromSourceWeights targetLDShiftMetricModel = 1 / 6 ∧
    targetR2FromSourceWeights baselineMetricModel = 1 / 2 ∧
    mechanisticPortabilityRatio targetLDShiftMetricModel = 1 / 3 := by
  simp [baselineMetricModel, targetLDShiftMetricModel, mechanisticPortabilityRatio,
    ancestrySpecificLDResidual, brokenTaggingResidual, sourceSpecificOverfitResidual,
    irreducibleTargetResidualBurden,
    sourceR2FromSourceWeights, targetR2FromSourceWeights,
    sourceExplainedSignalVarianceFromSourceWeights,
    targetExplainedSignalVarianceFromSourceWeights,
    sourcePredictiveCovarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights,
    sourceScoreVarianceFromExplicitDrivers,
    targetScoreVarianceFromSourceWeights,
    sigmaTagCausalSource, sigmaTagCausalTarget,
    sourceTaggingProjection, targetTaggingProjection,
    sourceDirectCausalProjection, sourceProxyTaggingProjection,
    targetDirectCausalProjection, targetProxyTaggingProjection,
    sourceWeightsFromExplicitDrivers, sourceERMWeights,
    sourceCrossCovariance, targetCrossCovariance,
    effectiveTargetOutcomeVariance,
    Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- Target proxy-tagging alignment changes target `R²` directly, even with the
same proxy-tag source score and the same source deployed `R²`. -/
theorem target_tagging_shift_changes_target_r2 :
    brokenTaggingResidual targetTaggingShiftMetricModel = 1 / 4 ∧
    sourceR2FromSourceWeights targetTaggingShiftMetricModel =
      sourceR2FromSourceWeights baselineProxyTagMetricModel ∧
    targetR2FromSourceWeights targetTaggingShiftMetricModel = 1 / 9 ∧
    mechanisticPortabilityRatio targetTaggingShiftMetricModel = 2 / 9 := by
  simp [baselineMetricModel, baselineProxyTagMetricModel, targetTaggingShiftMetricModel,
    mechanisticPortabilityRatio,
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    irreducibleTargetResidualBurden,
    sourceR2FromSourceWeights, targetR2FromSourceWeights,
    sourceExplainedSignalVarianceFromSourceWeights,
    targetExplainedSignalVarianceFromSourceWeights,
    sourcePredictiveCovarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights,
    sourceScoreVarianceFromExplicitDrivers,
    targetScoreVarianceFromSourceWeights,
    sigmaTagCausalSource, sigmaTagCausalTarget,
    sourceTaggingProjection, targetTaggingProjection,
    sourceDirectCausalProjection, sourceProxyTaggingProjection,
    targetDirectCausalProjection, targetProxyTaggingProjection,
    sourceWeightsFromExplicitDrivers, sourceERMWeights,
    sourceCrossCovariance, targetCrossCovariance,
    effectiveTargetOutcomeVariance,
    Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- Target effect-size shifts change target `R²` directly, even with unchanged
source score construction. -/
theorem target_effect_shift_changes_target_r2 :
    sourceR2FromSourceWeights targetEffectShiftMetricModel =
      sourceR2FromSourceWeights baselineMetricModel ∧
    irreducibleTargetResidualBurden targetEffectShiftMetricModel = 0 ∧
    targetR2FromSourceWeights targetEffectShiftMetricModel = 1 / 8 ∧
    mechanisticPortabilityRatio targetEffectShiftMetricModel = 1 / 4 := by
  simp [baselineMetricModel, targetEffectShiftMetricModel, mechanisticPortabilityRatio,
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    irreducibleTargetResidualBurden,
    sourceR2FromSourceWeights, targetR2FromSourceWeights,
    sourceExplainedSignalVarianceFromSourceWeights,
    targetExplainedSignalVarianceFromSourceWeights,
    sourcePredictiveCovarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights,
    sourceScoreVarianceFromExplicitDrivers,
    targetScoreVarianceFromSourceWeights,
    sigmaTagCausalSource, sigmaTagCausalTarget,
    sourceTaggingProjection, targetTaggingProjection,
    sourceDirectCausalProjection, sourceProxyTaggingProjection,
    targetDirectCausalProjection, targetProxyTaggingProjection,
    sourceWeightsFromExplicitDrivers, sourceERMWeights,
    sourceCrossCovariance, targetCrossCovariance,
    effectiveTargetOutcomeVariance,
    Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- Source-only context structure that does not transport creates an additive
source-specific overfit residual on the target side and lowers target `R²`. -/
theorem target_context_shift_creates_additive_overfit_loss_and_changes_target_r2 :
    sourceSpecificOverfitResidual targetContextShiftMetricModel = 1 / 4 ∧
    sourceR2FromSourceWeights targetContextShiftMetricModel =
      sourceR2FromSourceWeights baselineMetricModel ∧
    targetR2FromSourceWeights targetContextShiftMetricModel = 1 / 9 ∧
    mechanisticPortabilityRatio targetContextShiftMetricModel = 2 / 9 := by
  simp [baselineMetricModel, targetContextShiftMetricModel, mechanisticPortabilityRatio,
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    irreducibleTargetResidualBurden,
    sourceR2FromSourceWeights, targetR2FromSourceWeights,
    sourceExplainedSignalVarianceFromSourceWeights,
    targetExplainedSignalVarianceFromSourceWeights,
    sourcePredictiveCovarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights,
    sourceScoreVarianceFromExplicitDrivers,
    targetScoreVarianceFromSourceWeights,
    sigmaTagCausalSource, sigmaTagCausalTarget,
    sourceTaggingProjection, targetTaggingProjection,
    sourceDirectCausalProjection, sourceProxyTaggingProjection,
    targetDirectCausalProjection, targetProxyTaggingProjection,
    sourceWeightsFromExplicitDrivers, sourceERMWeights,
    sourceCrossCovariance, targetCrossCovariance,
    effectiveTargetOutcomeVariance,
    Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- Target prevalence changes the calibrated Brier score even when the score
moments and target `R²` are unchanged. -/
theorem target_prevalence_shift_changes_brier_without_changing_target_r2 :
    targetR2FromSourceWeights targetPrevalenceShiftMetricModel =
      targetR2FromSourceWeights baselineMetricModel ∧
    targetCalibratedBrierFromSourceWeights targetPrevalenceShiftMetricModel = 3 / 32 ∧
    targetCalibratedBrierFromSourceWeights baselineMetricModel = 1 / 8 := by
  simp [baselineMetricModel, targetPrevalenceShiftMetricModel,
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    irreducibleTargetResidualBurden,
    targetR2FromSourceWeights,
    targetExplainedSignalVarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights,
    targetScoreVarianceFromSourceWeights,
    sigmaTagCausalSource, sigmaTagCausalTarget,
    targetTaggingProjection, targetDirectCausalProjection, targetProxyTaggingProjection,
    sourceWeightsFromExplicitDrivers, sourceERMWeights,
    sourceCrossCovariance, targetCrossCovariance,
    effectiveTargetOutcomeVariance,
    targetCalibratedBrierFromSourceWeights,
    Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- The liability-threshold AUC coordinate is read from the explicit target
`R²` induced by the full mechanistic state; no source-`R²` transport summary
appears in the definition. -/
theorem target_metric_profile_auc_uses_explicit_target_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).auc =
      liabilityAUCFromExplainedR2 (targetR2FromSourceWeights m) := by
  simp [targetMetricProfileFromSourceWeights, targetLiabilityAUCFromSourceWeights]

/-- The standalone liability-threshold AUC accessor agrees with the canonical
target metric profile built from the explicit source-weights-on-target-state
equation. -/
theorem target_liability_auc_uses_explicit_target_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetLiabilityAUCFromSourceWeights m =
      liabilityAUCFromExplainedR2 (targetR2FromSourceWeights m) := by
  simpa using target_metric_profile_auc_uses_explicit_target_r2 m

/-- When target LD among scored SNPs changes, the deployed liability-threshold
AUC changes because the target `R²` itself changes under the explicit
mechanistic state. -/
theorem target_ld_shift_changes_liability_auc
    (hPhiStrict : StrictMono Phi) :
    targetLiabilityAUCFromSourceWeights targetLDShiftMetricModel <
      targetLiabilityAUCFromSourceWeights baselineMetricModel := by
  rcases target_ld_shift_changes_portability_without_changing_source_r2 with
    ⟨_, _, h_target_shift, h_target_base, _⟩
  rw [target_liability_auc_uses_explicit_target_r2,
    target_liability_auc_uses_explicit_target_r2,
    h_target_shift, h_target_base]
  exact liabilityAUCFromExplainedR2_strictMonoOn_unitInterval hPhiStrict
    ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩
    (by norm_num)

end MechanisticValidation

section GenerationalMechanisticValidation

/-- Simple generation-indexed population-genetic parameters used to validate
that the mechanistic target state can vary with time. Recombination, mutation,
and migration are set to zero here so the witness isolates allele-frequency
drift while still flowing through the same public API. -/
noncomputable def baselineGenerationalPopGen : GenerationalPopGenParameters := {
  Ne := 1
  μ := 0
  mig := 0
  recomb := 0
  V_A := 1
  Ne_pos := by norm_num
  μ_nonneg := by norm_num
  mig_nonneg := by norm_num
  recomb_nonneg := by norm_num
  recomb_le_half := by norm_num
  V_A_pos := by norm_num
}

/-- Single-locus generational witness where the target allele frequency drifts
away from the source after generation `0`, lowering tagging quality and target
`R²` even though the learned source score is unchanged. -/
noncomputable def timeVaryingAFGenerationalModel :
    CrossPopulationGenerationalModel 1 1 := {
  popGen := baselineGenerationalPopGen
  betaSource := ![1]
  targetEffectHeterogeneityAt := fun _ => ![0]
  sigmaTagSource := !![1]
  directCausalSource := !![0]
  proxyTaggingSource := !![1]
  tagDistance := !![1]
  tagCausalDistance := !![1]
  tagAlleleFreqSource := ![1 / 2]
  tagAlleleFreqTargetAt := fun t => ![if t = 0 then (1 / 2 : ℝ) else 3 / 4]
  causalAlleleFreqSource := ![1 / 2]
  causalAlleleFreqTargetAt := fun t => ![if t = 0 then (1 / 2 : ℝ) else 3 / 4]
  contextCrossSource := ![0]
  contextCrossTargetAt := fun _ => ![0]
  sourceOutcomeVariance := 2
  targetOutcomeVarianceAt := fun _ => 2
  targetPrevalenceAt := fun _ => 1 / 2
  sourceOutcomeVariance_pos := by norm_num
  targetOutcomeVariance_pos := by intro t; norm_num
  targetPrevalence_pos := by intro t; norm_num
  targetPrevalence_lt_one := by intro t; norm_num
}

/-- Single-locus generational witness where LD, tagging, and allele frequencies
stay fixed, but the target effect vector changes over time. This isolates
population/time-varying effect heterogeneity as the sole portability driver. -/
noncomputable def timeVaryingEffectGenerationalModel :
    CrossPopulationGenerationalModel 1 1 := {
  popGen := baselineGenerationalPopGen
  betaSource := ![1]
  targetEffectHeterogeneityAt := fun t =>
    ![if t = 0 then (0 : ℝ) else -(1 / 2)]
  sigmaTagSource := !![1]
  directCausalSource := !![1]
  proxyTaggingSource := !![0]
  tagDistance := !![1]
  tagCausalDistance := !![1]
  tagAlleleFreqSource := ![1 / 2]
  tagAlleleFreqTargetAt := fun _ => ![1 / 2]
  causalAlleleFreqSource := ![1 / 2]
  causalAlleleFreqTargetAt := fun _ => ![1 / 2]
  contextCrossSource := ![0]
  contextCrossTargetAt := fun _ => ![0]
  sourceOutcomeVariance := 2
  targetOutcomeVarianceAt := fun _ => 2
  targetPrevalenceAt := fun _ => 1 / 2
  sourceOutcomeVariance_pos := by norm_num
  targetOutcomeVariance_pos := by intro t; norm_num
  targetPrevalence_pos := by intro t; norm_num
  targetPrevalence_lt_one := by intro t; norm_num
}

/-- The generation-indexed target `R²` path reflects explicit allele-frequency
drift in the target population. At generation `0` the target matches the
source, while at generation `1` the target `R²` is reduced by the exact AF
mismatch penalty carried through the tagging surface. -/
theorem target_r2_changes_along_generation_indexed_af_path :
    targetR2AtGeneration timeVaryingAFGenerationalModel 0 = 1 / 2 ∧
    targetR2AtGeneration timeVaryingAFGenerationalModel 1 =
      Real.exp (-(1 / 2 : ℝ)) /
        (2 + 2 * (1 - Real.exp (-(1 / 2 : ℝ))) ^ 2) := by
  constructor
  · simp [baselineGenerationalPopGen, targetR2AtGeneration, timeVaryingAFGenerationalModel,
      CrossPopulationGenerationalModel.toMetricModelAt,
      sigmaTagTargetAt, directCausalTargetAt, proxyTaggingTargetAt, sigmaTagCausalTargetAt,
      tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      targetR2FromSourceWeights,
      targetExplainedSignalVarianceFromSourceWeights,
      targetPredictiveCovarianceFromSourceWeights,
      targetScoreVarianceFromSourceWeights,
      sigmaTagCausalSource, sigmaTagCausalTarget,
      sourceTaggingProjection, targetTaggingProjection,
      sourceDirectCausalProjection, sourceProxyTaggingProjection,
      targetDirectCausalProjection, targetProxyTaggingProjection,
      sourceWeightsFromExplicitDrivers, sourceERMWeights,
      sourceCrossCovariance, targetCrossCovariance,
      effectiveTargetOutcomeVariance, irreducibleTargetResidualBurden,
      brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      GenerationalPopGenParameters.bigM,
      ldCorrelationDecay,
      Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  · have h_cov :
        targetPredictiveCovarianceFromSourceWeights
            (timeVaryingAFGenerationalModel.toMetricModelAt 1) =
          Real.exp (-(1 / 2 : ℝ)) := by
      calc
        targetPredictiveCovarianceFromSourceWeights
            (timeVaryingAFGenerationalModel.toMetricModelAt 1) =
          Real.exp (-|(3 / 4 : ℝ) - 1 / 2|) *
            Real.exp (-|(3 / 4 : ℝ) - 1 / 2|) := by
              simp [baselineGenerationalPopGen, timeVaryingAFGenerationalModel,
                CrossPopulationGenerationalModel.toMetricModelAt,
                directCausalTargetAt, proxyTaggingTargetAt, sigmaTagCausalTargetAt,
                tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
                targetPredictiveCovarianceFromSourceWeights,
                sigmaTagCausalSource, sigmaTagCausalTarget,
                sourceTaggingProjection, targetTaggingProjection,
                sourceDirectCausalProjection, sourceProxyTaggingProjection,
                targetDirectCausalProjection, targetProxyTaggingProjection,
                sourceWeightsFromExplicitDrivers, sourceERMWeights,
                sourceCrossCovariance, targetCrossCovariance,
                GenerationalPopGenParameters.theta,
                GenerationalPopGenParameters.tauAt,
                GenerationalPopGenParameters.fstTransientAt,
                GenerationalPopGenParameters.mutationSharedRetentionAt,
                GenerationalPopGenParameters.migrationSharedBoostAt,
                GenerationalPopGenParameters.bigM,
                ldCorrelationDecay,
                Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
        _ = Real.exp (-(1 / 2 : ℝ)) := by
              rw [← Real.exp_add]
              congr 1
              ring_nf
    have h_var :
        targetScoreVarianceFromSourceWeights
            (timeVaryingAFGenerationalModel.toMetricModelAt 1) =
          Real.exp (-(1 / 2 : ℝ)) := by
      calc
        targetScoreVarianceFromSourceWeights
            (timeVaryingAFGenerationalModel.toMetricModelAt 1) =
          Real.exp (-|(3 / 4 : ℝ) - 1 / 2|) *
            Real.exp (-|(3 / 4 : ℝ) - 1 / 2|) := by
              simp [baselineGenerationalPopGen, timeVaryingAFGenerationalModel,
                CrossPopulationGenerationalModel.toMetricModelAt,
                sigmaTagTargetAt,
                tagAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
                targetScoreVarianceFromSourceWeights,
                sigmaTagCausalSource, sourceTaggingProjection,
                sourceDirectCausalProjection, sourceProxyTaggingProjection,
                sourceWeightsFromExplicitDrivers, sourceERMWeights,
                sourceCrossCovariance,
                GenerationalPopGenParameters.theta,
                GenerationalPopGenParameters.tauAt,
                GenerationalPopGenParameters.fstTransientAt,
                GenerationalPopGenParameters.mutationSharedRetentionAt,
                GenerationalPopGenParameters.migrationSharedBoostAt,
                GenerationalPopGenParameters.bigM,
                ldCorrelationDecay,
                Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
        _ = Real.exp (-(1 / 2 : ℝ)) := by
              rw [← Real.exp_add]
              congr 1
              ring_nf
    have h_exp_ne : Real.exp (-(2⁻¹ : ℝ)) ≠ 0 := by
      exact Real.exp_ne_zero _
    rw [targetR2AtGeneration_eq_targetR2From_slice]
    unfold targetR2FromSourceWeights targetExplainedSignalVarianceFromSourceWeights
    rw [h_cov, h_var]
    simp [baselineGenerationalPopGen, timeVaryingAFGenerationalModel,
      CrossPopulationGenerationalModel.toMetricModelAt,
      sigmaTagTargetAt, directCausalTargetAt, proxyTaggingTargetAt, sigmaTagCausalTargetAt,
      tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      sigmaTagCausalSource, sigmaTagCausalTarget,
      sourceTaggingProjection, targetTaggingProjection,
      sourceDirectCausalProjection, sourceProxyTaggingProjection,
      targetDirectCausalProjection, targetProxyTaggingProjection,
      effectiveTargetOutcomeVariance, irreducibleTargetResidualBurden,
      brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
      sourceWeightsFromExplicitDrivers, sourceERMWeights,
      sourceCrossCovariance,
      GenerationalPopGenParameters.theta,
      GenerationalPopGenParameters.tauAt,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      GenerationalPopGenParameters.bigM,
      ldCorrelationDecay,
      Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
    have h_ret :
        Real.exp (-|3 / 4 - (2⁻¹ : ℝ)|) *
            Real.exp (-|3 / 4 - (2⁻¹ : ℝ)|) =
          Real.exp (-(2⁻¹ : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      norm_num
    rw [h_ret]
    have h_loss :
        2 +
            ((1 - Real.exp (-(2⁻¹ : ℝ))) * (1 - Real.exp (-(2⁻¹ : ℝ))) +
              (1 - Real.exp (-(2⁻¹ : ℝ))) * (1 - Real.exp (-(2⁻¹ : ℝ)))) =
          2 + 2 * (1 - Real.exp (-(2⁻¹ : ℝ))) ^ 2 := by
      ring
    rw [h_loss]
    have hcalc :
        Real.exp (-(2⁻¹ : ℝ)) ^ 2 /
            Real.exp (-(2⁻¹ : ℝ)) /
              (2 + 2 * (1 - Real.exp (-(2⁻¹ : ℝ))) ^ 2) =
          Real.exp (-(2⁻¹ : ℝ)) /
            (2 + 2 * (1 - Real.exp (-(2⁻¹ : ℝ))) ^ 2) := by
      field_simp [h_exp_ne]
    simpa using hcalc

/-- With LD, tagging, and allele frequencies held fixed, a locus-resolved
target-effect heterogeneity path alone changes deployed target `R²`. This is
the required witness that portability can fail because `β_source ≠ β_target`
even when the covariance side of the model is unchanged. -/
theorem target_effect_heterogeneity_changes_generation_path_without_ld_or_af_change :
    sigmaTagTargetAt timeVaryingEffectGenerationalModel 0 =
      sigmaTagTargetAt timeVaryingEffectGenerationalModel 1 ∧
    sigmaTagCausalTargetAt timeVaryingEffectGenerationalModel 0 =
      sigmaTagCausalTargetAt timeVaryingEffectGenerationalModel 1 ∧
    targetSourceEffectProjectionAt timeVaryingEffectGenerationalModel 0 0 = 1 ∧
    targetSourceEffectProjectionAt timeVaryingEffectGenerationalModel 1 0 = 1 ∧
    targetEffectHeterogeneityProjectionAt timeVaryingEffectGenerationalModel 0 0 = 0 ∧
    targetEffectHeterogeneityProjectionAt timeVaryingEffectGenerationalModel 1 0 = -(1 / 2) ∧
    betaTargetAt timeVaryingEffectGenerationalModel 0 0 = 1 ∧
    betaTargetAt timeVaryingEffectGenerationalModel 1 0 = 1 / 2 ∧
    targetR2AtGeneration timeVaryingEffectGenerationalModel 0 = 1 / 2 ∧
    targetR2AtGeneration timeVaryingEffectGenerationalModel 1 = 1 / 8 := by
  repeat' constructor
  · ext i j
    fin_cases i
    fin_cases j
    simp [baselineGenerationalPopGen, timeVaryingEffectGenerationalModel,
      sigmaTagTargetAt, tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt,
      alleleFreqMismatchPenalty,
      GenerationalPopGenParameters.theta,
      GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt,
      GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay]
  · ext i j
    fin_cases i
    fin_cases j
    simp [baselineGenerationalPopGen, timeVaryingEffectGenerationalModel,
      sigmaTagCausalTargetAt, directCausalTargetAt, proxyTaggingTargetAt,
      tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      GenerationalPopGenParameters.theta,
      GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt,
      GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay]
  · simp [targetSourceEffectProjectionAt, sigmaTagCausalTargetAt,
      directCausalTargetAt, proxyTaggingTargetAt, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel, tagAlleleFreqRetentionAt,
      causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      GenerationalPopGenParameters.theta,
      GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt,
      GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay, Matrix.mulVec, dotProduct, Matrix.cons_val',
      Matrix.cons_val_fin_one]
  · simp [targetSourceEffectProjectionAt, sigmaTagCausalTargetAt,
      directCausalTargetAt, proxyTaggingTargetAt, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel, tagAlleleFreqRetentionAt,
      causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      GenerationalPopGenParameters.theta,
      GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt,
      GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay, Matrix.mulVec, dotProduct, Matrix.cons_val',
      Matrix.cons_val_fin_one]
  · simp [targetEffectHeterogeneityProjectionAt, sigmaTagCausalTargetAt,
      directCausalTargetAt, proxyTaggingTargetAt, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel, tagAlleleFreqRetentionAt,
      causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      GenerationalPopGenParameters.theta,
      GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt,
      GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay, Matrix.mulVec, dotProduct, Matrix.cons_val',
      Matrix.cons_val_fin_one]
  · simp [targetEffectHeterogeneityProjectionAt, sigmaTagCausalTargetAt,
      directCausalTargetAt, proxyTaggingTargetAt, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel, tagAlleleFreqRetentionAt,
      causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      GenerationalPopGenParameters.theta,
      GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt,
      GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay, Matrix.mulVec, dotProduct, Matrix.cons_val',
      Matrix.cons_val_fin_one]
  · simp [betaTargetAt, baselineGenerationalPopGen, timeVaryingEffectGenerationalModel]
  · simp [betaTargetAt, baselineGenerationalPopGen, timeVaryingEffectGenerationalModel]
    norm_num
  · simp [baselineGenerationalPopGen, timeVaryingEffectGenerationalModel,
      betaTargetAt, targetR2AtGeneration,
      CrossPopulationGenerationalModel.toMetricModelAt,
      targetR2FromSourceWeights, targetExplainedSignalVarianceFromSourceWeights,
      targetPredictiveCovarianceFromSourceWeights, targetScoreVarianceFromSourceWeights,
      sigmaTagTargetAt, directCausalTargetAt, proxyTaggingTargetAt, sigmaTagCausalTargetAt,
      sigmaTagCausalSource, sigmaTagCausalTarget,
      sourceWeightsFromExplicitDrivers, sourceERMWeights,
      sourceCrossCovariance, targetCrossCovariance,
      effectiveTargetOutcomeVariance, irreducibleTargetResidualBurden,
      brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
      tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      GenerationalPopGenParameters.theta,
      GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt,
      GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay,
      Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  · simp [baselineGenerationalPopGen, timeVaryingEffectGenerationalModel,
      betaTargetAt, targetR2AtGeneration,
      CrossPopulationGenerationalModel.toMetricModelAt,
      targetR2FromSourceWeights, targetExplainedSignalVarianceFromSourceWeights,
      targetPredictiveCovarianceFromSourceWeights, targetScoreVarianceFromSourceWeights,
      sigmaTagTargetAt, directCausalTargetAt, proxyTaggingTargetAt, sigmaTagCausalTargetAt,
      sigmaTagCausalSource, sigmaTagCausalTarget,
      sourceWeightsFromExplicitDrivers, sourceERMWeights,
      sourceCrossCovariance, targetCrossCovariance,
      effectiveTargetOutcomeVariance, irreducibleTargetResidualBurden,
      brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
      tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      GenerationalPopGenParameters.theta,
      GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt,
      GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay,
      Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
    norm_num

/-- The generation-indexed deployed profile reads its `R²` coordinate from the
same explicit time-sliced source-weights-on-target-state model. -/
theorem target_metric_profile_at_generation_reads_explicit_target_r2
    (t : ℕ) :
    (targetMetricProfileAtGeneration timeVaryingAFGenerationalModel t).r2 =
      targetR2AtGeneration timeVaryingAFGenerationalModel t := by
  simp [targetR2AtGeneration]

end GenerationalMechanisticValidation

/-- **Within-group variance dominates between-group variance.**
    The R² of genetic distance on individual squared error is bounded
    by the ratio of between-group to total variance. When within-group
    variance exceeds between-group by a factor k, R² < 1/(k+1) < 1/k. -/
theorem individual_error_r2_bounded
    (var_between var_within r2 k : ℝ)
    (h_vb : 0 ≤ var_between) (h_vw : 0 < var_within)
    (h_k : 0 < k)
    (h_r2 : r2 = var_between / (var_between + var_within))
    (h_small : var_between < var_within / k) :
    r2 < 1 / k := by
  rw [h_r2]
  rw [div_lt_div_iff₀ (by linarith) h_k]
  have hbk : var_between * k < var_within := by
    rwa [lt_div_iff₀ h_k] at h_small
  linarith

end Calibrator
