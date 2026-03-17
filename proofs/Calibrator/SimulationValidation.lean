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

/-- Total additive source squared-effect mass in a direct-causal witness. -/
noncomputable def sourceSquaredEffectMass {q : ℕ}
    (β : Fin q → ℝ) : ℝ :=
  ∑ i, β i ^ 2

/-- Generic `q`-locus direct-causal witness with identical source and target
states and no proxy, context, or novel-variant channels. This is the
multi-locus replacement for the old `1×1` baseline sanity check. -/
noncomputable def identityDirectMetricModel {q : ℕ}
    (β : Fin q → ℝ)
    (outcomeVariance targetPrevalence : ℝ)
    (h_out : 0 < outcomeVariance)
    (h_prev_pos : 0 < targetPrevalence)
    (h_prev_lt : targetPrevalence < 1) :
    CrossPopulationMetricModel q q where
  betaSource := β
  betaTarget := β
  sigmaTagSource := 1
  sigmaTagTarget := 1
  directCausalSource := 1
  directCausalTarget := 1
  novelDirectCausalTarget := 0
  proxyTaggingSource := 0
  proxyTaggingTarget := 0
  novelProxyTaggingTarget := 0
  novelCausalEffectTarget := 0
  contextCrossSource := 0
  contextCrossTarget := 0
  sourceOutcomeVariance := outcomeVariance
  targetOutcomeVariance := outcomeVariance
  novelUntaggablePhenotypeVarianceTarget := 0
  targetPrevalence := targetPrevalence
  sourceOutcomeVariance_pos := h_out
  targetOutcomeVariance_pos := h_out
  novelUntaggablePhenotypeVarianceTarget_nonneg := by simp
  targetPrevalence_pos := h_prev_pos
  targetPrevalence_lt_one := h_prev_lt

/-- In the generic identity/direct-causal witness, the mechanistic source and
target `R²` are exactly the squared-effect mass divided by outcome variance,
and portability is identically one. -/
theorem identityDirectMetricModel_source_weights {q : ℕ}
    (β : Fin q → ℝ)
    (outcomeVariance targetPrevalence : ℝ)
    (h_out : 0 < outcomeVariance)
    (h_prev_pos : 0 < targetPrevalence)
    (h_prev_lt : targetPrevalence < 1) :
    sourceWeightsFromExplicitDrivers
        (identityDirectMetricModel β outcomeVariance targetPrevalence
          h_out h_prev_pos h_prev_lt) = β := by
  ext i
  simp [identityDirectMetricModel, sourceWeightsFromExplicitDrivers, sourceERMWeights,
    sourceCrossCovariance, sigmaTagCausalSource, Matrix.one_mulVec]

theorem identityDirectMetricModel_metrics {q : ℕ}
    (β : Fin q → ℝ)
    (outcomeVariance targetPrevalence : ℝ)
    (h_out : 0 < outcomeVariance)
    (h_prev_pos : 0 < targetPrevalence)
    (h_prev_lt : targetPrevalence < 1)
    (h_mass : 0 < sourceSquaredEffectMass β) :
    sourceR2FromSourceWeights
        (identityDirectMetricModel β outcomeVariance targetPrevalence
          h_out h_prev_pos h_prev_lt) =
      sourceSquaredEffectMass β / outcomeVariance ∧
    targetR2FromSourceWeights
        (identityDirectMetricModel β outcomeVariance targetPrevalence
          h_out h_prev_pos h_prev_lt) =
      sourceSquaredEffectMass β / outcomeVariance ∧
    mechanisticPortabilityRatio
        (identityDirectMetricModel β outcomeVariance targetPrevalence
          h_out h_prev_pos h_prev_lt) = 1 := by
  let m :=
    identityDirectMetricModel β outcomeVariance targetPrevalence
      h_out h_prev_pos h_prev_lt
  have h_weights : sourceWeightsFromExplicitDrivers m = β := by
    simpa [m] using
      identityDirectMetricModel_source_weights β outcomeVariance targetPrevalence
        h_out h_prev_pos h_prev_lt
  have h_source_cross : sourceCrossCovariance m = β := by
    ext i
    simp [m, identityDirectMetricModel, sourceCrossCovariance, sigmaTagCausalSource,
      Matrix.one_mulVec]
  have h_target_cross : targetCrossCovariance m = β := by
    ext i
    simp [m, identityDirectMetricModel, targetCrossCovariance, sigmaTagCausalTarget,
      targetTotalEffect, Matrix.one_mulVec]
  have h_source_score : sourceScoreVarianceFromExplicitDrivers m = sourceSquaredEffectMass β := by
    rw [sourceScoreVarianceFromExplicitDrivers_eq_score_on_source_covariance_action]
    unfold sourceWeightedTagScore
    rw [h_weights]
    change dotProduct β (m.sigmaTagSource.mulVec β) = sourceSquaredEffectMass β
    simpa [m, identityDirectMetricModel, sourceSquaredEffectMass, Matrix.one_mulVec,
      dotProduct, pow_two]
  have h_source_cov : sourcePredictiveCovarianceFromSourceWeights m = sourceSquaredEffectMass β := by
    rw [sourcePredictiveCovarianceFromSourceWeights_eq_score_on_source_crossCov]
    unfold sourceWeightedTagScore
    rw [h_weights, h_source_cross]
    simpa [sourceSquaredEffectMass, dotProduct, pow_two]
  have h_source_signal : sourceExplainedSignalVarianceFromSourceWeights m = sourceSquaredEffectMass β := by
    unfold sourceExplainedSignalVarianceFromSourceWeights
    rw [h_source_cov, h_source_score]
    field_simp [ne_of_gt h_mass]
  have h_source :
      sourceR2FromSourceWeights m = sourceSquaredEffectMass β / outcomeVariance := by
    rw [sourceR2FromSourceWeights, h_source_signal]
    simp [m, identityDirectMetricModel]
  have h_target_score : targetScoreVarianceFromSourceWeights m = sourceSquaredEffectMass β := by
    rw [targetScoreVarianceFromSourceWeights_eq_score_on_target_covariance_action]
    unfold sourceWeightedTagScore
    rw [h_weights]
    change dotProduct β (m.sigmaTagTarget.mulVec β) = sourceSquaredEffectMass β
    simpa [m, identityDirectMetricModel, sourceSquaredEffectMass, Matrix.one_mulVec,
      dotProduct, pow_two]
  have h_target_cov : targetPredictiveCovarianceFromSourceWeights m = sourceSquaredEffectMass β := by
    rw [targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov]
    unfold sourceWeightedTagScore
    rw [h_weights, h_target_cross]
    simpa [sourceSquaredEffectMass, dotProduct, pow_two]
  have h_target_signal : targetExplainedSignalVarianceFromSourceWeights m = sourceSquaredEffectMass β := by
    unfold targetExplainedSignalVarianceFromSourceWeights
    rw [h_target_cov, h_target_score]
    field_simp [ne_of_gt h_mass]
  have h_eff : effectiveTargetOutcomeVariance m = outcomeVariance := by
    simp [m, identityDirectMetricModel, effectiveTargetOutcomeVariance,
      irreducibleTargetResidualBurden, brokenTaggingResidual, ancestrySpecificLDResidual,
      sourceSpecificOverfitResidual, novelUntaggablePhenotypeResidual, dotProduct]
  have h_target :
      targetR2FromSourceWeights m = sourceSquaredEffectMass β / outcomeVariance := by
    rw [targetR2FromSourceWeights, h_target_signal, h_eff]
  refine ⟨h_source, h_target, ?_⟩
  rw [mechanisticPortabilityRatio, h_source, h_target]
  have h_mass_ne : sourceSquaredEffectMass β ≠ 0 := ne_of_gt h_mass
  have h_ratio_ne : sourceSquaredEffectMass β / outcomeVariance ≠ 0 := by
    exact div_ne_zero h_mass_ne (ne_of_gt h_out)
  field_simp [h_ratio_ne]

/-- Baseline single-locus mechanistic witness with identical source and target
state where the scored SNP is itself the causal variant. -/
noncomputable def baselineMetricModel : CrossPopulationMetricModel 1 1 := {
  betaSource := ![1]
  betaTarget := ![1]
  sigmaTagSource := !![1]
  sigmaTagTarget := !![1]
  directCausalSource := !![1]
  directCausalTarget := !![1]
  novelDirectCausalTarget := !![0]
  proxyTaggingSource := !![0]
  proxyTaggingTarget := !![0]
  novelProxyTaggingTarget := !![0]
  novelCausalEffectTarget := ![0]
  contextCrossSource := ![0]
  contextCrossTarget := ![0]
  sourceOutcomeVariance := 2
  targetOutcomeVariance := 2
  novelUntaggablePhenotypeVarianceTarget := 0
  targetPrevalence := 1 / 2
  sourceOutcomeVariance_pos := by norm_num
  targetOutcomeVariance_pos := by norm_num
  novelUntaggablePhenotypeVarianceTarget_nonneg := by norm_num
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

/-- Novel target-only proxy-tagging witness: source fit is unchanged, but
target portability changes because new post-split tagging links appear. -/
noncomputable def novelTargetOnlyTaggingMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineProxyTagMetricModel with
      proxyTaggingTarget := !![0]
      novelProxyTaggingTarget := !![1 / 2] }

/-- Target-only novel untaggable phenotype variance witness: transported score
moments are unchanged, but target `R²` drops because new target-only causal
variance enters the phenotype and is not captured by the score. -/
noncomputable def novelUntaggablePhenotypeMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      novelUntaggablePhenotypeVarianceTarget := 1 / 2
      novelUntaggablePhenotypeVarianceTarget_nonneg := by norm_num }

/-- The baseline witness has exact source and target metrics that can be read
off from the explicit state. -/
theorem baseline_mechanistic_metrics :
    brokenTaggingResidual baselineMetricModel = 0 ∧
    ancestrySpecificLDResidual baselineMetricModel = 0 ∧
    sourceSpecificOverfitResidual baselineMetricModel = 0 ∧
    novelUntaggablePhenotypeResidual baselineMetricModel = 0 ∧
    sourceR2FromSourceWeights baselineMetricModel = 1 / 2 ∧
    targetR2FromSourceWeights baselineMetricModel = 1 / 2 ∧
    mechanisticPortabilityRatio baselineMetricModel = 1 ∧
    targetCalibratedBrierFromSourceWeights baselineMetricModel = 1 / 8 := by
  simp [baselineMetricModel, mechanisticPortabilityRatio,
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    novelUntaggablePhenotypeResidual,
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
    TransportedMetrics.calibratedBrier, TransportedMetrics.r2FromSignalVariance,
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
    TransportedMetrics.calibratedBrier, TransportedMetrics.r2FromSignalVariance,
    Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- New target-only tagging created after divergence can change target `R²`
without changing source fit, because the target tagging surface has genuinely
new support rather than being only an attenuation of the source proxy surface. -/
theorem novel_target_only_tagging_changes_target_r2 :
    sourceR2FromSourceWeights novelTargetOnlyTaggingMetricModel =
      sourceR2FromSourceWeights baselineProxyTagMetricModel ∧
    targetR2FromSourceWeights novelTargetOnlyTaggingMetricModel = 1 / 9 ∧
    targetR2FromSourceWeights baselineProxyTagMetricModel = 1 / 2 := by
  simp [baselineMetricModel, baselineProxyTagMetricModel, novelTargetOnlyTaggingMetricModel,
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
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    novelUntaggablePhenotypeResidual, irreducibleTargetResidualBurden,
    effectiveTargetOutcomeVariance, Matrix.mulVec, dotProduct,
    Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- Novel target-only causal variance that is not tagged by the transported
score lowers target `R²` by increasing the target outcome variance directly. -/
theorem novel_untaggable_phenotype_variance_lowers_target_r2 :
    targetPredictiveCovarianceFromSourceWeights novelUntaggablePhenotypeMetricModel =
      targetPredictiveCovarianceFromSourceWeights baselineMetricModel ∧
    novelUntaggablePhenotypeResidual novelUntaggablePhenotypeMetricModel = 1 / 2 ∧
    targetR2FromSourceWeights novelUntaggablePhenotypeMetricModel = 2 / 5 ∧
    targetR2FromSourceWeights baselineMetricModel = 1 / 2 := by
  simp [baselineMetricModel, novelUntaggablePhenotypeMetricModel,
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
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    novelUntaggablePhenotypeResidual, irreducibleTargetResidualBurden,
    effectiveTargetOutcomeVariance, Matrix.mulVec, dotProduct,
    Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- The liability-threshold AUC coordinate in the mechanistic metric profile is
built directly from target explained signal variance and target residual
variance; no source-`R²` transport summary appears in the definition. -/
theorem target_metric_profile_auc_uses_explicit_target_moments {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).auc =
      liabilityAUCFromVariances
        (targetExplainedSignalVarianceFromSourceWeights m)
        (targetResidualVarianceFromSourceWeights m) := by
  simp [targetMetricProfileFromSourceWeights, targetLiabilityAUCFromSourceWeights]

/-- The standalone liability-threshold AUC accessor agrees with the canonical
target metric profile built from the explicit source-weights-on-target-state
equation. -/
theorem target_liability_auc_uses_explicit_target_moments {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetLiabilityAUCFromSourceWeights m =
      liabilityAUCFromVariances
        (targetExplainedSignalVarianceFromSourceWeights m)
        (targetResidualVarianceFromSourceWeights m) := by
  simpa using target_metric_profile_auc_uses_explicit_target_moments m

/-- The mechanistic target AUC agrees with the `R²` chart induced by the same
explicit target explained-signal and total-variance decomposition. This is a
derived chart identity, not the definition of transported AUC. -/
theorem target_liability_auc_eq_explainedR2_chart {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetLiabilityAUCFromSourceWeights m =
      liabilityAUCFromExplainedR2 (targetR2FromSourceWeights m) := by
  simpa using targetLiabilityAUCFromSourceWeights_eq_explainedR2_chart m

/-- When target LD among scored SNPs changes, the deployed liability-threshold
AUC changes because the explicit target score moments, and therefore the
derived deployed `R²`, change under the mechanistic state. -/
theorem target_ld_shift_changes_liability_auc
    (hPhiStrict : StrictMono Phi) :
    targetLiabilityAUCFromSourceWeights targetLDShiftMetricModel <
      targetLiabilityAUCFromSourceWeights baselineMetricModel := by
  rcases target_ld_shift_changes_portability_without_changing_source_r2 with
    ⟨_, _, h_target_shift, h_target_base, _⟩
  rw [target_liability_auc_eq_explainedR2_chart,
    target_liability_auc_eq_explainedR2_chart,
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

/-- Nondegenerate generation-indexed population-genetic parameters with
positive mutation, migration, and recombination. This witness is used to show
that the public generational portability API changes because of explicit
population-genetic coordinates, not only because of hand-injected AF/effect
paths. -/
noncomputable def nondegenerateGenerationalPopGen : GenerationalPopGenParameters := {
  Ne := 1
  μ := 1 / 2
  mig := 1 / 8
  recomb := 1 / 4
  V_A := 1
  Ne_pos := by norm_num
  μ_nonneg := by norm_num
  mig_nonneg := by norm_num
  recomb_nonneg := by norm_num
  recomb_le_half := by norm_num
  V_A_pos := by norm_num
}

/-- Exact generation-1 popgen coordinates for the nondegenerate witness. -/
theorem nondegenerateGenerationalPopGen_coordinates_at_one :
    nondegenerateGenerationalPopGen.theta = 2 ∧
    nondegenerateGenerationalPopGen.bigM = 1 / 2 ∧
    nondegenerateGenerationalPopGen.tauAt 1 = 1 / 2 ∧
    nondegenerateGenerationalPopGen.fstTransientAt 1 = 2 / 7 ∧
    nondegenerateGenerationalPopGen.mutationSharedRetentionAt 1 = Real.exp (-(1 : ℝ)) ∧
    nondegenerateGenerationalPopGen.migrationSharedBoostAt 1 = 7 / 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [nondegenerateGenerationalPopGen, GenerationalPopGenParameters.theta]
  · norm_num [nondegenerateGenerationalPopGen, GenerationalPopGenParameters.bigM]
  · simp [nondegenerateGenerationalPopGen, GenerationalPopGenParameters.tauAt]
  · simp [nondegenerateGenerationalPopGen, GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.theta, GenerationalPopGenParameters.bigM]
    norm_num
  · simp [nondegenerateGenerationalPopGen,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.theta, GenerationalPopGenParameters.tauAt]
    ring_nf
  · simp [nondegenerateGenerationalPopGen,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      GenerationalPopGenParameters.bigM, GenerationalPopGenParameters.tauAt]
    norm_num

/-- Shared diagonal tag-LD scale at generation `1` in the nondegenerate
two-tag proxy witness. -/
noncomputable def popgenDrivenTagScale : ℝ :=
  (7 / 6 : ℝ) * Real.exp (-(1 : ℝ))

/-- Shared proxy-tagging scale at generation `1` in the nondegenerate two-tag
proxy witness. The additional `exp (-1/14)` factor comes from explicit
recombination-driven LD decay across one tag-causal unit of distance. -/
noncomputable def popgenDrivenProxyScale : ℝ :=
  (7 / 6 : ℝ) * Real.exp (-(15 / 14 : ℝ))

/-- Two-tag one-causal-variant generational witness with constant allele
frequencies and constant effects. Any transport change after generation `0`
comes from the explicit population-genetic kernels: transient `F_ST`,
recombination, mutation retention, and migration boost. -/
noncomputable def popgenDrivenProxyGenerationalModel :
    CrossPopulationGenerationalModel 2 1 := {
  popGen := nondegenerateGenerationalPopGen
  betaSource := ![1]
  targetEffectHeterogeneityAt := fun _ => ![0]
  novelCausalEffectTargetAt := fun _ => ![0]
  sigmaTagSource := 1
  directCausalSource := !![0; 0]
  novelDirectCausalTemplate := !![0; 0]
  proxyTaggingSource := !![1; 1]
  novelProxyTaggingTemplate := !![0; 0]
  tagDistance := !![0, 1; 1, 0]
  tagCausalDistance := !![1; 1]
  tagAlleleFreqSource := ![1 / 2, 1 / 2]
  tagAlleleFreqStandingTargetAt := fun _ => ![1 / 2, 1 / 2]
  tagAlleleFreqMutationShiftAt := fun _ => ![0, 0]
  causalAlleleFreqSource := ![1 / 2]
  causalAlleleFreqStandingTargetAt := fun _ => ![1 / 2]
  causalAlleleFreqMutationShiftAt := fun _ => ![0]
  contextCrossSource := ![0, 0]
  contextCrossTargetAt := fun _ => ![0, 0]
  sourceOutcomeVariance := 4
  targetOutcomeVarianceAt := fun _ => 4
  novelUntaggablePhenotypeVarianceAt := fun _ => 0
  targetPrevalenceAt := fun _ => 1 / 2
  sourceOutcomeVariance_pos := by norm_num
  targetOutcomeVariance_pos := by intro t; norm_num
  novelUntaggablePhenotypeVariance_nonneg := by intro t; norm_num
  targetPrevalence_pos := by intro t; norm_num
  targetPrevalence_lt_one := by intro t; norm_num
}

/-- The source weights in the nondegenerate two-tag proxy witness are the
source proxy covariances themselves, because the source scored-SNP covariance
is the identity. -/
theorem popgenDrivenProxyGenerationalModel_source_weights (t : ℕ) :
    sourceWeightsFromExplicitDrivers
        (CrossPopulationGenerationalModel.toMetricModelAt
          popgenDrivenProxyGenerationalModel t) = ![1, 1] := by
  ext i
  fin_cases i <;>
    simp [popgenDrivenProxyGenerationalModel,
      CrossPopulationGenerationalModel.toMetricModelAt,
      sourceWeightsFromExplicitDrivers, sourceERMWeights,
      sourceCrossCovariance, sigmaTagCausalSource,
      Matrix.one_mulVec, Matrix.mulVec, dotProduct,
      Matrix.cons_val', Matrix.cons_val_fin_one]

/-- At generation `0`, the nondegenerate proxy witness still matches its source
state exactly, so the target deployed `R²` equals the source-side value `1/2`. -/
theorem popgenDrivenProxyGenerationalModel_target_r2_at_zero :
    targetR2AtGeneration popgenDrivenProxyGenerationalModel 0 = 1 / 2 := by
  simp [targetR2AtGeneration, popgenDrivenProxyGenerationalModel,
    CrossPopulationGenerationalModel.toMetricModelAt,
    sigmaTagTargetAt, directCausalTargetAt, proxyTaggingTargetAt, sigmaTagCausalTargetAt,
    tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
    targetR2FromSourceWeights, targetExplainedSignalVarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights, targetScoreVarianceFromSourceWeights,
    sigmaTagCausalSource, sigmaTagCausalTarget,
    sourceWeightsFromExplicitDrivers, sourceERMWeights, sourceCrossCovariance,
    targetCrossCovariance, effectiveTargetOutcomeVariance, irreducibleTargetResidualBurden,
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    novelUntaggablePhenotypeResidual,
    GenerationalPopGenParameters.theta, GenerationalPopGenParameters.bigM,
    GenerationalPopGenParameters.tauAt, GenerationalPopGenParameters.hetDecayFactor,
    GenerationalPopGenParameters.fstTransientAt,
    GenerationalPopGenParameters.mutationSharedRetentionAt,
    GenerationalPopGenParameters.migrationSharedBoostAt,
    ldCorrelationDecay, Matrix.one_mulVec, Matrix.mulVec, dotProduct,
    Matrix.cons_val', Matrix.cons_val_fin_one]
  norm_num

/-- The nondegenerate multi-locus proxy witness yields exact generation-1
kernel scales on the public mechanistic surface. Mutation and migration change
both LD and tagging, while recombination enters the proxy channel through the
explicit tag-causal distance. -/
theorem popgenDrivenProxyGenerationalModel_generation_one_scales :
    sigmaTagTargetAt popgenDrivenProxyGenerationalModel 1 0 0 =
      popgenDrivenTagScale ∧
    sigmaTagTargetAt popgenDrivenProxyGenerationalModel 1 1 1 =
      popgenDrivenTagScale ∧
    proxyTaggingTargetAt popgenDrivenProxyGenerationalModel 1 0 0 =
      popgenDrivenProxyScale ∧
    proxyTaggingTargetAt popgenDrivenProxyGenerationalModel 1 1 0 =
      popgenDrivenProxyScale := by
  rcases nondegenerateGenerationalPopGen_coordinates_at_one with
    ⟨h_theta, h_bigM, h_tau, h_fst, h_mut, h_mig⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [popgenDrivenProxyGenerationalModel, popgenDrivenTagScale,
      sigmaTagTargetAt, jointTagLDKernelAt, tagAlleleFreqRetentionAt,
      tagAlleleFreqTargetAt, alleleFreqMismatchPenalty, nondegenerateGenerationalPopGen,
      GenerationalPopGenParameters.theta, GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt, GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay, h_theta, h_bigM, h_tau, h_fst, h_mut, h_mig]
    ring_nf
  · simp [popgenDrivenProxyGenerationalModel, popgenDrivenTagScale,
      sigmaTagTargetAt, jointTagLDKernelAt, tagAlleleFreqRetentionAt,
      tagAlleleFreqTargetAt, alleleFreqMismatchPenalty, nondegenerateGenerationalPopGen,
      GenerationalPopGenParameters.theta, GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt, GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay, h_theta, h_bigM, h_tau, h_fst, h_mut, h_mig]
    ring_nf
  · calc
      proxyTaggingTargetAt popgenDrivenProxyGenerationalModel 1 0 0
          = (7 / 6 : ℝ) * (Real.exp (-(1 : ℝ)) * Real.exp (-(1 / 14 : ℝ))) := by
              simp [popgenDrivenProxyGenerationalModel,
                proxyTaggingTargetAt, jointProxyTaggingKernelAt,
                tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt,
                tagAlleleFreqTargetAt, causalAlleleFreqTargetAt, alleleFreqMismatchPenalty,
                nondegenerateGenerationalPopGen,
                GenerationalPopGenParameters.theta, GenerationalPopGenParameters.bigM,
                GenerationalPopGenParameters.tauAt, GenerationalPopGenParameters.hetDecayFactor,
                GenerationalPopGenParameters.fstTransientAt,
                GenerationalPopGenParameters.mutationSharedRetentionAt,
                GenerationalPopGenParameters.migrationSharedBoostAt,
                ldCorrelationDecay, h_fst, h_mut, h_mig]
              ring_nf
      _ = (7 / 6 : ℝ) * Real.exp (-(15 / 14 : ℝ)) := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            norm_num
      _ = popgenDrivenProxyScale := by rfl
  · calc
      proxyTaggingTargetAt popgenDrivenProxyGenerationalModel 1 1 0
          = (7 / 6 : ℝ) * (Real.exp (-(1 : ℝ)) * Real.exp (-(1 / 14 : ℝ))) := by
              simp [popgenDrivenProxyGenerationalModel,
                proxyTaggingTargetAt, jointProxyTaggingKernelAt,
                tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt,
                tagAlleleFreqTargetAt, causalAlleleFreqTargetAt, alleleFreqMismatchPenalty,
                nondegenerateGenerationalPopGen,
                GenerationalPopGenParameters.theta, GenerationalPopGenParameters.bigM,
                GenerationalPopGenParameters.tauAt, GenerationalPopGenParameters.hetDecayFactor,
                GenerationalPopGenParameters.fstTransientAt,
                GenerationalPopGenParameters.mutationSharedRetentionAt,
                GenerationalPopGenParameters.migrationSharedBoostAt,
                ldCorrelationDecay, h_fst, h_mut, h_mig]
              ring_nf
      _ = (7 / 6 : ℝ) * Real.exp (-(15 / 14 : ℝ)) := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            norm_num
      _ = popgenDrivenProxyScale := by rfl

/-- In the nondegenerate proxy witness, generation-1 transport degrades target
`R²` even though target allele frequencies and target effects are held fixed.
The loss is caused by the explicit mutation/migration/recombination transport
kernels, not by hand-injected AF or effect shifts. -/
theorem popgenDrivenProxyGenerationalModel_target_r2_strictly_decreases_at_one :
    targetR2AtGeneration popgenDrivenProxyGenerationalModel 1 <
      targetR2AtGeneration popgenDrivenProxyGenerationalModel 0 := by
  let m1 :=
    CrossPopulationGenerationalModel.toMetricModelAt popgenDrivenProxyGenerationalModel 1
  have h_weights :
      sourceWeightsFromExplicitDrivers m1 = ![1, 1] := by
    simpa [m1] using popgenDrivenProxyGenerationalModel_source_weights 1
  have h_cov :
      targetPredictiveCovarianceFromSourceWeights m1 = 2 * popgenDrivenProxyScale := by
    rcases popgenDrivenProxyGenerationalModel_generation_one_scales with
      ⟨_, _, h_proxy0, h_proxy1⟩
    have h_cross :
        targetCrossCovariance m1 = ![popgenDrivenProxyScale, popgenDrivenProxyScale] := by
      ext i
      fin_cases i
      · simpa [m1, popgenDrivenProxyGenerationalModel,
          CrossPopulationGenerationalModel.toMetricModelAt,
          targetCrossCovariance, sigmaTagCausalTarget, directCausalTargetAt,
          novelDirectCausalTargetAt, proxyTaggingTargetAt, novelProxyTaggingTargetAt,
          targetTotalEffect, Matrix.mulVec, Matrix.cons_val', Matrix.cons_val_fin_one]
          using h_proxy0
      · simpa [m1, popgenDrivenProxyGenerationalModel,
          CrossPopulationGenerationalModel.toMetricModelAt,
          targetCrossCovariance, sigmaTagCausalTarget, directCausalTargetAt,
          novelDirectCausalTargetAt, proxyTaggingTargetAt, novelProxyTaggingTargetAt,
          targetTotalEffect, Matrix.mulVec, Matrix.cons_val', Matrix.cons_val_fin_one]
          using h_proxy1
    rw [targetPredictiveCovarianceFromSourceWeights]
    rw [h_weights, h_cross]
    simp [dotProduct]
    ring
  have h_var :
      targetScoreVarianceFromSourceWeights m1 = 2 * popgenDrivenTagScale := by
    rcases popgenDrivenProxyGenerationalModel_generation_one_scales with
      ⟨h_ld0, h_ld1, _, _⟩
    have h_sigma :
        m1.sigmaTagTarget = !![popgenDrivenTagScale, 0; 0, popgenDrivenTagScale] := by
      ext i j
      fin_cases i <;> fin_cases j
      · simpa [m1, popgenDrivenProxyGenerationalModel,
          CrossPopulationGenerationalModel.toMetricModelAt,
          sigmaTagTargetAt, Matrix.cons_val', Matrix.cons_val_fin_one]
          using h_ld0
      · simp [m1, popgenDrivenProxyGenerationalModel,
          CrossPopulationGenerationalModel.toMetricModelAt,
          sigmaTagTargetAt, Matrix.cons_val', Matrix.cons_val_fin_one]
      · simp [m1, popgenDrivenProxyGenerationalModel,
          CrossPopulationGenerationalModel.toMetricModelAt,
          sigmaTagTargetAt, Matrix.cons_val', Matrix.cons_val_fin_one]
      · simpa [m1, popgenDrivenProxyGenerationalModel,
          CrossPopulationGenerationalModel.toMetricModelAt,
          sigmaTagTargetAt, Matrix.cons_val', Matrix.cons_val_fin_one]
          using h_ld1
    rw [targetScoreVarianceFromSourceWeights]
    rw [h_weights, h_sigma]
    simp [Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
    ring
  have h_eff_ge :
      4 ≤ effectiveTargetOutcomeVariance m1 := by
    have := effectiveTargetOutcomeVariance_ge_targetOutcomeVariance m1
    change 4 ≤ effectiveTargetOutcomeVariance m1
    have h_target_var : m1.targetOutcomeVariance = 4 := by
      simp [m1, popgenDrivenProxyGenerationalModel,
        CrossPopulationGenerationalModel.toMetricModelAt]
    simpa [h_target_var] using this
  have h_tag_pos : 0 < popgenDrivenTagScale := by
    unfold popgenDrivenTagScale
    positivity
  have h_proxy_nonneg : 0 ≤ popgenDrivenProxyScale := by
    unfold popgenDrivenProxyScale
    positivity
  have h_ld_gap_lt_one : Real.exp (-(1 / 14 : ℝ)) < 1 := by
    have hneg : (-(1 / 14 : ℝ)) < 0 := by norm_num
    simpa using Real.exp_lt_one_iff.mpr hneg
  have h_proxy_lt_tag : popgenDrivenProxyScale < popgenDrivenTagScale := by
    unfold popgenDrivenProxyScale popgenDrivenTagScale
    calc
      (7 / 6 : ℝ) * Real.exp (-(15 / 14 : ℝ))
          = ((7 / 6 : ℝ) * Real.exp (-(1 : ℝ))) * Real.exp (-(1 / 14 : ℝ)) := by
              rw [show (-(15 / 14 : ℝ)) = (-(1 : ℝ)) + (-(1 / 14 : ℝ)) by norm_num,
                Real.exp_add]
              ring
      _ < ((7 / 6 : ℝ) * Real.exp (-(1 : ℝ))) * 1 := by
              exact mul_lt_mul_of_pos_left h_ld_gap_lt_one (by positivity)
      _ = popgenDrivenTagScale := by simp [popgenDrivenTagScale]
  have h_exp_one_ge_two : (2 : ℝ) ≤ Real.exp (1 : ℝ) := by
    have h := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  have h_exp_neg_one_le_half : Real.exp (-(1 : ℝ)) ≤ (1 / 2 : ℝ) := by
    have h_mul :
        (2 : ℝ) * Real.exp (-(1 : ℝ)) ≤ 1 := by
      have h_mul' := mul_le_mul_of_nonneg_right h_exp_one_ge_two (by positivity : 0 ≤ Real.exp (-(1 : ℝ)))
      have h_cancel : Real.exp (1 : ℝ) * Real.exp (-(1 : ℝ)) = 1 := by
        rw [← Real.exp_add]
        norm_num
      exact le_trans h_mul' (by simpa [h_cancel])
    nlinarith
  have h_proxy_lt_one : popgenDrivenProxyScale < 1 := by
    unfold popgenDrivenProxyScale
    calc
      (7 / 6 : ℝ) * Real.exp (-(15 / 14 : ℝ))
          = ((7 / 6 : ℝ) * Real.exp (-(1 : ℝ))) * Real.exp (-(1 / 14 : ℝ)) := by
              rw [show (-(15 / 14 : ℝ)) = (-(1 : ℝ)) + (-(1 / 14 : ℝ)) by norm_num,
                Real.exp_add]
              ring
      _ ≤ ((7 / 6 : ℝ) * (1 / 2 : ℝ)) * 1 := by
              have h_exp_nonneg : 0 ≤ Real.exp (-(1 / 14 : ℝ)) := by positivity
              nlinarith [h_exp_neg_one_le_half, le_of_lt h_ld_gap_lt_one, h_exp_nonneg]
      _ < (1 : ℝ) := by norm_num
  have h_proxy_sq_lt_tag : popgenDrivenProxyScale ^ 2 < popgenDrivenTagScale := by
    have h_proxy_sq_lt_proxy : popgenDrivenProxyScale ^ 2 < popgenDrivenProxyScale := by
      have h_proxy_pos : 0 < popgenDrivenProxyScale := by
        unfold popgenDrivenProxyScale
        positivity
      have h_mul_lt := mul_lt_mul_of_pos_left h_proxy_lt_one h_proxy_pos
      simpa [pow_two] using h_mul_lt
    exact lt_trans h_proxy_sq_lt_proxy h_proxy_lt_tag
  have h_signal_lt_two :
      targetExplainedSignalVarianceFromSourceWeights m1 < 2 := by
    rw [targetExplainedSignalVarianceFromSourceWeights, h_cov, h_var]
    have h_tag_ne : popgenDrivenTagScale ≠ 0 := ne_of_gt h_tag_pos
    have h_ratio_lt_one : popgenDrivenProxyScale ^ 2 / popgenDrivenTagScale < 1 := by
      have h_mul_form : popgenDrivenProxyScale ^ 2 < 1 * popgenDrivenTagScale := by
        simpa using h_proxy_sq_lt_tag
      exact (div_lt_iff₀ h_tag_pos).2 h_mul_form
    have h_eq :
        (2 * popgenDrivenProxyScale) ^ 2 / (2 * popgenDrivenTagScale) =
          2 * (popgenDrivenProxyScale ^ 2 / popgenDrivenTagScale) := by
      field_simp [h_tag_ne]
    rw [h_eq]
    nlinarith
  have h_r2_lt_half :
      targetR2AtGeneration popgenDrivenProxyGenerationalModel 1 < 1 / 2 := by
    rw [targetR2AtGeneration_eq_targetR2From_slice]
    rw [targetR2FromSourceWeights_eq_signalVariance_ratio]
    have h_eff_half_ge_two : 2 ≤ effectiveTargetOutcomeVariance m1 / 2 := by
      nlinarith
    have h_signal_lt_half_eff :
        targetExplainedSignalVarianceFromSourceWeights m1 <
          effectiveTargetOutcomeVariance m1 / 2 := by
      exact lt_of_lt_of_le h_signal_lt_two h_eff_half_ge_two
    have h_eff_pos : 0 < effectiveTargetOutcomeVariance m1 := effectiveTargetOutcomeVariance_pos m1
    rw [div_lt_iff₀ h_eff_pos]
    nlinarith
  rw [popgenDrivenProxyGenerationalModel_target_r2_at_zero]
  exact h_r2_lt_half

/-- Single-locus generational witness where the target allele frequency drifts
away from the source after generation `0`, lowering tagging quality and target
`R²` even though the learned source score is unchanged. -/
noncomputable def timeVaryingAFGenerationalModel :
    CrossPopulationGenerationalModel 1 1 := {
  popGen := baselineGenerationalPopGen
  betaSource := ![1]
  targetEffectHeterogeneityAt := fun _ => ![0]
  novelCausalEffectTargetAt := fun _ => ![0]
  sigmaTagSource := !![1]
  directCausalSource := !![0]
  novelDirectCausalTemplate := !![0]
  proxyTaggingSource := !![1]
  novelProxyTaggingTemplate := !![0]
  tagDistance := !![1]
  tagCausalDistance := !![1]
  tagAlleleFreqSource := ![1 / 2]
  tagAlleleFreqStandingTargetAt := fun _ => ![1 / 2]
  tagAlleleFreqMutationShiftAt := fun t => ![if t = 0 then (0 : ℝ) else 1 / 4]
  causalAlleleFreqSource := ![1 / 2]
  causalAlleleFreqStandingTargetAt := fun _ => ![1 / 2]
  causalAlleleFreqMutationShiftAt := fun t => ![if t = 0 then (0 : ℝ) else 1 / 4]
  contextCrossSource := ![0]
  contextCrossTargetAt := fun _ => ![0]
  sourceOutcomeVariance := 2
  targetOutcomeVarianceAt := fun _ => 2
  novelUntaggablePhenotypeVarianceAt := fun _ => 0
  targetPrevalenceAt := fun _ => 1 / 2
  sourceOutcomeVariance_pos := by norm_num
  targetOutcomeVariance_pos := by intro t; norm_num
  novelUntaggablePhenotypeVariance_nonneg := by intro t; norm_num
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
  novelCausalEffectTargetAt := fun _ => ![0]
  sigmaTagSource := !![1]
  directCausalSource := !![1]
  novelDirectCausalTemplate := !![0]
  proxyTaggingSource := !![0]
  novelProxyTaggingTemplate := !![0]
  tagDistance := !![1]
  tagCausalDistance := !![1]
  tagAlleleFreqSource := ![1 / 2]
  tagAlleleFreqStandingTargetAt := fun _ => ![1 / 2]
  tagAlleleFreqMutationShiftAt := fun _ => ![0]
  causalAlleleFreqSource := ![1 / 2]
  causalAlleleFreqStandingTargetAt := fun _ => ![1 / 2]
  causalAlleleFreqMutationShiftAt := fun _ => ![0]
  contextCrossSource := ![0]
  contextCrossTargetAt := fun _ => ![0]
  sourceOutcomeVariance := 2
  targetOutcomeVarianceAt := fun _ => 2
  novelUntaggablePhenotypeVarianceAt := fun _ => 0
  targetPrevalenceAt := fun _ => 1 / 2
  sourceOutcomeVariance_pos := by norm_num
  targetOutcomeVariance_pos := by intro t; norm_num
  novelUntaggablePhenotypeVariance_nonneg := by intro t; norm_num
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
          Real.exp (-(1 / 4 : ℝ)) *
            Real.exp (-(1 / 4 : ℝ)) := by
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
          Real.exp (-(1 / 4 : ℝ)) *
            Real.exp (-(1 / 4 : ℝ)) := by
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
    have h_ret :
        Real.exp (-(1 / 4 : ℝ)) *
            Real.exp (-(1 / 4 : ℝ)) =
          Real.exp (-(1 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      norm_num
    have h_ret_norm :
        Real.exp (-((4 : ℝ)⁻¹)) * Real.exp (-((4 : ℝ)⁻¹)) =
          Real.exp (-(1 / 2 : ℝ)) := by
      simpa using h_ret
    have h_eff :
        effectiveTargetOutcomeVariance
            (timeVaryingAFGenerationalModel.toMetricModelAt 1) =
          2 + 2 * (1 - Real.exp (-(1 / 2 : ℝ))) ^ 2 := by
      simp [baselineGenerationalPopGen, timeVaryingAFGenerationalModel,
        CrossPopulationGenerationalModel.toMetricModelAt,
        sigmaTagTargetAt, directCausalTargetAt, proxyTaggingTargetAt, sigmaTagCausalTargetAt,
        tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
        effectiveTargetOutcomeVariance, irreducibleTargetResidualBurden,
        brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
        novelUntaggablePhenotypeResidual,
        sigmaTagCausalSource, sigmaTagCausalTarget,
        sourceTaggingProjection, targetTaggingProjection,
        sourceDirectCausalProjection, sourceProxyTaggingProjection,
        targetDirectCausalProjection, targetProxyTaggingProjection,
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
      rw [h_ret_norm]
      ring
    have h_exp_ne : Real.exp (-(1 / 2 : ℝ)) ≠ 0 := by
      exact Real.exp_ne_zero _
    rw [targetR2AtGeneration_eq_targetR2From_slice]
    unfold targetR2FromSourceWeights targetExplainedSignalVarianceFromSourceWeights
    rw [h_cov, h_var, h_eff]
    have hcalc :
        Real.exp (-(1 / 2 : ℝ)) ^ 2 /
            Real.exp (-(1 / 2 : ℝ)) /
              (2 + 2 * (1 - Real.exp (-(1 / 2 : ℝ))) ^ 2) =
          Real.exp (-(1 / 2 : ℝ)) /
            (2 + 2 * (1 - Real.exp (-(1 / 2 : ℝ))) ^ 2) := by
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

/-- The generation-indexed deployed profile always reads its `R²` coordinate
from the same explicit time-sliced source-weights-on-target-state model. This
is a generic bridge theorem for the full mechanistic generational API, not an
accidental theorem about an implicit witness. -/
theorem target_metric_profile_at_generation_reads_explicit_target_r2
    {p q : ℕ} (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    (targetMetricProfileAtGeneration m t).r2 =
      targetR2AtGeneration m t := by
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
