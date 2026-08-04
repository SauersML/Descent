/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.PortabilityDrift

namespace Calibrator

open Matrix
open scoped Matrix

/-- **Evaluate a generational witness on the transport kernels.**

Everything a generational witness has to unfold from `Calibrator.PortabilityDrift` -- the
target kernels, the allele-frequency retentions, the source-weight chain, the residual
decomposition and the popgen parameter projections -- is the same at every witness, and it
was written out at each of them: a dozen copies of twenty-odd lines, so a lemma added to
one chain left the others unfolding a different one.

The witness passes its own models and hypotheses, because a macro resolves the names in its
quotation where it is DECLARED and the witnesses are defined below this point. -/
macro "generational_witness_simp" ms:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| simp [$ms,*, CrossPopulationGenerationalModel.toMetricModelAt,
      sigmaTagTargetAt, directCausalTargetAt, proxyTaggingTargetAt, sigmaTagCausalTargetAt,
      tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      tagAlleleFreqTargetAt, causalAlleleFreqTargetAt, jointTagLDKernelAt,
      jointProxyTaggingKernelAt, betaTargetAt,
      targetSourceEffectProjectionAt, targetEffectHeterogeneityProjectionAt,
      r2FromSourceWeights, explainedSignalVarianceFromSourceWeights,
      predictiveCovarianceFromSourceWeights, scoreVarianceFromSourceWeights,
      sigmaTagCausal, sourceWeightsFromExplicitDrivers, sourceERMWeights, crossCovariance,
      effectiveOutcomeVariance, irreducibleTargetResidualBurden,
      brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
      novelUntaggablePhenotypeResidual,
      taggingProjection, directCausalProjection, proxyTaggingProjection,
      GenerationalPopGenParameters.theta, GenerationalPopGenParameters.bigM,
      GenerationalPopGenParameters.tauAt, GenerationalPopGenParameters.hetDecayFactor,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      ldCorrelationDecay, Matrix.one_mulVec, Matrix.mulVec, dotProduct,
      Matrix.cons_val', Matrix.cons_val_fin_one])

/-!
# Simulation Theory and Mechanistic Validation of Portability Models

This file records only simulation-validation objects that remain honest under
the explicit SNP/LD-aware portability surface in `PortabilityDrift`.

No source-`R²` attenuation law is assumed. Target metrics are evaluated
directly from explicit source/target biological state:

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
  r2FromSourceWeights m Pop.target / r2FromSourceWeights m Pop.source

/-- Total additive source squared-effect mass in a direct-causal witness.

    Empirical status: UNTESTED. -/
noncomputable def sourceSquaredEffectMass {q : ℕ}
    (β : Fin q → ℝ) : ℝ :=
  ∑ i, β i ^ 2

/-- Generic `q`-locus direct-causal witness with identical source and target
states and no proxy, context, or novel-variant channels. Serves as the
multi-locus baseline sanity check. -/
noncomputable def identityDirectMetricModel {q : ℕ}
    (β : Fin q → ℝ)
    (outcomeVariance targetPrevalence : ℝ)
    (h_out : 0 < outcomeVariance)
    (h_prev_pos : 0 < targetPrevalence)
    (h_prev_lt : targetPrevalence < 1) :
    CrossPopulationMetricModel q q where
  beta := Pop.pair (β) (β)
  sigmaTag := Pop.pair 1 1
  directCausal := Pop.pair 1 1
  proxyTagging := Pop.pair 0 0
  contextCross := Pop.pair 0 0
  outcomeVariance := Pop.pair outcomeVariance outcomeVariance
  novelDirectCausal := Pop.pair 0 0
  novelProxyTagging := Pop.pair 0 0
  novelCausalEffect := Pop.pair 0 0
  novelUntaggablePhenotypeVarianceTarget := 0
  targetPrevalence := targetPrevalence
  novelUntaggablePhenotypeVarianceTarget_nonneg := by simp
  targetPrevalence_pos := h_prev_pos
  targetPrevalence_lt_one := h_prev_lt
  novelDirectCausal_source := rfl
  novelProxyTagging_source := rfl
  novelCausalEffect_source := rfl
  outcomeVariance_pos := by intro P; cases P <;> simp_all <;> norm_num

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
    crossCovariance, sigmaTagCausal, Matrix.one_mulVec]

theorem identityDirectMetricModel_metrics {q : ℕ}
    (β : Fin q → ℝ)
    (outcomeVariance targetPrevalence : ℝ)
    (h_out : 0 < outcomeVariance)
    (h_prev_pos : 0 < targetPrevalence)
    (h_prev_lt : targetPrevalence < 1)
    (h_mass : 0 < sourceSquaredEffectMass β) :
    r2FromSourceWeights
        (identityDirectMetricModel β outcomeVariance targetPrevalence
          h_out h_prev_pos h_prev_lt) Pop.source =
      sourceSquaredEffectMass β / outcomeVariance ∧
    r2FromSourceWeights
        (identityDirectMetricModel β outcomeVariance targetPrevalence
          h_out h_prev_pos h_prev_lt) Pop.target =
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
  have h_source_cross : crossCovariance m Pop.source = β := by
    ext i
    simp [m, identityDirectMetricModel, crossCovariance, sigmaTagCausal,
      Matrix.one_mulVec]
  have h_target_cross : crossCovariance m Pop.target = β := by
    ext i
    simp [m, identityDirectMetricModel, crossCovariance, sigmaTagCausal,
      totalEffect, Matrix.one_mulVec]
  have h_source_score :
      scoreVarianceFromSourceWeights m Pop.source = sourceSquaredEffectMass β := by
    rw [scoreVarianceFromSourceWeights_source_eq_score_on_covariance_action]
    unfold sourceWeightedTagScore
    rw [h_weights]
    change dotProduct β ((m.sigmaTag Pop.source).mulVec β) = sourceSquaredEffectMass β
    simpa [m, identityDirectMetricModel, sourceSquaredEffectMass, Matrix.one_mulVec,
      dotProduct, pow_two]
  have h_source_cov :
      predictiveCovarianceFromSourceWeights m Pop.source = sourceSquaredEffectMass β := by
    rw [sourcePredictiveCovarianceFromSourceWeights_eq_score_on_source_crossCov]
    unfold sourceWeightedTagScore
    rw [h_weights, h_source_cross]
    simpa [sourceSquaredEffectMass, dotProduct, pow_two]
  have h_source_signal :
      explainedSignalVarianceFromSourceWeights m Pop.source = sourceSquaredEffectMass β := by
    unfold explainedSignalVarianceFromSourceWeights
    rw [h_source_cov, h_source_score]
    field_simp [ne_of_gt h_mass]
  have h_source :
      r2FromSourceWeights m Pop.source = sourceSquaredEffectMass β / outcomeVariance := by
    rw [r2FromSourceWeights, h_source_signal]
    simp [m, identityDirectMetricModel]
  have h_target_score :
      scoreVarianceFromSourceWeights m Pop.target = sourceSquaredEffectMass β := by
    rw [targetScoreVarianceFromSourceWeights_eq_score_on_target_covariance_action]
    unfold sourceWeightedTagScore
    rw [h_weights]
    change dotProduct β ((m.sigmaTag Pop.target).mulVec β) = sourceSquaredEffectMass β
    simpa [m, identityDirectMetricModel, sourceSquaredEffectMass, Matrix.one_mulVec,
      dotProduct, pow_two]
  have h_target_cov :
      predictiveCovarianceFromSourceWeights m Pop.target = sourceSquaredEffectMass β := by
    rw [targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov]
    unfold sourceWeightedTagScore
    rw [h_weights, h_target_cross]
    simpa [sourceSquaredEffectMass, dotProduct, pow_two]
  have h_target_signal :
      explainedSignalVarianceFromSourceWeights m Pop.target = sourceSquaredEffectMass β := by
    unfold explainedSignalVarianceFromSourceWeights
    rw [h_target_cov, h_target_score]
    field_simp [ne_of_gt h_mass]
  have h_eff : effectiveOutcomeVariance m Pop.target = outcomeVariance := by
    simp [m, identityDirectMetricModel, effectiveOutcomeVariance,
      irreducibleTargetResidualBurden, brokenTaggingResidual, ancestrySpecificLDResidual,
      sourceSpecificOverfitResidual, novelUntaggablePhenotypeResidual, dotProduct]
  have h_target :
      r2FromSourceWeights m Pop.target = sourceSquaredEffectMass β / outcomeVariance := by
    rw [r2FromSourceWeights, h_target_signal, h_eff]
  refine ⟨h_source, h_target, ?_⟩
  rw [mechanisticPortabilityRatio, h_source, h_target]
  have h_mass_ne : sourceSquaredEffectMass β ≠ 0 := ne_of_gt h_mass
  have h_ratio_ne : sourceSquaredEffectMass β / outcomeVariance ≠ 0 := by
    exact div_ne_zero h_mass_ne (ne_of_gt h_out)
  field_simp [h_ratio_ne]

/-- Baseline single-locus mechanistic witness with identical source and target
state where the scored SNP is itself the causal variant. -/
noncomputable def baselineMetricModel : CrossPopulationMetricModel 1 1 := {
  beta := Pop.pair ![1] ![1]
  sigmaTag := Pop.pair !![1] !![1]
  directCausal := Pop.pair !![1] !![1]
  proxyTagging := Pop.pair !![0] !![0]
  novelDirectCausal := Pop.pair 0 !![0]
  novelProxyTagging := Pop.pair 0 !![0]
  novelCausalEffect := Pop.pair 0 ![0]
  contextCross := Pop.pair ![0] ![0]
  outcomeVariance := Pop.pair 2 2
  novelUntaggablePhenotypeVarianceTarget := 0
  targetPrevalence := 1 / 2
  novelDirectCausal_source := rfl
  novelProxyTagging_source := rfl
  novelCausalEffect_source := rfl
  outcomeVariance_pos := by intro P; cases P <;> norm_num
  novelUntaggablePhenotypeVarianceTarget_nonneg := by norm_num
  targetPrevalence_pos := by norm_num
  targetPrevalence_lt_one := by norm_num
}

/-- Target-LD-shift witness: only the target LD among scored SNPs changes.

    Empirical status: UNTESTED. -/
noncomputable def targetLDShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      sigmaTag := Pop.withTarget baselineMetricModel.sigmaTag !![2] }

/-- Proxy-tag baseline witness: the scored SNP is not itself causal, but is a
perfect source and target proxy for the unscored causal variant. -/
noncomputable def baselineProxyTagMetricModel : CrossPopulationMetricModel 1 1 := {
  baselineMetricModel with
    directCausal := Pop.pair !![0] !![0]
    proxyTagging := Pop.pair !![1] !![1] }

/-- Target tagging-shift witness: only the target proxy-tagging alignment
changes. -/
noncomputable def targetTaggingShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineProxyTagMetricModel with
      proxyTagging := Pop.withTarget baselineProxyTagMetricModel.proxyTagging !![1 / 2] }

/-- Target effect-shift witness: only the target causal effect size changes.

    Empirical status: UNTESTED. -/
noncomputable def targetEffectShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      beta := Pop.withTarget baselineMetricModel.beta ![1 / 2] }

/-- Target context-shift witness: only the target context/environment
cross-covariance changes. -/
noncomputable def targetContextShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      contextCross := Pop.withTarget baselineMetricModel.contextCross ![-(1 / 2)] }

/-- Irreducible target mismatch witness.

    Empirical status: UNTESTED. -/
noncomputable def targetPrevalenceShiftMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      targetPrevalence := 1 / 4
      targetPrevalence_pos := by norm_num
      targetPrevalence_lt_one := by norm_num }

/-- Novel target-only proxy-tagging witness: source fit is unchanged, but
target portability changes because new post-split tagging links appear. -/
noncomputable def novelTargetOnlyTaggingMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineProxyTagMetricModel with
      proxyTagging := Pop.withTarget baselineProxyTagMetricModel.proxyTagging !![0]
      novelProxyTagging := Pop.withTarget baselineProxyTagMetricModel.novelProxyTagging !![1 / 2] }

/-- Target-only novel untaggable phenotype variance witness: transported score
moments are unchanged, but target `R²` drops because new target-only causal
variance enters the phenotype and is not captured by the score. -/
noncomputable def novelUntaggablePhenotypeMetricModel : CrossPopulationMetricModel 1 1 :=
  { baselineMetricModel with
      novelUntaggablePhenotypeVarianceTarget := 1 / 2
      novelUntaggablePhenotypeVarianceTarget_nonneg := by norm_num }

/-- **Evaluate a witness model's metrics from its explicit state.**

Every witness theorem below reduces the same way: unfold the model, the residual
decomposition, the source-weight chain and the Brier chart, then finish with `norm_num`.
That list was written out once per theorem -- nine copies of twenty lines, differing only
in which model names led the list, so a lemma added to one chain silently left the others
evaluating a different one.  The list is the tactic; the witnesses just invoke it. -/
macro "metric_witness_simp" : tactic =>
  `(tactic| simp [baselineMetricModel, baselineProxyTagMetricModel,
      targetTaggingShiftMetricModel, targetLDShiftMetricModel, targetEffectShiftMetricModel,
      targetContextShiftMetricModel, targetPrevalenceShiftMetricModel,
      novelTargetOnlyTaggingMetricModel, novelUntaggablePhenotypeMetricModel,
      mechanisticPortabilityRatio,
      brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
      novelUntaggablePhenotypeResidual, irreducibleTargetResidualBurden,
      r2FromSourceWeights,
      explainedSignalVarianceFromSourceWeights,
      predictiveCovarianceFromSourceWeights,
      scoreVarianceFromSourceWeights,
      sigmaTagCausal,
      taggingProjection, directCausalProjection, proxyTaggingProjection,
      sourceWeightsFromExplicitDrivers, sourceERMWeights,
      crossCovariance,
      effectiveOutcomeVariance,
      targetCalibratedBrierFromSourceWeights,
      TransportedMetrics.calibratedBrier, TransportedMetrics.r2FromSignalVariance,
      Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one])

/-- The baseline witness has exact source and target metrics that can be read
off from the explicit state. -/
theorem baseline_mechanistic_metrics :
    brokenTaggingResidual baselineMetricModel = 0 ∧
    ancestrySpecificLDResidual baselineMetricModel = 0 ∧
    sourceSpecificOverfitResidual baselineMetricModel = 0 ∧
    novelUntaggablePhenotypeResidual baselineMetricModel = 0 ∧
    r2FromSourceWeights baselineMetricModel Pop.source = 1 / 2 ∧
    r2FromSourceWeights baselineMetricModel Pop.target = 1 / 2 ∧
    mechanisticPortabilityRatio baselineMetricModel = 1 ∧
    targetCalibratedBrierFromSourceWeights baselineMetricModel = 1 / 8 := by
  metric_witness_simp
  norm_num

/-- A score built on the directly causal SNP and a score built on a perfect
proxy tag can have the same source `R²`, but once proxy tagging degrades in the
target population the tag-based score loses portability while the direct-causal
score does not. This is the explicit direct-vs-tag witness missing from the old
abstraction. -/
theorem direct_causal_vs_proxy_tag_same_source_r2_different_portability :
    directCausalProjection baselineMetricModel Pop.source 0 = 1 ∧
    proxyTaggingProjection baselineMetricModel Pop.source 0 = 0 ∧
    directCausalProjection baselineProxyTagMetricModel Pop.source 0 = 0 ∧
    proxyTaggingProjection baselineProxyTagMetricModel Pop.source 0 = 1 ∧
    r2FromSourceWeights baselineMetricModel Pop.source =
      r2FromSourceWeights baselineProxyTagMetricModel Pop.source ∧
    r2FromSourceWeights targetTaggingShiftMetricModel Pop.target <
      r2FromSourceWeights baselineMetricModel Pop.target := by
  metric_witness_simp
  norm_num

/-- Target LD among scored SNPs changes target `R²` and portability even when
the source state, and therefore the source `R²`, are unchanged. -/
theorem target_ld_shift_changes_portability_without_changing_source_r2 :
    ancestrySpecificLDResidual targetLDShiftMetricModel = 1 ∧
    r2FromSourceWeights targetLDShiftMetricModel Pop.source =
      r2FromSourceWeights baselineMetricModel Pop.source ∧
    r2FromSourceWeights targetLDShiftMetricModel Pop.target = 1 / 6 ∧
    r2FromSourceWeights baselineMetricModel Pop.target = 1 / 2 ∧
    mechanisticPortabilityRatio targetLDShiftMetricModel = 1 / 3 := by
  metric_witness_simp
  norm_num

/-- Target proxy-tagging alignment changes target `R²` directly, even with the
same proxy-tag source score and the same source deployed `R²`. -/
theorem target_tagging_shift_changes_target_r2 :
    brokenTaggingResidual targetTaggingShiftMetricModel = 1 / 4 ∧
    r2FromSourceWeights targetTaggingShiftMetricModel Pop.source =
      r2FromSourceWeights baselineProxyTagMetricModel Pop.source ∧
    r2FromSourceWeights targetTaggingShiftMetricModel Pop.target = 1 / 9 ∧
    mechanisticPortabilityRatio targetTaggingShiftMetricModel = 2 / 9 := by
  metric_witness_simp
  norm_num

/-- Target effect-size shifts change target `R²` directly, even with unchanged
source score construction. -/
theorem target_effect_shift_changes_target_r2 :
    r2FromSourceWeights targetEffectShiftMetricModel Pop.source =
      r2FromSourceWeights baselineMetricModel Pop.source ∧
    irreducibleTargetResidualBurden targetEffectShiftMetricModel = 0 ∧
    r2FromSourceWeights targetEffectShiftMetricModel Pop.target = 1 / 8 ∧
    mechanisticPortabilityRatio targetEffectShiftMetricModel = 1 / 4 := by
  metric_witness_simp
  norm_num

/-- Source-only context structure that does not transport creates an additive
source-specific overfit residual on the target side and lowers target `R²`. -/
theorem target_context_shift_creates_additive_overfit_loss_and_changes_target_r2 :
    sourceSpecificOverfitResidual targetContextShiftMetricModel = 1 / 4 ∧
    r2FromSourceWeights targetContextShiftMetricModel Pop.source =
      r2FromSourceWeights baselineMetricModel Pop.source ∧
    r2FromSourceWeights targetContextShiftMetricModel Pop.target = 1 / 9 ∧
    mechanisticPortabilityRatio targetContextShiftMetricModel = 2 / 9 := by
  metric_witness_simp
  norm_num

/-- Target prevalence changes the calibrated Brier score even when the score
moments and target `R²` are unchanged. -/
theorem target_prevalence_shift_changes_brier_without_changing_target_r2 :
    r2FromSourceWeights targetPrevalenceShiftMetricModel Pop.target =
      r2FromSourceWeights baselineMetricModel Pop.target ∧
    targetCalibratedBrierFromSourceWeights targetPrevalenceShiftMetricModel = 3 / 32 ∧
    targetCalibratedBrierFromSourceWeights baselineMetricModel = 1 / 8 := by
  metric_witness_simp
  norm_num

/-- New target-only tagging created after divergence can change target `R²`
without changing source fit, because the target tagging surface has genuinely
new support rather than being only an attenuation of the source proxy surface. -/
theorem novel_target_only_tagging_changes_target_r2 :
    r2FromSourceWeights novelTargetOnlyTaggingMetricModel Pop.source =
      r2FromSourceWeights baselineProxyTagMetricModel Pop.source ∧
    r2FromSourceWeights novelTargetOnlyTaggingMetricModel Pop.target = 1 / 9 ∧
    r2FromSourceWeights baselineProxyTagMetricModel Pop.target = 1 / 2 := by
  metric_witness_simp
  norm_num

/-- Novel target-only causal variance that is not tagged by the transported
score lowers target `R²` by increasing the target outcome variance directly. -/
theorem novel_untaggable_phenotype_variance_lowers_target_r2 :
    predictiveCovarianceFromSourceWeights novelUntaggablePhenotypeMetricModel Pop.target =
      predictiveCovarianceFromSourceWeights baselineMetricModel Pop.target ∧
    novelUntaggablePhenotypeResidual novelUntaggablePhenotypeMetricModel = 1 / 2 ∧
    r2FromSourceWeights novelUntaggablePhenotypeMetricModel Pop.target = 2 / 5 ∧
    r2FromSourceWeights baselineMetricModel Pop.target = 1 / 2 := by
  metric_witness_simp
  norm_num

/-- The liability-threshold AUC coordinate in the mechanistic metric profile is
built directly from target explained signal variance and target residual
variance; no source-`R²` transport summary appears in the definition. -/
theorem target_metric_profile_auc_uses_explicit_target_moments {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).auc =
      TransportedMetrics.equalVarianceGaussianAUCFromSignalVariance
        (explainedSignalVarianceFromSourceWeights m Pop.target)
        (residualVarianceFromSourceWeights m Pop.target) := by
  simp [targetMetricProfileFromSourceWeights, equalVarianceGaussianAUCFromSourceWeights]

/-- The mechanistic target AUC agrees with the `R²` chart induced by the same
explicit target explained-signal and total-variance decomposition. This is a
derived chart identity, not the definition of transported AUC. -/
theorem target_liability_auc_eq_explainedR2_chart {p q : ℕ}
    (m : CrossPopulationMetricModel p q)
    (h_r2 : r2FromSourceWeights m Pop.target < 1) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.target =
      equalVarianceGaussianAUCFromExplainedR2 (r2FromSourceWeights m Pop.target) := by
  simpa using targetEqualVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_lt_one m h_r2

/-- When target LD among scored SNPs changes, the deployed liability-threshold
AUC changes because the explicit target score moments, and therefore the
derived deployed `R²`, change under the mechanistic state. -/
theorem target_ld_shift_changes_liability_auc :
    equalVarianceGaussianAUCFromSourceWeights targetLDShiftMetricModel Pop.target <
      equalVarianceGaussianAUCFromSourceWeights baselineMetricModel Pop.target := by
  rcases target_ld_shift_changes_portability_without_changing_source_r2 with
    ⟨_, _, h_target_shift, h_target_base, _⟩
  rw [target_liability_auc_eq_explainedR2_chart _ (by simpa [h_target_shift] using
      (show (1 / 6 : ℝ) < 1 by norm_num)),
    target_liability_auc_eq_explainedR2_chart _ (by simpa [h_target_base] using
      (show (1 / 2 : ℝ) < 1 by norm_num)),
    h_target_shift, h_target_base]
  exact equalVarianceGaussianAUCFromExplainedR2_strictMonoOn_unitInterval
    ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩
    (by norm_num)

end MechanisticValidation

section GenerationalMechanisticValidation

-- These primitive population-genetic rates are deliberately kept transparent in
-- the concrete witnesses below.  Registering them locally prevents exact
-- generation checks from getting stuck at an otherwise opaque `4 * Nₑ * rate`.
attribute [local simp] scaledMutationRate scaledMigrationRate hetDecayFromScaled
  novelDirectCausalTargetAt novelProxyTaggingTargetAt

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
  targetEffectHeterogeneityAt := fun _ ↦ ![0]
  novelCausalEffectTargetAt := fun _ ↦ ![0]
  sigmaTagSource := 1
  directCausalSource := !![0; 0]
  novelDirectCausalTemplate := !![0; 0]
  proxyTaggingSource := !![1; 1]
  novelProxyTaggingTemplate := !![0; 0]
  tagDistance := !![0, 1; 1, 0]
  tagCausalDistance := !![1; 1]
  tagAlleleFreqSource := ![1 / 2, 1 / 2]
  tagAlleleFreqStandingTargetAt := fun _ ↦ ![1 / 2, 1 / 2]
  tagAlleleFreqMutationShiftAt := fun _ ↦ ![0, 0]
  causalAlleleFreqSource := ![1 / 2]
  causalAlleleFreqStandingTargetAt := fun _ ↦ ![1 / 2]
  causalAlleleFreqMutationShiftAt := fun _ ↦ ![0]
  contextCrossSource := ![0, 0]
  contextCrossTargetAt := fun _ ↦ ![0, 0]
  sourceOutcomeVariance := 4
  targetOutcomeVarianceAt := fun _ ↦ 4
  novelUntaggablePhenotypeVarianceAt := fun _ ↦ 0
  targetPrevalenceAt := fun _ ↦ 1 / 2
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
      crossCovariance, sigmaTagCausal,
      Matrix.one_mulVec, Matrix.mulVec, dotProduct,
      Matrix.cons_val', Matrix.cons_val_fin_one]

/-- At generation `0`, the nondegenerate proxy witness still matches its source
state exactly, so the target deployed `R²` equals the source-side value `1/2`. -/
theorem popgenDrivenProxyGenerationalModel_target_r2_at_zero :
    r2FromSourceWeights
      (popgenDrivenProxyGenerationalModel.toMetricModelAt 0) Pop.target = 1 / 2 := by
  -- The generational witness needs the transport kernels as well as the metric chain, so
  -- it does not go through `metric_witness_simp`.
  generational_witness_simp popgenDrivenProxyGenerationalModel
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
  -- Both tags carry the same proxy scale at generation one, and the calculation that shows
  -- it does not depend on which: it was written out once per tag, `calc` step for `calc`
  -- step. Proved for an arbitrary tag, the last two goals are two instances of it.
  have proxy_scale_at :
      ∀ i : Fin 2, proxyTaggingTargetAt popgenDrivenProxyGenerationalModel 1 i 0 =
        popgenDrivenProxyScale := by
    intro i
    calc
      proxyTaggingTargetAt popgenDrivenProxyGenerationalModel 1 i 0
          = (7 / 6 : ℝ) * (Real.exp (-(1 : ℝ)) * Real.exp (-(1 / 14 : ℝ))) := by
              fin_cases i <;>
                generational_witness_simp nondegenerateGenerationalPopGen,
                  popgenDrivenProxyGenerationalModel, h_fst, h_mut, h_mig <;>
                ring_nf
      _ = (7 / 6 : ℝ) * Real.exp (-(15 / 14 : ℝ)) := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            norm_num
      _ = popgenDrivenProxyScale := by rfl
  refine ⟨?_, ?_, proxy_scale_at 0, proxy_scale_at 1⟩
  · generational_witness_simp popgenDrivenProxyGenerationalModel, popgenDrivenTagScale,
      nondegenerateGenerationalPopGen, h_theta, h_bigM, h_tau, h_fst, h_mut, h_mig
    ring_nf
  · generational_witness_simp popgenDrivenProxyGenerationalModel, popgenDrivenTagScale,
      nondegenerateGenerationalPopGen, h_theta, h_bigM, h_tau, h_fst, h_mut, h_mig
    ring_nf

/-- In the nondegenerate proxy witness, generation-1 transport degrades target
`R²` even though target allele frequencies and target effects are held fixed.
The loss is caused by the explicit mutation/migration/recombination transport
kernels, not by hand-injected AF or effect shifts. -/
theorem popgenDrivenProxyGenerationalModel_target_r2_strictly_decreases_at_one :
    r2FromSourceWeights (popgenDrivenProxyGenerationalModel.toMetricModelAt 1) Pop.target <
      r2FromSourceWeights (popgenDrivenProxyGenerationalModel.toMetricModelAt 0) Pop.target := by
  let m1 :=
    CrossPopulationGenerationalModel.toMetricModelAt popgenDrivenProxyGenerationalModel 1
  have h_weights :
      sourceWeightsFromExplicitDrivers m1 = ![1, 1] := by
    simpa [m1] using popgenDrivenProxyGenerationalModel_source_weights 1
  have h_cov :
      predictiveCovarianceFromSourceWeights m1 Pop.target = 2 * popgenDrivenProxyScale := by
    rcases popgenDrivenProxyGenerationalModel_generation_one_scales with
      ⟨_, _, h_proxy0, h_proxy1⟩
    have h_cross :
        crossCovariance m1 Pop.target = ![popgenDrivenProxyScale, popgenDrivenProxyScale] := by
      ext i
      fin_cases i
      · simpa [m1, popgenDrivenProxyGenerationalModel,
          CrossPopulationGenerationalModel.toMetricModelAt,
          crossCovariance, sigmaTagCausal, directCausalTargetAt,
          novelDirectCausalTargetAt, proxyTaggingTargetAt, novelProxyTaggingTargetAt,
          totalEffect, Matrix.mulVec, Matrix.cons_val', Matrix.cons_val_fin_one]
          using h_proxy0
      · simpa [m1, popgenDrivenProxyGenerationalModel,
          CrossPopulationGenerationalModel.toMetricModelAt,
          crossCovariance, sigmaTagCausal, directCausalTargetAt,
          novelDirectCausalTargetAt, proxyTaggingTargetAt, novelProxyTaggingTargetAt,
          totalEffect, Matrix.mulVec, Matrix.cons_val', Matrix.cons_val_fin_one]
          using h_proxy1
    rw [predictiveCovarianceFromSourceWeights]
    rw [h_weights, h_cross]
    simp [dotProduct]
    ring
  have h_var :
      scoreVarianceFromSourceWeights m1 Pop.target = 2 * popgenDrivenTagScale := by
    rcases popgenDrivenProxyGenerationalModel_generation_one_scales with
      ⟨h_ld0, h_ld1, _, _⟩
    have h_sigma :
        (m1.sigmaTag Pop.target) = !![popgenDrivenTagScale, 0; 0, popgenDrivenTagScale] := by
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
    rw [scoreVarianceFromSourceWeights]
    rw [h_weights, h_sigma]
    simp [Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
    ring
  have h_eff_ge :
      4 ≤ effectiveOutcomeVariance m1 Pop.target := by
    have := effectiveTargetOutcomeVariance_ge_targetOutcomeVariance m1
    change 4 ≤ effectiveOutcomeVariance m1 Pop.target
    have h_target_var : (m1.outcomeVariance Pop.target) = 4 := by
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
      have h_mul' := mul_le_mul_of_nonneg_right h_exp_one_ge_two
        (by positivity : 0 ≤ Real.exp (-(1 : ℝ)))
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
      explainedSignalVarianceFromSourceWeights m1 Pop.target < 2 := by
    rw [explainedSignalVarianceFromSourceWeights, h_cov, h_var]
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
      r2FromSourceWeights
        (popgenDrivenProxyGenerationalModel.toMetricModelAt 1) Pop.target < 1 / 2 := by
    rw [targetR2FromSourceWeights_eq_signalVariance_ratio]
    have h_eff_half_ge_two : 2 ≤ effectiveOutcomeVariance m1 Pop.target / 2 := by
      nlinarith
    have h_signal_lt_half_eff :
        explainedSignalVarianceFromSourceWeights m1 Pop.target <
          effectiveOutcomeVariance m1 Pop.target / 2 := by
      exact lt_of_lt_of_le h_signal_lt_two h_eff_half_ge_two
    have h_eff_pos : 0 < effectiveOutcomeVariance m1 Pop.target :=
      effectiveTargetOutcomeVariance_pos m1
    rw [div_lt_iff₀ h_eff_pos]
    nlinarith
  rw [popgenDrivenProxyGenerationalModel_target_r2_at_zero]
  exact h_r2_lt_half
/-- **The single-locus generational scaffold.**

The two single-locus witnesses below differ in five fields -- the effect heterogeneity, which
locus is scored directly rather than tagged, and the two allele-frequency mutation shifts --
and agreed in the other twenty, which they each wrote out.  A witness for one driver could
therefore differ from its neighbour in a field neither is about, and the closing block
(context, variances, prevalence and its four positivity proofs) was a third copy of what the
two-tag witness above already says.

Taken as a function of the five, the twenty are stated once and every witness theorem still
evaluates them: a function application unfolds by `simp`, which a structure update does not
-- that was tried first, and it left six goals open that the literals close. -/
noncomputable def singleLocusGenerationalWitness
    (targetEffectHeterogeneityAt : ℕ → Fin 1 → ℝ)
    (directCausalSource proxyTaggingSource : Matrix (Fin 1) (Fin 1) ℝ)
    (tagAlleleFreqMutationShiftAt causalAlleleFreqMutationShiftAt : ℕ → Fin 1 → ℝ) :
    CrossPopulationGenerationalModel 1 1 := {
  popGen := baselineGenerationalPopGen
  betaSource := ![1]
  targetEffectHeterogeneityAt := targetEffectHeterogeneityAt
  novelCausalEffectTargetAt := fun _ ↦ ![0]
  sigmaTagSource := !![1]
  directCausalSource := directCausalSource
  novelDirectCausalTemplate := !![0]
  proxyTaggingSource := proxyTaggingSource
  novelProxyTaggingTemplate := !![0]
  tagDistance := !![1]
  tagCausalDistance := !![1]
  tagAlleleFreqSource := ![1 / 2]
  tagAlleleFreqStandingTargetAt := fun _ ↦ ![1 / 2]
  tagAlleleFreqMutationShiftAt := tagAlleleFreqMutationShiftAt
  causalAlleleFreqSource := ![1 / 2]
  causalAlleleFreqStandingTargetAt := fun _ ↦ ![1 / 2]
  causalAlleleFreqMutationShiftAt := causalAlleleFreqMutationShiftAt
  contextCrossSource := ![0]
  contextCrossTargetAt := fun _ ↦ ![0]
  sourceOutcomeVariance := 2
  targetOutcomeVarianceAt := fun _ ↦ 2
  novelUntaggablePhenotypeVarianceAt := fun _ ↦ 0
  targetPrevalenceAt := fun _ ↦ 1 / 2
  sourceOutcomeVariance_pos := by norm_num
  targetOutcomeVariance_pos := by intro t; norm_num
  novelUntaggablePhenotypeVariance_nonneg := by intro t; norm_num
  targetPrevalence_pos := by intro t; norm_num
  targetPrevalence_lt_one := by intro t; norm_num
}

/-- Single-locus generational witness where the target allele frequency drifts
away from the source after generation `0`, lowering tagging quality and target
`R²` even though the learned source score is unchanged. -/
noncomputable def timeVaryingAFGenerationalModel :
    CrossPopulationGenerationalModel 1 1 :=
  singleLocusGenerationalWitness (fun _ ↦ ![0]) !![0] !![1]
    (fun t ↦ ![if t = 0 then (0 : ℝ) else 1 / 4])
    (fun t ↦ ![if t = 0 then (0 : ℝ) else 1 / 4])

/-- Single-locus generational witness where LD, tagging, and allele frequencies
stay fixed, but the target effect vector changes over time. This isolates
population/time-varying effect heterogeneity as the sole portability driver.

    Empirical status: UNTESTED. -/
noncomputable def timeVaryingEffectGenerationalModel :
    CrossPopulationGenerationalModel 1 1 :=
  singleLocusGenerationalWitness (fun t ↦ ![if t = 0 then (0 : ℝ) else -(1 / 2)]) !![1] !![0]
    (fun _ ↦ ![0]) (fun _ ↦ ![0])

/-- The generation-indexed target `R²` path reflects explicit allele-frequency
drift in the target population. At generation `0` the target matches the
source, while at generation `1` the target `R²` is reduced by the exact AF
mismatch penalty carried through the tagging surface. -/
theorem target_r2_changes_along_generation_indexed_af_path :
    r2FromSourceWeights (timeVaryingAFGenerationalModel.toMetricModelAt 0) Pop.target = 1 / 2 ∧
    r2FromSourceWeights (timeVaryingAFGenerationalModel.toMetricModelAt 1) Pop.target =
      Real.exp (-(1 / 2 : ℝ)) /
        (2 + 2 * (1 - Real.exp (-(1 / 2 : ℝ))) ^ 2) := by
  constructor
  · simp [singleLocusGenerationalWitness, baselineGenerationalPopGen, r2FromSourceWeights,
    timeVaryingAFGenerationalModel,
      CrossPopulationGenerationalModel.toMetricModelAt,
      sigmaTagTargetAt, directCausalTargetAt, proxyTaggingTargetAt, sigmaTagCausalTargetAt,
      tagAlleleFreqRetentionAt, causalAlleleFreqRetentionAt, alleleFreqMismatchPenalty,
      r2FromSourceWeights,
      explainedSignalVarianceFromSourceWeights,
      predictiveCovarianceFromSourceWeights,
      scoreVarianceFromSourceWeights,
      sigmaTagCausal,
      taggingProjection,
      directCausalProjection, proxyTaggingProjection,
      sourceWeightsFromExplicitDrivers, sourceERMWeights,
      crossCovariance,
      effectiveOutcomeVariance, irreducibleTargetResidualBurden,
      brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
      GenerationalPopGenParameters.fstTransientAt,
      GenerationalPopGenParameters.mutationSharedRetentionAt,
      GenerationalPopGenParameters.migrationSharedBoostAt,
      GenerationalPopGenParameters.bigM,
      ldCorrelationDecay,
      Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one]
  -- Both moments land on the same product of two quarter-retentions, and the step from
  -- that product to `exp(-1/2)` is one fact. It was carried inside both `calc` chains,
  -- and then a third time below; stated first, both moments are three lines.
  · have h_ret :
        Real.exp (-(1 / 4 : ℝ)) *
            Real.exp (-(1 / 4 : ℝ)) =
          Real.exp (-(1 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      norm_num
    have h_cov :
        predictiveCovarianceFromSourceWeights
            (timeVaryingAFGenerationalModel.toMetricModelAt 1) Pop.target =
          Real.exp (-(1 / 2 : ℝ)) := by
      have h_product :
          predictiveCovarianceFromSourceWeights
              (timeVaryingAFGenerationalModel.toMetricModelAt 1) Pop.target =
            Real.exp (-(1 / 4 : ℝ)) * Real.exp (-(1 / 4 : ℝ)) := by
        generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingAFGenerationalModel
      rw [h_product, h_ret]
    have h_var :
        scoreVarianceFromSourceWeights
            (timeVaryingAFGenerationalModel.toMetricModelAt 1) Pop.target =
          Real.exp (-(1 / 2 : ℝ)) := by
      have h_product :
          scoreVarianceFromSourceWeights
              (timeVaryingAFGenerationalModel.toMetricModelAt 1) Pop.target =
            Real.exp (-(1 / 4 : ℝ)) * Real.exp (-(1 / 4 : ℝ)) := by
        generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingAFGenerationalModel
      rw [h_product, h_ret]
    have h_ret_norm :
        Real.exp (-((4 : ℝ)⁻¹)) * Real.exp (-((4 : ℝ)⁻¹)) =
          Real.exp (-(1 / 2 : ℝ)) := by
      simpa using h_ret
    have h_eff :
        effectiveOutcomeVariance
            (timeVaryingAFGenerationalModel.toMetricModelAt 1) Pop.target =
          2 + 2 * (1 - Real.exp (-(1 / 2 : ℝ))) ^ 2 := by
      generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingAFGenerationalModel
      rw [h_ret_norm]
      ring
    have h_exp_ne : Real.exp (-(1 / 2 : ℝ)) ≠ 0 := by
      exact Real.exp_ne_zero _
    unfold r2FromSourceWeights explainedSignalVarianceFromSourceWeights
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
    r2FromSourceWeights
      (timeVaryingEffectGenerationalModel.toMetricModelAt 0) Pop.target = 1 / 2 ∧
    r2FromSourceWeights
      (timeVaryingEffectGenerationalModel.toMetricModelAt 1) Pop.target = 1 / 8 := by
  repeat' constructor
  · ext i j
    fin_cases i
    fin_cases j
    generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingAFGenerationalModel,
      timeVaryingEffectGenerationalModel
  · ext i j
    fin_cases i
    fin_cases j
    generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingAFGenerationalModel,
      timeVaryingEffectGenerationalModel
  · generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel
  · generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel
  · generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel
  · generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel
  · simp [betaTargetAt, singleLocusGenerationalWitness, baselineGenerationalPopGen,
    timeVaryingAFGenerationalModel,
    timeVaryingEffectGenerationalModel]
  · simp [betaTargetAt, singleLocusGenerationalWitness, baselineGenerationalPopGen,
    timeVaryingAFGenerationalModel,
    timeVaryingEffectGenerationalModel]
    norm_num
  · generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel
  · generational_witness_simp singleLocusGenerationalWitness, baselineGenerationalPopGen,
      timeVaryingEffectGenerationalModel
    norm_num

/-- The generation-indexed deployed profile always reads its `R²` coordinate
from the same explicit time-sliced source-weights-on-target-state model. This
is a generic bridge theorem for the full mechanistic generational API, not an
accidental theorem about an implicit witness. -/
theorem target_metric_profile_at_generation_reads_explicit_target_r2
    {p q : ℕ} (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    (targetMetricProfileAtGeneration m t).r2 =
      r2FromSourceWeights (m.toMetricModelAt t) Pop.target := by
  simp [r2FromSourceWeights]

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
