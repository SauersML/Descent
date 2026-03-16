import Calibrator.Probability
import Calibrator.Conclusions
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# PGS Calibration Theory

This file formalizes the theory of PGS calibration — the relationship
between predicted risk and observed outcomes. Calibration is distinct
from discrimination (AUC/R²) and can vary independently across
populations.

Key results:
1. Calibration definitions (calibration-in-the-large, slope, Hosmer-Lemeshow)
2. Calibration vs discrimination independence
3. Population-specific calibration drift
4. Recalibration methods and their limits
5. Decision-theoretic implications of miscalibration

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Calibration Definitions

A PGS is well-calibrated if E[Y|PGS = s] = s for binary outcomes,
or if E[Y|PGS = s] = f(s) where f is the identity for the
intended scale.
-/

section CalibrationDefinitions

/-- Link scale on which calibration is interpreted. -/
inductive CalibrationLink where
  | identity
  | logistic
deriving DecidableEq, Repr

/-- Shared calibration surface used across the codebase. -/
structure CalibrationProfile where
  citl : ℝ
  slope : ℝ
  link : CalibrationLink

/-- **Calibration-in-the-large (CITL).**
    CITL = mean(observed) - mean(predicted).
    CITL = 0 means the average prediction matches the average outcome. -/
noncomputable def calibrationInTheLarge (mean_observed mean_predicted : ℝ) : ℝ :=
  mean_observed - mean_predicted

/-- **Calibration slope.**
    Regress observed on predicted: Y = a + b × predicted.
    b = 1 means well-calibrated spread.
    b < 1 means predictions are too extreme (overfitting).
    b > 1 means predictions are too conservative. -/
noncomputable def calibrationSlopeDeviation (slope : ℝ) : ℝ := |slope - 1|

/-- Shared calibration profile constructor. -/
noncomputable def calibrationProfile
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    CalibrationProfile where
  citl := calibrationInTheLarge mean_observed mean_predicted
  slope := slope
  link := link

/-- Identity-scale calibration profile. -/
noncomputable def identityCalibrationProfile
    (mean_observed mean_predicted slope : ℝ) : CalibrationProfile :=
  calibrationProfile CalibrationLink.identity mean_observed mean_predicted slope

/-- Logistic-scale calibration profile. -/
noncomputable def logisticCalibrationProfile
    (mean_observed mean_predicted slope : ℝ) : CalibrationProfile :=
  calibrationProfile CalibrationLink.logistic mean_observed mean_predicted slope

/-- Calibration-slope deviation attached to a shared calibration profile. -/
noncomputable def CalibrationProfile.slopeDeviation (p : CalibrationProfile) : ℝ :=
  calibrationSlopeDeviation p.slope

/-- The simp lemmas immediately below are definitional facts about the shared
calibration-profile container. They do not encode any cross-population
transport model. The biologically meaningful cross-ancestry calibration state
starts later in `CrossPopulationCalibrationShiftModel`. -/

@[simp] theorem calibrationProfile_citl
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    (calibrationProfile link mean_observed mean_predicted slope).citl =
      calibrationInTheLarge mean_observed mean_predicted := by
  rfl

@[simp] theorem calibrationProfile_slope
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    (calibrationProfile link mean_observed mean_predicted slope).slope = slope := by
  rfl

@[simp] theorem calibrationProfile_link
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    (calibrationProfile link mean_observed mean_predicted slope).link = link := by
  rfl

@[simp] theorem identityCalibrationProfile_citl
    (mean_observed mean_predicted slope : ℝ) :
    (identityCalibrationProfile mean_observed mean_predicted slope).citl =
      calibrationInTheLarge mean_observed mean_predicted := by
  rfl

@[simp] theorem identityCalibrationProfile_slope
    (mean_observed mean_predicted slope : ℝ) :
    (identityCalibrationProfile mean_observed mean_predicted slope).slope = slope := by
  rfl

@[simp] theorem identityCalibrationProfile_link
    (mean_observed mean_predicted slope : ℝ) :
    (identityCalibrationProfile mean_observed mean_predicted slope).link =
      CalibrationLink.identity := by
  rfl

@[simp] theorem logisticCalibrationProfile_citl
    (mean_observed mean_predicted slope : ℝ) :
    (logisticCalibrationProfile mean_observed mean_predicted slope).citl =
      calibrationInTheLarge mean_observed mean_predicted := by
  rfl

@[simp] theorem logisticCalibrationProfile_slope
    (mean_observed mean_predicted slope : ℝ) :
    (logisticCalibrationProfile mean_observed mean_predicted slope).slope = slope := by
  rfl

@[simp] theorem logisticCalibrationProfile_link
    (mean_observed mean_predicted slope : ℝ) :
    (logisticCalibrationProfile mean_observed mean_predicted slope).link =
      CalibrationLink.logistic := by
  rfl

@[simp] theorem calibrationProfile_slopeDeviation
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    (calibrationProfile link mean_observed mean_predicted slope).slopeDeviation =
      calibrationSlopeDeviation slope := by
  rfl

/-- Shared absolute-deviation identity for any subunit calibration slope. -/
theorem calibrationSlopeDeviation_eq_one_sub_of_lt_one
    (slope : ℝ) (h_slope : slope < 1) :
    calibrationSlopeDeviation slope = 1 - slope := by
  unfold calibrationSlopeDeviation
  have hneg : slope - 1 < 0 := by linarith
  rw [abs_of_neg hneg]
  ring

/-- **Hosmer-Lemeshow statistic.**
    Group predictions into deciles, compare observed vs expected
    in each group. H-L ~ χ² under good calibration. -/
noncomputable def hosmerLemeshowContrib (observed expected n_group : ℝ) : ℝ :=
  n_group * (observed - expected)^2 / (expected * (1 - expected))

/-- H-L contribution is nonneg. -/
theorem hl_contrib_nonneg (obs exp n : ℝ)
    (h_n : 0 ≤ n) (h_exp : 0 < exp) (h_exp_lt : exp < 1) :
    0 ≤ hosmerLemeshowContrib obs exp n := by
  unfold hosmerLemeshowContrib
  apply div_nonneg
  · exact mul_nonneg h_n (sq_nonneg _)
  · exact mul_nonneg (le_of_lt h_exp) (by linarith)

end CalibrationDefinitions

/-- Logistic-scale prevalence log-odds. -/
noncomputable def prevalenceLogit (pi : ℝ) : ℝ :=
  Real.log (pi / (1 - pi))

/-- **Prevalence-driven logistic intercept shift.**
    If disease prevalence is `π_source` in training and `π_target`
    in the target, the exact intercept shift on the logistic linear-predictor
    scale is `logit(π_target) - logit(π_source)`. -/
noncomputable def prevalenceCITLShift (pi_source pi_target : ℝ) : ℝ :=
  prevalenceLogit pi_target - prevalenceLogit pi_source

/-- Benchmark-only identity-scale calibration profile for the neutral
allele-frequency deployment surrogate.

This object is intentionally coarse: its CITL component is just the supplied
`mean_observed - mean_predicted`, and its slope component is the neutral-AF
benchmark ratio. It is useful for benchmark slope algebra, but it is not a
full SNP-level model of cross-ancestry calibration degradation. -/
noncomputable def neutralAFIdentityCalibrationProfile
    (mean_observed mean_predicted fst_source fst_target : ℝ) : CalibrationProfile :=
  identityCalibrationProfile mean_observed mean_predicted
    (neutralAFBenchmarkRatio fst_source fst_target)

/-- Benchmark-only logistic-scale calibration profile for the neutral
allele-frequency deployment surrogate.

Like `neutralAFIdentityCalibrationProfile`, this packages a benchmark
intercept/slope pair but is not itself a mechanistic SNP-level transport law
for deployed cross-ancestry calibration. -/
noncomputable def neutralAFLogisticCalibrationProfile
    (pi_source pi_target fst_source fst_target : ℝ) : CalibrationProfile :=
  logisticCalibrationProfile (prevalenceLogit pi_target) (prevalenceLogit pi_source)
    (neutralAFBenchmarkRatio fst_source fst_target)

@[simp] theorem neutralAFIdentityCalibrationProfile_citl
    (mean_observed mean_predicted fst_source fst_target : ℝ) :
    (neutralAFIdentityCalibrationProfile
      mean_observed mean_predicted fst_source fst_target).citl =
      calibrationInTheLarge mean_observed mean_predicted := by
  rfl

@[simp] theorem neutralAFIdentityCalibrationProfile_slope
    (mean_observed mean_predicted fst_source fst_target : ℝ) :
    (neutralAFIdentityCalibrationProfile
      mean_observed mean_predicted fst_source fst_target).slope =
      neutralAFBenchmarkRatio fst_source fst_target := by
  rfl

@[simp] theorem neutralAFLogisticCalibrationProfile_citl
    (pi_source pi_target fst_source fst_target : ℝ) :
    (neutralAFLogisticCalibrationProfile
      pi_source pi_target fst_source fst_target).citl =
      prevalenceCITLShift pi_source pi_target := by
  unfold neutralAFLogisticCalibrationProfile prevalenceCITLShift
    logisticCalibrationProfile calibrationProfile prevalenceLogit
    calibrationInTheLarge
  ring

@[simp] theorem neutralAFLogisticCalibrationProfile_slope
    (pi_source pi_target fst_source fst_target : ℝ) :
    (neutralAFLogisticCalibrationProfile
      pi_source pi_target fst_source fst_target).slope =
      neutralAFBenchmarkRatio fst_source fst_target := by
  rfl

theorem neutralAFCalibrationProfiles_share_slope
    (mean_observed mean_predicted pi_source pi_target fst_source fst_target : ℝ) :
    (neutralAFIdentityCalibrationProfile
      mean_observed mean_predicted fst_source fst_target).slope =
      (neutralAFLogisticCalibrationProfile
        pi_source pi_target fst_source fst_target).slope := by
  rfl

theorem neutralAFCalibrationProfiles_share_slopeDeviation
    (mean_observed mean_predicted pi_source pi_target fst_source fst_target : ℝ) :
    (neutralAFIdentityCalibrationProfile
      mean_observed mean_predicted fst_source fst_target).slopeDeviation =
      (neutralAFLogisticCalibrationProfile
        pi_source pi_target fst_source fst_target).slopeDeviation := by
  rfl


/-!
## Calibration vs Discrimination

Calibration and discrimination are independent properties.
A model can have good discrimination but poor calibration
and vice versa.
-/

section CalibrationVsDiscrimination

/-- **Additive score shifts preserve AUC but change calibration.**
    AUC depends only on pairwise ranking of scores. Adding a constant offset
    leaves every pairwise comparison unchanged, so population AUC is
    invariant. Calibration-in-the-large, however, shifts by exactly the same
    offset with opposite sign. This is the formal content behind the claim
    that discrimination does not determine calibration. -/
theorem auc_independent_of_calibration
    {Z : Type*} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (score : Z → ℝ)
    (mean_obs mean_pred c : ℝ) :
    populationAUC pop (fun z => score z + c) = populationAUC pop score ∧
      calibrationInTheLarge mean_obs (mean_pred + c) =
        calibrationInTheLarge mean_obs mean_pred - c := by
  constructor
  · simpa [Function.comp] using
      populationAUC_strictMono_invariant pop score (fun x => x + c) (by
        intro a b hab
        linarith)
  · unfold calibrationInTheLarge
    ring

/-- **Prevalence shift changes calibration.**
    Prevalence shift changes calibration: if prevalence changes from
    π₁ to π₂, the CITL shifts. Using calibrationInTheLarge, the shift
    is exactly (π₂ - π₁) when the model's mean prediction remains fixed. -/
theorem prevalence_shift_changes_calibration
    (mean_pred π₁ π₂ : ℝ) :
    calibrationInTheLarge π₂ mean_pred -
      calibrationInTheLarge π₁ mean_pred = π₂ - π₁ := by
  unfold calibrationInTheLarge
  ring

/-- Explicit cross-population calibration-shift budget.

This state separates the distinct reasons why identity-scale calibration can
change after transport:

- prevalence / mean outcome shift,
- environmental mean-outcome shift,
- genetic mean-outcome shift not captured by prevalence alone,
- score-mean transport shift from changed target genetic architecture, and
- any deployment intercept offset applied to the transported score.

Unlike the deleted prevalence-only headline theorem, this does not treat target
calibration drift as a function of prevalence alone. -/
structure CrossPopulationCalibrationShiftModel where
  sourceObservedMean : ℝ
  sourcePredictedMean : ℝ
  prevalenceShift : ℝ
  environmentalObservedShift : ℝ
  geneticObservedShift : ℝ
  scoreMeanShift : ℝ
  deploymentInterceptShift : ℝ
  sourceSlope : ℝ
  targetSlope : ℝ

/-- Total target observed-mean shift relative to source. -/
noncomputable def CrossPopulationCalibrationShiftModel.observedMeanShift
    (m : CrossPopulationCalibrationShiftModel) : ℝ :=
  m.prevalenceShift + m.environmentalObservedShift + m.geneticObservedShift

/-- Total target predicted-mean shift relative to source. -/
noncomputable def CrossPopulationCalibrationShiftModel.predictedMeanShift
    (m : CrossPopulationCalibrationShiftModel) : ℝ :=
  m.scoreMeanShift + m.deploymentInterceptShift

/-- Source observed mean under the explicit calibration-shift state. -/
noncomputable def CrossPopulationCalibrationShiftModel.targetObservedMean
    (m : CrossPopulationCalibrationShiftModel) : ℝ :=
  m.sourceObservedMean + m.observedMeanShift

/-- Target deployed mean prediction under the explicit calibration-shift state. -/
noncomputable def CrossPopulationCalibrationShiftModel.targetPredictedMean
    (m : CrossPopulationCalibrationShiftModel) : ℝ :=
  m.sourcePredictedMean + m.predictedMeanShift

/-- Source identity-scale calibration profile under the explicit shift state. -/
noncomputable def CrossPopulationCalibrationShiftModel.sourceIdentityCalibrationProfile
    (m : CrossPopulationCalibrationShiftModel) : CalibrationProfile :=
  identityCalibrationProfile m.sourceObservedMean m.sourcePredictedMean m.sourceSlope

/-- Target identity-scale calibration profile under the explicit shift state. -/
noncomputable def CrossPopulationCalibrationShiftModel.targetIdentityCalibrationProfile
    (m : CrossPopulationCalibrationShiftModel) : CalibrationProfile :=
  identityCalibrationProfile m.targetObservedMean m.targetPredictedMean m.targetSlope

@[simp] theorem CrossPopulationCalibrationShiftModel.targetObservedMean_eq
    (m : CrossPopulationCalibrationShiftModel) :
    m.targetObservedMean =
      m.sourceObservedMean +
        m.prevalenceShift + m.environmentalObservedShift + m.geneticObservedShift := by
  simp [CrossPopulationCalibrationShiftModel.targetObservedMean,
    CrossPopulationCalibrationShiftModel.observedMeanShift, add_left_comm,
    add_comm]

@[simp] theorem CrossPopulationCalibrationShiftModel.targetPredictedMean_eq
    (m : CrossPopulationCalibrationShiftModel) :
    m.targetPredictedMean =
      m.sourcePredictedMean + m.scoreMeanShift + m.deploymentInterceptShift := by
  simp [CrossPopulationCalibrationShiftModel.targetPredictedMean,
    CrossPopulationCalibrationShiftModel.predictedMeanShift, add_assoc]

/-- Exact CITL decomposition under the explicit calibration-shift budget. -/
theorem CrossPopulationCalibrationShiftModel.target_citl_eq_source_citl_add_shift_budget
    (m : CrossPopulationCalibrationShiftModel) :
    (m.targetIdentityCalibrationProfile).citl =
      (m.sourceIdentityCalibrationProfile).citl +
        m.observedMeanShift - m.predictedMeanShift := by
  unfold CrossPopulationCalibrationShiftModel.targetIdentityCalibrationProfile
    CrossPopulationCalibrationShiftModel.sourceIdentityCalibrationProfile
    CrossPopulationCalibrationShiftModel.targetObservedMean
    CrossPopulationCalibrationShiftModel.targetPredictedMean
    CrossPopulationCalibrationShiftModel.observedMeanShift
    CrossPopulationCalibrationShiftModel.predictedMeanShift
    identityCalibrationProfile calibrationProfile calibrationInTheLarge
  ring

/-- Under a source model calibrated in the large, target CITL is exactly the
full explicit shift budget: observed-mean drift minus predicted-mean drift. -/
theorem source_calibrated_target_citl_eq_shift_budget
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : (m.sourceIdentityCalibrationProfile).citl = 0) :
    (m.targetIdentityCalibrationProfile).citl =
      m.observedMeanShift - m.predictedMeanShift := by
  rw [m.target_citl_eq_source_citl_add_shift_budget, h_src_cal]
  ring

/-- Under a source model calibrated in the large, absolute target CITL is the
absolute explicit shift budget. -/
theorem source_calibrated_target_abs_citl_eq_abs_shift_budget
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : (m.sourceIdentityCalibrationProfile).citl = 0) :
    |(m.targetIdentityCalibrationProfile).citl| =
      |m.observedMeanShift - m.predictedMeanShift| := by
  rw [source_calibrated_target_citl_eq_shift_budget m h_src_cal]

/-- With no environmental, genetic, score-mean, or deployment-intercept shifts,
the explicit calibration budget reduces to pure prevalence shift. This is a
special case, not the general cross-population calibration law. -/
theorem source_calibrated_target_citl_eq_prevalence_shift_of_no_other_shifts
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : (m.sourceIdentityCalibrationProfile).citl = 0)
    (h_env : m.environmentalObservedShift = 0)
    (h_genetic : m.geneticObservedShift = 0)
    (h_score : m.scoreMeanShift = 0)
    (h_intercept : m.deploymentInterceptShift = 0) :
    (m.targetIdentityCalibrationProfile).citl = m.prevalenceShift := by
  rw [source_calibrated_target_citl_eq_shift_budget m h_src_cal]
  simp [CrossPopulationCalibrationShiftModel.observedMeanShift,
    CrossPopulationCalibrationShiftModel.predictedMeanShift,
    h_env, h_genetic, h_score, h_intercept]

/-- The absolute pure-prevalence formula is likewise only a zero-other-shifts
special case of the full calibration budget. -/
theorem source_calibrated_target_abs_citl_eq_abs_prevalence_shift_of_no_other_shifts
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : (m.sourceIdentityCalibrationProfile).citl = 0)
    (h_env : m.environmentalObservedShift = 0)
    (h_genetic : m.geneticObservedShift = 0)
    (h_score : m.scoreMeanShift = 0)
    (h_intercept : m.deploymentInterceptShift = 0) :
    |(m.targetIdentityCalibrationProfile).citl| = |m.prevalenceShift| := by
  rw [source_calibrated_target_abs_citl_eq_abs_shift_budget m h_src_cal]
  simp [CrossPopulationCalibrationShiftModel.observedMeanShift,
    CrossPopulationCalibrationShiftModel.predictedMeanShift,
    h_env, h_genetic, h_score, h_intercept]

/-- Prevalence equality does not force zero target CITL. If the source is
calibrated and non-prevalence calibration shifts remain, then target CITL
still changes even when prevalence itself is unchanged. -/
theorem source_calibrated_target_citl_eq_nonprevalence_shift_when_prevalence_preserved
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : (m.sourceIdentityCalibrationProfile).citl = 0)
    (h_prev : m.prevalenceShift = 0) :
    (m.targetIdentityCalibrationProfile).citl =
      m.environmentalObservedShift + m.geneticObservedShift -
        m.scoreMeanShift - m.deploymentInterceptShift := by
  rw [source_calibrated_target_citl_eq_shift_budget m h_src_cal]
  simp [CrossPopulationCalibrationShiftModel.observedMeanShift,
    CrossPopulationCalibrationShiftModel.predictedMeanShift, h_prev]
  ring

/-- **Exact cross-ancestry metric profile under drift and an explicit target
calibration-shift budget.**

This is the headline mechanistic theorem for the calibration block:

- exact transported liability-threshold AUC strictly drops under positive drift;
- exact target CITL equals the full explicit target shift budget, not just
  prevalence shift;
- absolute target CITL equals the absolute value of that same full shift budget;
- target absolute CITL is strictly worse whenever the explicit shift budget is
  nonzero; and
- exact calibrated target Brier is strictly worse than the source Brier at the
  same target observed mean because transported `R²` drops.

The calibration term is therefore driven by explicit observed-mean and
predicted-mean transport changes, not by prevalence alone. -/
theorem cross_ancestry_exact_metric_profile
    (V_A V_E fstSource fstTarget : ℝ)
    (cal : CrossPopulationCalibrationShiftModel)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (h_src_cal : (cal.sourceIdentityCalibrationProfile).citl = 0)
    (h_shift_nonzero :
      cal.observedMeanShift - cal.predictedMeanShift ≠ 0)
    (hπT0 : 0 < cal.targetObservedMean)
    (hπT1 : cal.targetObservedMean < 1)
    (hPhiStrict : StrictMono Phi) :
    let sourceProfile := cal.sourceIdentityCalibrationProfile
    let targetProfile := cal.targetIdentityCalibrationProfile
    targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget <
      presentDayLiabilityAUC V_A V_E fstSource ∧
    targetProfile.citl = cal.observedMeanShift - cal.predictedMeanShift ∧
    |targetProfile.citl| = |cal.observedMeanShift - cal.predictedMeanShift| ∧
    |sourceProfile.citl| < |targetProfile.citl| ∧
    sourceBrierFromR2 cal.targetObservedMean (presentDayR2 V_A V_E fstSource) <
      targetExactCalibratedBrierRisk cal.targetObservedMean V_A V_E fstTarget := by
  dsimp
  have h_auc :
      targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget <
        presentDayLiabilityAUC V_A V_E fstSource := by
    exact targetLiabilityAUC_lt_source_of_neutralAF_benchmark
      V_A V_E fstSource fstTarget hVA hVE h_fst h_fst_bounds hPhiStrict
  have h_citl_eq :
      (cal.targetIdentityCalibrationProfile).citl =
        cal.observedMeanShift - cal.predictedMeanShift := by
    exact source_calibrated_target_citl_eq_shift_budget cal h_src_cal
  have h_abs_eq :
      |(cal.targetIdentityCalibrationProfile).citl| =
        |cal.observedMeanShift - cal.predictedMeanShift| := by
    exact source_calibrated_target_abs_citl_eq_abs_shift_budget cal h_src_cal
  have h_tgt_ne_zero : (cal.targetIdentityCalibrationProfile).citl ≠ 0 := by
    rw [h_citl_eq]
    exact h_shift_nonzero
  have h_abs_worse :
      |(cal.sourceIdentityCalibrationProfile).citl| <
        |(cal.targetIdentityCalibrationProfile).citl| := by
    have h_tgt_abs_pos :
        0 < |(cal.targetIdentityCalibrationProfile).citl| :=
      abs_pos.mpr h_tgt_ne_zero
    simpa [h_src_cal] using h_tgt_abs_pos
  have h_brier :
      sourceBrierFromR2 cal.targetObservedMean (presentDayR2 V_A V_E fstSource) <
        targetExactCalibratedBrierRisk cal.targetObservedMean V_A V_E fstTarget := by
    exact targetBrier_strict_gt_source_of_neutralAF_benchmark
      cal.targetObservedMean V_A V_E fstSource fstTarget
      hπT0 hπT1 hVA hVE h_fst h_fst_bounds
  exact ⟨h_auc, h_citl_eq, h_abs_eq, h_abs_worse, h_brier⟩

/-- **Cross-ancestry AUC drops while CITL worsens from an explicit target shift
budget.**

This theorem is the calibration analogue of the mechanistic portability
results elsewhere in the repo: discrimination worsens under drift, while CITL
is governed by the full observed-minus-predicted target shift budget rather
than by prevalence alone. -/
theorem cross_ancestry_auc_drops_and_citl_worsens_from_explicit_shift_budget
    (V_A V_E fstSource fstTarget : ℝ)
    (cal : CrossPopulationCalibrationShiftModel)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (h_src_cal : (cal.sourceIdentityCalibrationProfile).citl = 0)
    (h_shift_nonzero :
      cal.observedMeanShift - cal.predictedMeanShift ≠ 0)
    (hPhiStrict : StrictMono Phi) :
    let sourceProfile := cal.sourceIdentityCalibrationProfile
    let targetProfile := cal.targetIdentityCalibrationProfile
    targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget <
      presentDayLiabilityAUC V_A V_E fstSource ∧
    targetProfile.citl = cal.observedMeanShift - cal.predictedMeanShift ∧
    |targetProfile.citl| = |cal.observedMeanShift - cal.predictedMeanShift| ∧
    |sourceProfile.citl| < |targetProfile.citl| := by
  dsimp
  have h_auc :
      targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget <
        presentDayLiabilityAUC V_A V_E fstSource := by
    exact targetLiabilityAUC_lt_source_of_neutralAF_benchmark
      V_A V_E fstSource fstTarget hVA hVE h_fst h_fst_bounds hPhiStrict
  have h_citl_eq :
      (cal.targetIdentityCalibrationProfile).citl =
        cal.observedMeanShift - cal.predictedMeanShift := by
    exact source_calibrated_target_citl_eq_shift_budget cal h_src_cal
  have h_abs_eq :
      |(cal.targetIdentityCalibrationProfile).citl| =
        |cal.observedMeanShift - cal.predictedMeanShift| := by
    exact source_calibrated_target_abs_citl_eq_abs_shift_budget cal h_src_cal
  have h_tgt_ne_zero : (cal.targetIdentityCalibrationProfile).citl ≠ 0 := by
    rw [h_citl_eq]
    exact h_shift_nonzero
  have h_abs_worse :
      |(cal.sourceIdentityCalibrationProfile).citl| <
        |(cal.targetIdentityCalibrationProfile).citl| := by
    have h_tgt_abs_pos :
        0 < |(cal.targetIdentityCalibrationProfile).citl| :=
      abs_pos.mpr h_tgt_ne_zero
    simpa [h_src_cal] using h_tgt_abs_pos
  exact ⟨h_auc, h_citl_eq, h_abs_eq, h_abs_worse⟩

/-- **Prevalence-only cross-ancestry CITL worsening is just a special case.**
When every non-prevalence calibration shift vanishes, the full explicit shift
budget reduces to prevalence shift alone. This theorem is deliberately scoped
as a benchmark special case rather than a general SNP-level deployment law. -/
theorem cross_ancestry_auc_drops_and_prevalence_only_citl_worsens_special_case
    (V_A V_E fstSource fstTarget : ℝ)
    (cal : CrossPopulationCalibrationShiftModel)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (h_src_cal : (cal.sourceIdentityCalibrationProfile).citl = 0)
    (h_env : cal.environmentalObservedShift = 0)
    (h_genetic : cal.geneticObservedShift = 0)
    (h_score : cal.scoreMeanShift = 0)
    (h_intercept : cal.deploymentInterceptShift = 0)
    (h_prev_shift : cal.prevalenceShift ≠ 0)
    (hPhiStrict : StrictMono Phi) :
    let sourceProfile := cal.sourceIdentityCalibrationProfile
    let targetProfile := cal.targetIdentityCalibrationProfile
    targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget <
      presentDayLiabilityAUC V_A V_E fstSource ∧
    targetProfile.citl = cal.prevalenceShift ∧
    |targetProfile.citl| = |cal.prevalenceShift| ∧
    |sourceProfile.citl| < |targetProfile.citl| := by
  have h_shift_nonzero :
      cal.observedMeanShift - cal.predictedMeanShift ≠ 0 := by
    simp [CrossPopulationCalibrationShiftModel.observedMeanShift,
      CrossPopulationCalibrationShiftModel.predictedMeanShift,
      h_env, h_genetic, h_score, h_intercept, h_prev_shift]
  have h_main :=
    cross_ancestry_auc_drops_and_citl_worsens_from_explicit_shift_budget
      V_A V_E fstSource fstTarget cal hVA hVE h_fst h_fst_bounds
      h_src_cal h_shift_nonzero hPhiStrict
  dsimp at h_main ⊢
  rcases h_main with ⟨h_auc, h_citl, h_abs, h_worse⟩
  refine ⟨h_auc, ?_, ?_, h_worse⟩
  · rw [source_calibrated_target_citl_eq_prevalence_shift_of_no_other_shifts
      cal h_src_cal h_env h_genetic h_score h_intercept]
  · rw [source_calibrated_target_abs_citl_eq_abs_prevalence_shift_of_no_other_shifts
      cal h_src_cal h_env h_genetic h_score h_intercept]

/-- **Cross-ancestry AUC drops while observable calibrated Brier worsens.**
    `AUC` measures discrimination, while `Brier` is the standard proper scoring
    rule carried by the observable drift model. Under positive drift, the target
    AUC is strictly lower and the target Brier score is strictly higher. -/
theorem cross_ancestry_auc_drops_and_observable_brier_worsens
    (π V_A V_E fstSource fstTarget : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (hPhiStrict : StrictMono Phi) :
    targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget <
      presentDayLiabilityAUC V_A V_E fstSource ∧
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstSource) <
      targetExactCalibratedBrierRisk π V_A V_E fstTarget := by
  constructor
  · exact targetLiabilityAUC_lt_source_of_neutralAF_benchmark
      V_A V_E fstSource fstTarget hVA hVE h_fst h_fst_bounds hPhiStrict
  · exact targetBrier_strict_gt_source_of_neutralAF_benchmark π V_A V_E fstSource fstTarget
      hπ0 hπ1 hVA hVE h_fst h_fst_bounds

end CalibrationVsDiscrimination


/-!
## Population-Specific Calibration Drift

When a PGS trained in one population is applied to another,
calibration drifts systematically.
-/

section PopulationCalibrationDrift

/-- Shared logistic-scale calibration profile induced by a prevalence shift. -/
noncomputable def prevalenceLogisticCalibrationProfile
    (pi_source pi_target slope : ℝ) : CalibrationProfile :=
  logisticCalibrationProfile (prevalenceLogit pi_target) (prevalenceLogit pi_source) slope

/-- Literal cov/var calibration slope for a transported source-calibrated score.

    This is the common drift-calibration slope used across the repo:

    `Cov(Y_target, Ŷ_source) / Var(Ŷ_source)`.

    Under the additive drift model with fixed effects and varying allele
    frequencies, it is exactly the ratio of target to source score variance. -/
noncomputable def transportedLinearCalibrationSlope
    (V_A fst_source fst_target : ℝ) : ℝ :=
  presentDayPGSVariance V_A fst_target / presentDayPGSVariance V_A fst_source

/-- Coarse identity-scale calibration profile for a transported score under the
observable drift benchmark.

This packages literal CITL and the benchmark regression slope
`Cov(Y_target, Ŷ_source) / Var(Ŷ_source)`. It is useful as a slope coordinate,
but it is not a sufficient mechanistic description of SNP-level calibration
degradation by itself. -/
noncomputable def transportedIdentityCalibrationProfile
    (mean_observed mean_predicted V_A fst_source fst_target : ℝ) : CalibrationProfile :=
  identityCalibrationProfile mean_observed mean_predicted
    (transportedLinearCalibrationSlope V_A fst_source fst_target)

@[simp] theorem prevalenceLogisticCalibrationProfile_citl
    (pi_source pi_target slope : ℝ) :
    (prevalenceLogisticCalibrationProfile pi_source pi_target slope).citl =
      prevalenceCITLShift pi_source pi_target := by
  unfold prevalenceLogisticCalibrationProfile prevalenceCITLShift
    logisticCalibrationProfile calibrationProfile prevalenceLogit
    calibrationInTheLarge
  ring

@[simp] theorem prevalenceLogisticCalibrationProfile_slope
    (pi_source pi_target slope : ℝ) :
    (prevalenceLogisticCalibrationProfile pi_source pi_target slope).slope = slope := by
  rfl

@[simp] theorem transportedIdentityCalibrationProfile_citl
    (mean_observed mean_predicted V_A fst_source fst_target : ℝ) :
    (transportedIdentityCalibrationProfile
      mean_observed mean_predicted V_A fst_source fst_target).citl =
      calibrationInTheLarge mean_observed mean_predicted := by
  rfl

@[simp] theorem transportedIdentityCalibrationProfile_slope
    (mean_observed mean_predicted V_A fst_source fst_target : ℝ) :
    (transportedIdentityCalibrationProfile
      mean_observed mean_predicted V_A fst_source fst_target).slope =
      transportedLinearCalibrationSlope V_A fst_source fst_target := by
  rfl

/-- The shared transported linear calibration slope equals the neutral
allele-frequency benchmark ratio. -/
theorem transportedLinearCalibrationSlope_eq_neutralAFBenchmarkRatio
    (V_A fstS fstT : ℝ)
    (hVA : 0 < V_A)
    (hfstS_lt_one : fstS < 1) :
    transportedLinearCalibrationSlope V_A fstS fstT = neutralAFBenchmarkRatio fstS fstT := by
  have hVA_ne : V_A ≠ 0 := ne_of_gt hVA
  have hden_ne : 1 - fstS ≠ 0 := by linarith
  unfold transportedLinearCalibrationSlope neutralAFBenchmarkRatio presentDayPGSVariance
  field_simp [hVA_ne, hden_ne]

/-- Exact closed form of the shared transported linear calibration slope. -/
theorem transportedLinearCalibrationSlope_eq_fst_ratio
    (V_A fstS fstT : ℝ)
    (hVA : 0 < V_A)
    (hfstS_lt_one : fstS < 1) :
    transportedLinearCalibrationSlope V_A fstS fstT = (1 - fstT) / (1 - fstS) := by
  have hVA_ne : V_A ≠ 0 := ne_of_gt hVA
  have hden_ne : 1 - fstS ≠ 0 := by linarith
  unfold transportedLinearCalibrationSlope presentDayPGSVariance
  field_simp [hVA_ne, hden_ne]

/-- Positive drift pushes the shared transported linear calibration slope below
`1`. -/
theorem transportedLinearCalibrationSlope_lt_one
    (V_A fst_source fst_target : ℝ)
    (hVA : 0 < V_A)
    (h_drift : fst_source < fst_target)
    (h_target_le_one : fst_target ≤ 1) :
    transportedLinearCalibrationSlope V_A fst_source fst_target < 1 := by
  have h_source_lt_one : fst_source < 1 := lt_of_lt_of_le h_drift h_target_le_one
  unfold transportedLinearCalibrationSlope presentDayPGSVariance
  have h_den : 0 < (1 - fst_source) * V_A := by
    have h_one_minus : 0 < 1 - fst_source := by linarith
    exact mul_pos h_one_minus hVA
  rw [div_lt_one h_den]
  nlinarith [mul_lt_mul_of_pos_right h_drift hVA]

/-- CITL shift is zero when prevalences match. -/
theorem no_citl_shift_same_prevalence (pi : ℝ) :
    prevalenceCITLShift pi pi = 0 := by
  rw [← prevalenceLogisticCalibrationProfile_citl pi pi (1 : ℝ)]
  simp [prevalenceLogisticCalibrationProfile, logisticCalibrationProfile,
    calibrationProfile, calibrationInTheLarge]

/-- CITL shift is positive when target has higher prevalence. -/
theorem citl_shift_positive_higher_prevalence
    (pi_s pi_t : ℝ) (h_s : 0 < pi_s)
    (h_higher : pi_s < pi_t)
    (h_t : pi_t < 1) :
    0 < prevalenceCITLShift pi_s pi_t := by
  have h_t_pos : 0 < pi_t := lt_trans h_s h_higher
  have h_den_s : 0 < 1 - pi_s := by linarith
  have h_den_t : 0 < 1 - pi_t := by linarith
  have h_odds_pos_s : 0 < pi_s / (1 - pi_s) := by
    exact div_pos h_s h_den_s
  have h_odds_lt : pi_s / (1 - pi_s) < pi_t / (1 - pi_t) := by
    rw [div_lt_div_iff₀ h_den_s h_den_t]
    nlinarith
  unfold prevalenceCITLShift prevalenceLogit
  apply sub_pos.mpr
  exact Real.log_lt_log h_odds_pos_s h_odds_lt

/-- **Environmental confounding shifts calibration.**
    If environmental risk factors change the population mean outcome by
    `env_effect` while the model's mean prediction is unchanged, then
    calibration-in-the-large shifts by exactly `env_effect`. -/
theorem env_differences_shift_calibration
    (mean_obs mean_pred env_effect : ℝ) :
    calibrationInTheLarge (mean_obs + env_effect) mean_pred =
      calibrationInTheLarge mean_obs mean_pred + env_effect := by
  unfold calibrationInTheLarge
  ring

/-- Under a source model calibrated in the large, any nonzero environmental
    shift induces nonzero target CITL. -/
theorem env_differences_shift_calibration_nonzero_of_calibrated_source
    (mean_obs mean_pred env_effect : ℝ)
    (h_src_cal : calibrationInTheLarge mean_obs mean_pred = 0)
    (h_effect : env_effect ≠ 0) :
    calibrationInTheLarge (mean_obs + env_effect) mean_pred ≠ 0 := by
  rw [env_differences_shift_calibration]
  rw [h_src_cal]
  simpa using h_effect

/-- **Genetic risk distribution shift.**
    If the PGS mean shifts by Δμ in the target population, the CITL
    shifts correspondingly. Using calibrationInTheLarge:
    CITL_target = (mean_obs_target) - (mean_pred), where mean_pred
    was calibrated to source. The shift in mean PGS creates a CITL
    equal to the mean difference when the model was calibrated (CITL=0) in source.
    CITL_target = mean_obs_target - mean_obs_source + (mean_pgs_source - mean_pgs_target). -/
theorem genetic_distribution_shift
    (mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t : ℝ) :
    calibrationInTheLarge mean_obs_t mean_pgs_t =
      calibrationInTheLarge mean_obs_s mean_pgs_s +
        (mean_obs_t - mean_obs_s) + (mean_pgs_s - mean_pgs_t) := by
  unfold calibrationInTheLarge
  ring

/-- If the source model is calibrated in the large, the target CITL equals the
    observed-mean shift plus the PGS-mean shift exactly. -/
theorem genetic_distribution_shift_of_calibrated_source
    (mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t : ℝ)
    (h_calibrated_source : calibrationInTheLarge mean_obs_s mean_pgs_s = 0) :
    calibrationInTheLarge mean_obs_t mean_pgs_t =
      mean_obs_t - mean_obs_s + (mean_pgs_s - mean_pgs_t) := by
  rw [genetic_distribution_shift]
  rw [h_calibrated_source]
  ring

/-- Under a calibrated source model, any nonzero net mean shift induces
    nonzero target CITL. -/
theorem genetic_distribution_shift_nonzero_of_calibrated_source
    (mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t : ℝ)
    (h_calibrated_source : calibrationInTheLarge mean_obs_s mean_pgs_s = 0)
    (h_net_shift : mean_obs_t - mean_obs_s + (mean_pgs_s - mean_pgs_t) ≠ 0) :
    calibrationInTheLarge mean_obs_t mean_pgs_t ≠ 0 := by
  rw [genetic_distribution_shift_of_calibrated_source
    mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t h_calibrated_source]
  exact h_net_shift

end PopulationCalibrationDrift


/-!
## Recalibration Methods

Methods to restore calibration when applying PGS across populations.
-/

section RecalibrationMethods

/-- **Intercept recalibration.**
    Fit new intercept a in Y = a + PGS.
    This corrects CITL but not slope miscalibration. -/
noncomputable def interceptRecalibrated (pgs new_intercept : ℝ) : ℝ :=
  new_intercept + pgs

/-- Intercept recalibration shifts CITL by exactly the fitted intercept. -/
theorem intercept_recalibration_shifts_citl
    (mean_obs mean_pgs new_intercept : ℝ) :
    calibrationInTheLarge mean_obs
        (interceptRecalibrated mean_pgs new_intercept) =
      calibrationInTheLarge mean_obs mean_pgs - new_intercept := by
  unfold calibrationInTheLarge interceptRecalibrated
  ring

/-- Intercept recalibration corrects CITL exactly when the fitted intercept
    equals the original CITL. -/
theorem intercept_recal_corrects_citl
    (mean_obs mean_pgs new_intercept : ℝ)
    (h_correction : new_intercept = calibrationInTheLarge mean_obs mean_pgs) :
    calibrationInTheLarge mean_obs
      (interceptRecalibrated mean_pgs new_intercept) = 0 := by
  rw [intercept_recalibration_shifts_citl, h_correction]
  ring

/-- **Logistic recalibration.**
    Fit Y = a + b × PGS (both intercept and slope).
    This corrects both CITL and slope miscalibration
    but requires labeled target data. -/
noncomputable def logisticRecalibrated (pgs a b : ℝ) : ℝ :=
  a + b * pgs

/-- Exact CITL formula after logistic recalibration. -/
theorem logistic_recalibration_shifts_citl
    (mean_obs mean_pgs a b : ℝ) :
    calibrationInTheLarge mean_obs (logisticRecalibrated mean_pgs a b) =
      calibrationInTheLarge mean_obs mean_pgs - a - (b - 1) * mean_pgs := by
  unfold calibrationInTheLarge logisticRecalibrated
  ring

/-- Choosing the fitted intercept `a = mean_obs - b * mean_pgs` makes the
    recalibrated prediction match the observed mean exactly, so CITL becomes
    zero for any chosen slope `b`. -/
theorem logistic_recalibration_corrects_citl
    (mean_obs mean_pgs b : ℝ) :
    calibrationInTheLarge mean_obs
      (logisticRecalibrated mean_pgs (mean_obs - b * mean_pgs) b) = 0 := by
  rw [logistic_recalibration_shifts_citl]
  unfold calibrationInTheLarge
  ring

/-- Effective calibration slope after logistic recalibration.
    If the target linear predictor uses slope `targetSlope` on the original PGS
    scale, and deployed predictions use fitted slope `fittedSlope`, then the
    target linear predictor as a function of the deployed predictor has slope
    `targetSlope / fittedSlope`. -/
noncomputable def recalibratedCalibrationSlope
    (targetSlope fittedSlope : ℝ) : ℝ :=
  targetSlope / fittedSlope

/-- Exact affine representation of the target linear predictor in terms of the
    logistic-recalibrated predictor. -/
theorem target_linear_predictor_eq_affine_in_logistic_recalibrated
    (pgs targetIntercept targetSlope fittedIntercept fittedSlope : ℝ)
    (h_fit_nonzero : fittedSlope ≠ 0) :
    targetIntercept + targetSlope * pgs =
      (targetIntercept -
          recalibratedCalibrationSlope targetSlope fittedSlope * fittedIntercept) +
        recalibratedCalibrationSlope targetSlope fittedSlope *
          logisticRecalibrated pgs fittedIntercept fittedSlope := by
  unfold recalibratedCalibrationSlope logisticRecalibrated
  field_simp [h_fit_nonzero]
  ring

/-- If the fitted slope equals the target calibration slope, the recalibrated
    predictor has exact calibration slope `1`. -/
theorem logistic_recalibration_corrects_slope
    (targetSlope : ℝ)
    (h_slope_nonzero : targetSlope ≠ 0) :
    recalibratedCalibrationSlope targetSlope targetSlope = 1 ∧
      calibrationSlopeDeviation
        (recalibratedCalibrationSlope targetSlope targetSlope) = 0 := by
  constructor
  · unfold recalibratedCalibrationSlope
    exact div_self h_slope_nonzero
  · unfold calibrationSlopeDeviation recalibratedCalibrationSlope
    rw [div_self h_slope_nonzero, sub_self, abs_zero]

/-- Shared logistic calibration profile of the fully recalibrated predictor. -/
theorem logistic_recalibrated_profile_corrects_citl_and_slope
    (mean_obs mean_pgs targetSlope : ℝ)
    (h_slope_nonzero : targetSlope ≠ 0) :
    let profile :=
      logisticCalibrationProfile
        mean_obs
        (logisticRecalibrated mean_pgs (mean_obs - targetSlope * mean_pgs) targetSlope)
        (recalibratedCalibrationSlope targetSlope targetSlope)
    profile.citl = 0 ∧ profile.slopeDeviation = 0 := by
  dsimp
  constructor
  · exact logistic_recalibration_corrects_citl mean_obs mean_pgs targetSlope
  · exact (logistic_recalibration_corrects_slope targetSlope h_slope_nonzero).2

/-- Logistic recalibration with the fitted intercept and fitted slope corrects
    both calibration-in-the-large and slope deviation exactly. -/
theorem logistic_recalibration_corrects_citl_and_slope
    (mean_obs mean_pgs targetSlope : ℝ)
    (h_slope_nonzero : targetSlope ≠ 0) :
    calibrationInTheLarge mean_obs
        (logisticRecalibrated mean_pgs (mean_obs - targetSlope * mean_pgs) targetSlope) = 0 ∧
      calibrationSlopeDeviation
        (recalibratedCalibrationSlope targetSlope targetSlope) = 0 := by
  simpa [CalibrationProfile.slopeDeviation] using
    logistic_recalibrated_profile_corrects_citl_and_slope
      mean_obs mean_pgs targetSlope h_slope_nonzero

/-- Logistic recalibration preserves AUC because it is a strictly increasing
    affine transform when the fitted slope is positive. -/
theorem logistic_recalibration_preserves_auc
    {Z : Type*} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (score : Z → ℝ)
    (a b : ℝ)
    (h_b_pos : 0 < b) :
    populationAUC pop (fun z => logisticRecalibrated (score z) a b) =
      populationAUC pop score := by
  simpa [logisticRecalibrated, Function.comp] using
    (populationAUC_strictMono_invariant pop score (fun x => a + b * x) (by
      intro x y hxy
      linarith [mul_lt_mul_of_pos_left hxy h_b_pos]))

/-- **Trace-MSE lower bound for target recalibration.**
    In an orthogonal Fisher model with `d` target calibration parameters and
    per-event Fisher information `I_event`, the summed estimation variance is
    lower-bounded by `d / (n_events * I_event)`. This is the exact precision
    object that drives target-data requirements; there is no hard-coded
    "200 events per parameter" rule in the theorem. -/
noncomputable def recalibrationTraceMSELowerBound
    (nEvents nParams infoPerEvent : ℝ) : ℝ :=
  nParams / (nEvents * infoPerEvent)

/-- **Exact event threshold for a target recalibration precision goal.**
    Solving `d / (n_events * I_event) ≤ τ` for `n_events` gives the exact event
    requirement `d / (I_event * τ)`. Specializing to logistic recalibration
    means `d = 2` (intercept and slope), but the theorem is generic in the
    number of calibration parameters. -/
noncomputable def requiredEventsForRecalibration
    (nParams infoPerEvent targetTraceMSE : ℝ) : ℝ :=
  nParams / (infoPerEvent * targetTraceMSE)

/-- **Sample size needed for recalibration.**
    Under the orthogonal Fisher trace-MSE model, achieving target calibration
    precision `τ` is equivalent to having at least
    `d / (I_event * τ)` target events, where `d` is the number of fitted
    recalibration parameters and `I_event` is the per-event Fisher information.
    This is an exact event-threshold theorem about calibration uncertainty,
    not bookkeeping on a fixed heuristic constant. -/
theorem recalibration_needs_events
    (nEvents nParams infoPerEvent targetTraceMSE : ℝ)
    (h_n : 0 < nEvents)
    (h_info : 0 < infoPerEvent)
    (h_target : 0 < targetTraceMSE) :
    recalibrationTraceMSELowerBound nEvents nParams infoPerEvent ≤ targetTraceMSE ↔
      requiredEventsForRecalibration nParams infoPerEvent targetTraceMSE ≤ nEvents := by
  unfold recalibrationTraceMSELowerBound requiredEventsForRecalibration
  constructor
  · intro h
    rw [div_le_iff₀ (mul_pos h_n h_info)] at h
    rw [div_le_iff₀ (mul_pos h_info h_target)]
    nlinarith
  · intro h
    rw [div_le_iff₀ (mul_pos h_info h_target)] at h
    rw [div_le_iff₀ (mul_pos h_n h_info)]
    nlinarith

/-- **Required event count increases with recalibration dimension.**
    Holding per-event information and the target trace-MSE goal fixed, fitting
    more target-specific calibration parameters strictly increases the event
    count needed to achieve the same uncertainty target. -/
theorem required_events_increase_with_recalibration_dimension
    (nParams₁ nParams₂ infoPerEvent targetTraceMSE : ℝ)
    (h_dim : nParams₁ < nParams₂)
    (h_info : 0 < infoPerEvent)
    (h_target : 0 < targetTraceMSE) :
    requiredEventsForRecalibration nParams₁ infoPerEvent targetTraceMSE <
      requiredEventsForRecalibration nParams₂ infoPerEvent targetTraceMSE := by
  unfold requiredEventsForRecalibration
  exact div_lt_div_of_pos_right h_dim (mul_pos h_info h_target)

/-- **Required event count decreases with per-event information.**
    More informative target events, whether from sharper score spread or richer
    recalibration covariates, strictly reduce the event count needed to hit a
    fixed trace-MSE target. -/
theorem required_events_decrease_with_event_information
    (nParams info₁ info₂ targetTraceMSE : ℝ)
    (h_params : 0 < nParams)
    (h_info₁ : 0 < info₁)
    (h_info : info₁ < info₂)
    (h_target : 0 < targetTraceMSE) :
    requiredEventsForRecalibration nParams info₂ targetTraceMSE <
      requiredEventsForRecalibration nParams info₁ targetTraceMSE := by
  unfold requiredEventsForRecalibration
  have hden₁ : 0 < info₁ * targetTraceMSE := mul_pos h_info₁ h_target
  exact div_lt_div_of_pos_left h_params hden₁ (by nlinarith)

/-- **Rarer target prevalence requires more labeled target samples for the same
    recalibration precision.**
    If only a fraction `π` of target individuals are events, then the total
    target cohort size needed to reach a given recalibration trace-MSE target is
    the required event count divided by `π`. Therefore rarer diseases require
    larger target cohorts even when the per-event information and calibration
    precision target are fixed. -/
noncomputable def requiredTargetCohortSizeForRecalibration
    (nParams prevalence infoPerEvent targetTraceMSE : ℝ) : ℝ :=
  requiredEventsForRecalibration nParams infoPerEvent targetTraceMSE / prevalence

/-- **Exact labeled-cohort threshold for target recalibration.**
    If a fraction `π` of target individuals are events, then `n = n_events / π`
    labeled target samples are needed. Therefore hitting a target trace-MSE
    level is equivalent to having at least
    `requiredTargetCohortSizeForRecalibration d π I_event τ` labeled target
    individuals. This connects calibration precision directly to the clinically
    relevant target-cohort size rather than only to the abstract event count. -/
theorem recalibration_needs_target_cohort
    (nTarget nParams prevalence infoPerEvent targetTraceMSE : ℝ)
    (h_target_n : 0 < nTarget)
    (h_prev : 0 < prevalence)
    (h_info : 0 < infoPerEvent)
    (h_target : 0 < targetTraceMSE) :
    recalibrationTraceMSELowerBound (prevalence * nTarget) nParams infoPerEvent ≤ targetTraceMSE ↔
      requiredTargetCohortSizeForRecalibration nParams prevalence infoPerEvent targetTraceMSE ≤ nTarget := by
  have h_events : 0 < prevalence * nTarget := mul_pos h_prev h_target_n
  rw [recalibration_needs_events (prevalence * nTarget) nParams infoPerEvent targetTraceMSE
    h_events h_info h_target]
  unfold requiredTargetCohortSizeForRecalibration
  rw [div_le_iff₀ h_prev]
  ring_nf

/-- At fixed parameter count, per-event information, and target precision,
    lower event prevalence strictly increases the total target cohort size
    needed for recalibration. -/
theorem rarer_target_prevalence_requires_larger_recalibration_cohort
    (nParams π₁ π₂ infoPerEvent targetTraceMSE : ℝ)
    (h_params : 0 < nParams)
    (hπ₁ : 0 < π₁)
    (hπ : π₁ < π₂)
    (h_info : 0 < infoPerEvent)
    (h_target : 0 < targetTraceMSE) :
    requiredTargetCohortSizeForRecalibration nParams π₂ infoPerEvent targetTraceMSE <
      requiredTargetCohortSizeForRecalibration nParams π₁ infoPerEvent targetTraceMSE := by
  have h_required_pos : 0 < requiredEventsForRecalibration nParams infoPerEvent targetTraceMSE := by
    unfold requiredEventsForRecalibration
    exact div_pos h_params (mul_pos h_info h_target)
  have hπ₂ : 0 < π₂ := lt_trans hπ₁ hπ
  unfold requiredTargetCohortSizeForRecalibration
  field_simp [ne_of_gt h_required_pos, ne_of_gt hπ₁, ne_of_gt hπ₂]
  nlinarith

/-- **Recalibration does not change AUC.**
    Recalibration applies a strictly increasing affine transform
    `s ↦ a + b × s` with `b > 0`. Such transforms preserve pairwise score
    orderings, so population AUC is unchanged. -/
theorem recalibration_preserves_auc
    {Z : Type*} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (score : Z → ℝ)
    (a b : ℝ)
    (h_b_pos : 0 < b) :
    populationAUC pop (fun z => a + b * score z) = populationAUC pop score := by
  simpa [Function.comp] using
    populationAUC_strictMono_invariant pop score (fun x => a + b * x) (by
      intro x y hxy
      linarith [mul_lt_mul_of_pos_left hxy h_b_pos])

end RecalibrationMethods


/-!
## Decision-Theoretic Implications

Miscalibration has direct consequences for clinical decisions
based on PGS thresholds.
-/

section DecisionImplications

/-- A risk score is classified as high risk when it exceeds the decision
    threshold. -/
def classifiedHighRisk (threshold predictedRisk : ℝ) : Prop :=
  threshold < predictedRisk

/-- **Miscalibration changes clinical decisions.**
    If the PGS is miscalibrated with CITL shift c > 0 (over-prediction),
    a patient with true risk r < threshold gets predicted risk r + c.
    When c > threshold - r, the patient is incorrectly classified
    as high risk: predicted_risk = r + c > threshold > r = true_risk. -/
theorem miscalibration_changes_decisions
    (true_risk threshold c : ℝ)
    (h_truly_low : true_risk < threshold)
    (h_miscal : threshold - true_risk < c) :
    ¬ classifiedHighRisk threshold true_risk ∧
      classifiedHighRisk threshold (true_risk + c) := by
  unfold classifiedHighRisk
  constructor
  · linarith
  · linarith

/-- **Net reclassification improvement (NRI) from recalibration.**
    NRI measures the proportion of patients correctly reclassified.
    NRI = (net up-classification among events) + (net down-classification among non-events). -/
noncomputable def nri (up_events down_events up_nonevents down_nonevents n_events n_nonevents : ℝ) : ℝ :=
  (up_events - down_events) / n_events + (down_nonevents - up_nonevents) / n_nonevents

/-- **Downward reclassification at a clinical decision threshold.**
    A downward intercept correction of size `δ > 0` moves an individual from
    high risk to low risk exactly when the baseline score lies in the threshold
    band `(threshold, threshold + δ]`. -/
theorem down_reclassified_after_downward_shift_iff_mem_band
    (threshold score δ : ℝ) :
    classifiedHighRisk threshold score ∧
      ¬ classifiedHighRisk threshold (score - δ) ↔
      score ∈ Set.Ioc threshold (threshold + δ) := by
  unfold classifiedHighRisk
  constructor
  · intro h
    rcases h with ⟨h_high, h_not_high_after⟩
    constructor
    · exact h_high
    · have h_after_le : score - δ ≤ threshold := not_lt.mp h_not_high_after
      linarith
  · intro h
    rcases h with ⟨h_high, h_band_upper⟩
    constructor
    · exact h_high
    · have h_after_le : score - δ ≤ threshold := by
        linarith
      exact not_lt.mpr h_after_le

/-- **Threshold-band reclassification rate.**
    Under a downward intercept correction by `δ > 0`, this is the fraction of
    a class-specific score law lying in the band `(threshold, threshold + δ]`.
    It is exactly the reclassification rate for that class. -/
noncomputable def thresholdBandRate
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (threshold δ : ℝ) : ℝ :=
  (μ (Set.Ioc threshold (threshold + δ))).toReal

/-- **Downward reclassification rate under intercept recalibration.**
    This is the probability that a score is above threshold before
    recalibration but at or below threshold after subtracting `δ`. -/
noncomputable def downReclassificationRate
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (threshold δ : ℝ) : ℝ :=
  (μ {score | classifiedHighRisk threshold score ∧
      ¬ classifiedHighRisk threshold (score - δ)}).toReal

/-- Downward reclassification is exactly threshold-band mass. -/
theorem downReclassificationRate_eq_thresholdBandRate
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (threshold δ : ℝ) :
    downReclassificationRate μ threshold δ = thresholdBandRate μ threshold δ := by
  unfold downReclassificationRate thresholdBandRate
  have hset :
      {score | classifiedHighRisk threshold score ∧
          ¬ classifiedHighRisk threshold (score - δ)} =
        Set.Ioc threshold (threshold + δ) := by
    ext score
    exact down_reclassified_after_downward_shift_iff_mem_band threshold score δ
  rw [hset]

/-- **NRI induced by a downward intercept recalibration.**
    For an over-predicting model corrected by subtracting `δ > 0` from every
    score, only downward reclassifications can occur. Event NRI is therefore
    the sensitivity loss, while non-event NRI is the specificity gain. -/
noncomputable def nriFromDownwardInterceptRecalibration
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ) : ℝ :=
  nri
    0 (downReclassificationRate μevent threshold δ)
    0 (downReclassificationRate μnonevent threshold δ)
    1 1

/-- Exact NRI formula for a downward intercept correction. -/
theorem nriFromDownwardInterceptRecalibration_eq_band_difference
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ) :
    nriFromDownwardInterceptRecalibration μevent μnonevent threshold δ =
      thresholdBandRate μnonevent threshold δ -
        thresholdBandRate μevent threshold δ := by
  unfold nriFromDownwardInterceptRecalibration nri
  rw [downReclassificationRate_eq_thresholdBandRate μevent threshold δ]
  rw [downReclassificationRate_eq_thresholdBandRate μnonevent threshold δ]
  ring

/-- **Positive NRI means recalibration improves threshold classification.**
    For a downward intercept recalibration, positive NRI is equivalent to the
    moved threshold band `(threshold, threshold + δ]` containing a larger
    fraction of non-events than of events. Equivalently, the specificity gain
    exceeds the sensitivity loss. -/
theorem positive_nri_means_improvement
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ) :
    0 < nriFromDownwardInterceptRecalibration μevent μnonevent threshold δ ↔
      thresholdBandRate μevent threshold δ <
        thresholdBandRate μnonevent threshold δ := by
  rw [nriFromDownwardInterceptRecalibration_eq_band_difference
    μevent μnonevent threshold δ]
  constructor <;> intro h <;> linarith

/-- **Outcome prevalence among reclassified patients.**
    Let `π` be the cohort event prevalence. Among the patients moved across the
    decision threshold by a downward intercept recalibration, this is the event
    rate in the moved threshold band `(threshold, threshold + δ]`. -/
noncomputable def reclassifiedBandEventPrevalence
    (π : ℝ)
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ) : ℝ :=
  (π * thresholdBandRate μevent threshold δ) /
    (π * thresholdBandRate μevent threshold δ +
      (1 - π) * thresholdBandRate μnonevent threshold δ)

/-- **Positive NRI means the reclassified band is lower risk than the cohort.**
    For a downward intercept recalibration, positive NRI is equivalent to the
    patients moved from high risk to low risk having event prevalence below the
    overall cohort prevalence `π`. This is the clinically useful interpretation:
    threshold reclassification helps exactly when the patients being moved below
    threshold are genuinely lower risk than the cohort average. -/
theorem positive_nri_iff_reclassifiedBandEventPrevalence_below_cohort_prevalence
    (π : ℝ)
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ)
    (h_pi : 0 < π)
    (h_pi_lt : π < 1)
    (h_band :
      0 < π * thresholdBandRate μevent threshold δ +
          (1 - π) * thresholdBandRate μnonevent threshold δ) :
    0 < nriFromDownwardInterceptRecalibration μevent μnonevent threshold δ ↔
      reclassifiedBandEventPrevalence π μevent μnonevent threshold δ < π := by
  rw [positive_nri_means_improvement μevent μnonevent threshold δ]
  unfold reclassifiedBandEventPrevalence
  constructor
  · intro h
    have h_scale_pos : 0 < π * (1 - π) := by
      nlinarith
    have h_scaled :
        π * (1 - π) * thresholdBandRate μevent threshold δ <
          π * (1 - π) * thresholdBandRate μnonevent threshold δ := by
      exact mul_lt_mul_of_pos_left h h_scale_pos
    rw [div_lt_iff₀ h_band]
    nlinarith [h_scaled]
  · intro h
    have h_cross :
        π * thresholdBandRate μevent threshold δ <
          π *
            (π * thresholdBandRate μevent threshold δ +
              (1 - π) * thresholdBandRate μnonevent threshold δ) := by
      exact (div_lt_iff₀ h_band).1 h
    have h_scale_pos : 0 < π * (1 - π) := by
      nlinarith
    have h_scaled :
        π * (1 - π) * thresholdBandRate μevent threshold δ <
          π * (1 - π) * thresholdBandRate μnonevent threshold δ := by
      nlinarith [h_cross]
    have h_scaled' :
        (π * (1 - π)) * thresholdBandRate μevent threshold δ <
          (π * (1 - π)) * thresholdBandRate μnonevent threshold δ := by
      simpa [mul_assoc] using h_scaled
    nlinarith [h_scaled', h_scale_pos]

/-- **Finite-horizon longitudinal treatment model.**
    `discount t` encodes the time value of health at follow-up time `t`. -/
structure LongitudinalTreatmentModel (T : ℕ) where
  discount : Fin T → ℝ
  discount_nonneg : ∀ t, 0 ≤ discount t

/-- **Individual clinical pathway over a finite horizon.**
    `followupWeight` can encode uncensoring, freedom from competing events,
    adherence, or clinical eligibility at each follow-up time. Treatment
    benefit and harm are allowed to vary across time. -/
structure ClinicalPathway (T : ℕ) where
  followupWeight : Fin T → ℝ
  eventProb : Fin T → ℝ
  treatmentBenefit : Fin T → ℝ
  treatmentHarm : Fin T → ℝ
  followupWeight_nonneg : ∀ t, 0 ≤ followupWeight t

/-- **Per-time discounted QALY contribution under treatment.**
    This is the exact contribution of a treated patient at time `t` under the
    clinical pathway model. -/
noncomputable def qalyContributionAtTime {T : ℕ}
    (model : LongitudinalTreatmentModel T) (path : ClinicalPathway T) (t : Fin T) : ℝ :=
  model.discount t * path.followupWeight t *
    (path.eventProb t * path.treatmentBenefit t - path.treatmentHarm t)

/-- **Net treatment margin of a clinical pathway.**
    Positive margin means treatment is beneficial in expectation after exact
    aggregation over discounted follow-up, treatment heterogeneity, and
    censoring/eligibility weights. -/
noncomputable def treatmentMargin {T : ℕ}
    (model : LongitudinalTreatmentModel T) (path : ClinicalPathway T) : ℝ :=
  Finset.univ.sum (fun t => qalyContributionAtTime model path t)

/-- A deployed rule treats when the predicted pathway has positive net QALY
    margin. -/
def receivesTreatment {T : ℕ}
    (model : LongitudinalTreatmentModel T) (path : ClinicalPathway T) : Prop :=
  0 < treatmentMargin model path

/-- **QALY gain under a predicted-pathway treatment decision.**
    The deployed decision treats iff the predicted pathway implies positive
    net benefit; realized utility is then evaluated under the true pathway. -/
noncomputable def qalyGainUnderDecision {T : ℕ}
    (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) : ℝ :=
  by
    classical
    exact if receivesTreatment model predictedPath then
      treatmentMargin model truePath
    else
      0

/-- **Per-individual QALY loss from using a predicted instead of true pathway.**
    This is exact oracle regret relative to the decision that would be made
    from the patient's true longitudinal pathway. -/
noncomputable def qalyLoss {T : ℕ}
    (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) : ℝ :=
  qalyGainUnderDecision model truePath truePath -
    qalyGainUnderDecision model truePath predictedPath

/-- **Decision-regret margin for longitudinal clinical utility.**
    False positives pay the negative part of the true treatment margin, false
    negatives pay the positive part, and correct decisions pay zero. -/
noncomputable def qalyDecisionRegretMargin {T : ℕ}
    (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) : ℝ :=
  by
    classical
    exact if receivesTreatment model predictedPath then
        max (-treatmentMargin model truePath) 0
      else
        max (treatmentMargin model truePath) 0

/-- Oracle self-decision recovers the positive part of the true treatment
    margin. -/
theorem qalyGainUnderDecision_self_eq_max_treatmentMargin
    {T : ℕ} (model : LongitudinalTreatmentModel T) (path : ClinicalPathway T) :
    qalyGainUnderDecision model path path = max (treatmentMargin model path) 0 := by
  unfold qalyGainUnderDecision receivesTreatment
  by_cases h : 0 < treatmentMargin model path
  · rw [if_pos h, max_eq_left (le_of_lt h)]
  · rw [if_neg h, max_eq_right (not_lt.mp h)]

/-- **QALY loss equals the exact longitudinal decision-regret margin.** -/
theorem qalyLoss_eq_qalyDecisionRegretMargin
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) :
    qalyLoss model truePath predictedPath =
      qalyDecisionRegretMargin model truePath predictedPath := by
  by_cases h_pred : receivesTreatment model predictedPath
  · by_cases h_true : receivesTreatment model truePath
    · have h_true_pos : 0 < treatmentMargin model truePath := h_true
      have h_max : max (-treatmentMargin model truePath) 0 = 0 := by
        exact max_eq_right (by linarith)
      unfold qalyLoss qalyGainUnderDecision qalyDecisionRegretMargin
      rw [if_pos h_true, if_pos h_pred, if_pos h_pred, h_max]
      ring
    · have h_true_nonpos : treatmentMargin model truePath ≤ 0 := not_lt.mp h_true
      have h_max :
          max (-treatmentMargin model truePath) 0 =
            -treatmentMargin model truePath := by
        exact max_eq_left (by linarith)
      unfold qalyLoss qalyGainUnderDecision qalyDecisionRegretMargin
      rw [if_neg h_true, if_pos h_pred, if_pos h_pred, h_max]
      ring
  · by_cases h_true : receivesTreatment model truePath
    · have h_max :
          max (treatmentMargin model truePath) 0 =
            treatmentMargin model truePath := by
        exact max_eq_left (le_of_lt h_true)
      unfold qalyLoss qalyGainUnderDecision qalyDecisionRegretMargin
      rw [if_pos h_true, if_neg h_pred, if_neg h_pred, h_max]
      ring
    · have h_true_nonpos : treatmentMargin model truePath ≤ 0 := not_lt.mp h_true
      have h_max : max (treatmentMargin model truePath) 0 = 0 := by
        exact max_eq_right h_true_nonpos
      unfold qalyLoss qalyGainUnderDecision qalyDecisionRegretMargin
      rw [if_neg h_true, if_neg h_pred, if_neg h_pred, h_max]
      ring

/-- QALY loss is always nonnegative under the longitudinal regret model. -/
theorem qalyLoss_nonneg
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) :
    0 ≤ qalyLoss model truePath predictedPath := by
  rw [qalyLoss_eq_qalyDecisionRegretMargin]
  unfold qalyDecisionRegretMargin
  by_cases h_pred : receivesTreatment model predictedPath
  · rw [if_pos h_pred]
    exact le_max_right _ _
  · rw [if_neg h_pred]
    exact le_max_right _ _

/-- **Perfect pathway calibration implies zero QALY loss.**
    If the predicted pathway induces the same net treatment margin as the true
    pathway, then the deployed treatment decision matches the oracle decision. -/
theorem qalyLoss_eq_zero_of_perfect_pathway_calibration
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (h_cal :
      treatmentMargin model predictedPath =
        treatmentMargin model truePath) :
    qalyLoss model truePath predictedPath = 0 := by
  unfold qalyLoss qalyGainUnderDecision receivesTreatment
  simp [h_cal]

/-- If the deployed and oracle pathway margins induce the same treatment
    decision, the exact QALY regret is zero. -/
theorem qalyLoss_eq_zero_of_same_decision
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (h_decision :
      receivesTreatment model predictedPath ↔
        receivesTreatment model truePath) :
    qalyLoss model truePath predictedPath = 0 := by
  unfold qalyLoss qalyGainUnderDecision
  by_cases h_true : receivesTreatment model truePath
  · have h_pred : receivesTreatment model predictedPath := h_decision.mpr h_true
    rw [if_pos h_true, if_pos h_pred]
    ring
  · have h_pred : ¬ receivesTreatment model predictedPath := by
      intro h_pred
      exact h_true (h_decision.mp h_pred)
    rw [if_neg h_true, if_neg h_pred]
    ring

/-- **A margin error smaller than the true decision margin preserves the
    treatment decision.**
    This is the exact finite-horizon decision-stability criterion under the
    longitudinal pathway model. -/
theorem receivesTreatment_iff_of_margin_error_lt_abs_true_margin
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (h_margin :
      |treatmentMargin model predictedPath - treatmentMargin model truePath| <
        |treatmentMargin model truePath|) :
    receivesTreatment model predictedPath ↔
      receivesTreatment model truePath := by
  unfold receivesTreatment
  set mTrue : ℝ := treatmentMargin model truePath
  set mPred : ℝ := treatmentMargin model predictedPath
  by_cases h_true : 0 < mTrue
  · have h_pred : 0 < mPred := by
      by_cases h_pred_nonpos : mPred ≤ 0
      · have h_abs_eq : |mPred - mTrue| = -(mPred - mTrue) := by
          exact abs_of_nonpos (by linarith)
        have h_true_abs : |mTrue| = mTrue := abs_of_pos h_true
        rw [h_abs_eq, h_true_abs] at h_margin
        linarith
      · linarith
    constructor
    · intro _
      exact h_true
    · intro _
      exact h_pred
  · have h_true_nonpos : mTrue ≤ 0 := not_lt.mp h_true
    have h_pred_nonpos : mPred ≤ 0 := by
      by_cases h_pred : 0 < mPred
      · have h_abs_eq : |mPred - mTrue| = mPred - mTrue := by
          apply abs_of_nonneg
          linarith
        have h_true_abs : |mTrue| = -mTrue := abs_of_nonpos h_true_nonpos
        rw [h_abs_eq, h_true_abs] at h_margin
        linarith
      · exact not_lt.mp h_pred
    constructor
    · intro h_pred
      exact False.elim ((not_lt_of_ge h_pred_nonpos) h_pred)
    · intro h_true'
      exact False.elim ((not_lt_of_ge h_true_nonpos) h_true')

/-- **Exact pathway-margin stability implies zero QALY regret.**
    If the deployed pathway margin error is smaller than the absolute true
    treatment margin, the deployed and oracle treatment decisions coincide. -/
theorem qalyLoss_eq_zero_of_margin_error_lt_abs_true_margin
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (h_margin :
      |treatmentMargin model predictedPath - treatmentMargin model truePath| <
        |treatmentMargin model truePath|) :
    qalyLoss model truePath predictedPath = 0 := by
  apply qalyLoss_eq_zero_of_same_decision
  exact receivesTreatment_iff_of_margin_error_lt_abs_true_margin
    model truePath predictedPath h_margin

/-- **Exact longitudinal QALY regret is bounded by pathway-margin error.**
    This converts miscalibration of the finite-horizon treatment margin into an
    exact utility-loss bound with no surrogate risk approximation. -/
theorem qalyLoss_le_abs_margin_error
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) :
    qalyLoss model truePath predictedPath ≤
      |treatmentMargin model predictedPath - treatmentMargin model truePath| := by
  rw [qalyLoss_eq_qalyDecisionRegretMargin]
  set mTrue : ℝ := treatmentMargin model truePath
  set mPred : ℝ := treatmentMargin model predictedPath
  unfold qalyDecisionRegretMargin receivesTreatment
  change (if 0 < mPred then max (-mTrue) 0 else max mTrue 0) ≤ |mPred - mTrue|
  by_cases h_pred : 0 < mPred
  · rw [if_pos h_pred]
    by_cases h_true : 0 < mTrue
    · have h_max : max (-mTrue) 0 = 0 := by
        exact max_eq_right (by linarith)
      rw [h_max]
      exact abs_nonneg (mPred - mTrue)
    · have h_true_nonpos : mTrue ≤ 0 := not_lt.mp h_true
      have h_max : max (-mTrue) 0 = -mTrue := by
        exact max_eq_left (by linarith)
      have h_abs_eq : |mPred - mTrue| = mPred - mTrue := by
        exact abs_of_nonneg (by linarith)
      rw [h_max, h_abs_eq]
      linarith
  · rw [if_neg h_pred]
    have h_pred_nonpos : mPred ≤ 0 := not_lt.mp h_pred
    by_cases h_true : 0 < mTrue
    · have h_max : max mTrue 0 = mTrue := by
        exact max_eq_left (le_of_lt h_true)
      have h_abs_eq : |mPred - mTrue| = -(mPred - mTrue) := by
        exact abs_of_nonpos (by linarith)
      rw [h_max, h_abs_eq]
      linarith
    · have h_true_nonpos : mTrue ≤ 0 := not_lt.mp h_true
      have h_max : max mTrue 0 = 0 := by
        exact max_eq_right h_true_nonpos
      rw [h_max]
      exact abs_nonneg (mPred - mTrue)

/-- **Exact componentwise decomposition of longitudinal treatment-margin error.**
    This separates the effect of miscalibrating censoring/follow-up weights,
    event risk, heterogeneous treatment benefit, and treatment harm. -/
theorem treatmentMargin_error_eq_componentwise_sum
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) :
    treatmentMargin model predictedPath - treatmentMargin model truePath =
      Finset.univ.sum (fun t =>
        model.discount t *
          ((predictedPath.followupWeight t - truePath.followupWeight t) *
              (truePath.eventProb t * truePath.treatmentBenefit t -
                truePath.treatmentHarm t) +
            predictedPath.followupWeight t *
              ((predictedPath.eventProb t - truePath.eventProb t) *
                  truePath.treatmentBenefit t +
                predictedPath.eventProb t *
                  (predictedPath.treatmentBenefit t -
                    truePath.treatmentBenefit t) -
                (predictedPath.treatmentHarm t - truePath.treatmentHarm t)))) := by
  unfold treatmentMargin qalyContributionAtTime
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro t _
  ring

/-- **Componentwise calibration error bound for longitudinal treatment margin.**
    If the deployed pathway approximates the true censoring/eligibility weights,
    event probabilities, treatment-benefit heterogeneity, and treatment harm
    with bounded error, then the exact finite-horizon treatment-margin error is
    bounded by the corresponding weighted sum of those componentwise errors. -/
theorem abs_treatmentMargin_error_le_componentwise_calibration_bound
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (εWeight εEvent εBenefit εHarm
      weightBound eventBound benefitBound netBound : Fin T → ℝ)
    (h_weight_err : ∀ t,
      |predictedPath.followupWeight t - truePath.followupWeight t| ≤ εWeight t)
    (h_event_err : ∀ t,
      |predictedPath.eventProb t - truePath.eventProb t| ≤ εEvent t)
    (h_benefit_err : ∀ t,
      |predictedPath.treatmentBenefit t - truePath.treatmentBenefit t| ≤ εBenefit t)
    (h_harm_err : ∀ t,
      |predictedPath.treatmentHarm t - truePath.treatmentHarm t| ≤ εHarm t)
    (h_weight_bound : ∀ t, |predictedPath.followupWeight t| ≤ weightBound t)
    (h_event_bound : ∀ t, |predictedPath.eventProb t| ≤ eventBound t)
    (h_benefit_bound : ∀ t, |truePath.treatmentBenefit t| ≤ benefitBound t)
    (h_net_bound : ∀ t,
      |truePath.eventProb t * truePath.treatmentBenefit t -
          truePath.treatmentHarm t| ≤ netBound t) :
    |treatmentMargin model predictedPath - treatmentMargin model truePath| ≤
      Finset.univ.sum (fun t =>
        model.discount t *
          (εWeight t * netBound t +
            weightBound t *
              (εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t))) := by
  rw [treatmentMargin_error_eq_componentwise_sum]
  calc
    |∑ t,
        model.discount t *
          ((predictedPath.followupWeight t - truePath.followupWeight t) *
              (truePath.eventProb t * truePath.treatmentBenefit t -
                truePath.treatmentHarm t) +
            predictedPath.followupWeight t *
              ((predictedPath.eventProb t - truePath.eventProb t) *
                  truePath.treatmentBenefit t +
                predictedPath.eventProb t *
                  (predictedPath.treatmentBenefit t -
                    truePath.treatmentBenefit t) -
                (predictedPath.treatmentHarm t - truePath.treatmentHarm t)))| ≤
        ∑ t,
          |model.discount t *
            ((predictedPath.followupWeight t - truePath.followupWeight t) *
                (truePath.eventProb t * truePath.treatmentBenefit t -
                  truePath.treatmentHarm t) +
              predictedPath.followupWeight t *
                ((predictedPath.eventProb t - truePath.eventProb t) *
                    truePath.treatmentBenefit t +
                  predictedPath.eventProb t *
                    (predictedPath.treatmentBenefit t -
                      truePath.treatmentBenefit t) -
                  (predictedPath.treatmentHarm t - truePath.treatmentHarm t)))| := by
        simpa using Finset.abs_sum_le_sum_abs
          (s := Finset.univ)
          (f := fun t =>
            model.discount t *
              ((predictedPath.followupWeight t - truePath.followupWeight t) *
                  (truePath.eventProb t * truePath.treatmentBenefit t -
                    truePath.treatmentHarm t) +
                predictedPath.followupWeight t *
                  ((predictedPath.eventProb t - truePath.eventProb t) *
                      truePath.treatmentBenefit t +
                    predictedPath.eventProb t *
                      (predictedPath.treatmentBenefit t -
                        truePath.treatmentBenefit t) -
                    (predictedPath.treatmentHarm t - truePath.treatmentHarm t))))
    _ ≤ ∑ t,
        model.discount t *
          (εWeight t * netBound t +
            weightBound t *
              (εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t)) := by
        refine Finset.sum_le_sum ?_
        intro t _
        have hdisc : 0 ≤ model.discount t := model.discount_nonneg t
        have hεWeight_nonneg : 0 ≤ εWeight t := by
          exact le_trans (abs_nonneg _) (h_weight_err t)
        have hεEvent_nonneg : 0 ≤ εEvent t := by
          exact le_trans (abs_nonneg _) (h_event_err t)
        have hεBenefit_nonneg : 0 ≤ εBenefit t := by
          exact le_trans (abs_nonneg _) (h_benefit_err t)
        have hεHarm_nonneg : 0 ≤ εHarm t := by
          exact le_trans (abs_nonneg _) (h_harm_err t)
        have hWeight_nonneg : 0 ≤ weightBound t := by
          exact le_trans (abs_nonneg _) (h_weight_bound t)
        have hEvent_nonneg : 0 ≤ eventBound t := by
          exact le_trans (abs_nonneg _) (h_event_bound t)
        have hBenefit_nonneg : 0 ≤ benefitBound t := by
          exact le_trans (abs_nonneg _) (h_benefit_bound t)
        have hNet_nonneg : 0 ≤ netBound t := by
          exact le_trans (abs_nonneg _) (h_net_bound t)
        have h_term1 :
            |predictedPath.followupWeight t - truePath.followupWeight t| *
                |truePath.eventProb t * truePath.treatmentBenefit t -
                  truePath.treatmentHarm t| ≤
              εWeight t * netBound t := by
          exact mul_le_mul (h_weight_err t) (h_net_bound t)
            (abs_nonneg _) hεWeight_nonneg
        have h_term2a :
            |predictedPath.eventProb t - truePath.eventProb t| *
                |truePath.treatmentBenefit t| ≤
              εEvent t * benefitBound t := by
          exact mul_le_mul (h_event_err t) (h_benefit_bound t)
            (abs_nonneg _) hεEvent_nonneg
        have h_term2b :
            |predictedPath.eventProb t| *
                |predictedPath.treatmentBenefit t - truePath.treatmentBenefit t| ≤
              eventBound t * εBenefit t := by
          exact mul_le_mul (h_event_bound t) (h_benefit_err t)
            (abs_nonneg _) hEvent_nonneg
        have h_nested :
            |(predictedPath.eventProb t - truePath.eventProb t) *
                truePath.treatmentBenefit t +
              predictedPath.eventProb t *
                (predictedPath.treatmentBenefit t -
                  truePath.treatmentBenefit t) -
              (predictedPath.treatmentHarm t - truePath.treatmentHarm t)| ≤
              εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t := by
          have h_split2 :
              |(predictedPath.eventProb t - truePath.eventProb t) *
                  truePath.treatmentBenefit t +
                predictedPath.eventProb t *
                  (predictedPath.treatmentBenefit t -
                    truePath.treatmentBenefit t)| ≤
                |(predictedPath.eventProb t - truePath.eventProb t) *
                    truePath.treatmentBenefit t| +
                  |predictedPath.eventProb t *
                    (predictedPath.treatmentBenefit t -
                      truePath.treatmentBenefit t)| := by
            exact abs_add_le _ _
          calc
            |(predictedPath.eventProb t - truePath.eventProb t) *
                truePath.treatmentBenefit t +
              predictedPath.eventProb t *
                (predictedPath.treatmentBenefit t -
                  truePath.treatmentBenefit t) -
              (predictedPath.treatmentHarm t - truePath.treatmentHarm t)| ≤
                |(predictedPath.eventProb t - truePath.eventProb t) *
                    truePath.treatmentBenefit t| +
                  |predictedPath.eventProb t *
                      (predictedPath.treatmentBenefit t -
                        truePath.treatmentBenefit t)| +
                  |truePath.treatmentHarm t - predictedPath.treatmentHarm t| := by
                    calc
                      |(predictedPath.eventProb t - truePath.eventProb t) *
                          truePath.treatmentBenefit t +
                        predictedPath.eventProb t *
                          (predictedPath.treatmentBenefit t -
                            truePath.treatmentBenefit t) -
                        (predictedPath.treatmentHarm t - truePath.treatmentHarm t)| =
                          |((predictedPath.eventProb t - truePath.eventProb t) *
                              truePath.treatmentBenefit t +
                            predictedPath.eventProb t *
                              (predictedPath.treatmentBenefit t -
                                truePath.treatmentBenefit t)) +
                            (-(predictedPath.treatmentHarm t -
                              truePath.treatmentHarm t))| := by ring
                      _ ≤
                          |(predictedPath.eventProb t - truePath.eventProb t) *
                              truePath.treatmentBenefit t +
                            predictedPath.eventProb t *
                              (predictedPath.treatmentBenefit t -
                                truePath.treatmentBenefit t)| +
                          |truePath.treatmentHarm t -
                              predictedPath.treatmentHarm t| := by
                            simpa [abs_neg, sub_eq_add_neg, add_comm, add_left_comm,
                              add_assoc] using
                              (abs_add_le
                                ((predictedPath.eventProb t - truePath.eventProb t) *
                                  truePath.treatmentBenefit t +
                                  predictedPath.eventProb t *
                                    (predictedPath.treatmentBenefit t -
                                      truePath.treatmentBenefit t))
                                (-(predictedPath.treatmentHarm t -
                                  truePath.treatmentHarm t)))
                      _ ≤
                          (|(predictedPath.eventProb t - truePath.eventProb t) *
                              truePath.treatmentBenefit t| +
                            |predictedPath.eventProb t *
                                (predictedPath.treatmentBenefit t -
                                  truePath.treatmentBenefit t)|) +
                          |truePath.treatmentHarm t - predictedPath.treatmentHarm t| := by
                            linarith
            _ = |predictedPath.eventProb t - truePath.eventProb t| *
                  |truePath.treatmentBenefit t| +
                |predictedPath.eventProb t| *
                  |predictedPath.treatmentBenefit t -
                    truePath.treatmentBenefit t| +
                |predictedPath.treatmentHarm t - truePath.treatmentHarm t| := by
                  rw [abs_mul, abs_mul]
                  have hharm :
                      |truePath.treatmentHarm t - predictedPath.treatmentHarm t| =
                        |predictedPath.treatmentHarm t - truePath.treatmentHarm t| := by
                    exact abs_sub_comm _ _
                  simp [hharm]
            _ ≤ εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t := by
                  have h_term2a' :
                      |truePath.eventProb t - predictedPath.eventProb t| *
                          |truePath.treatmentBenefit t| ≤
                        εEvent t * benefitBound t := by
                    simpa [abs_sub_comm] using h_term2a
                  linarith [h_term2a', h_term2b, h_harm_err t]
        have h_term2 :
            |predictedPath.followupWeight t| *
                |(predictedPath.eventProb t - truePath.eventProb t) *
                    truePath.treatmentBenefit t +
                  predictedPath.eventProb t *
                    (predictedPath.treatmentBenefit t -
                      truePath.treatmentBenefit t) -
                  (predictedPath.treatmentHarm t - truePath.treatmentHarm t)| ≤
              weightBound t *
                (εEvent t * benefitBound t +
                  eventBound t * εBenefit t + εHarm t) := by
          have h_nested_nonneg :
              0 ≤ εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t := by
            nlinarith
              [hεEvent_nonneg, hBenefit_nonneg, hEvent_nonneg,
                hεBenefit_nonneg, hεHarm_nonneg]
          exact mul_le_mul (h_weight_bound t) h_nested
            (abs_nonneg _) hWeight_nonneg
        have h_inner_bound :
            |predictedPath.followupWeight t - truePath.followupWeight t| *
                |truePath.eventProb t * truePath.treatmentBenefit t -
                  truePath.treatmentHarm t| +
              |predictedPath.followupWeight t| *
                |(predictedPath.eventProb t - truePath.eventProb t) *
                    truePath.treatmentBenefit t +
                  predictedPath.eventProb t *
                    (predictedPath.treatmentBenefit t -
                      truePath.treatmentBenefit t) -
                  (predictedPath.treatmentHarm t - truePath.treatmentHarm t)| ≤
              εWeight t * netBound t +
                weightBound t *
                  (εEvent t * benefitBound t +
                    eventBound t * εBenefit t + εHarm t) := by
          linarith [h_term1, h_term2]
        calc
          |model.discount t *
            ((predictedPath.followupWeight t - truePath.followupWeight t) *
                (truePath.eventProb t * truePath.treatmentBenefit t -
                  truePath.treatmentHarm t) +
              predictedPath.followupWeight t *
                ((predictedPath.eventProb t - truePath.eventProb t) *
                    truePath.treatmentBenefit t +
                  predictedPath.eventProb t *
                    (predictedPath.treatmentBenefit t -
                      truePath.treatmentBenefit t) -
                  (predictedPath.treatmentHarm t - truePath.treatmentHarm t)))| =
              model.discount t *
                |(predictedPath.followupWeight t - truePath.followupWeight t) *
                    (truePath.eventProb t * truePath.treatmentBenefit t -
                      truePath.treatmentHarm t) +
                  predictedPath.followupWeight t *
                    ((predictedPath.eventProb t - truePath.eventProb t) *
                        truePath.treatmentBenefit t +
                      predictedPath.eventProb t *
                        (predictedPath.treatmentBenefit t -
                          truePath.treatmentBenefit t) -
                      (predictedPath.treatmentHarm t - truePath.treatmentHarm t))| := by
                rw [abs_mul, abs_of_nonneg hdisc]
          _ ≤ model.discount t *
                (|(predictedPath.followupWeight t - truePath.followupWeight t) *
                    (truePath.eventProb t * truePath.treatmentBenefit t -
                      truePath.treatmentHarm t)| +
                  |predictedPath.followupWeight t *
                    ((predictedPath.eventProb t - truePath.eventProb t) *
                        truePath.treatmentBenefit t +
                      predictedPath.eventProb t *
                        (predictedPath.treatmentBenefit t -
                          truePath.treatmentBenefit t) -
                      (predictedPath.treatmentHarm t - truePath.treatmentHarm t))|) := by
                gcongr
                exact abs_add_le _ _
          _ = model.discount t *
                (|predictedPath.followupWeight t - truePath.followupWeight t| *
                    |truePath.eventProb t * truePath.treatmentBenefit t -
                      truePath.treatmentHarm t| +
                  |predictedPath.followupWeight t| *
                    |(predictedPath.eventProb t - truePath.eventProb t) *
                        truePath.treatmentBenefit t +
                      predictedPath.eventProb t *
                        (predictedPath.treatmentBenefit t -
                          truePath.treatmentBenefit t) -
                      (predictedPath.treatmentHarm t - truePath.treatmentHarm t)|) := by
                rw [abs_mul, abs_mul]
          _ ≤ model.discount t *
                (εWeight t * netBound t +
                  weightBound t *
                    (εEvent t * benefitBound t +
                      eventBound t * εBenefit t + εHarm t)) := by
                exact mul_le_mul_of_nonneg_left h_inner_bound hdisc

/-- **Exact longitudinal QALY-loss bound from calibration errors in the event
    process, heterogeneous treatment effects, harms, and censoring weights.** -/
theorem qalyLoss_le_componentwise_calibration_bound
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (εWeight εEvent εBenefit εHarm
      weightBound eventBound benefitBound netBound : Fin T → ℝ)
    (h_weight_err : ∀ t,
      |predictedPath.followupWeight t - truePath.followupWeight t| ≤ εWeight t)
    (h_event_err : ∀ t,
      |predictedPath.eventProb t - truePath.eventProb t| ≤ εEvent t)
    (h_benefit_err : ∀ t,
      |predictedPath.treatmentBenefit t - truePath.treatmentBenefit t| ≤ εBenefit t)
    (h_harm_err : ∀ t,
      |predictedPath.treatmentHarm t - truePath.treatmentHarm t| ≤ εHarm t)
    (h_weight_bound : ∀ t, |predictedPath.followupWeight t| ≤ weightBound t)
    (h_event_bound : ∀ t, |predictedPath.eventProb t| ≤ eventBound t)
    (h_benefit_bound : ∀ t, |truePath.treatmentBenefit t| ≤ benefitBound t)
    (h_net_bound : ∀ t,
      |truePath.eventProb t * truePath.treatmentBenefit t -
          truePath.treatmentHarm t| ≤ netBound t) :
    qalyLoss model truePath predictedPath ≤
      Finset.univ.sum (fun t =>
        model.discount t *
          (εWeight t * netBound t +
            weightBound t *
              (εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t))) := by
  exact le_trans (qalyLoss_le_abs_margin_error model truePath predictedPath)
    (abs_treatmentMargin_error_le_componentwise_calibration_bound
      model truePath predictedPath εWeight εEvent εBenefit εHarm
      weightBound eventBound benefitBound netBound
      h_weight_err h_event_err h_benefit_err h_harm_err
      h_weight_bound h_event_bound h_benefit_bound h_net_bound)

/-- **If componentwise pathway calibration error is smaller than the true
    longitudinal treatment margin, the deployed and oracle clinical decisions
    coincide exactly and QALY regret vanishes.** -/
theorem qalyLoss_eq_zero_of_componentwise_calibration_bound_lt_abs_true_margin
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (εWeight εEvent εBenefit εHarm
      weightBound eventBound benefitBound netBound : Fin T → ℝ)
    (h_weight_err : ∀ t,
      |predictedPath.followupWeight t - truePath.followupWeight t| ≤ εWeight t)
    (h_event_err : ∀ t,
      |predictedPath.eventProb t - truePath.eventProb t| ≤ εEvent t)
    (h_benefit_err : ∀ t,
      |predictedPath.treatmentBenefit t - truePath.treatmentBenefit t| ≤ εBenefit t)
    (h_harm_err : ∀ t,
      |predictedPath.treatmentHarm t - truePath.treatmentHarm t| ≤ εHarm t)
    (h_weight_bound : ∀ t, |predictedPath.followupWeight t| ≤ weightBound t)
    (h_event_bound : ∀ t, |predictedPath.eventProb t| ≤ eventBound t)
    (h_benefit_bound : ∀ t, |truePath.treatmentBenefit t| ≤ benefitBound t)
    (h_net_bound : ∀ t,
      |truePath.eventProb t * truePath.treatmentBenefit t -
          truePath.treatmentHarm t| ≤ netBound t)
    (h_small :
      Finset.univ.sum (fun t =>
        model.discount t *
          (εWeight t * netBound t +
            weightBound t *
              (εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t))) <
        |treatmentMargin model truePath|) :
    qalyLoss model truePath predictedPath = 0 := by
  apply qalyLoss_eq_zero_of_margin_error_lt_abs_true_margin
  exact lt_of_le_of_lt
    (abs_treatmentMargin_error_le_componentwise_calibration_bound
      model truePath predictedPath εWeight εEvent εBenefit εHarm
      weightBound eventBound benefitBound netBound
      h_weight_err h_event_err h_benefit_err h_harm_err
      h_weight_bound h_event_bound h_benefit_bound h_net_bound)
    h_small

/-- **Expected QALY loss from pathway miscalibration.**
    This is the population expectation of exact oracle regret under the
    longitudinal pathway model. -/
noncomputable def expectedQalyLoss {Z : Type*} [MeasurableSpace Z] {T : ℕ}
    (μ : Measure Z) (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : Z → ClinicalPathway T) : ℝ :=
  ∫ z, qalyLoss model (truePath z) (predictedPath z) ∂μ

/-- Perfect pathway calibration implies zero expected QALY loss. -/
theorem expectedQalyLoss_eq_zero_of_perfect_pathway_calibration
    {Z : Type*} [MeasurableSpace Z] {T : ℕ}
    (μ : Measure Z) (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : Z → ClinicalPathway T)
    (h_cal : ∀ z,
      treatmentMargin model (predictedPath z) =
        treatmentMargin model (truePath z)) :
    expectedQalyLoss μ model truePath predictedPath = 0 := by
  unfold expectedQalyLoss
  have hfun :
      (fun z => qalyLoss model (truePath z) (predictedPath z)) =
        fun _ => (0 : ℝ) := by
    funext z
    exact qalyLoss_eq_zero_of_perfect_pathway_calibration
      model (truePath z) (predictedPath z) (h_cal z)
  rw [hfun]
  simp

/-- **Expected QALY loss equals expected longitudinal decision regret.** -/
theorem expectedQalyLoss_eq_expected_qalyDecisionRegretMargin
    {Z : Type*} [MeasurableSpace Z] {T : ℕ}
    (μ : Measure Z) (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : Z → ClinicalPathway T) :
    expectedQalyLoss μ model truePath predictedPath =
      ∫ z, qalyDecisionRegretMargin model (truePath z) (predictedPath z) ∂μ := by
  unfold expectedQalyLoss
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z =>
    qalyLoss_eq_qalyDecisionRegretMargin
      model (truePath z) (predictedPath z))

/-- Shared one-step screening decision interface.
    `threshold` is the risk cutoff used by the policy, `benefit` is the utility
    of a true-positive treatment, and `harm` is the utility cost of a
    false-positive treatment. -/
structure ScreeningDecisionModel where
  threshold : ℝ
  benefit : ℝ
  harm : ℝ

/-- One-step longitudinal embedding of the shared screening model. -/
noncomputable def screeningLongitudinalModel
    (_model : ScreeningDecisionModel) : LongitudinalTreatmentModel 1 where
  discount := fun _ => 1
  discount_nonneg := by
    intro _
    norm_num

/-- One-step clinical pathway induced by a scalar event risk under the shared
    screening model. A treated event yields utility `benefit`, a treated
    non-event yields utility `-harm`, and no treatment yields `0`. -/
noncomputable def screeningClinicalPathway
    (model : ScreeningDecisionModel) (risk : ℝ) : ClinicalPathway 1 where
  followupWeight := fun _ => 1
  eventProb := fun _ => risk
  treatmentBenefit := fun _ => model.benefit + model.harm
  treatmentHarm := fun _ => model.harm
  followupWeight_nonneg := by
    intro _
    norm_num

/-- If the screening-model utility ratio matches the decision threshold, the
    one-step treatment margin is exactly `(benefit + harm) × (risk - threshold)`.
    This is the shared bridge from policy thresholding to exact pathway utility. -/
theorem treatmentMargin_screeningClinicalPathway
    (model : ScreeningDecisionModel) (risk : ℝ)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm)) :
    treatmentMargin (screeningLongitudinalModel model)
      (screeningClinicalPathway model risk) =
        (model.benefit + model.harm) * (risk - model.threshold) := by
  unfold treatmentMargin qalyContributionAtTime
    screeningLongitudinalModel screeningClinicalPathway
  rw [Fin1_sum_eq]
  dsimp
  norm_num
  nlinarith

/-- Under the exact threshold/utility relation, the shared screening model
    treats exactly when the input risk exceeds the policy threshold. -/
theorem receivesTreatment_screeningClinicalPathway_iff
    (model : ScreeningDecisionModel) (risk : ℝ)
    (h_total_pos : 0 < model.benefit + model.harm)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm)) :
    receivesTreatment (screeningLongitudinalModel model)
      (screeningClinicalPathway model risk) ↔
        classifiedHighRisk model.threshold risk := by
  unfold receivesTreatment classifiedHighRisk
  rw [treatmentMargin_screeningClinicalPathway model risk h_threshold]
  constructor <;> intro h <;> nlinarith

/-- Count-based expected screening utility on a per-person scale. -/
noncomputable def screeningUtilityFromCounts
    (model : ScreeningDecisionModel) (tp fp n : ℝ) : ℝ :=
  model.benefit * (tp / n) - model.harm * (fp / n)

/-- Rate-based expected screening utility on a per-person scale. -/
noncomputable def screeningUtilityFromRates
    (model : ScreeningDecisionModel) (sens spec prevalence : ℝ) : ℝ :=
  sens * prevalence * model.benefit -
    (1 - spec) * (1 - prevalence) * model.harm

/-- The count-based and rate-based screening utilities agree when true- and
    false-positive counts are instantiated from sensitivity, specificity,
    prevalence, and sample size. -/
theorem screeningUtilityFromCounts_eq_screeningUtilityFromRates
    (model : ScreeningDecisionModel)
    (sens spec prevalence n : ℝ)
    (h_n : 0 < n) :
    screeningUtilityFromCounts model
        (sens * prevalence * n)
        ((1 - spec) * (1 - prevalence) * n) n =
      screeningUtilityFromRates model sens spec prevalence := by
  unfold screeningUtilityFromCounts screeningUtilityFromRates
  field_simp [ne_of_gt h_n]

/-- Treating an event under the shared screening model yields exactly the
    model's true-positive utility. -/
theorem qalyGainUnderDecision_screening_case_treat
    (model : ScreeningDecisionModel) (decisionRisk : ℝ)
    (h_total_pos : 0 < model.benefit + model.harm)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm))
    (h_decision : classifiedHighRisk model.threshold decisionRisk) :
    qalyGainUnderDecision (screeningLongitudinalModel model)
      (screeningClinicalPathway model 1)
      (screeningClinicalPathway model decisionRisk) =
        model.benefit := by
  have h_treat :
      receivesTreatment (screeningLongitudinalModel model)
        (screeningClinicalPathway model decisionRisk) := by
    exact (receivesTreatment_screeningClinicalPathway_iff
      model decisionRisk h_total_pos h_threshold).2 h_decision
  unfold qalyGainUnderDecision
  rw [if_pos h_treat, treatmentMargin_screeningClinicalPathway model 1 h_threshold]
  nlinarith

/-- Treating a non-event under the shared screening model yields exactly the
    model's false-positive utility cost. -/
theorem qalyGainUnderDecision_screening_control_treat
    (model : ScreeningDecisionModel) (decisionRisk : ℝ)
    (h_total_pos : 0 < model.benefit + model.harm)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm))
    (h_decision : classifiedHighRisk model.threshold decisionRisk) :
    qalyGainUnderDecision (screeningLongitudinalModel model)
      (screeningClinicalPathway model 0)
      (screeningClinicalPathway model decisionRisk) =
        -model.harm := by
  have h_treat :
      receivesTreatment (screeningLongitudinalModel model)
        (screeningClinicalPathway model decisionRisk) := by
    exact (receivesTreatment_screeningClinicalPathway_iff
      model decisionRisk h_total_pos h_threshold).2 h_decision
  unfold qalyGainUnderDecision
  rw [if_pos h_treat, treatmentMargin_screeningClinicalPathway model 0 h_threshold]
  nlinarith

/-- If the shared screening policy does not treat, realized utility is zero for
    both events and non-events. -/
theorem qalyGainUnderDecision_screening_no_treat
    (model : ScreeningDecisionModel) (trueRisk decisionRisk : ℝ)
    (h_total_pos : 0 < model.benefit + model.harm)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm))
    (h_not_decision : ¬ classifiedHighRisk model.threshold decisionRisk) :
    qalyGainUnderDecision (screeningLongitudinalModel model)
      (screeningClinicalPathway model trueRisk)
      (screeningClinicalPathway model decisionRisk) =
        0 := by
  have h_not_treat :
      ¬ receivesTreatment (screeningLongitudinalModel model)
        (screeningClinicalPathway model decisionRisk) := by
    intro h_treat
    exact h_not_decision
      ((receivesTreatment_screeningClinicalPathway_iff
        model decisionRisk h_total_pos h_threshold).1 h_treat)
  unfold qalyGainUnderDecision
  simp [h_not_treat]

/-- Canonical screening model behind the cost-effectiveness section:
    the policy threshold is exactly `harm / (benefit + harm)`. -/
noncomputable def qalyScreeningDecisionModel
    (benefit harm : ℝ) : ScreeningDecisionModel where
  threshold := harm / (benefit + harm)
  benefit := benefit
  harm := harm

/-- The canonical cost-effectiveness screening model satisfies the exact
    threshold/utility bridge equation. -/
theorem qalyScreeningDecisionModel_harm_eq_threshold_scale
    (benefit harm : ℝ)
    (h_total : benefit + harm ≠ 0) :
    (qalyScreeningDecisionModel benefit harm).harm =
      (qalyScreeningDecisionModel benefit harm).threshold *
        ((qalyScreeningDecisionModel benefit harm).benefit +
          (qalyScreeningDecisionModel benefit harm).harm) := by
  unfold qalyScreeningDecisionModel
  field_simp [h_total]

/-- The canonical QALY-style screening model has positive total utility scale
    whenever benefit and harm are both positive. -/
theorem qalyScreeningDecisionModel_total_pos
    (benefit harm : ℝ)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm) :
    0 <
      (qalyScreeningDecisionModel benefit harm).benefit +
        (qalyScreeningDecisionModel benefit harm).harm := by
  unfold qalyScreeningDecisionModel
  linarith

/-- Canonical QALY-style screening utility on operating-point rates. -/
noncomputable def screeningQalyGain
    (sens spec prevalence benefit harm : ℝ) : ℝ :=
  screeningUtilityFromRates (qalyScreeningDecisionModel benefit harm)
    sens spec prevalence

/-- The canonical screening-QALY utility is exactly the familiar
    `sens × π × benefit − (1−spec) × (1−π) × harm` formula. -/
theorem screeningQalyGain_eq_formula
    (sens spec prevalence benefit harm : ℝ) :
    screeningQalyGain sens spec prevalence benefit harm =
      sens * prevalence * benefit -
        (1 - spec) * (1 - prevalence) * harm := by
  unfold screeningQalyGain screeningUtilityFromRates qalyScreeningDecisionModel
  ring

/-- Canonical decision-curve screening model: benefit is normalized to `1` and
    false-positive harm is the usual decision-curve odds weight `t / (1-t)`. -/
noncomputable def decisionCurveScreeningModel
    (t : ℝ) : ScreeningDecisionModel where
  threshold := t
  benefit := 1
  harm := t / (1 - t)

/-- The decision-curve screening model satisfies the exact threshold/utility
    bridge equation whenever `t ≠ 1`. -/
theorem decisionCurveScreeningModel_harm_eq_threshold_scale
    (t : ℝ) (h_t : t ≠ 1) :
    (decisionCurveScreeningModel t).harm =
      (decisionCurveScreeningModel t).threshold *
        ((decisionCurveScreeningModel t).benefit +
          (decisionCurveScreeningModel t).harm) := by
  unfold decisionCurveScreeningModel
  have h_one_sub : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm h_t)
  field_simp [h_one_sub]
  ring

/-- The decision-curve screening model has positive total utility scale in the
    standard regime `0 < t < 1`. -/
theorem decisionCurveScreeningModel_total_pos
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 <
      (decisionCurveScreeningModel t).benefit +
        (decisionCurveScreeningModel t).harm := by
  unfold decisionCurveScreeningModel
  have h_one_sub : 0 < 1 - t := by linarith
  have h_div : 0 < t / (1 - t) := div_pos ht h_one_sub
  linarith

/-- Canonical decision-curve net benefit on a per-person scale. -/
noncomputable def decisionCurveNetBenefit
    (tp fp n t : ℝ) : ℝ :=
  screeningUtilityFromCounts (decisionCurveScreeningModel t) tp fp n

/-- The canonical decision-curve net benefit is exactly the usual
    `TP/N − FP/N × t/(1−t)` expression. -/
theorem decisionCurveNetBenefit_eq_formula
    (tp fp n t : ℝ) :
    decisionCurveNetBenefit tp fp n t =
      tp / n - fp / n * (t / (1 - t)) := by
  unfold decisionCurveNetBenefit screeningUtilityFromCounts
    decisionCurveScreeningModel
  ring

/-- **Clinical treatment model induced by a decision threshold.**
    This is the exact one-time specialization of the longitudinal pathway model
    in which treatment yields benefit `benefit × trueRisk` in expectation and
    incurs harm `harm` whenever given. The clinically optimal threshold is
    therefore `harm / benefit`; we encode this exactly as
    `harm = benefit × threshold`. -/
structure ThresholdTreatmentModel where
  threshold : ℝ
  benefit : ℝ
  harm : ℝ
  benefit_pos : 0 < benefit
  harm_eq_threshold : harm = benefit * threshold

/-- One-step longitudinal model corresponding to a single threshold-based
    treatment decision. -/
noncomputable def thresholdLongitudinalModel
    (_model : ThresholdTreatmentModel) : LongitudinalTreatmentModel 1 where
  discount := fun _ => 1
  discount_nonneg := by
    intro _
    norm_num

/-- One-step clinical pathway induced by a scalar risk under the threshold
    treatment model. -/
noncomputable def thresholdClinicalPathway
    (model : ThresholdTreatmentModel) (risk : ℝ) : ClinicalPathway 1 where
  followupWeight := fun _ => 1
  eventProb := fun _ => risk
  treatmentBenefit := fun _ => model.benefit
  treatmentHarm := fun _ => model.harm
  followupWeight_nonneg := by
    intro _
    norm_num

/-- The exact one-step treatment margin is benefit times risk above threshold. -/
theorem treatmentMargin_thresholdClinicalPathway
    (model : ThresholdTreatmentModel) (risk : ℝ) :
    treatmentMargin (thresholdLongitudinalModel model)
      (thresholdClinicalPathway model risk) =
        model.benefit * (risk - model.threshold) := by
  unfold treatmentMargin qalyContributionAtTime
    thresholdLongitudinalModel thresholdClinicalPathway
  rw [Fin1_sum_eq]
  simp [model.harm_eq_threshold]
  ring

/-- In the one-step specialization, positive treatment margin is exactly the
    high-risk classification event. -/
theorem receivesTreatment_thresholdClinicalPathway_iff
    (model : ThresholdTreatmentModel) (risk : ℝ) :
    receivesTreatment (thresholdLongitudinalModel model)
      (thresholdClinicalPathway model risk) ↔
        classifiedHighRisk model.threshold risk := by
  unfold receivesTreatment classifiedHighRisk
  rw [treatmentMargin_thresholdClinicalPathway]
  constructor <;> intro h <;> nlinarith [model.benefit_pos]

/-- **Threshold-based QALY gain under a scalar risk decision.**
    The deployed system treats when the risk used for decision-making exceeds
    the clinical treatment threshold. -/
noncomputable def thresholdQalyGainUnderDecision
    (model : ThresholdTreatmentModel) (trueRisk decisionRisk : ℝ) : ℝ :=
  if _ : model.threshold < decisionRisk then
      model.benefit * trueRisk - model.harm
    else
      0

/-- **Per-individual one-step QALY loss from using predicted instead of true
    risk.** This is the threshold-rule specialization of `qalyLoss`. -/
noncomputable def thresholdQalyLoss
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) : ℝ :=
  thresholdQalyGainUnderDecision model trueRisk trueRisk -
    thresholdQalyGainUnderDecision model trueRisk predictedRisk

/-- **Threshold-decision regret margin.**
    This is the clinically relevant risk margin by which the deployed decision
    disagrees with the oracle threshold rule:
    - false positives pay `threshold - trueRisk`,
    - false negatives pay `trueRisk - threshold`,
    - correct decisions pay `0`. -/
noncomputable def thresholdDecisionRegretMargin
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) : ℝ :=
  by
    classical
    exact if classifiedHighRisk model.threshold predictedRisk then
        max (model.threshold - trueRisk) 0
      else
        max (trueRisk - model.threshold) 0

/-- The threshold one-step gain is exactly the general pathway gain under the
    threshold specialization. -/
theorem qalyGainUnderDecision_threshold_eq_thresholdQalyGainUnderDecision
    (model : ThresholdTreatmentModel) (trueRisk decisionRisk : ℝ) :
    qalyGainUnderDecision (thresholdLongitudinalModel model)
      (thresholdClinicalPathway model trueRisk)
      (thresholdClinicalPathway model decisionRisk) =
        thresholdQalyGainUnderDecision model trueRisk decisionRisk := by
  by_cases h : model.threshold < decisionRisk
  · have h_treat :
        receivesTreatment (thresholdLongitudinalModel model)
          (thresholdClinicalPathway model decisionRisk) := by
      exact (receivesTreatment_thresholdClinicalPathway_iff model decisionRisk).2 h
    unfold qalyGainUnderDecision
    rw [if_pos h_treat, treatmentMargin_thresholdClinicalPathway]
    simp [thresholdQalyGainUnderDecision, h, model.harm_eq_threshold]
    ring
  · have h_not_treat :
        ¬ receivesTreatment (thresholdLongitudinalModel model)
          (thresholdClinicalPathway model decisionRisk) := by
      exact fun h_treat =>
        h ((receivesTreatment_thresholdClinicalPathway_iff model decisionRisk).1 h_treat)
    unfold qalyGainUnderDecision
    rw [if_neg h_not_treat]
    simp [thresholdQalyGainUnderDecision, h]

/-- The threshold one-step loss is exactly the general pathway loss under the
    threshold specialization. -/
theorem qalyLoss_threshold_eq_thresholdQalyLoss
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) :
    qalyLoss (thresholdLongitudinalModel model)
      (thresholdClinicalPathway model trueRisk)
      (thresholdClinicalPathway model predictedRisk) =
        thresholdQalyLoss model trueRisk predictedRisk := by
  unfold qalyLoss thresholdQalyLoss
  rw [qalyGainUnderDecision_threshold_eq_thresholdQalyGainUnderDecision,
    qalyGainUnderDecision_threshold_eq_thresholdQalyGainUnderDecision]

/-- **Exact QALY loss for a false positive treatment decision.**
    If the patient's true risk is below threshold but the predicted risk is
    above threshold, the loss equals the treatment benefit scale times the
    distance from the true risk to the treatment threshold. -/
theorem thresholdQalyLoss_false_positive_exact
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ)
    (h_true_low : trueRisk ≤ model.threshold)
    (h_pred_high : classifiedHighRisk model.threshold predictedRisk) :
    thresholdQalyLoss model trueRisk predictedRisk =
      model.benefit * (model.threshold - trueRisk) := by
  have h_true_not_high : ¬ model.threshold < trueRisk := not_lt.mpr h_true_low
  have h_pred_high' : model.threshold < predictedRisk := by
    simpa [classifiedHighRisk] using h_pred_high
  unfold thresholdQalyLoss thresholdQalyGainUnderDecision
  simp [h_true_not_high, h_pred_high', model.harm_eq_threshold]
  ring_nf

/-- **Exact QALY loss for a false negative treatment decision.**
    If the patient's true risk is above threshold but the predicted risk is
    at or below threshold, the loss equals the missed-treatment margin above
    threshold on the QALY-benefit scale. -/
theorem thresholdQalyLoss_false_negative_exact
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ)
    (h_true_high : model.threshold < trueRisk)
    (h_pred_not_high : ¬ classifiedHighRisk model.threshold predictedRisk) :
    thresholdQalyLoss model trueRisk predictedRisk =
      model.benefit * (trueRisk - model.threshold) := by
  have h_pred_not_high' : ¬ model.threshold < predictedRisk := by
    simpa [classifiedHighRisk] using h_pred_not_high
  unfold thresholdQalyLoss thresholdQalyGainUnderDecision
  simp [h_true_high, h_pred_not_high', model.harm_eq_threshold]
  ring_nf

/-- **Threshold QALY loss equals benefit-scaled threshold-decision regret.**
    This is the exact one-step specialization of the general longitudinal QALY
    regret model. -/
theorem thresholdQalyLoss_eq_benefit_mul_thresholdDecisionRegretMargin
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) :
    thresholdQalyLoss model trueRisk predictedRisk =
      model.benefit * thresholdDecisionRegretMargin model trueRisk predictedRisk := by
  by_cases h_pred : classifiedHighRisk model.threshold predictedRisk
  · by_cases h_true_low : trueRisk ≤ model.threshold
    · unfold thresholdDecisionRegretMargin
      rw [if_pos h_pred]
      rw [thresholdQalyLoss_false_positive_exact model trueRisk predictedRisk h_true_low h_pred]
      have hmax : max (model.threshold - trueRisk) 0 = model.threshold - trueRisk := by
        exact max_eq_left (by linarith)
      rw [hmax]
    · have h_true_high : model.threshold < trueRisk := by linarith
      have h_pred_high' : model.threshold < predictedRisk := by
        simpa [classifiedHighRisk] using h_pred
      have h_zero : thresholdQalyLoss model trueRisk predictedRisk = 0 := by
        unfold thresholdQalyLoss thresholdQalyGainUnderDecision
        simp [h_true_high, h_pred_high', model.harm_eq_threshold]
      unfold thresholdDecisionRegretMargin
      rw [if_pos h_pred]
      rw [h_zero]
      have hmax : max (model.threshold - trueRisk) 0 = 0 := by
        exact max_eq_right (by linarith)
      rw [hmax]
      ring
  · by_cases h_true_high : model.threshold < trueRisk
    · unfold thresholdDecisionRegretMargin
      rw [if_neg h_pred]
      rw [thresholdQalyLoss_false_negative_exact model trueRisk predictedRisk h_true_high h_pred]
      have hmax : max (trueRisk - model.threshold) 0 = trueRisk - model.threshold := by
        exact max_eq_left (by linarith)
      rw [hmax]
    · have h_true_low : trueRisk ≤ model.threshold := by linarith
      have h_pred_not_high' : ¬ model.threshold < predictedRisk := by
        simpa [classifiedHighRisk] using h_pred
      have h_zero : thresholdQalyLoss model trueRisk predictedRisk = 0 := by
        unfold thresholdQalyLoss thresholdQalyGainUnderDecision
        simp [h_true_high, h_pred_not_high']
      unfold thresholdDecisionRegretMargin
      rw [if_neg h_pred]
      rw [h_zero]
      have hmax : max (trueRisk - model.threshold) 0 = 0 := by
        exact max_eq_right (by linarith)
      rw [hmax]
      ring

/-- Threshold-specialized QALY loss is always nonnegative. -/
theorem thresholdQalyLoss_nonneg
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) :
    0 ≤ thresholdQalyLoss model trueRisk predictedRisk := by
  rw [thresholdQalyLoss_eq_benefit_mul_thresholdDecisionRegretMargin]
  have h_margin_nonneg :
      0 ≤ thresholdDecisionRegretMargin model trueRisk predictedRisk := by
    unfold thresholdDecisionRegretMargin
    by_cases h_pred : classifiedHighRisk model.threshold predictedRisk
    · rw [if_pos h_pred]
      exact le_max_right _ _
    · rw [if_neg h_pred]
      exact le_max_right _ _
  exact mul_nonneg model.benefit_pos.le h_margin_nonneg

/-- **Threshold-specialized QALY loss is zero under perfect calibration at the
    decision point.** -/
theorem thresholdQalyLoss_eq_zero_of_perfect_calibration
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ)
    (h_cal : predictedRisk = trueRisk) :
    thresholdQalyLoss model trueRisk predictedRisk = 0 := by
  subst h_cal
  unfold thresholdQalyLoss
  ring

/-- **Miscalibration-induced overtreatment has an exact threshold QALY cost.**
    A positive intercept shift that pushes a truly low-risk patient above the
    treatment threshold creates a false positive treatment decision, and the
    resulting regret is exactly the false-positive QALY loss. -/
theorem miscalibration_induced_false_positive_qaly_loss
    (model : ThresholdTreatmentModel) (trueRisk c : ℝ)
    (h_truly_low : trueRisk < model.threshold)
    (h_miscal : model.threshold - trueRisk < c) :
    thresholdQalyLoss model trueRisk (trueRisk + c) =
      model.benefit * (model.threshold - trueRisk) := by
  have h_decision :=
    miscalibration_changes_decisions trueRisk model.threshold c h_truly_low h_miscal
  exact thresholdQalyLoss_false_positive_exact
    model trueRisk (trueRisk + c) (le_of_lt h_truly_low) h_decision.2

/-- **Expected threshold-specialized QALY loss from miscalibration.** -/
noncomputable def expectedThresholdQalyLoss {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ) : ℝ :=
  ∫ z, thresholdQalyLoss model (trueRisk z) (predictedRisk z) ∂μ

/-- The expected loss under the threshold specialization agrees exactly with
    the general pathway expected loss. -/
theorem expectedQalyLoss_threshold_eq_expectedThresholdQalyLoss
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ) :
    expectedQalyLoss μ (thresholdLongitudinalModel model)
      (fun z => thresholdClinicalPathway model (trueRisk z))
      (fun z => thresholdClinicalPathway model (predictedRisk z)) =
        expectedThresholdQalyLoss μ model trueRisk predictedRisk := by
  unfold expectedQalyLoss expectedThresholdQalyLoss
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z =>
    qalyLoss_threshold_eq_thresholdQalyLoss
      model (trueRisk z) (predictedRisk z))

/-- Perfect calibration implies zero expected threshold-specialized QALY loss. -/
theorem expectedThresholdQalyLoss_eq_zero_of_perfect_calibration
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ)
    (h_cal : ∀ z, predictedRisk z = trueRisk z) :
    expectedThresholdQalyLoss μ model trueRisk predictedRisk = 0 := by
  unfold expectedThresholdQalyLoss
  have hfun :
      (fun z => thresholdQalyLoss model (trueRisk z) (predictedRisk z)) =
        fun _ => (0 : ℝ) := by
    funext z
    exact thresholdQalyLoss_eq_zero_of_perfect_calibration
      model (trueRisk z) (predictedRisk z) (h_cal z)
  rw [hfun]
  simp

/-- **Expected threshold-specialized QALY loss is the expected
    threshold-decision regret.** -/
theorem expectedThresholdQalyLoss_eq_expected_thresholdDecisionRegret
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ) :
    expectedThresholdQalyLoss μ model trueRisk predictedRisk =
      ∫ z, model.benefit *
        thresholdDecisionRegretMargin model (trueRisk z) (predictedRisk z) ∂μ := by
  unfold expectedThresholdQalyLoss
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z =>
    thresholdQalyLoss_eq_benefit_mul_thresholdDecisionRegretMargin
      model (trueRisk z) (predictedRisk z))

end DecisionImplications

end Calibrator
