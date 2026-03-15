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

/-- **Cross-ancestry AUC drops while calibration-in-the-large worsens.**
    This theorem states the claim on the repository's actual metrics:

    - discrimination is measured by observable transport AUC;
    - calibration is measured by absolute calibration-in-the-large.

    Under positive drift (`fstTarget > fstSource`), the transported target
    AUC is strictly below the source AUC. If the source is calibrated in the
    large but target prevalence differs, then absolute CITL is strictly larger
    in the target. -/
theorem cross_ancestry_auc_and_citl_worsen
    (r2Source fstSource fstTarget mean_pred πSource πTarget : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (h_src_cal : calibrationInTheLarge πSource mean_pred = 0)
    (h_prev_shift : πSource ≠ πTarget)
    (hPhiStrict : StrictMono Phi) :
    targetExactLiabilityAUC r2Source fstSource fstTarget <
      sourceExactLiabilityAUC r2Source ∧
    |calibrationInTheLarge πSource mean_pred| <
      |calibrationInTheLarge πTarget mean_pred| := by
  constructor
  · exact targetLiabilityAUC_lt_source_of_observables
      r2Source fstSource fstTarget h_r2 h_fst h_fst_bounds hPhiStrict
  · have h_citl_shift :
        calibrationInTheLarge πTarget mean_pred -
          calibrationInTheLarge πSource mean_pred = πTarget - πSource :=
      prevalence_shift_changes_calibration mean_pred πSource πTarget
    have h_tgt_eq :
        calibrationInTheLarge πTarget mean_pred = πTarget - πSource := by
      linarith [h_citl_shift, h_src_cal]
    have h_tgt_ne_zero : calibrationInTheLarge πTarget mean_pred ≠ 0 := by
      intro h_tgt_zero
      apply h_prev_shift
      linarith [h_tgt_eq, h_tgt_zero]
    have h_tgt_abs_pos : 0 < |calibrationInTheLarge πTarget mean_pred| :=
      abs_pos.mpr h_tgt_ne_zero
    simpa [h_src_cal] using h_tgt_abs_pos

/-- **Cross-ancestry AUC drops while Brier worsens.**
    `AUC` measures discrimination, while `Brier` is the standard proper scoring
    rule carried by the observable drift model. Under positive drift, the target
    AUC is strictly lower and the target Brier score is strictly higher. -/
theorem cross_ancestry_auc_and_brier_worsen
    (π r2Source fstSource fstTarget : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (hPhiStrict : StrictMono Phi) :
    targetExactLiabilityAUC r2Source fstSource fstTarget <
      sourceExactLiabilityAUC r2Source ∧
    sourceExactCalibratedBrierRisk π r2Source <
      targetExactCalibratedBrierRisk π r2Source fstSource fstTarget := by
  constructor
  · exact targetLiabilityAUC_lt_source_of_observables
      r2Source fstSource fstTarget h_r2 h_fst h_fst_bounds hPhiStrict
  · exact targetBrier_strict_gt_source_of_observables π r2Source fstSource fstTarget
      hπ0 hπ1 h_r2 h_fst h_fst_bounds

end CalibrationVsDiscrimination


/-!
## Population-Specific Calibration Drift

When a PGS trained in one population is applied to another,
calibration drifts systematically.
-/

section PopulationCalibrationDrift

/-- **Prevalence-driven miscalibration.**
    If disease prevalence is π_source in training and π_target
    in the target, the CITL shifts by log(π_target/π_source)
    on the logistic scale. -/
noncomputable def prevalenceCITLShift (pi_source pi_target : ℝ) : ℝ :=
  Real.log (pi_target / pi_source)

/-- CITL shift is zero when prevalences match. -/
theorem no_citl_shift_same_prevalence (pi : ℝ) (h_pi : 0 < pi) :
    prevalenceCITLShift pi pi = 0 := by
  unfold prevalenceCITLShift
  rw [div_self (ne_of_gt h_pi), Real.log_one]

/-- CITL shift is positive when target has higher prevalence. -/
theorem citl_shift_positive_higher_prevalence
    (pi_s pi_t : ℝ) (h_s : 0 < pi_s)
    (h_higher : pi_s < pi_t) :
    0 < prevalenceCITLShift pi_s pi_t := by
  unfold prevalenceCITLShift
  apply Real.log_pos
  rw [one_lt_div h_s]
  exact h_higher

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
  simpa [mul_comm, mul_left_comm, mul_assoc]

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
    exact (mul_lt_mul_left h_scale_pos).mp (by simpa [mul_assoc] using h_scaled)

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
  change (0 < mPred ↔ 0 < mTrue)
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
