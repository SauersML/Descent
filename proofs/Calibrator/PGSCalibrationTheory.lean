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
    (aucLink : ℝ → ℝ) (hauc : StrictMono aucLink)
    (r2Source fstSource fstTarget mean_pred πSource πTarget : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (h_src_cal : calibrationInTheLarge πSource mean_pred = 0)
    (h_prev_shift : πSource ≠ πTarget) :
    targetAUCFromObservables aucLink r2Source fstSource fstTarget <
      sourceAUCFromObservables aucLink r2Source ∧
    |calibrationInTheLarge πSource mean_pred| <
      |calibrationInTheLarge πTarget mean_pred| := by
  constructor
  · exact targetAUC_lt_source_of_observables aucLink hauc
      r2Source fstSource fstTarget h_r2 h_fst h_fst_bounds
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
    (aucLink : ℝ → ℝ) (hauc : StrictMono aucLink)
    (π r2Source fstSource fstTarget : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetAUCFromObservables aucLink r2Source fstSource fstTarget <
      sourceAUCFromObservables aucLink r2Source ∧
    sourceBrierFromObservables π r2Source <
      targetBrierFromObservables π r2Source fstSource fstTarget := by
  constructor
  · exact targetAUC_lt_source_of_observables aucLink hauc
      r2Source fstSource fstTarget h_r2 h_fst h_fst_bounds
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

/-- **Clinical treatment model induced by a decision threshold.**
    Treatment yields benefit `benefit × trueRisk` in expectation and incurs
    harm `harm` whenever given. The clinically optimal threshold is therefore
    `harm / benefit`; we encode this exactly as `harm = benefit × threshold`. -/
structure ThresholdTreatmentModel where
  threshold : ℝ
  benefit : ℝ
  harm : ℝ
  benefit_pos : 0 < benefit
  harm_eq_threshold : harm = benefit * threshold

/-- **QALY gain under a threshold-based treatment decision.**
    The deployed system treats when the risk used for decision-making exceeds
    the clinical treatment threshold. -/
noncomputable def qalyGainUnderDecision
    (model : ThresholdTreatmentModel) (trueRisk decisionRisk : ℝ) : ℝ :=
  if _ : model.threshold < decisionRisk then
      model.benefit * trueRisk - model.harm
    else
      0

/-- **Per-individual QALY loss from using predicted instead of true risk.**
    This is the regret relative to the oracle threshold rule that would act on
    the individual's true risk. -/
noncomputable def qalyLoss
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) : ℝ :=
  qalyGainUnderDecision model trueRisk trueRisk -
    qalyGainUnderDecision model trueRisk predictedRisk

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

/-- **Exact QALY loss for a false positive treatment decision.**
    If the patient's true risk is below threshold but the predicted risk is
    above threshold, the loss equals the treatment benefit scale times the
    distance from the true risk to the treatment threshold. -/
theorem qalyLoss_false_positive_exact
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ)
    (h_true_low : trueRisk ≤ model.threshold)
    (h_pred_high : classifiedHighRisk model.threshold predictedRisk) :
    qalyLoss model trueRisk predictedRisk =
      model.benefit * (model.threshold - trueRisk) := by
  have h_true_not_high : ¬ model.threshold < trueRisk := not_lt.mpr h_true_low
  have h_pred_high' : model.threshold < predictedRisk := by
    simpa [classifiedHighRisk] using h_pred_high
  unfold qalyLoss qalyGainUnderDecision
  simp [h_true_not_high, h_pred_high', model.harm_eq_threshold]
  ring_nf

/-- **Exact QALY loss for a false negative treatment decision.**
    If the patient's true risk is above threshold but the predicted risk is
    at or below threshold, the loss equals the missed-treatment margin above
    threshold on the QALY-benefit scale. -/
theorem qalyLoss_false_negative_exact
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ)
    (h_true_high : model.threshold < trueRisk)
    (h_pred_not_high : ¬ classifiedHighRisk model.threshold predictedRisk) :
    qalyLoss model trueRisk predictedRisk =
      model.benefit * (trueRisk - model.threshold) := by
  have h_pred_not_high' : ¬ model.threshold < predictedRisk := by
    simpa [classifiedHighRisk] using h_pred_not_high
  unfold qalyLoss qalyGainUnderDecision
  simp [h_true_high, h_pred_not_high', model.harm_eq_threshold]
  ring_nf

/-- **QALY loss equals benefit-scaled threshold-decision regret.**
    The QALY object above is exactly the regret of using the predicted-risk
    threshold rule instead of the oracle true-risk threshold rule, scaled by the
    treatment benefit. This gives a single exact piecewise formula covering
    false positives, false negatives, and correct decisions. -/
theorem qalyLoss_eq_benefit_mul_thresholdDecisionRegretMargin
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) :
    qalyLoss model trueRisk predictedRisk =
      model.benefit * thresholdDecisionRegretMargin model trueRisk predictedRisk := by
  by_cases h_pred : classifiedHighRisk model.threshold predictedRisk
  · by_cases h_true_low : trueRisk ≤ model.threshold
    · unfold thresholdDecisionRegretMargin
      rw [if_pos h_pred]
      rw [qalyLoss_false_positive_exact model trueRisk predictedRisk h_true_low h_pred]
      have hmax : max (model.threshold - trueRisk) 0 = model.threshold - trueRisk := by
        exact max_eq_left (by linarith)
      rw [hmax]
    · have h_true_high : model.threshold < trueRisk := by linarith
      have h_pred_high' : model.threshold < predictedRisk := by
        simpa [classifiedHighRisk] using h_pred
      have h_zero : qalyLoss model trueRisk predictedRisk = 0 := by
        unfold qalyLoss qalyGainUnderDecision
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
      rw [qalyLoss_false_negative_exact model trueRisk predictedRisk h_true_high h_pred]
      have hmax : max (trueRisk - model.threshold) 0 = trueRisk - model.threshold := by
        exact max_eq_left (by linarith)
      rw [hmax]
    · have h_true_low : trueRisk ≤ model.threshold := by linarith
      have h_pred_not_high' : ¬ model.threshold < predictedRisk := by
        simpa [classifiedHighRisk] using h_pred
      have h_zero : qalyLoss model trueRisk predictedRisk = 0 := by
        unfold qalyLoss qalyGainUnderDecision
        simp [h_true_high, h_pred_not_high', model.harm_eq_threshold]
      unfold thresholdDecisionRegretMargin
      rw [if_neg h_pred]
      rw [h_zero]
      have hmax : max (trueRisk - model.threshold) 0 = 0 := by
        exact max_eq_right (by linarith)
      rw [hmax]
      ring

/-- QALY loss is always nonnegative under the threshold-decision regret model. -/
theorem qalyLoss_nonneg
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) :
    0 ≤ qalyLoss model trueRisk predictedRisk := by
  rw [qalyLoss_eq_benefit_mul_thresholdDecisionRegretMargin]
  have h_margin_nonneg :
      0 ≤ thresholdDecisionRegretMargin model trueRisk predictedRisk := by
    unfold thresholdDecisionRegretMargin
    by_cases h_pred : classifiedHighRisk model.threshold predictedRisk
    · rw [if_pos h_pred]
      exact le_max_right _ _
    · rw [if_neg h_pred]
      exact le_max_right _ _
  exact mul_nonneg model.benefit_pos.le h_margin_nonneg

/-- **QALY loss is zero under perfect calibration at the decision point.**
    If the deployed decision uses the true risk itself, it matches the oracle
    threshold rule and incurs no regret. -/
theorem qalyLoss_eq_zero_of_perfect_calibration
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ)
    (h_cal : predictedRisk = trueRisk) :
    qalyLoss model trueRisk predictedRisk = 0 := by
  subst h_cal
  unfold qalyLoss
  ring

/-- **Miscalibration-induced overtreatment has an exact QALY cost.**
    A positive intercept shift that pushes a truly low-risk patient above the
    treatment threshold creates a false positive treatment decision, and the
    resulting regret is exactly the false-positive QALY loss. -/
theorem miscalibration_induced_false_positive_qaly_loss
    (model : ThresholdTreatmentModel) (trueRisk c : ℝ)
    (h_truly_low : trueRisk < model.threshold)
    (h_miscal : model.threshold - trueRisk < c) :
    qalyLoss model trueRisk (trueRisk + c) =
      model.benefit * (model.threshold - trueRisk) := by
  have h_decision :=
    miscalibration_changes_decisions trueRisk model.threshold c h_truly_low h_miscal
  exact qalyLoss_false_positive_exact model trueRisk (trueRisk + c) (le_of_lt h_truly_low) h_decision.2

/-- **Expected QALY loss from miscalibration.**
    This is the population expectation of threshold-decision regret under the
    joint law of true risk and predicted risk. -/
noncomputable def expectedQalyLoss {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ) : ℝ :=
  ∫ z, qalyLoss model (trueRisk z) (predictedRisk z) ∂μ

/-- Perfect calibration implies zero expected QALY loss. -/
theorem expectedQalyLoss_eq_zero_of_perfect_calibration
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ)
    (h_cal : ∀ z, predictedRisk z = trueRisk z) :
    expectedQalyLoss μ model trueRisk predictedRisk = 0 := by
  unfold expectedQalyLoss
  have hfun :
      (fun z => qalyLoss model (trueRisk z) (predictedRisk z)) = fun _ => (0 : ℝ) := by
    funext z
    exact qalyLoss_eq_zero_of_perfect_calibration model (trueRisk z) (predictedRisk z) (h_cal z)
  rw [hfun]
  simp

/-- **Expected QALY loss is the expected threshold-decision regret.**
    Population QALY loss is exactly the expected decision-regret margin scaled
    by the treatment benefit. This makes the population-level clinical utility
    object a direct consequence of the threshold treatment model above. -/
theorem expectedQalyLoss_eq_expected_thresholdDecisionRegret
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ) :
    expectedQalyLoss μ model trueRisk predictedRisk =
      ∫ z, model.benefit *
        thresholdDecisionRegretMargin model (trueRisk z) (predictedRisk z) ∂μ := by
  unfold expectedQalyLoss
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z =>
    qalyLoss_eq_benefit_mul_thresholdDecisionRegretMargin
      model (trueRisk z) (predictedRisk z))

end DecisionImplications

end Calibrator
