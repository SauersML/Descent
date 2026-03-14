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

/-- **Sample size needed for recalibration.**
    Good calibration requires ~200 events per parameter.
    With 2 parameters (intercept + slope), need ~400 events.
    This can be limiting in rare diseases or small populations. -/
theorem recalibration_needs_events
    (n_events n_params events_per_param : ℕ)
    (h_rule : events_per_param = 200)
    (h_params : n_params = 2)
    (h_insufficient : n_events < n_params * events_per_param) :
    n_events < 400 := by subst h_rule; subst h_params; omega

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

/-- Positive NRI means recalibration improves classification. -/
theorem positive_nri_means_improvement
    (up_e down_e up_ne down_ne n_e n_ne : ℝ)
    (h_events : down_e < up_e) (h_nonevents : up_ne < down_ne)
    (h_ne : 0 < n_e) (h_nne : 0 < n_ne) :
    0 < nri up_e down_e up_ne down_ne n_e n_ne := by
  unfold nri
  apply add_pos
  · exact div_pos (by linarith) h_ne
  · exact div_pos (by linarith) h_nne

/-- **Expected QALY loss from miscalibration.**
    Miscalibrated PGS leads to suboptimal treatment decisions.
    The QALY loss is proportional to the miscalibration magnitude
    and the treatment effect. -/
noncomputable def qalyLoss (miscalibration treatment_effect prevalence : ℝ) : ℝ :=
  |miscalibration| * treatment_effect * prevalence

/-- QALY loss is nonneg. -/
theorem qaly_loss_nonneg (miscal treat prev : ℝ)
    (h_treat : 0 ≤ treat) (h_prev : 0 ≤ prev) :
    0 ≤ qalyLoss miscal treat prev := by
  unfold qalyLoss
  exact mul_nonneg (mul_nonneg (abs_nonneg _) h_treat) h_prev

end DecisionImplications

end Calibrator
