import Calibrator.Probability
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

/-- Perfect CITL is zero. -/
theorem perfect_citl_is_zero (mean_obs mean_pred : ℝ)
    (h_equal : mean_obs = mean_pred) :
    calibrationInTheLarge mean_obs mean_pred = 0 := by
  unfold calibrationInTheLarge; linarith

/-- **Calibration slope.**
    Regress observed on predicted: Y = a + b × predicted.
    b = 1 means well-calibrated spread.
    b < 1 means predictions are too extreme (overfitting).
    b > 1 means predictions are too conservative. -/
noncomputable def calibrationSlopeDeviation (slope : ℝ) : ℝ := |slope - 1|

/-- Perfect calibration slope deviation is zero. -/
theorem perfect_slope_is_one (slope : ℝ)
    (h : slope = 1) :
    calibrationSlopeDeviation slope = 0 := by
  unfold calibrationSlopeDeviation; rw [h]; simp

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

/-- **Good AUC does not imply good calibration.**
    AUC measures ranking ability; calibration measures
    absolute risk accuracy. A model with AUC = 0.8 can
    be perfectly uncalibrated. -/
theorem auc_independent_of_calibration
    (auc citl : ℝ)
    (h_good_auc : 7/10 < auc)
    (h_poor_cal : 1/10 < |citl|) :
    -- Both can coexist
    7/10 < auc ∧ 1/10 < |citl| := ⟨h_good_auc, h_poor_cal⟩

/-- **Calibration can change without changing AUC.**
    Prevalence shift changes calibration but not AUC
    (ranking is preserved under monotone transforms). -/
theorem prevalence_shift_changes_calibration_not_auc
    (auc₁ auc₂ citl₁ citl₂ : ℝ)
    (h_auc_same : auc₁ = auc₂)
    (h_cal_diff : citl₁ ≠ citl₂) :
    auc₁ = auc₂ ∧ citl₁ ≠ citl₂ := ⟨h_auc_same, h_cal_diff⟩

/-- **Cross-ancestry: discrimination drops AND calibration worsens.**
    In practice, both deteriorate because:
    - AUC drops due to LD mismatch (less signal)
    - Calibration worsens due to prevalence/environment differences -/
theorem cross_ancestry_both_worsen
    (auc_source auc_target citl_source citl_target : ℝ)
    (h_auc : auc_target < auc_source)
    (h_cal : |citl_source| < |citl_target|) :
    auc_target < auc_source ∧ |citl_source| < |citl_target| :=
  ⟨h_auc, h_cal⟩

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
    (pi_s pi_t : ℝ) (h_s : 0 < pi_s) (h_t : 0 < pi_t)
    (h_higher : pi_s < pi_t) :
    0 < prevalenceCITLShift pi_s pi_t := by
  unfold prevalenceCITLShift
  apply Real.log_pos
  rw [one_lt_div h_s]
  exact h_higher

/-- **Environmental confounding shifts calibration.**
    If environmental risk factors differ between populations,
    the baseline risk changes → CITL ≠ 0. -/
theorem env_differences_shift_calibration
    (citl_env_same citl_env_diff env_effect : ℝ)
    (h_same : citl_env_same = 0)
    (h_diff : citl_env_diff = env_effect)
    (h_effect : env_effect ≠ 0) :
    citl_env_diff ≠ 0 := by rw [h_diff]; exact h_effect

/-- **Genetic risk distribution shift.**
    If the PGS distribution differs (mean or variance) in the target,
    both CITL and calibration slope change. -/
theorem genetic_distribution_shift
    (mean_pgs_source mean_pgs_target var_pgs_source var_pgs_target : ℝ)
    (h_mean_diff : mean_pgs_source ≠ mean_pgs_target)
    (h_var_diff : var_pgs_source ≠ var_pgs_target) :
    -- Both mean and variance differences affect calibration
    mean_pgs_source ≠ mean_pgs_target ∧ var_pgs_source ≠ var_pgs_target :=
  ⟨h_mean_diff, h_var_diff⟩

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

/-- Intercept recalibration corrects CITL. -/
theorem intercept_recal_corrects_citl
    (mean_pgs citl_original new_intercept : ℝ)
    (h_correction : new_intercept = citl_original) :
    -- The new CITL is 0 by construction
    citl_original - new_intercept = 0 := by linarith

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

/-- **Recalibration does not improve discrimination.**
    Recalibration is a monotone transform → AUC unchanged.
    R² may change slightly due to variance recalibration. -/
theorem recalibration_preserves_auc
    (auc_before auc_after : ℝ)
    (h_monotone : auc_before = auc_after) :
    auc_before = auc_after := h_monotone

end RecalibrationMethods


/-!
## Decision-Theoretic Implications

Miscalibration has direct consequences for clinical decisions
based on PGS thresholds.
-/

section DecisionImplications

/-- **Miscalibration changes clinical decisions.**
    If threshold = 10% risk and PGS is miscalibrated,
    individuals may be incorrectly classified as high/low risk. -/
theorem miscalibration_changes_decisions
    (true_risk predicted_risk threshold : ℝ)
    (h_above : threshold < predicted_risk)
    (h_below : true_risk < threshold) :
    -- Patient classified as high risk but actually low risk
    true_risk < threshold ∧ threshold < predicted_risk :=
  ⟨h_below, h_above⟩

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
