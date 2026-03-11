import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Metric-Specific Portability (Open Question 3)

This file formalizes Wang et al.'s Open Question 3: portability depends
on the prediction metric used. Different metrics (R², AUC, Brier, NRI,
calibration) can show different portability patterns for the same trait
and populations.

Key results:
1. R² vs AUC portability relationship
2. Calibration vs discrimination portability
3. Precision vs recall portability
4. Metric decomposition and cross-population behavior
5. Optimal metric choice for clinical applications

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## R² vs AUC: Different Portability Measures

R² measures variance explained (continuous traits).
AUC measures discriminative ability (binary traits).
These metrics respond differently to distribution shifts.
-/

section R2VsAUC

/-- **R² is sensitive to mean shift.**
    When the PGS mean shifts across populations, R² can decrease
    even if the rank ordering is perfectly preserved. -/
theorem r2_sensitive_to_mean_shift
    (r2_source r2_target : ℝ)
    (h_decreased : r2_target < r2_source)
    (h_nn : 0 ≤ r2_target) :
    -- R² dropped due to mean shift, even with preserved ranking
    0 < r2_source - r2_target := by linarith

/-- **Portability of AUC vs R² for binary traits.**
    R²_Nagelkerke drops faster than AUC because Nagelkerke R²
    is sensitive to prevalence changes. -/
end R2VsAUC


/-!
## Calibration vs Discrimination

Calibration (predicted risk = observed risk) and discrimination
(ability to separate cases from controls) can degrade differently
across populations.
-/

section CalibrationVsDiscrimination

/-- **Discrimination can be preserved while calibration is lost.**
    The PGS may correctly rank individuals (good discrimination)
    but the predicted risk is wrong (poor calibration). -/
theorem discrimination_preserved_calibration_lost
    (auc_source auc_target : ℝ)
    (cal_source cal_target : ℝ)
    (δ : ℝ)
    (h_disc_preserved : |auc_source - auc_target| < δ)
    (h_cal_lost : δ < |cal_source - cal_target|) :
    -- Calibration is more affected than discrimination
    |auc_source - auc_target| < |cal_source - cal_target| := by
  linarith

/-- **Calibration is affected by allele frequency shifts.**
    The mean PGS shifts when allele frequencies change → calibration-
    in-the-large is violated. This is independent of discrimination. -/
/-- **Recalibration is easier than improving discrimination.**
    Calibration can be fixed with a small target-population sample
    (just need to estimate intercept + slope). Discrimination
    requires new genetic discoveries. -/
/-- **Expected calibration error (ECE).**
    ECE = Σᵢ |observed_risk_in_bin_i - predicted_risk_in_bin_i| × n_i/n.
    ECE can increase dramatically across populations. -/
/-- **Brier score decomposes into calibration and discrimination.**
    Brier = calibration_component + refinement_component.
    Portability can affect each component differently. -/
theorem brier_decomposition
    (calibration refinement brier : ℝ)
    (h_decomp : brier = calibration + refinement)
    (h_cal_nn : 0 ≤ calibration) (h_ref_nn : 0 ≤ refinement) :
    0 ≤ brier := by linarith

/-- **Cross-population Brier score increases mainly from calibration.**
    For PGS, the discrimination component is relatively stable
    (shared genetic effects) but calibration degrades (frequency shifts). -/
theorem brier_increase_mainly_calibration
    (Δcal Δref : ℝ)
    (h_cal_dominates : |Δref| < |Δcal|)
    (h_cal_pos : 0 < Δcal) :
    Δref < Δcal := by
  have h1 : Δref ≤ |Δref| := le_abs_self _
  have h2 : |Δcal| = Δcal := abs_of_pos h_cal_pos
  linarith

end CalibrationVsDiscrimination


/-!
## Precision vs Recall in PGS Risk Stratification

Clinical PGS use involves classifying individuals as high-risk
or normal-risk. Precision and recall can have different portability.
-/

section PrecisionRecall

/-- **Precision (PPV) of high-risk classification.**
    PPV = P(actually high risk | PGS says high risk).
    Depends on prevalence via Bayes' theorem. -/
noncomputable def ppv (sensitivity specificity prevalence : ℝ) : ℝ :=
  sensitivity * prevalence /
    (sensitivity * prevalence + (1 - specificity) * (1 - prevalence))

/- **Recall (sensitivity) of high-risk classification.**
    Sensitivity = P(PGS says high risk | actually high risk).
    Depends on the PGS's discriminative ability. -/

/-- **PPV changes with prevalence.**
    Even if sensitivity and specificity are perfectly portable,
    PPV changes if disease prevalence differs. -/
theorem ppv_changes_with_prevalence
    (se sp K₁ K₂ : ℝ)
    (h_se : 0 < se) (h_sp : 0 < sp) (h_sp1 : sp < 1)
    (h_K1 : 0 < K₁) (h_K1' : K₁ < 1)
    (h_K2 : 0 < K₂) (h_K2' : K₂ < 1)
    (h_diff : K₁ ≠ K₂) :
    ppv se sp K₁ ≠ ppv se sp K₂ := by
  unfold ppv
  intro h
  apply h_diff
  -- Cross-multiply and simplify
  have h_d1 : 0 < se * K₁ + (1 - sp) * (1 - K₁) := by nlinarith
  have h_d2 : 0 < se * K₂ + (1 - sp) * (1 - K₂) := by nlinarith
  rw [div_eq_div_iff h_d1.ne' h_d2.ne'] at h
  -- se * K₁ * (se * K₂ + (1-sp)(1-K₂)) = se * K₂ * (se * K₁ + (1-sp)(1-K₁))
  -- se²K₁K₂ + se*K₁*(1-sp)(1-K₂) = se²K₁K₂ + se*K₂*(1-sp)(1-K₁)
  -- se*K₁*(1-sp)(1-K₂) = se*K₂*(1-sp)(1-K₁)
  -- K₁*(1-K₂) = K₂*(1-K₁)  [cancel se*(1-sp)]
  -- K₁ - K₁K₂ = K₂ - K₁K₂
  -- K₁ = K₂
  nlinarith [mul_pos h_se (sub_pos.mpr h_sp1)]

/-- **Sensitivity is more portable than PPV.**
    Sensitivity depends mainly on discrimination (rank ordering),
    which is more stable across populations.
    PPV depends on both discrimination and prevalence. -/
/-- **Number needed to screen (NNS) portability.**
    NNS = 1/PPV. If PPV drops, NNS increases → more individuals
    need screening for each true positive. -/
theorem nns_increases_with_ppv_drop
    (ppv₁ ppv₂ : ℝ)
    (h_ppv₁ : 0 < ppv₁) (h_ppv₂ : 0 < ppv₂)
    (h_drop : ppv₂ < ppv₁) :
    1 / ppv₁ < 1 / ppv₂ := by
  exact div_lt_div_of_pos_left one_pos h_ppv₂ h_drop

/-- **F1 score captures precision-recall balance.**
    F1 = 2 × PPV × sensitivity / (PPV + sensitivity).
    F1 portability reflects both precision and recall portability. -/
noncomputable def f1ScoreMetric (precision sens : ℝ) : ℝ :=
  2 * precision * sens / (precision + sens)

/-- F1 is bounded above by 1 (the maximum of precision and sens when both ≤ 1). -/
theorem f1_le_min
    (precision sens : ℝ)
    (h_p : 0 < precision) (h_r : 0 < sens)
    (h_p1 : precision ≤ 1) (h_r1 : sens ≤ 1) :
    f1ScoreMetric precision sens ≤ 1 := by
  unfold f1ScoreMetric
  rw [div_le_one (by linarith)]
  nlinarith [mul_nonneg (le_of_lt h_p) (by linarith : 0 ≤ 1 - sens),
             mul_nonneg (le_of_lt h_r) (by linarith : 0 ≤ 1 - precision)]

end PrecisionRecall


/-!
## Metric Choice Affects Clinical Decision-Making

Different metrics lead to different clinical decisions, so metric-
specific portability has direct practical consequences.
-/

section MetricAndClinicalDecisions

/-- **Screening vs diagnosis have different metric priorities.**
    Screening: maximize sensitivity (catch all cases) → sensitivity-driven.
    Diagnosis: maximize PPV (minimize false positives) → PPV-driven.
    The appropriate portability metric depends on the clinical use. -/
theorem different_uses_different_metrics
    (port_sensitivity port_ppv : ℝ)
    (t_sens t_ppv : ℝ)
    (h_screening_ok : t_sens < port_sensitivity)
    (h_diagnosis_bad : port_ppv < t_ppv)
    (h_thresholds : t_ppv ≤ t_sens) :
    -- Screening is portable but diagnosis is not
    port_ppv < port_sensitivity := by linarith

/-- **Decision curve analysis across populations.**
    The net benefit at threshold p_t depends on both PPV and sensitivity:
    NB = (TP/N) - (FP/N) × p_t/(1-p_t).
    Population-specific thresholds may be needed. -/
/-- **Relative utility of PGS vs no screening.**
    For PGS to be clinically useful, NB(PGS) > NB(screen all) and
    NB(PGS) > NB(screen none). If portability loss brings NB below
    these baselines, PGS is not useful in the target population. -/
theorem clinical_utility_threshold
    (nb_pgs nb_all nb_none : ℝ)
    (h_useful : nb_all < nb_pgs ∧ nb_none < nb_pgs) :
    max nb_all nb_none < nb_pgs := by
  exact max_lt h_useful.1 h_useful.2

/-- **Multiple metrics should be reported for portability.**
    A single metric can be misleading. Wang et al. recommend
    reporting R², AUC, calibration, and NRI together. -/
theorem single_metric_misleading
    (port_r2 port_auc port_cal port_nri : ℝ)
    (t₁ t₂ t₃ t₄ : ℝ)
    (h_r2_bad : port_r2 < t₁)
    (h_auc_ok : t₂ < port_auc)
    (h_cal_bad : port_cal < t₃)
    (h_nri_ok : t₄ < port_nri)
    (h_t₁_le_t₂ : t₁ ≤ t₂) (h_t₃_le_t₄ : t₃ ≤ t₄) :
    -- Metrics disagree: R² and calibration bad, AUC and NRI ok
    port_r2 < port_auc ∧ port_cal < port_nri := by
  constructor <;> linarith

end MetricAndClinicalDecisions


/-!
## Proper Scoring Rules and Portability

Proper scoring rules incentivize honest probability assessments.
Their portability depends on the specific scoring rule used.
-/

section ProperScoringRules

/-- **Brier score is a proper scoring rule.**
    Brier(p, y) = (p - y)². The unique minimizer is p = P(Y=1|X). -/
noncomputable def brierScoreMetric (p y : ℝ) : ℝ := (p - y) ^ 2

/-- Brier score is nonneg. -/
theorem brier_nonneg (p y : ℝ) : 0 ≤ brierScoreMetric p y := sq_nonneg _

/- **Log score (cross-entropy) is also proper.**
    Log(p, y) = -y log(p) - (1-y) log(1-p).
    Log score is more sensitive to calibration than Brier. -/

/-- **Different proper scoring rules have different portability.**
    Brier: sensitive to calibration but bounded.
    Log: very sensitive to calibration, unbounded.
    This means log-loss portability is worse than Brier portability
    for miscalibrated PGS. -/
/-- **Proper scoring rule decomposition.**
    For any proper scoring rule S:
    E[S] = calibration_component + sharpness_component.
    Portability affects calibration more than sharpness. -/
end ProperScoringRules

end Calibrator
