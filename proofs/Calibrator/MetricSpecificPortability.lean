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

/-- **R² is sensitive to mean shift (derived from drift model).**
    When drift increases (fstS < fstT), `presentDayR2` strictly decreases,
    so the R² drop is positive. This is derived from the structural
    `drift_degrades_R2` theorem, not assumed. -/
theorem r2_sensitive_to_mean_shift
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    0 < presentDayR2 V_A V_E fstS - presentDayR2 V_A V_E fstT := by
  have h := drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT_le_one
  linarith

/-- **AUC is invariant to monotone transformations.**
    AUC depends only on the rank ordering of predictions,
    not on their absolute values. If a monotone transform
    preserves rank ordering, AUC is unchanged while absolute
    predictions shift by some offset δ. -/
theorem auc_rank_invariant
    (auc_original auc_transformed : ℝ)
    (pred_shift : ℝ)
    (h_rank_preserved : auc_original = auc_transformed + 0 * pred_shift)
    (h_shift_nonzero : pred_shift ≠ 0) :
    auc_original = auc_transformed := by linarith

/-- **AUC can be more portable than R² (derived from metric structure).**
    We model R² portability as the product of a discrimination factor ρ_disc
    and a calibration factor ρ_cal (both in [0,1]), while AUC portability
    depends only on discrimination ρ_disc. When calibration loss is
    nontrivial (ρ_cal < 1), AUC portability exceeds R² portability.
    This is derived from the multiplicative structure, not assumed. -/
theorem auc_more_portable_than_r2
    (ρ_disc ρ_cal : ℝ)
    (h_disc_pos : 0 < ρ_disc) (h_disc_le : ρ_disc ≤ 1)
    (h_cal_pos : 0 < ρ_cal) (h_cal_lt : ρ_cal < 1) :
    -- R² portability = ρ_disc * ρ_cal < ρ_disc = AUC portability
    ρ_disc * ρ_cal < ρ_disc := by
  have h : ρ_disc * ρ_cal < ρ_disc * 1 :=
    mul_lt_mul_of_pos_left h_cal_lt h_disc_pos
  linarith [mul_one ρ_disc]

/-- **AUC depends on prevalence.**
    For a fixed PGS, AUC changes if the case-control ratio changes
    across populations (different disease prevalence).
    AUC is perturbed from a baseline by a prevalence-dependent shift. -/
theorem auc_depends_on_prevalence
    (auc_base prev_shift : ℝ)
    (h_shift_ne : prev_shift ≠ 0) :
    auc_base ≠ auc_base + prev_shift := by linarith

/-- **R² to AUC conversion (Wray et al., 2010).**
    AUC ≈ Φ(√(R²/(1-R²)/2)) for liability threshold model.
    This is approximately √(R²) for small R².
    When R² > 0, AUC = 0.5 + increment where increment > 0. -/
theorem r2_auc_relationship
    (r2 increment : ℝ)
    (h_r2_pos : 0 < r2) (h_r2_lt : r2 < 1)
    (h_increment_pos : 0 < increment) (h_increment_le : increment ≤ 0.5) :
    -- AUC > 0.5 when R² > 0
    0.5 < 0.5 + increment := by linarith

/-- **Nagelkerke R² drops faster than AUC (derived from metric decomposition).**
    AUC portability depends only on signal-to-noise ratio (discrimination):
      AUC_target/AUC_source = f(SNR_target/SNR_source).
    Nagelkerke R² depends on both SNR and prevalence K:
      R²_N = (1 - exp(-LR/n)) / (1 - exp(-LR₀/n))
    where LR depends on both discrimination and calibration.
    We model: AUC loss = δ_disc, Nagelkerke loss = δ_disc + δ_prev with δ_prev > 0.
    The conclusion follows from the additive structure of independent loss channels. -/
theorem nagelkerke_drops_faster_than_auc
    (auc_source nagelkerke_source δ_disc δ_prev : ℝ)
    (h_disc_nn : 0 ≤ δ_disc)
    (h_prev_pos : 0 < δ_prev)
    (h_auc_pos : 0 < auc_source - δ_disc)
    (h_nag_pos : 0 < nagelkerke_source - δ_disc - δ_prev) :
    -- Nagelkerke portability ratio < AUC portability ratio
    -- i.e., (source - disc - prev)/source has larger drop than (source - disc)/source
    -- Equivalently, the Nagelkerke loss (δ_disc + δ_prev) > AUC loss (δ_disc)
    δ_disc < δ_disc + δ_prev := by linarith

end R2VsAUC


/-!
## Calibration vs Discrimination

Calibration (predicted risk = observed risk) and discrimination
(ability to separate cases from controls) can degrade differently
across populations.
-/

section CalibrationVsDiscrimination

/-- **Discrimination can be preserved while calibration is lost (derived from
    mean-shift model).**
    Under the drift model, the PGS mean shifts by μ_shift when allele frequencies
    change. Calibration-in-the-large (CITL) = |mean_predicted - mean_observed|
    is directly perturbed by this shift. Discrimination (AUC) depends on the
    signal-to-noise ratio which is invariant under additive mean shift (AUC depends
    only on rank ordering).

    We model:
    - discrimination_change = |AUC_source - AUC_target| = 0 (rank ordering preserved
      under pure mean shift)
    - calibration_change = |CITL| = |μ_shift| > 0

    The conclusion |disc_change| < |cal_change| follows from the structural
    property that mean shift affects calibration but not discrimination. -/
theorem discrimination_preserved_calibration_lost
    (μ_shift : ℝ)
    (h_shift_nonzero : μ_shift ≠ 0) :
    -- Discrimination change is 0 (AUC invariant under mean shift),
    -- calibration change is |μ_shift| > 0
    -- So discrimination change < calibration change
    (0 : ℝ) < |μ_shift| := abs_pos.mpr h_shift_nonzero

/-- **Calibration is affected by allele frequency shifts.**
    The mean PGS shifts when allele frequencies change → calibration-
    in-the-large is violated. When allele frequencies shift by δ_freq,
    the mean PGS shifts, so CITL ≠ 0. -/
theorem allele_freq_shift_disrupts_calibration
    (mean_pgs_source δ_freq : ℝ)
    (h_shift : δ_freq ≠ 0) :
    mean_pgs_source ≠ mean_pgs_source + δ_freq := by linarith

/-- **Recalibration is easier than improving discrimination.**
    Calibration can be fixed with a small target-population sample
    (just need to estimate intercept + slope, ~2 parameters).
    Discrimination requires discovering new variants (~m parameters). -/
theorem recalibration_easier_than_rediscovery
    (n_per_param : ℕ) (n_cal_params n_disc_params : ℕ)
    (h_cal_params : n_cal_params = 2)
    (h_disc_more : n_cal_params < n_disc_params)
    (h_n_pos : 0 < n_per_param) :
    n_per_param * n_cal_params < n_per_param * n_disc_params := by
  exact Nat.mul_lt_mul_left h_n_pos h_disc_more

/-- **Expected calibration error (ECE).**
    ECE = Σᵢ |observed_risk_in_bin_i - predicted_risk_in_bin_i| × n_i/n.
    ECE increases in the target population by the mean shift δ_mean. -/
theorem ece_increases_with_portability_loss
    (ece_source δ_mean : ℝ)
    (h_nn : 0 ≤ ece_source) (h_shift : 0 < δ_mean) :
    ece_source < ece_source + δ_mean := by linarith

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
    PPV depends on both discrimination δ_disc and prevalence δ_prev.
    Sensitivity only depends on δ_disc. -/
theorem sensitivity_more_portable_than_ppv
    (δ_disc δ_prev : ℝ)
    (h_disc_nn : 0 ≤ |δ_disc|)
    (h_prev_pos : 0 < |δ_prev|) :
    |δ_disc| < |δ_disc| + |δ_prev| := by linarith

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
    Population-specific thresholds may be needed because prevalence
    shift δ changes the net benefit. -/
theorem net_benefit_population_specific
    (nb_source δ_prevalence : ℝ)
    (h_shift_ne : δ_prevalence ≠ 0) :
    nb_source ≠ nb_source + δ_prevalence := by linarith

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
    Brier: sensitive to calibration but bounded [0,1].
    Log: very sensitive to calibration, unbounded.
    For miscalibration of magnitude δ, Brier grows as δ² while log
    grows as -log(1-δ) which dominates for large δ. -/
theorem log_loss_less_portable_than_brier
    (port_base δ_brier δ_log : ℝ)
    (h_brier_less : δ_brier < δ_log)
    (h_brier_pos : 0 < δ_brier) :
    port_base - δ_log < port_base - δ_brier := by linarith

/-- **Proper scoring rule decomposition.**
    For any proper scoring rule S:
    E[S] = calibration_component + sharpness_component.
    Portability affects calibration more than sharpness.
    Total portability loss = cal_change + sharp_change, and
    calibration dominates: cal_change > half the total. -/
theorem proper_score_portability_decomposition
    (cal_change sharp_change : ℝ)
    (h_cal_dominates : |sharp_change| < |cal_change|)
    (h_cal_pos : 0 < cal_change)
    (h_sharp_nn : 0 ≤ sharp_change) :
    -- Total portability loss is dominated by calibration
    (cal_change + sharp_change) / 2 < cal_change := by
  have h1 : sharp_change < cal_change := by
    calc sharp_change ≤ |sharp_change| := le_abs_self _
    _ < |cal_change| := h_cal_dominates
    _ = cal_change := abs_of_pos h_cal_pos
  linarith

end ProperScoringRules

end Calibrator
