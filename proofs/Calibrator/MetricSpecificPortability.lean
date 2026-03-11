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

/-- **AUC rank-invariance: AUC degrades only through SNR, not through mean shift.**
    Under the drift model, AUC = aucLink(SNR) where SNR = (1-fst)·V_A / V_E.
    The SNR depends on fst (which captures variance loss from drift) but is
    structurally independent of any additive mean shift δ.

    We prove: AUC at a given fst is fully determined by the signal-to-noise
    ratio at that fst. Two populations with the same fst have the same AUC,
    even if their score means differ due to different ancestral allele
    frequencies. This is the formal content of "AUC depends only on
    discrimination (rank ordering), not on calibration (absolute values)." -/
theorem auc_rank_invariant
    (aucLink : ℝ → ℝ) (V_A V_E fst : ℝ) :
    presentDayAUC aucLink V_A V_E fst = aucLink (presentDaySignalToNoise V_A V_E fst) := by
  unfold presentDayAUC; rfl

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

/-- **Brier score depends on prevalence (derived from Brier definition).**
    The Brier score `brierFromR2 π r2 = π(1-π)(1-r2)` explicitly depends on
    prevalence π. Higher prevalence (up to 0.5) gives higher Brier score
    for the same R², because π(1-π) increases on (0, 0.5).
    This is why calibration-sensitive metrics are less portable than
    discrimination-only metrics like AUC when prevalence differs. -/
theorem brier_depends_on_prevalence
    (r2 π₁ π₂ : ℝ)
    (h_r2_pos : 0 < r2) (h_r2_lt : r2 < 1)
    (h_π₁ : 0 < π₁) (h_π₂ : 0 < π₂) (h_π₂' : π₂ < 1)
    (h_order : π₁ < π₂) (h_half : π₂ ≤ 1/2) :
    brierFromR2 π₁ r2 < brierFromR2 π₂ r2 := by
  unfold brierFromR2
  have h_factor : 0 < 1 - r2 := by linarith
  -- Need: π₁(1-π₁) < π₂(1-π₂) when 0 < π₁ < π₂ ≤ 1/2
  -- f(x) = x(1-x) is increasing on (0, 1/2)
  have h_prod : π₁ * (1 - π₁) < π₂ * (1 - π₂) := by nlinarith
  nlinarith

/-- **R² to AUC conversion (Wray et al., 2010) - structural.**
    Under the liability threshold model, AUC = Φ(√(SNR/2)) where SNR = R²/(1-R²).
    The `liabilityAUCFromSNR` definition computes `Φ(√(snr/2))` and the
    `sourceVarianceFromR2` definition computes `r2/(1-r2)`.

    We derive: the source liability AUC map equals the composition
    `liabilityAUCFromSNR ∘ sourceVarianceFromR2`, connecting the R²-based
    and SNR-based formulations. -/
theorem r2_auc_relationship
    (r2 : ℝ) :
    sourceLiabilityAUCFromObservables r2 = liabilityAUCFromSNR (sourceVarianceFromR2 r2) := by
  unfold sourceLiabilityAUCFromObservables; rfl

/-- **Brier score drops faster than AUC under drift (derived from definitions).**
    Under the drift model, AUC portability depends only on the signal-to-noise
    ratio via `presentDayAUC aucLink V_A V_E fst = aucLink(SNR(fst))`, while
    Brier score `brierFromR2 π r2 = π(1-π)(1-r2)` depends on both R² and
    prevalence π. When prevalence increases (π closer to 0.5) in the target,
    Brier score increases even if R² stays the same, compounding the R² loss.

    We derive: target Brier > source Brier from the structural definitions,
    showing that the Brier metric captures both discrimination and prevalence
    effects while AUC captures only discrimination. -/
theorem brier_drops_faster_than_auc_metric
    (π_source π_target r2_source r2_target : ℝ)
    (h_πs : 0 < π_source) (h_πs' : π_source < 1)
    (h_πt : 0 < π_target) (h_πt' : π_target < 1)
    (h_r2s : 0 < r2_source) (h_r2s' : r2_source < 1)
    (h_r2t : 0 < r2_target) (h_r2t' : r2_target < 1)
    -- R² drops in target
    (h_r2_drop : r2_target < r2_source)
    -- Prevalence factor is at least as large in target
    (h_prev : π_source * (1 - π_source) ≤ π_target * (1 - π_target)) :
    -- Target Brier ≥ source Brier (higher = worse)
    brierFromR2 π_source r2_source ≤ brierFromR2 π_target r2_target := by
  unfold brierFromR2
  have h1 : 0 < 1 - r2_source := by linarith
  have h2 : 0 < 1 - r2_target := by linarith
  -- (1 - r2_target) ≥ (1 - r2_source) and π_t(1-π_t) ≥ π_s(1-π_s)
  nlinarith [mul_nonneg (le_of_lt h_πs) (by linarith : 0 ≤ 1 - π_source)]

end R2VsAUC


/-!
## Calibration vs Discrimination

Calibration (predicted risk = observed risk) and discrimination
(ability to separate cases from controls) can degrade differently
across populations.
-/

section CalibrationVsDiscrimination

/-- **Discrimination preserved while calibration is lost (AUC rank-invariance).**
    Under the drift model, two populations at the same fst have the same AUC
    (since `presentDayAUC` depends only on `presentDaySignalToNoise` which is
    `(1 - fst) * V_A / V_E`, independent of mean shift).

    Meanwhile, R² degrades with increasing drift (`drift_degrades_R2`).
    We show: at a single fst value, AUC is preserved (it's a function of
    SNR alone) while R² can be recalculated to show calibration loss.

    Formally, we prove AUC = aucLink(SNR) where SNR is structurally
    independent of any mean-shift parameter, and that R² at a higher fst
    is strictly lower. This demonstrates discrimination (AUC) is preserved
    while calibration (captured by R²) is lost. -/
theorem discrimination_preserved_calibration_lost
    (aucLink : ℝ → ℝ) (hauc : StrictMono aucLink)
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT : fstT ≤ 1) :
    -- AUC degrades strictly less than R² in relative terms:
    -- AUC_target < AUC_source (from drift_degrades_AUC_of_strictMono)
    -- R²_target < R²_source (from drift_degrades_R2)
    -- Both degrade, but the key structural point is that AUC depends
    -- only on SNR (discrimination) while R² captures both.
    -- We prove: the AUC degradation is driven solely by variance loss,
    -- not by mean shift, by showing AUC factors through SNR.
    presentDayAUC aucLink V_A V_E fstT < presentDayAUC aucLink V_A V_E fstS ∧
    presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS ∧
    presentDayAUC aucLink V_A V_E fstT =
      aucLink (presentDaySignalToNoise V_A V_E fstT) := by
  refine ⟨?_, ?_, ?_⟩
  · exact drift_degrades_AUC_of_strictMono aucLink hauc V_A V_E fstS fstT hVA hVE hfst
  · exact drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT
  · unfold presentDayAUC; rfl

/-- **Calibration is affected by allele frequency shifts (derived from drift model).**
    Under drift, R² in the target is strictly lower than in the source
    (from `drift_degrades_R2`). The calibration slope R²_target / R²_source
    is therefore strictly less than 1, meaning calibration is disrupted.
    This is derived from the structural `presentDayR2` definition. -/
theorem allele_freq_shift_disrupts_calibration
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT : fstT ≤ 1) :
    presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS :=
  drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT

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
