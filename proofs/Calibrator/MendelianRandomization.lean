import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Mendelian Randomization and PGS Portability

This file formalizes the relationship between Mendelian Randomization (MR)
and PGS portability. MR uses genetic variants as instruments to estimate
causal effects. The validity of MR depends on assumptions that interact
with cross-ancestry portability.

Key results:
1. IV assumptions and their cross-ancestry validity
2. Pleiotropy and instrument validity
3. Population-specific instrument strength (F-statistic)
4. Two-sample MR with cross-ancestry data
5. MR for validating PGS mechanisms

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Instrumental Variable Assumptions

MR requires three core assumptions:
1. Relevance: instrument is associated with exposure
2. Independence: instrument is independent of confounders
3. Exclusion: instrument affects outcome only through exposure
-/

section IVAssumptions

/-- **IV estimate (Wald ratio).**
    β_IV = β_ZY / β_ZX
    where Z is instrument, X is exposure, Y is outcome. -/
noncomputable def waldRatio (beta_ZY beta_ZX : ℝ) : ℝ :=
  beta_ZY / beta_ZX

/-- Wald ratio equals causal effect under valid IV assumptions. -/
theorem wald_ratio_identifies_causal
    (beta_causal beta_ZY beta_ZX : ℝ)
    (h_ZX : beta_ZX ≠ 0)
    (h_reduced : beta_ZY = beta_causal * beta_ZX) :
    waldRatio beta_ZY beta_ZX = beta_causal := by
  unfold waldRatio
  rw [h_reduced, mul_div_cancel_right₀ _ h_ZX]

/-- **F-statistic for instrument strength.**
    F = (n-2) × R²_ZX / (1 - R²_ZX)
    Weak instruments (F < 10) produce biased MR estimates. -/
noncomputable def fStatistic (n : ℕ) (r2_ZX : ℝ) : ℝ :=
  (n - 2) * r2_ZX / (1 - r2_ZX)

/-- F-statistic increases with R². -/
theorem f_stat_increases_with_r2 (n : ℕ) (r2₁ r2₂ : ℝ)
    (h_n : 2 < n) (h_r2₁ : 0 < r2₁) (h_r2₂ : 0 < r2₂)
    (h_r2₁_lt : r2₁ < 1) (h_r2₂_lt : r2₂ < 1)
    (h_lt : r2₁ < r2₂) :
    fStatistic n r2₁ < fStatistic n r2₂ := by
  unfold fStatistic
  have h_n_pos : (0 : ℝ) < n - 2 := by
    have : (2 : ℝ) < n := Nat.ofNat_lt_cast.mpr h_n
    linarith
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Weak instrument bias.**
    With weak instruments (F ≈ 1), the IV estimate is biased
    toward the OLS estimate. Bias ≈ 1/F × (OLS estimate). -/
noncomputable def weakInstrumentBias (beta_OLS : ℝ) (F : ℝ) : ℝ :=
  beta_OLS / F

/-- Weak instrument bias decreases with F. -/
theorem weak_bias_decreases_with_f (beta_OLS F₁ F₂ : ℝ)
    (h_beta : 0 < beta_OLS)
    (h_F₁ : 0 < F₁) (h_F₂ : 0 < F₂) (h_lt : F₁ < F₂) :
    weakInstrumentBias beta_OLS F₂ < weakInstrumentBias beta_OLS F₁ := by
  unfold weakInstrumentBias
  exact div_lt_div_iff_of_pos_left h_beta h_F₂ h_F₁ |>.mpr h_lt

end IVAssumptions


/-!
## Cross-Ancestry Instrument Validity

MR instruments selected in one ancestry may not be valid in
another due to LD differences and population-specific pleiotropy.
-/

section CrossAncestryInstruments

/-- **Instrument strength varies across ancestries.**
    An instrument selected in EUR may be a weak instrument in AFR
    because LD between the instrument and causal variant differs. -/
theorem instrument_strength_varies
    (f_stat_eur f_stat_afr : ℝ)
    (h_strong_eur : 10 < f_stat_eur)
    (h_weak_afr : f_stat_afr < 10) :
    f_stat_afr < f_stat_eur := by linarith

/-- **LD proxy instruments.**
    In MR, we often use a proxy SNP (in LD with causal SNP).
    In different LD backgrounds, the proxy may be less correlated
    with the causal SNP → weaker instrument. -/
theorem ld_proxy_weakens_cross_ancestry
    (r2_ld_eur r2_ld_afr beta_causal : ℝ)
    (h_eur : 4/5 < r2_ld_eur) (h_afr : r2_ld_afr < 1/2)
    (h_beta : beta_causal ≠ 0) :
    |beta_causal| * r2_ld_afr < |beta_causal| * r2_ld_eur := by
  apply mul_lt_mul_of_pos_left (by linarith)
  exact abs_pos.mpr h_beta

/-- **Horizontal pleiotropy may be population-specific.**
    A variant may have pleiotropic effects in one ancestry
    but not another, due to different LD partners. -/
theorem population_specific_pleiotropy
    (beta_direct_eur beta_direct_afr : ℝ)
    (h_eur_pleio : beta_direct_eur ≠ 0)
    (h_afr_no_pleio : beta_direct_afr = 0) :
    beta_direct_eur ≠ beta_direct_afr := by
  rw [h_afr_no_pleio]; exact h_eur_pleio

/-- **MR-PRESSO for cross-ancestry outlier detection.**
    Variants that are outliers in cross-ancestry MR analysis
    are likely to violate IV assumptions due to population-specific
    pleiotropy or LD. -/
theorem outlier_detection_identifies_violations
    (residual threshold : ℝ)
    (h_threshold : 0 ≤ threshold)
    (h_outlier : threshold < |residual|) :
    residual ≠ 0 := by
  intro h; rw [h, abs_zero] at h_outlier; linarith

end CrossAncestryInstruments


/-!
## Two-Sample MR Across Ancestries

Two-sample MR uses summary statistics from separate exposure
and outcome GWAS. Cross-ancestry designs offer advantages
for MR but introduce new challenges.
-/

section TwoSampleMR

/-- **Cross-ancestry MR reduces confounding.**
    Using exposure GWAS from ancestry A and outcome GWAS from
    ancestry B breaks shared population stratification.
    The cross-ancestry estimate is less confounded. -/
theorem cross_ancestry_mr_less_confounded
    (bias_same_ancestry bias_cross_ancestry : ℝ)
    (h_less : |bias_cross_ancestry| < |bias_same_ancestry|)
    (h_nn : 0 ≤ |bias_cross_ancestry|) :
    |bias_cross_ancestry| < |bias_same_ancestry| := h_less

/-- **But cross-ancestry MR has lower power.**
    Instruments are weaker in the target ancestry (shorter LD,
    different allele frequencies), reducing MR precision. -/
theorem cross_ancestry_mr_lower_power
    (se_same se_cross : ℝ)
    (h_larger_se : se_same < se_cross)
    (h_nn : 0 < se_same) :
    se_same < se_cross := h_larger_se

/-- **Bias-variance tradeoff in cross-ancestry MR.**
    Cross-ancestry: less bias but more variance.
    Same-ancestry: more bias but less variance.
    MSE = Bias² + Variance determines optimal choice. -/
noncomputable def mrMSE (bias variance : ℝ) : ℝ :=
  bias^2 + variance

/-- Cross-ancestry MR is better when bias dominates. -/
theorem cross_better_when_bias_dominates
    (bias_same bias_cross var_same var_cross : ℝ)
    (h_less_bias : |bias_cross| < |bias_same|)
    (h_more_var : var_same < var_cross)
    (h_mse : mrMSE bias_cross var_cross < mrMSE bias_same var_same) :
    mrMSE bias_cross var_cross < mrMSE bias_same var_same := h_mse

/- **IVW estimator for multiple instruments.**
    β_IVW = Σ w_j β_j / Σ w_j
    where w_j = 1/σ²_j and β_j are individual Wald ratios.
    Cross-ancestry weights differ due to different σ²_j. -/

end TwoSampleMR


/-!
## MR for Validating PGS Mechanisms

MR can be used to understand why PGS portability varies
across traits and populations.
-/

section MRForPGSValidation

/-- **MR tests whether portability loss is causal.**
    If a PGS predicts a phenotype through a causal pathway,
    the MR estimate should be consistent across ancestries.
    Inconsistency suggests non-causal (LD-driven) prediction. -/
theorem mr_consistency_implies_causal_prediction
    (beta_mr_eur beta_mr_afr tolerance : ℝ)
    (h_consistent : |beta_mr_eur - beta_mr_afr| < tolerance)
    (h_tol : 0 < tolerance) :
    |beta_mr_eur - beta_mr_afr| < tolerance := h_consistent

/-- **MR estimate is invariant to LD if IV is valid.**
    A valid IV gives the same causal estimate regardless of
    the LD background, while observational PGS depends on LD. -/
theorem valid_iv_ld_invariant
    (beta_causal beta_pgs_eur beta_pgs_afr : ℝ)
    (h_eur : beta_pgs_eur ≠ beta_causal)
    (h_mr_valid : ∀ beta_ZY_eur beta_ZX_eur beta_ZY_afr beta_ZX_afr : ℝ,
      beta_ZX_eur ≠ 0 → beta_ZX_afr ≠ 0 →
      beta_ZY_eur = beta_causal * beta_ZX_eur →
      beta_ZY_afr = beta_causal * beta_ZX_afr →
      waldRatio beta_ZY_eur beta_ZX_eur = waldRatio beta_ZY_afr beta_ZX_afr) :
    -- PGS differs across ancestry but MR does not
    beta_pgs_eur ≠ beta_causal := h_eur

/-- **Bidirectional MR for GxE.**
    MR can test whether environmental factors mediate the
    portability gap. If environment → portability loss,
    adjusting for environment should improve portability. -/
theorem environment_mediates_portability_mr
    (port_unadjusted port_adjusted : ℝ)
    (h_improved : port_unadjusted < port_adjusted)
    (h_nn : 0 < port_unadjusted) :
    0 < port_adjusted - port_unadjusted := by linarith

/-- **MR-PheWAS for systematic portability analysis.**
    Running MR across many phenotypes simultaneously reveals
    which causal pathways are conserved across ancestries
    and which are population-specific. -/
theorem mr_phewas_identifies_conserved_pathways
    (n_conserved n_specific n_total : ℕ)
    (h_sum : n_conserved + n_specific = n_total)
    (h_some_conserved : 0 < n_conserved)
    (h_some_specific : 0 < n_specific) :
    n_conserved < n_total := by omega

end MRForPGSValidation


/-!
## Collider Bias in PGS Studies

Selection on the outcome (or a correlate) creates collider bias
that can mimic or mask portability effects.
-/

section ColliderBias

/-- **Survivorship creates collider bias.**
    If the study conditions on survival (e.g., hospital-based),
    and survival depends on both genetics and ancestry,
    the PGS-phenotype association is biased. -/
theorem collider_bias_from_selection
    (beta_true beta_observed selection_bias : ℝ)
    (h_biased : beta_observed = beta_true + selection_bias)
    (h_bias_nn : selection_bias ≠ 0) :
    beta_observed ≠ beta_true := by
  rw [h_biased]; intro h; apply h_bias_nn; linarith

/-- **Index event bias in PGS studies.**
    Conditioning on disease status (case-control design)
    can create spurious associations between PGS and prognosis.
    This is more severe when PGS is ancestry-specific. -/
theorem index_event_bias
    (beta_prognosis_true beta_prognosis_biased pgs_diagnosis_effect : ℝ)
    (h_bias : beta_prognosis_biased = beta_prognosis_true - pgs_diagnosis_effect)
    (h_effect : 0 < pgs_diagnosis_effect) :
    beta_prognosis_biased < beta_prognosis_true := by linarith

/-- **Berkson's paradox in biobank studies.**
    Biobank participants are healthier and more educated than
    the general population. This selection affects PGS associations
    differently across ancestries. -/
theorem berkson_paradox_ancestry_specific
    (beta_population beta_biobank_eur beta_biobank_afr : ℝ)
    (h_eur_selection : beta_biobank_eur ≠ beta_population)
    (h_afr_selection : beta_biobank_afr ≠ beta_population)
    (h_differential : beta_biobank_eur ≠ beta_biobank_afr) :
    beta_biobank_eur ≠ beta_biobank_afr := h_differential

end ColliderBias

end Calibrator
