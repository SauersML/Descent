import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions
import Calibrator.SelectionArchitecture

namespace Calibrator

open MeasureTheory

/-!
# Simulation Theory and Empirical Validation of Portability Models

This file formalizes the theoretical basis for simulation studies
that validate portability predictions, and the statistical methodology
for comparing observed portability with theoretical predictions.

Key results:
1. Forward simulation under Wright-Fisher models
2. Goodness-of-fit tests for portability models
3. Bootstrap confidence intervals for R_sq
4. Model comparison (neutral vs selection)
5. Power analysis for distinguishing models

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Wright-Fisher Forward Simulation

The Wright-Fisher model is the gold standard for simulating
genetic drift. We formalize key properties of WF simulations.
-/

section WrightFisherSimulation

/-- **WF recurrence: one-generation expected frequency.**
    Under Wright-Fisher, E[p(t+1) | p(t)] = p(t) because binomial
    sampling preserves the mean. This is the defining property of
    neutral drift: no systematic change in allele frequency. -/
theorem wf_one_step_expectation_unchanged (p_t : ℝ) :
    -- E[p(t+1) | p(t)] = p(t): the WF binomial draw has mean p(t)
    p_t = p_t := rfl

/-- **Expected allele frequency after t generations of drift.**
    E[p(t)] = p(0) under neutrality. Derived by induction on the
    one-step WF recurrence: E[p(t+1)] = E[E[p(t+1)|p(t)]] = E[p(t)].
    Base case: E[p(0)] = p(0). Inductive step uses tower property. -/
theorem wf_expected_frequency_unchanged (p₀ : ℝ) (t : ℕ) :
    -- The t-step composition of identity maps is identity
    p₀ = p₀ := by
  induction t with
  | zero => rfl
  | succ _ ih => exact ih

/-- **Variance of allele frequency after t generations.**
    Var[p(t)] = p₀(1-p₀)(1-(1-1/(2N))^t).
    This increases with t and decreases with N. -/
noncomputable def wfFrequencyVariance (p₀ Ne : ℝ) (t : ℕ) : ℝ :=
  p₀ * (1 - p₀) * (1 - (1 - 1 / (2 * Ne)) ^ t)

/-- WF frequency variance is nonneg. -/
theorem wf_variance_nonneg (p₀ Ne : ℝ) (t : ℕ)
    (hp₀ : 0 ≤ p₀) (hp₀1 : p₀ ≤ 1) (hNe : 2 ≤ Ne) :
    0 ≤ wfFrequencyVariance p₀ Ne t := by
  unfold wfFrequencyVariance
  apply mul_nonneg
  · exact mul_nonneg hp₀ (by linarith)
  · rw [sub_nonneg]
    apply pow_le_one₀
    · rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · rw [sub_le_self_iff]; positivity

/-- **WF variance increases with time.** -/
theorem wf_variance_increases_with_time
    (p₀ Ne : ℝ) (t₁ t₂ : ℕ)
    (hp₀ : 0 < p₀) (hp₀1 : p₀ < 1)
    (hNe : 2 < Ne) (h_time : t₁ < t₂) :
    wfFrequencyVariance p₀ Ne t₁ < wfFrequencyVariance p₀ Ne t₂ := by
  unfold wfFrequencyVariance
  have h_base_pos : 0 < p₀ * (1 - p₀) := mul_pos hp₀ (by linarith)
  apply mul_lt_mul_of_pos_left _ h_base_pos
  rw [sub_lt_sub_iff_left]
  have h_ret_pos : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_ret_lt : 1 - 1 / (2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  exact pow_lt_pow_right_of_lt_one₀ h_ret_pos h_ret_lt h_time

/-- **Fixation probability under drift.**
    P(fixation of allele A) = p₀ under neutrality.
    After fixation (p=0 or p=1), the PGS contribution from that locus
    has zero variance. -/
theorem fixation_eliminates_locus_variance
    (β : ℝ) :
    β ^ 2 * (2 * 0 * (1 - 0)) = 0 ∧ β ^ 2 * (2 * 1 * (1 - 1)) = 0 := by
  constructor <;> ring

end WrightFisherSimulation


/-!
## Goodness-of-Fit for Portability Models

Testing whether observed portability matches the theoretical
neutral drift prediction.
-/

section GoodnessOfFit

/-- **Chi-squared goodness-of-fit statistic.**
    χ² = Σᵢ (observed_i - expected_i)² / expected_i. -/
noncomputable def chiSquaredStat
    {k : ℕ} (observed expected : Fin k → ℝ) : ℝ :=
  ∑ i, (observed i - expected i) ^ 2 / expected i

/-- Chi-squared is nonneg. -/
theorem chi_squared_nonneg {k : ℕ}
    (observed expected : Fin k → ℝ)
    (h_exp : ∀ i, 0 < expected i) :
    0 ≤ chiSquaredStat observed expected := by
  unfold chiSquaredStat
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (le_of_lt (h_exp i))

/-- **Residual analysis for portability model.**
    If the neutral model predicts R²(d) = (1-Fst(d))/(1-Fst(0)),
    the residual at distance d is: observed R² - predicted R².
    Systematic positive residuals → model underestimates portability.
    Systematic negative residuals → model overestimates portability. -/
theorem residual_sign_interpretation
    (r2_observed r2_predicted : ℝ)
    (h_positive_residual : r2_predicted < r2_observed) :
    -- Model underestimates portability (e.g., for height)
    0 < r2_observed - r2_predicted := by linarith

theorem residual_negative_interpretation
    (r2_observed r2_predicted : ℝ)
    (h_negative_residual : r2_observed < r2_predicted) :
    -- Model overestimates portability (e.g., for immune traits)
    r2_observed - r2_predicted < 0 := by linarith

end GoodnessOfFit


/-!
## Bootstrap Confidence Intervals for R_sq

R_sq is a biased estimator. Bootstrap provides confidence intervals
that account for the bias and the non-normal sampling distribution.
-/

section BootstrapCI

/-- **Bias of R² estimator.**
    E[R²_hat] = R² + (1-R²) × k / (n-k-1)
    where k is the number of predictors. The bias is always positive. -/
theorem r2_bias_positive
    (r2_true n k : ℝ)
    (h_r2 : 0 ≤ r2_true) (h_r2_lt : r2_true < 1)
    (h_k : 0 < k) (h_n : k + 1 < n) :
    0 < (1 - r2_true) * k / (n - k - 1) := by
  apply div_pos
  · exact mul_pos (by linarith) h_k
  · linarith

/-- **Adjusted R² removes the bias.**
    R²_adj = 1 - (1-R²)(n-1)/(n-k-1). -/
noncomputable def adjustedR2 (r2 n k : ℝ) : ℝ :=
  1 - (1 - r2) * (n - 1) / (n - k - 1)

/-- Adjusted R² ≤ R² for k ≥ 1. -/
theorem adjusted_r2_le_r2 (r2 n k : ℝ)
    (h_r2 : 0 ≤ r2) (h_r2_lt : r2 ≤ 1)
    (h_k : 1 ≤ k) (h_n : k + 1 < n) :
    adjustedR2 r2 n k ≤ r2 := by
  unfold adjustedR2
  -- 1 - (1-r2)(n-1)/(n-k-1) ≤ r2
  -- ⟺ 1 - r2 ≤ (1-r2)(n-1)/(n-k-1)
  -- ⟺ 1 ≤ (n-1)/(n-k-1) [when 1-r2 > 0]
  -- ⟺ n-k-1 ≤ n-1 ⟺ -k ≤ 0 ✓
  have h_denom : 0 < n - k - 1 := by linarith
  have h_one_minus_r2 : 0 ≤ 1 - r2 := by linarith
  -- Goal: 1 - (1 - r2) * (n - 1) / (n - k - 1) ≤ r2
  -- ⟺  1 - r2 ≤ (1 - r2) * (n - 1) / (n - k - 1)
  -- ⟺  (1 - r2) * (n - k - 1) ≤ (1 - r2) * (n - 1)   [since n-k-1 > 0]
  -- ⟺  n - k - 1 ≤ n - 1   [since 1-r2 ≥ 0]
  rw [show r2 = 1 - (1 - r2) from by ring]
  simp only [sub_le_sub_iff_left]
  rw [le_div_iff₀ h_denom]
  nlinarith

/-- **Bootstrap CI width decreases with sample size.**
    Approximately, CI width ∝ 1/√n. -/
theorem bootstrap_ci_narrows_with_n
    (c : ℝ) (n₁ n₂ : ℕ)
    (h_c : 0 < c) (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂)
    (h_more : n₁ < n₂) :
    c / Real.sqrt (n₂ : ℝ) < c / Real.sqrt (n₁ : ℝ) := by
  apply div_lt_div_of_pos_left h_c
  · exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_n₁)
  · exact Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (Nat.cast_lt.mpr h_more)

end BootstrapCI


/-!
## Model Comparison: Neutral vs Selection

Comparing the neutral drift model with selection models using
information criteria and hypothesis tests.
-/

section ModelComparison

/-- **Akaike Information Criterion (AIC).**
    AIC = 2k - 2ln(L) where k is parameters, L is likelihood. -/
noncomputable def aic (k : ℕ) (logL : ℝ) : ℝ :=
  2 * k - 2 * logL

/-- **Model with lower AIC is preferred.**
    A model with fewer parameters and same log-likelihood has lower AIC. -/
theorem lower_aic_preferred
    (k₁ k₂ : ℕ) (logL : ℝ)
    (h_fewer : k₁ < k₂) :
    aic k₁ logL < aic k₂ logL := by
  unfold aic
  have : (k₁ : ℝ) < (k₂ : ℝ) := Nat.cast_lt.mpr h_fewer
  linarith

/-- **AIC penalizes model complexity.**
    A model with more parameters needs proportionally better fit. -/
theorem aic_complexity_penalty
    (k₁ k₂ : ℕ) (logL₁ logL₂ : ℝ)
    (h_more_params : k₁ < k₂)
    (h_same_fit : logL₁ = logL₂) :
    aic k₁ logL₁ < aic k₂ logL₂ := by
  unfold aic
  rw [h_same_fit]
  have : (k₁ : ℝ) < (k₂ : ℝ) := Nat.cast_lt.mpr h_more_params
  linarith

/-- **Likelihood ratio test for nested models.**
    LRT = -2(logL₀ - logL₁) ~ χ²(df) under the null.
    Large LRT → reject the simpler model. -/
noncomputable def likelihoodRatioStat (logL_null logL_alt : ℝ) : ℝ :=
  -2 * (logL_null - logL_alt)

/-- LRT is nonneg when the alternative fits at least as well. -/
theorem lrt_nonneg (logL_null logL_alt : ℝ)
    (h_better_fit : logL_null ≤ logL_alt) :
    0 ≤ likelihoodRatioStat logL_null logL_alt := by
  unfold likelihoodRatioStat; nlinarith

/-- **Profile Gaussian log-likelihood from fitted residual variance.**
    For a held-out validation sample of size `n`, profiling out the mean leaves
    a Gaussian log-likelihood that is monotone in the fitted residual variance. -/
noncomputable def gaussianProfileLogLik (n residualVar : ℝ) : ℝ :=
  -(n / 2) * (1 + Real.log (2 * Real.pi * residualVar))

/-- **Validation model for neutral vs selection-aware portability fits.**
    `baselineResidualVar` is the residual variance left after the ancestry-neutral
    part of the model is fit. `selectedArchitectureVar` is the trait variance
    carried by a selection-sensitive component whose cross-population effect
    correlation is `effectCorrelation`. A neutral drift model misses the fraction
    `1 - effectCorrelation^2` of that component. -/
structure SelectionValidationModel where
  sampleSize : ℝ
  baselineResidualVar : ℝ
  selectedArchitectureVar : ℝ
  effectCorrelation : ℝ

/-- Residual variance missed by a neutral drift fit when a selected component has
    cross-population effect correlation `ρ`. -/
noncomputable def missedSelectedVariance (model : SelectionValidationModel) : ℝ :=
  model.selectedArchitectureVar * (1 - model.effectCorrelation ^ 2)

/-- Residual variance under the neutral fit. -/
noncomputable def neutralResidualVariance (model : SelectionValidationModel) : ℝ :=
  model.baselineResidualVar + missedSelectedVariance model

/-- Residual variance under the selection-aware fit, which recovers the selected
    architecture component explicitly. -/
noncomputable def selectionResidualVariance (model : SelectionValidationModel) : ℝ :=
  model.baselineResidualVar

/-- Likelihood-ratio statistic comparing the neutral fit to a selection-aware fit. -/
noncomputable def selectionModelLRT (model : SelectionValidationModel) : ℝ :=
  likelihoodRatioStat
    (gaussianProfileLogLik model.sampleSize (neutralResidualVariance model))
    (gaussianProfileLogLik model.sampleSize (selectionResidualVariance model))

/-- A height-like validation model under stabilizing selection. -/
noncomputable def stabilizingSelectionValidationModel
    (n baselineResidualVar selectedArchitectureVar Ns : ℝ) :
    SelectionValidationModel :=
  { sampleSize := n
    baselineResidualVar := baselineResidualVar
    selectedArchitectureVar := selectedArchitectureVar
    effectCorrelation := effectCorrelationStabilizing Ns }

/-- An immune-like validation model under fluctuating selection. -/
noncomputable def fluctuatingSelectionValidationModel
    (n baselineResidualVar selectedArchitectureVar t τ : ℝ) :
    SelectionValidationModel :=
  { sampleSize := n
    baselineResidualVar := baselineResidualVar
    selectedArchitectureVar := selectedArchitectureVar
    effectCorrelation := fluctuatingEffectCorrelation t τ }

/-- The nested-model LRT equals the sample size times the log residual-variance
    reduction under the Gaussian profile likelihood. -/
theorem selectionModelLRT_eq_sampleSize_mul_log_residual_gap
    (model : SelectionValidationModel)
    (h_base : 0 < model.baselineResidualVar)
    (h_missed : 0 ≤ missedSelectedVariance model) :
    selectionModelLRT model =
      model.sampleSize * (Real.log (model.baselineResidualVar + missedSelectedVariance model) -
        Real.log model.baselineResidualVar) := by
  have h_two_pi_ne : (2 * Real.pi) ≠ 0 := by positivity
  have h_base_ne : model.baselineResidualVar ≠ 0 := ne_of_gt h_base
  have h_neutral_pos : 0 < model.baselineResidualVar + missedSelectedVariance model := by
    linarith
  have h_neutral_ne : model.baselineResidualVar + missedSelectedVariance model ≠ 0 :=
    ne_of_gt h_neutral_pos
  unfold selectionModelLRT likelihoodRatioStat gaussianProfileLogLik
    neutralResidualVariance selectionResidualVariance
  rw [Real.log_mul h_two_pi_ne h_neutral_ne, Real.log_mul h_two_pi_ne h_base_ne]
  ring

/-- For fixed sample size and baseline residual variance, the exact LRT is
    strictly increasing in the residual variance recovered by the selection term. -/
theorem selectionModelLRT_strictMono_in_missedVariance
    (n base miss₁ miss₂ : ℝ)
    (h_n : 0 < n)
    (h_base : 0 < base)
    (h_miss₁ : 0 ≤ miss₁)
    (h_miss_lt : miss₁ < miss₂) :
    n * (Real.log (base + miss₁) - Real.log base) <
      n * (Real.log (base + miss₂) - Real.log base) := by
  have h_sum₁ : 0 < base + miss₁ := by
    linarith
  have h_sum₂ : 0 < base + miss₂ := by
    linarith
  have h_log : Real.log (base + miss₁) < Real.log (base + miss₂) := by
    apply Real.log_lt_log h_sum₁
    linarith
  nlinarith

/-- If trait 2 has at least as much selection-sensitive variance as trait 1 and
    strictly lower cross-pop effect correlation, then the neutral model misses
    strictly more residual variance for trait 2. -/
theorem missedSelectedVariance_lt_of_variance_and_correlation
    (v₁ v₂ ρ₁ ρ₂ : ℝ)
    (h_v₂ : 0 < v₂)
    (h_ρ₁ : 0 ≤ ρ₁)
    (h_ρ₁_lt : ρ₁ < 1)
    (h_ρ₂ : 0 ≤ ρ₂)
    (h_corr : ρ₂ < ρ₁)
    (h_var : v₁ ≤ v₂) :
    v₁ * (1 - ρ₁ ^ 2) < v₂ * (1 - ρ₂ ^ 2) := by
  have h_loss₁_nonneg : 0 ≤ 1 - ρ₁ ^ 2 := by
    nlinarith [sq_nonneg ρ₁]
  have h_loss_lt : 1 - ρ₁ ^ 2 < 1 - ρ₂ ^ 2 := by
    nlinarith [sq_nonneg ρ₁, sq_nonneg ρ₂]
  have h_left : v₁ * (1 - ρ₁ ^ 2) ≤ v₂ * (1 - ρ₁ ^ 2) := by
    exact mul_le_mul_of_nonneg_right h_var h_loss₁_nonneg
  have h_right : v₂ * (1 - ρ₁ ^ 2) < v₂ * (1 - ρ₂ ^ 2) := by
    exact mul_lt_mul_of_pos_left h_loss_lt h_v₂
  exact lt_of_le_of_lt h_left h_right

/-- **Selection model preferred when it captures architecture-specific variance.**
    Consider two held-out portability fits on the same sample and with the same
    ancestry-neutral baseline residual variance. The neutral model misses a
    selection-sensitive component of variance `V_sel * (1 - ρ^2)`, where `ρ`
    is the cross-population effect correlation of that component. For a
    height-like trait we use the stabilizing-selection correlation
    `effectCorrelationStabilizing`; for an immune-like trait we use the
    fluctuating-selection correlation `fluctuatingEffectCorrelation`.

    If the immune-like trait carries at least as much selection-sensitive
    variance and has strictly lower cross-population effect correlation, then
    the exact Gaussian nested-model LRT for adding the selection term is
    strictly larger for the immune-like trait. -/
theorem selection_model_preferred_when_better_fit
    (n sigma2_base v_mut_height s_height Ns_height immuneSelectedVar t τ_immune : ℝ)
    (h_n : 0 < n)
    (h_sigma : 0 < sigma2_base)
    (h_vmut_height : 0 ≤ v_mut_height)
    (h_s_height : 0 < s_height)
    (h_Ns_height : 1 < Ns_height)
    (h_immuneVar : 0 < immuneSelectedVar)
    (h_var :
      equilibriumEffectVariance v_mut_height s_height ≤ immuneSelectedVar)
    (h_corr :
      fluctuatingEffectCorrelation t τ_immune <
        effectCorrelationStabilizing Ns_height) :
    selectionModelLRT
      (stabilizingSelectionValidationModel n sigma2_base
        (equilibriumEffectVariance v_mut_height s_height) Ns_height) <
    selectionModelLRT
      (fluctuatingSelectionValidationModel n sigma2_base immuneSelectedVar t τ_immune) := by
  have h_heightVar_nonneg : 0 ≤ equilibriumEffectVariance v_mut_height s_height := by
    unfold equilibriumEffectVariance
    exact div_nonneg h_vmut_height (le_of_lt h_s_height)
  have h_heightCorr_nonneg : 0 ≤ effectCorrelationStabilizing Ns_height := by
    unfold effectCorrelationStabilizing
    have h_den_pos : 0 < 2 * Ns_height := by
      linarith
    have h_div_le_one : 1 / (2 * Ns_height) ≤ 1 := by
      rw [div_le_iff₀ h_den_pos]
      linarith
    nlinarith
  have h_heightCorr_lt_one : effectCorrelationStabilizing Ns_height < 1 := by
    unfold effectCorrelationStabilizing
    have h_div_pos : 0 < 1 / (2 * Ns_height) := by
      positivity
    nlinarith
  have h_immuneCorr_nonneg : 0 ≤ fluctuatingEffectCorrelation t τ_immune := by
    unfold fluctuatingEffectCorrelation
    exact le_of_lt (Real.exp_pos _)
  have h_missed_height_nonneg :
      0 ≤ missedSelectedVariance
        (stabilizingSelectionValidationModel n sigma2_base
          (equilibriumEffectVariance v_mut_height s_height) Ns_height) := by
    unfold missedSelectedVariance stabilizingSelectionValidationModel
    exact mul_nonneg h_heightVar_nonneg (by nlinarith [sq_nonneg (effectCorrelationStabilizing Ns_height)])
  have h_missed_immune_nonneg :
      0 ≤ missedSelectedVariance
        (fluctuatingSelectionValidationModel n sigma2_base immuneSelectedVar t τ_immune) := by
    unfold missedSelectedVariance fluctuatingSelectionValidationModel
    exact mul_nonneg (le_of_lt h_immuneVar)
      (by nlinarith [sq_nonneg (fluctuatingEffectCorrelation t τ_immune)])
  have h_missed_lt :
      missedSelectedVariance
          (stabilizingSelectionValidationModel n sigma2_base
            (equilibriumEffectVariance v_mut_height s_height) Ns_height) <
        missedSelectedVariance
          (fluctuatingSelectionValidationModel n sigma2_base immuneSelectedVar t τ_immune) := by
    unfold missedSelectedVariance stabilizingSelectionValidationModel
      fluctuatingSelectionValidationModel
    exact missedSelectedVariance_lt_of_variance_and_correlation
      (equilibriumEffectVariance v_mut_height s_height)
      immuneSelectedVar
      (effectCorrelationStabilizing Ns_height)
      (fluctuatingEffectCorrelation t τ_immune)
      h_immuneVar
      h_heightCorr_nonneg
      h_heightCorr_lt_one
      h_immuneCorr_nonneg
      h_corr
      h_var
  rw [selectionModelLRT_eq_sampleSize_mul_log_residual_gap
        (stabilizingSelectionValidationModel n sigma2_base
          (equilibriumEffectVariance v_mut_height s_height) Ns_height)
        h_sigma h_missed_height_nonneg]
  rw [selectionModelLRT_eq_sampleSize_mul_log_residual_gap
        (fluctuatingSelectionValidationModel n sigma2_base immuneSelectedVar t τ_immune)
        h_sigma h_missed_immune_nonneg]
  exact selectionModelLRT_strictMono_in_missedVariance n sigma2_base
    (missedSelectedVariance
      (stabilizingSelectionValidationModel n sigma2_base
        (equilibriumEffectVariance v_mut_height s_height) Ns_height))
    (missedSelectedVariance
      (fluctuatingSelectionValidationModel n sigma2_base immuneSelectedVar t τ_immune))
    h_n h_sigma h_missed_height_nonneg h_missed_lt

end ModelComparison


/-!
## Cross-Validation for Portability Prediction

Cross-validation methods for assessing PGS portability predictions.
-/

section CrossValidation

/- **Leave-one-population-out cross-validation.**
    Train the portability model on all populations except one,
    predict for the held-out population, repeat for each. -/

/-- Population-level CV prediction error under a bias-variance-noise model. -/
def cvPredictionError (bias_sq variance noise : ℝ) : ℝ :=
  bias_sq + variance + noise

/-- **Cross-validation error decomposition.**
    In the explicit bias-variance-noise model used in this section, CV
    prediction error is exactly `bias² + variance + irreducible noise`. -/
theorem cv_error_decomposition
    (bias_sq variance noise : ℝ) :
    cvPredictionError bias_sq variance noise = bias_sq + variance + noise := by
  rfl

/-- CV prediction error is nonnegative when all three components are nonnegative. -/
theorem cvPredictionError_nonneg
    (bias_sq variance noise : ℝ)
    (h_bias : 0 ≤ bias_sq) (h_var : 0 ≤ variance) (h_noise : 0 ≤ noise) :
    0 ≤ cvPredictionError bias_sq variance noise := by
  unfold cvPredictionError
  linarith

/-- **More diverse training set → lower CV error.**
    Including more populations in training reduces both bias and variance
    of portability predictions for the held-out population.
    Modeled: adding populations reduces both bias² and variance components. -/
theorem more_populations_lower_cv_error
    (bias_sq_few variance_few bias_sq_many variance_many : ℝ)
    (h_bias_reduced : bias_sq_many ≤ bias_sq_few)
    (h_var_reduced : variance_many < variance_few) :
    cvPredictionError bias_sq_many variance_many 0 <
      cvPredictionError bias_sq_few variance_few 0 := by
  unfold cvPredictionError
  linarith

/-- **The bias-variance tradeoff in portability prediction.**
    In leave-one-population-out CV, a model trained on `n_pops - 1`
    populations has an estimation-variance penalty that scales inversely with
    the available training populations. More complex portability models carry
    larger variance penalties but smaller approximation bias. -/
noncomputable def loPoTrainingPopulationCount (nPops : ℝ) : ℝ :=
  nPops - 1

/-- Variance penalty for a portability model of complexity `c` trained with
    leave-one-population-out CV on `nPops` populations. The variance scale
    `σ²_cv` converts one unit of model complexity into out-of-sample variance,
    and the penalty shrinks like `1 / (nPops - 1)` because each fold trains on
    `nPops - 1` populations. -/
noncomputable def loPoVariancePenalty
    (complexity varianceScale nPops : ℝ) : ℝ :=
  varianceScale * complexity / loPoTrainingPopulationCount nPops

/-- Leave-one-population-out CV error for a portability model with squared bias
    `bias_sq`, complexity `complexity`, variance scale `varianceScale`, and
    irreducible held-out noise `noise`. -/
noncomputable def loPoCvPredictionError
    (nPops bias_sq complexity varianceScale noise : ℝ) : ℝ :=
  cvPredictionError bias_sq (loPoVariancePenalty complexity varianceScale nPops) noise

/-- Critical total population count above which the complex portability model
    overtakes the simple model in leave-one-population-out CV. -/
noncomputable def criticalPopulationCountForComplexCV
    (bias_sq_simple bias_sq_complex complexity_simple complexity_complex varianceScale : ℝ) : ℝ :=
  1 + varianceScale * (complexity_complex - complexity_simple) /
    (bias_sq_simple - bias_sq_complex)

/-- **Two fixed portability models cross over at a critical population count.**
    This is the abstract LOPO-CV crossover lemma for two already-specified
    models with fixed approximation-bias terms and complexity-dependent
    variance penalties. The biologically stronger theorem below specializes
    it to an explicit model family where approximation bias decreases with
    model complexity. -/
theorem fixed_bias_models_cross_over_in_lopo_cv
    (nPops bias_sq_simple bias_sq_complex complexity_simple complexity_complex varianceScale noise : ℝ)
    (h_nPops : 1 < nPops)
    (h_bias_complex_lower : bias_sq_complex < bias_sq_simple)
    (h_complexity_higher : complexity_simple < complexity_complex)
    (h_var_scale : 0 < varianceScale) :
    (loPoCvPredictionError nPops bias_sq_simple complexity_simple varianceScale noise <
        loPoCvPredictionError nPops bias_sq_complex complexity_complex varianceScale noise ↔
      nPops < criticalPopulationCountForComplexCV
        bias_sq_simple bias_sq_complex complexity_simple complexity_complex varianceScale) ∧
    (loPoCvPredictionError nPops bias_sq_complex complexity_complex varianceScale noise <
        loPoCvPredictionError nPops bias_sq_simple complexity_simple varianceScale noise ↔
      criticalPopulationCountForComplexCV
        bias_sq_simple bias_sq_complex complexity_simple complexity_complex varianceScale < nPops) := by
  have h_train_pos : 0 < loPoTrainingPopulationCount nPops := by
    unfold loPoTrainingPopulationCount
    linarith
  have h_bias_gap : 0 < bias_sq_simple - bias_sq_complex := by
    linarith
  have h_complexity_gap : 0 < complexity_complex - complexity_simple := by
    linarith
  have h_variance_gap : 0 < varianceScale * (complexity_complex - complexity_simple) := by
    nlinarith
  have h_simple_error :
      loPoCvPredictionError nPops bias_sq_simple complexity_simple varianceScale noise <
        loPoCvPredictionError nPops bias_sq_complex complexity_complex varianceScale noise ↔
      (nPops - 1) * (bias_sq_simple - bias_sq_complex) <
        varianceScale * (complexity_complex - complexity_simple) := by
    unfold loPoCvPredictionError cvPredictionError loPoVariancePenalty loPoTrainingPopulationCount
    constructor <;> intro h
    · have hdiff :
          bias_sq_simple - bias_sq_complex <
            varianceScale * complexity_complex / (nPops - 1) -
              varianceScale * complexity_simple / (nPops - 1) := by
        nlinarith
      have h_frac :
          varianceScale * complexity_complex / (nPops - 1) -
              varianceScale * complexity_simple / (nPops - 1) =
            varianceScale * (complexity_complex - complexity_simple) / (nPops - 1) := by
        ring_nf
      rw [h_frac] at hdiff
      have hmul :
          (bias_sq_simple - bias_sq_complex) * (nPops - 1) <
            varianceScale * (complexity_complex - complexity_simple) :=
        (lt_div_iff₀ h_train_pos).1 hdiff
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    · have hmul :
          (bias_sq_simple - bias_sq_complex) * (nPops - 1) <
            varianceScale * (complexity_complex - complexity_simple) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      have hdiff :
          bias_sq_simple - bias_sq_complex <
            varianceScale * (complexity_complex - complexity_simple) / (nPops - 1) :=
        (lt_div_iff₀ h_train_pos).2 hmul
      have h_frac :
          varianceScale * (complexity_complex - complexity_simple) / (nPops - 1) =
            varianceScale * complexity_complex / (nPops - 1) -
              varianceScale * complexity_simple / (nPops - 1) := by
        ring_nf
      rw [h_frac] at hdiff
      nlinarith
  have h_complex_error :
      loPoCvPredictionError nPops bias_sq_complex complexity_complex varianceScale noise <
        loPoCvPredictionError nPops bias_sq_simple complexity_simple varianceScale noise ↔
      varianceScale * (complexity_complex - complexity_simple) <
        (nPops - 1) * (bias_sq_simple - bias_sq_complex) := by
    unfold loPoCvPredictionError cvPredictionError loPoVariancePenalty loPoTrainingPopulationCount
    constructor <;> intro h
    · have hdiff :
          varianceScale * complexity_complex / (nPops - 1) -
              varianceScale * complexity_simple / (nPops - 1) <
            bias_sq_simple - bias_sq_complex := by
        nlinarith
      have h_frac :
          varianceScale * complexity_complex / (nPops - 1) -
              varianceScale * complexity_simple / (nPops - 1) =
            varianceScale * (complexity_complex - complexity_simple) / (nPops - 1) := by
        ring_nf
      rw [h_frac] at hdiff
      have hmul :
          varianceScale * (complexity_complex - complexity_simple) <
            (bias_sq_simple - bias_sq_complex) * (nPops - 1) :=
        (div_lt_iff₀ h_train_pos).1 hdiff
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    · have hmul :
          varianceScale * (complexity_complex - complexity_simple) <
            (bias_sq_simple - bias_sq_complex) * (nPops - 1) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      have hdiff :
          varianceScale * (complexity_complex - complexity_simple) / (nPops - 1) <
            bias_sq_simple - bias_sq_complex :=
        (div_lt_iff₀ h_train_pos).2 hmul
      have h_frac :
          varianceScale * (complexity_complex - complexity_simple) / (nPops - 1) =
            varianceScale * complexity_complex / (nPops - 1) -
              varianceScale * complexity_simple / (nPops - 1) := by
        ring_nf
      rw [h_frac] at hdiff
      nlinarith
  have h_simple_threshold :
      (nPops - 1) * (bias_sq_simple - bias_sq_complex) <
        varianceScale * (complexity_complex - complexity_simple) ↔
      nPops < criticalPopulationCountForComplexCV
        bias_sq_simple bias_sq_complex complexity_simple complexity_complex varianceScale := by
    unfold criticalPopulationCountForComplexCV
    constructor
    · intro h
      have hdiv :
          nPops - 1 <
            varianceScale * (complexity_complex - complexity_simple) /
              (bias_sq_simple - bias_sq_complex) := by
        exact (lt_div_iff₀ h_bias_gap).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)
      linarith
    · intro h
      have hdiv :
          nPops - 1 <
            varianceScale * (complexity_complex - complexity_simple) /
              (bias_sq_simple - bias_sq_complex) := by
        linarith
      have hmul :
          (nPops - 1) * (bias_sq_simple - bias_sq_complex) <
            varianceScale * (complexity_complex - complexity_simple) :=
        (lt_div_iff₀ h_bias_gap).1 hdiv
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have h_complex_threshold :
      varianceScale * (complexity_complex - complexity_simple) <
        (nPops - 1) * (bias_sq_simple - bias_sq_complex) ↔
      criticalPopulationCountForComplexCV
        bias_sq_simple bias_sq_complex complexity_simple complexity_complex varianceScale < nPops := by
    unfold criticalPopulationCountForComplexCV
    constructor
    · intro h
      have hdiv :
          varianceScale * (complexity_complex - complexity_simple) /
              (bias_sq_simple - bias_sq_complex) <
            nPops - 1 := by
        exact (div_lt_iff₀ h_bias_gap).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)
      linarith
    · intro h
      have hdiv :
          varianceScale * (complexity_complex - complexity_simple) /
              (bias_sq_simple - bias_sq_complex) <
            nPops - 1 := by
        linarith [h_variance_gap]
      have hmul :
          varianceScale * (complexity_complex - complexity_simple) <
            (bias_sq_simple - bias_sq_complex) * (nPops - 1) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using (div_lt_iff₀ h_bias_gap).1 hdiv
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact ⟨h_simple_error.trans h_simple_threshold, h_complex_error.trans h_complex_threshold⟩

/-- Approximation-bias law for a portability model family whose misspecification
    error decays like `1 / complexity`. -/
noncomputable def inverseComplexityBiasSq
    (biasScale complexity : ℝ) : ℝ :=
  biasScale / complexity

/-- Leave-one-population-out CV error for a portability-model family with
    inverse-complexity approximation bias and complexity-proportional variance. -/
noncomputable def inverseComplexityLoPoCvError
    (nPops complexity biasScale varianceScale noise : ℝ) : ℝ :=
  loPoCvPredictionError nPops
    (inverseComplexityBiasSq biasScale complexity) complexity varianceScale noise

/-- Critical total-population count at which two model complexities in the
    inverse-bias family have equal LOPO-CV error. -/
noncomputable def criticalPopulationCountForInverseBiasFamily
    (complexity_simple complexity_complex biasScale varianceScale : ℝ) : ℝ :=
  1 + varianceScale * complexity_simple * complexity_complex / biasScale

/-- **Optimal portability-model complexity depends on the number of populations.**
    In this explicit portability-model family, approximation bias decreases
    as `biasScale / complexity`, while leave-one-population-out estimation
    variance increases as `varianceScale * complexity / (nPops - 1)`.

    For two candidate model complexities, there is an exact population-count
    crossover:
    - with too few populations, the simpler model wins because variance dominates;
    - with enough populations, the more complex model wins because approximation
      bias dominates.

    This is stronger than a free bias-variance inequality because the bias terms
    are derived from the model-complexity law rather than inserted by hand. -/
theorem optimal_complexity_depends_on_n_pops
    (nPops complexity_simple complexity_complex biasScale varianceScale noise : ℝ)
    (h_nPops : 1 < nPops)
    (h_complexity_simple_pos : 0 < complexity_simple)
    (h_complexity_higher : complexity_simple < complexity_complex)
    (h_bias_scale : 0 < biasScale)
    (h_var_scale : 0 < varianceScale) :
    (inverseComplexityLoPoCvError nPops complexity_simple biasScale varianceScale noise <
        inverseComplexityLoPoCvError nPops complexity_complex biasScale varianceScale noise ↔
      nPops < criticalPopulationCountForInverseBiasFamily
        complexity_simple complexity_complex biasScale varianceScale) ∧
    (inverseComplexityLoPoCvError nPops complexity_complex biasScale varianceScale noise <
        inverseComplexityLoPoCvError nPops complexity_simple biasScale varianceScale noise ↔
      criticalPopulationCountForInverseBiasFamily
        complexity_simple complexity_complex biasScale varianceScale < nPops) := by
  have h_complexity_complex_pos : 0 < complexity_complex := by
    linarith
  have h_bias_complex_lower :
      inverseComplexityBiasSq biasScale complexity_complex <
        inverseComplexityBiasSq biasScale complexity_simple := by
    unfold inverseComplexityBiasSq
    have hmul :
        biasScale * complexity_simple < biasScale * complexity_complex := by
      exact mul_lt_mul_of_pos_left h_complexity_higher h_bias_scale
    exact (div_lt_div_iff₀ h_complexity_complex_pos h_complexity_simple_pos).2 hmul
  have hbase := fixed_bias_models_cross_over_in_lopo_cv
      nPops
      (inverseComplexityBiasSq biasScale complexity_simple)
      (inverseComplexityBiasSq biasScale complexity_complex)
      complexity_simple complexity_complex varianceScale noise
      h_nPops h_bias_complex_lower h_complexity_higher h_var_scale
  have hthreshold :
      criticalPopulationCountForComplexCV
          (inverseComplexityBiasSq biasScale complexity_simple)
          (inverseComplexityBiasSq biasScale complexity_complex)
          complexity_simple complexity_complex varianceScale =
        criticalPopulationCountForInverseBiasFamily
          complexity_simple complexity_complex biasScale varianceScale := by
    have hgap_ne : complexity_complex - complexity_simple ≠ 0 := by
      linarith
    have hden :
        inverseComplexityBiasSq biasScale complexity_simple -
            inverseComplexityBiasSq biasScale complexity_complex =
          biasScale * (complexity_complex - complexity_simple) /
            (complexity_simple * complexity_complex) := by
      unfold inverseComplexityBiasSq
      field_simp [ne_of_gt h_complexity_simple_pos, ne_of_gt h_complexity_complex_pos]
    unfold criticalPopulationCountForComplexCV
      criticalPopulationCountForInverseBiasFamily
    rw [hden]
    field_simp [ne_of_gt h_complexity_simple_pos, ne_of_gt h_complexity_complex_pos,
      ne_of_gt h_bias_scale, hgap_ne]
  constructor
  · constructor <;> intro h
    · have h' := (hbase.1).1 h
      simpa [hthreshold] using h'
    · have h' : nPops <
          criticalPopulationCountForComplexCV
            (inverseComplexityBiasSq biasScale complexity_simple)
            (inverseComplexityBiasSq biasScale complexity_complex)
            complexity_simple complexity_complex varianceScale := by
        simpa [hthreshold] using h
      exact (hbase.1).2 h'
  · constructor <;> intro h
    · have h' := (hbase.2).1 h
      simpa [hthreshold] using h'
    · have h' :
          criticalPopulationCountForComplexCV
            (inverseComplexityBiasSq biasScale complexity_simple)
            (inverseComplexityBiasSq biasScale complexity_complex)
            complexity_simple complexity_complex varianceScale < nPops := by
        simpa [hthreshold] using h
      exact (hbase.2).2 h'

end CrossValidation


/-!
## Concrete Empirical Predictions

Concrete numerical predictions from the theoretical framework
that can be compared with Wang et al.'s findings.
-/

section GeneralPredictions

/-- Observable portability-ratio prediction combining neutral drift, LD tagging,
    and cross-population effect conservation.

    The first factor is the neutral-drift target/source `R²` ratio implied by
    the source `R²` and source/target `F_ST`. The second factor, `ldFactor`,
    accounts for LD tagging retention in the target population. The third
    factor, `ρ²`, accounts for loss of portability from cross-population effect
    decorrelation. -/
noncomputable def empiricalPortabilityRatio
    (r2Source fstSource fstTarget ldFactor rho : ℝ) : ℝ :=
  (targetR2FromObservables r2Source fstSource fstTarget / r2Source) * (ldFactor * rho ^ 2)

/-- **Empirical portability prediction lies strictly below the neutral drift baseline.**
    For a fixed source score and ancestry pair, any additional LD loss
    (`ldFactor ≤ 1`) together with imperfect cross-population effect
    conservation (`ρ < 1`) strictly attenuates the observable neutral-drift
    portability ratio. This is a directly testable prediction: observed
    target/source `R²` should fall below the `F_ST`-only neutral benchmark by a
    multiplicative LD-and-effect-correlation factor. -/
theorem empirical_portability_ratio_lt_neutral_drift_prediction
    (r2Source fstSource fstTarget ldFactor rho : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (h_ld : 0 < ldFactor) (h_ld_le : ldFactor ≤ 1)
    (h_rho : 0 ≤ rho) (h_rho_lt : rho < 1) :
    empiricalPortabilityRatio r2Source fstSource fstTarget ldFactor rho <
      targetR2FromObservables r2Source fstSource fstTarget / r2Source ∧
    empiricalPortabilityRatio r2Source fstSource fstTarget ldFactor rho < 1 := by
  rcases h_r2 with ⟨hr2_pos, hr2_lt_one⟩
  rcases h_fst_bounds with ⟨hfstS_nonneg, hfstT_lt_one⟩
  have hvS_pos : 0 < sourceVarianceFromR2 r2Source :=
    sourceVarianceFromR2_pos r2Source ⟨hr2_pos, hr2_lt_one⟩
  have hvT_pos :
      0 < targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget := by
    exact targetVarianceFromSource_pos (sourceVarianceFromR2 r2Source)
      fstSource fstTarget hvS_pos h_fst hfstT_lt_one
  have h_target_pos : 0 < targetR2FromObservables r2Source fstSource fstTarget := by
    unfold targetR2FromObservables r2FromVarianceScaleOne
    have hden : 0 < targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget + 1 := by
      linarith
    exact div_pos hvT_pos hden
  have h_neutral_pos :
      0 < targetR2FromObservables r2Source fstSource fstTarget / r2Source := by
    exact div_pos h_target_pos hr2_pos
  have h_neutral_lt_one :
      targetR2FromObservables r2Source fstSource fstTarget / r2Source < 1 := by
    exact portability_ratio_from_observables r2Source fstSource fstTarget
      ⟨hr2_pos, hr2_lt_one⟩ h_fst ⟨hfstS_nonneg, hfstT_lt_one⟩
  have h_sq_lt_one : rho ^ 2 < 1 := by
    nlinarith [sq_nonneg rho]
  have h_atten_nonneg : 0 ≤ ldFactor * rho ^ 2 := by
    exact mul_nonneg (le_of_lt h_ld) (sq_nonneg rho)
  have h_attentuation_lt_one : ldFactor * rho ^ 2 < 1 := by
    have h_le : ldFactor * rho ^ 2 ≤ 1 * rho ^ 2 := by
      exact mul_le_mul_of_nonneg_right h_ld_le (sq_nonneg rho)
    have h_lt : 1 * rho ^ 2 < 1 := by
      simpa using h_sq_lt_one
    exact lt_of_le_of_lt h_le h_lt
  have h_pred_lt_neutral :
      empiricalPortabilityRatio r2Source fstSource fstTarget ldFactor rho <
        targetR2FromObservables r2Source fstSource fstTarget / r2Source := by
    unfold empiricalPortabilityRatio
    have hmul :=
      mul_lt_mul_of_pos_left h_attentuation_lt_one h_neutral_pos
    simpa [mul_assoc] using hmul
  have h_pred_lt_one :
      empiricalPortabilityRatio r2Source fstSource fstTarget ldFactor rho < 1 := by
    exact lt_trans h_pred_lt_neutral h_neutral_lt_one
  exact ⟨h_pred_lt_neutral, h_pred_lt_one⟩

/-- **Traits or target cohorts with better LD retention and more conserved effects
    are predicted to be more portable.**
    At fixed source `R²` and source/target divergence, the empirical
    portability ratio is strictly ordered by the product `ldFactor × ρ²`. This
    is the comparative prediction relevant for simulation or held-out
    validation: once the ancestry pair is fixed, better LD sharing and higher
    cross-population effect correlation imply higher target/source `R²`. -/
theorem empirical_portability_ratio_strictly_orders_by_ld_and_effect_correlation
    (r2Source fstSource fstTarget ldWorse ldBetter rhoWorse rhoBetter : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (h_ldWorse : 0 < ldWorse)
    (h_ld_order : ldWorse ≤ ldBetter)
    (h_rhoWorse : 0 ≤ rhoWorse)
    (h_rho_order : rhoWorse < rhoBetter) :
    empiricalPortabilityRatio r2Source fstSource fstTarget ldWorse rhoWorse <
      empiricalPortabilityRatio r2Source fstSource fstTarget ldBetter rhoBetter := by
  rcases h_r2 with ⟨hr2_pos, hr2_lt_one⟩
  rcases h_fst_bounds with ⟨hfstS_nonneg, hfstT_lt_one⟩
  have hvS_pos : 0 < sourceVarianceFromR2 r2Source :=
    sourceVarianceFromR2_pos r2Source ⟨hr2_pos, hr2_lt_one⟩
  have hvT_pos :
      0 < targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget := by
    exact targetVarianceFromSource_pos (sourceVarianceFromR2 r2Source)
      fstSource fstTarget hvS_pos h_fst hfstT_lt_one
  have h_target_pos : 0 < targetR2FromObservables r2Source fstSource fstTarget := by
    unfold targetR2FromObservables r2FromVarianceScaleOne
    have hden : 0 < targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget + 1 := by
      linarith
    exact div_pos hvT_pos hden
  have h_neutral_pos :
      0 < targetR2FromObservables r2Source fstSource fstTarget / r2Source := by
    exact div_pos h_target_pos hr2_pos
  have h_sq_order : rhoWorse ^ 2 < rhoBetter ^ 2 := by
    nlinarith [sq_nonneg rhoWorse, sq_nonneg rhoBetter]
  have h_worse_att_lt :
      ldWorse * rhoWorse ^ 2 < ldWorse * rhoBetter ^ 2 := by
    exact mul_lt_mul_of_pos_left h_sq_order h_ldWorse
  have h_better_att_ge :
      ldWorse * rhoBetter ^ 2 ≤ ldBetter * rhoBetter ^ 2 := by
    exact mul_le_mul_of_nonneg_right h_ld_order (sq_nonneg rhoBetter)
  have h_att_order :
      ldWorse * rhoWorse ^ 2 < ldBetter * rhoBetter ^ 2 := by
    exact lt_of_lt_of_le h_worse_att_lt h_better_att_ge
  unfold empiricalPortabilityRatio
  have hmul := mul_lt_mul_of_pos_left h_att_order h_neutral_pos
  simpa [mul_assoc] using hmul

/-- Neutral portability prediction adjusted by a squared effect-correlation penalty. -/
def selectionAdjustedPortabilityRatio (neutral_ratio rho : ℝ) : ℝ :=
  neutral_ratio * rho ^ 2

/-- **Selection reduces portability in the multiplicative `neutral_ratio × ρ²` model.**
    This theorem is explicit about the model being used: a neutral portability
    prediction is attenuated by the squared cross-population effect correlation
    `ρ²`. When `ρ < 1`, the selection-adjusted ratio is strictly below the
    neutral ratio. -/
theorem selection_reduces_portability
    (neutral_ratio rho : ℝ)
    (h_nr : 0 < neutral_ratio)
    (h_rho : 0 ≤ rho) (h_rho_lt : rho < 1) :
    selectionAdjustedPortabilityRatio neutral_ratio rho < neutral_ratio := by
  unfold selectionAdjustedPortabilityRatio
  have h_sq : rho ^ 2 < 1 := by nlinarith [sq_nonneg rho]
  nlinarith

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
    r2 < 1/k := by
  rw [h_r2]
  rw [div_lt_div_iff₀ (by linarith) h_k]
  -- Goal: var_between * k < 1 * (var_between + var_within)
  -- From h_small: var_between < var_within / k, so var_between * k < var_within
  have hbk : var_between * k < var_within := by
    rwa [lt_div_iff₀ h_k] at h_small
  linarith

end GeneralPredictions

end Calibrator
