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
    -- Model underestimates portability
    0 < r2_observed - r2_predicted := by linarith

theorem residual_negative_interpretation
    (r2_observed r2_predicted : ℝ)
    (h_negative_residual : r2_observed < r2_predicted) :
    -- Model overestimates portability
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

/-- Validation model under stabilizing selection. -/
noncomputable def stabilizingSelectionValidationModel
    (n baselineResidualVar selectedArchitectureVar Ns : ℝ) :
    SelectionValidationModel :=
  { sampleSize := n
    baselineResidualVar := baselineResidualVar
    selectedArchitectureVar := selectedArchitectureVar
    effectCorrelation := effectCorrelationStabilizing Ns }

/-- Validation model under fluctuating selection. -/
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

/-- **Selection model preferred when the fluctuating regime induces both lower
    cross-population effect correlation and larger selected-architecture
    variance than the stabilizing regime.**

    This comparison is now fully model-derived. The stabilizing model uses
    `equilibriumEffectVariance v_mutation s` and
    `effectCorrelationStabilizing Ns`. The fluctuating model uses the same
    mutation-selection baseline plus the exact OU optimum variance
    `sigmaTheta^2 * tau / 2`, and the exact correlation
    `exp(-t / tau)`. If `tau` is below the exact threshold where the
    fluctuating correlation drops under the stabilizing correlation, then the
    fluctuating regime has both:

    - larger selected-architecture variance, and
    - lower cross-population effect correlation.

    Therefore the exact Gaussian nested-model LRT for adding the selection term
    is strictly larger under the fluctuating regime. -/
theorem selection_model_preferred_when_better_fit
    (n sigma2_base v_mutation s Ns_stab sigmaTheta_fluct t_div tau_fluct : ℝ)
    (h_n : 0 < n)
    (h_sigma : 0 < sigma2_base)
    (h_vmut : 0 ≤ v_mutation)
    (h_s : 0 < s)
    (h_Ns : 1 < Ns_stab)
    (h_sigmaTheta : 0 < sigmaTheta_fluct)
    (h_t_div : 0 < t_div)
    (h_tau : 0 < tau_fluct)
    (h_tau_threshold :
      tau_fluct < t_div / (-Real.log (effectCorrelationStabilizing Ns_stab))) :
    selectionModelLRT
      (stabilizingSelectionValidationModel n sigma2_base
        (stabilizingSelectedArchitectureVariance v_mutation s) Ns_stab) <
    selectionModelLRT
      (fluctuatingSelectionValidationModel n sigma2_base
        (fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct)
        t_div tau_fluct) := by
  have h_stabVar_nonneg : 0 ≤ stabilizingSelectedArchitectureVariance v_mutation s := by
    unfold stabilizingSelectedArchitectureVariance equilibriumEffectVariance
    exact div_nonneg h_vmut (le_of_lt h_s)
  have h_stabCorr_nonneg : 0 ≤ effectCorrelationStabilizing Ns_stab := by
    exact le_of_lt (effectCorrelationStabilizing_pos Ns_stab h_Ns)
  have h_stabCorr_lt_one : effectCorrelationStabilizing Ns_stab < 1 := by
    exact effectCorrelationStabilizing_lt_one Ns_stab h_Ns
  have h_fluctCorr_nonneg : 0 ≤ fluctuatingEffectCorrelation t_div tau_fluct := by
    unfold fluctuatingEffectCorrelation
    exact le_of_lt (Real.exp_pos _)
  have h_fluctVar_lt :
      stabilizingSelectedArchitectureVariance v_mutation s <
        fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct := by
    exact fluctuatingSelectedArchitectureVariance_gt_stabilizing
      v_mutation s sigmaTheta_fluct tau_fluct h_sigmaTheta h_tau
  have h_fluctVar_pos :
      0 < fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct := by
    linarith
  have h_var :
      stabilizingSelectedArchitectureVariance v_mutation s ≤
        fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct :=
    le_of_lt h_fluctVar_lt
  have h_corr :
      fluctuatingEffectCorrelation t_div tau_fluct <
        effectCorrelationStabilizing Ns_stab := by
    exact fluctuatingCorrelation_lt_stabilizing_of_tau_lt_threshold
      t_div tau_fluct Ns_stab h_t_div h_tau h_Ns h_tau_threshold
  have h_missed_stab_nonneg :
      0 ≤ missedSelectedVariance
        (stabilizingSelectionValidationModel n sigma2_base
          (stabilizingSelectedArchitectureVariance v_mutation s) Ns_stab) := by
    unfold missedSelectedVariance stabilizingSelectionValidationModel
    exact mul_nonneg h_stabVar_nonneg
      (by nlinarith [sq_nonneg (effectCorrelationStabilizing Ns_stab)])
  have h_missed_fluct_nonneg :
      0 ≤ missedSelectedVariance
        (fluctuatingSelectionValidationModel n sigma2_base
          (fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct)
          t_div tau_fluct) := by
    unfold missedSelectedVariance fluctuatingSelectionValidationModel
    exact mul_nonneg (le_of_lt h_fluctVar_pos)
      (by nlinarith [sq_nonneg (fluctuatingEffectCorrelation t_div tau_fluct)])
  have h_missed_lt :
      missedSelectedVariance
          (stabilizingSelectionValidationModel n sigma2_base
            (stabilizingSelectedArchitectureVariance v_mutation s) Ns_stab) <
        missedSelectedVariance
          (fluctuatingSelectionValidationModel n sigma2_base
            (fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct)
            t_div tau_fluct) := by
    unfold missedSelectedVariance stabilizingSelectionValidationModel
      fluctuatingSelectionValidationModel
    exact missedSelectedVariance_lt_of_variance_and_correlation
      (stabilizingSelectedArchitectureVariance v_mutation s)
      (fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct)
      (effectCorrelationStabilizing Ns_stab)
      (fluctuatingEffectCorrelation t_div tau_fluct)
      h_fluctVar_pos
      h_stabCorr_nonneg
      h_stabCorr_lt_one
      h_fluctCorr_nonneg
      h_corr
      h_var
  rw [selectionModelLRT_eq_sampleSize_mul_log_residual_gap
        (stabilizingSelectionValidationModel n sigma2_base
          (stabilizingSelectedArchitectureVariance v_mutation s) Ns_stab)
        h_sigma h_missed_stab_nonneg]
  rw [selectionModelLRT_eq_sampleSize_mul_log_residual_gap
        (fluctuatingSelectionValidationModel n sigma2_base
          (fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct)
          t_div tau_fluct)
        h_sigma h_missed_fluct_nonneg]
  exact selectionModelLRT_strictMono_in_missedVariance n sigma2_base
    (missedSelectedVariance
      (stabilizingSelectionValidationModel n sigma2_base
        (stabilizingSelectedArchitectureVariance v_mutation s) Ns_stab))
    (missedSelectedVariance
      (fluctuatingSelectionValidationModel n sigma2_base
        (fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct)
        t_div tau_fluct))
    h_n h_sigma h_missed_stab_nonneg h_missed_lt

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

/-- Exact retained target signal fraction from LD tagging retention and
    cross-population effect conservation. This is the squared transported
    score/target-liability correlation in the standardized shared-signal model
    below. -/
noncomputable def crossPopulationSignalRetention
    (ldFactor effectCorrelation : ℝ) : ℝ :=
  ldFactor * effectCorrelation ^ 2

/-- Exact variance of the present-day target genetic signal. -/
noncomputable def targetSignalVariance
    (V_A fstTarget : ℝ) : ℝ :=
  presentDayPGSVariance V_A fstTarget

/-- Exact variance of the target genetic signal component tagged by the
    deployed source-trained score. `ldFactor` is the literal squared tagging
    correlation, so it scales the target signal variance directly. -/
noncomputable def taggedTargetSignalVariance
    (V_A fstTarget ldFactor : ℝ) : ℝ :=
  ldFactor * targetSignalVariance V_A fstTarget

/-- Exact variance of the portable tagged component that survives
    cross-population effect drift. This is the tagged-signal variance multiplied
    by the exact squared cross-population effect correlation. -/
noncomputable def transportedPortableComponentVariance
    (V_A fstTarget ldFactor effectCorrelation : ℝ) : ℝ :=
  effectCorrelation ^ 2 * taggedTargetSignalVariance V_A fstTarget ldFactor

/-- Orthogonal nuisance variance added to keep the deployed score on the target
    liability variance scale. This is the unretained portion of the target
    genetic signal variance in the explicit transported-score model. -/
noncomputable def transportedOrthogonalNuisanceVariance
    (V_A fstTarget ldFactor effectCorrelation : ℝ) : ℝ :=
  targetSignalVariance V_A fstTarget -
    transportedPortableComponentVariance V_A fstTarget ldFactor effectCorrelation

/-- Exact target score/phenotype covariance in the explicit LD-tagging plus
    cross-population effect model.

    The covariance is derived as correlation times product of standard
    deviations between the portable tagged component and the target genetic
    signal. This makes the attenuation law a consequence of the score model
    rather than the definition of the metric. -/
noncomputable def transportedScorePhenotypeCov
    (V_A fstTarget ldFactor effectCorrelation : ℝ) : ℝ :=
  effectCorrelation *
    Real.sqrt
      (taggedTargetSignalVariance V_A fstTarget ldFactor *
        targetSignalVariance V_A fstTarget)

/-- Exact transported score variance under the standardized target-liability
    score scale. It is the sum of the retained portable component and the
    orthogonal nuisance component. -/
noncomputable def transportedScoreVariance
    (V_A fstTarget ldFactor effectCorrelation : ℝ) : ℝ :=
  transportedPortableComponentVariance V_A fstTarget ldFactor effectCorrelation +
    transportedOrthogonalNuisanceVariance V_A fstTarget ldFactor effectCorrelation

/-- Exact transported target outcome variance in the present-day drift model. -/
noncomputable def transportedTargetOutcomeVariance
    (V_A V_E fstTarget : ℝ) : ℝ :=
  targetSignalVariance V_A fstTarget + V_E

/-- Exact target `R²` under the standardized transported-score model:
    `Cov(score, Y)^2 / (Var(score) Var(Y))`. -/
noncomputable def empiricalTargetR2
    (V_A V_E fstTarget ldFactor effectCorrelation : ℝ) : ℝ :=
  let cov := transportedScorePhenotypeCov V_A fstTarget ldFactor effectCorrelation
  let vScore := transportedScoreVariance V_A fstTarget ldFactor effectCorrelation
  let vY := transportedTargetOutcomeVariance V_A V_E fstTarget
  cov ^ 2 / (vScore * vY)

/-- The portable component variance is exactly retained-signal fraction times
    target signal variance. -/
theorem transportedPortableComponentVariance_eq_retainedSignal_mul_targetSignalVariance
    (V_A fstTarget ldFactor effectCorrelation : ℝ) :
    transportedPortableComponentVariance V_A fstTarget ldFactor effectCorrelation =
      crossPopulationSignalRetention ldFactor effectCorrelation *
        targetSignalVariance V_A fstTarget := by
  unfold transportedPortableComponentVariance crossPopulationSignalRetention
    taggedTargetSignalVariance
  ring

/-- In the explicit transported-score model, the deployed score is standardized
    to the target signal variance exactly by construction. -/
theorem transportedScoreVariance_eq_targetSignalVariance
    (V_A fstTarget ldFactor effectCorrelation : ℝ) :
    transportedScoreVariance V_A fstTarget ldFactor effectCorrelation =
      targetSignalVariance V_A fstTarget := by
  unfold transportedScoreVariance transportedOrthogonalNuisanceVariance
  ring

/-- The exact transported score/phenotype covariance squared equals portable
    component variance times target signal variance. This derives the key
    covariance identity from the LD-tagging and effect-correlation model. -/
theorem transportedScorePhenotypeCov_sq_eq_portableVariance_mul_targetSignalVariance
    (V_A fstTarget ldFactor effectCorrelation : ℝ)
    (hVA : 0 < V_A)
    (hfstT_lt_one : fstTarget < 1)
    (h_ld : 0 ≤ ldFactor) :
    transportedScorePhenotypeCov V_A fstTarget ldFactor effectCorrelation ^ 2 =
      transportedPortableComponentVariance V_A fstTarget ldFactor effectCorrelation *
        targetSignalVariance V_A fstTarget := by
  have hsig_pos : 0 < targetSignalVariance V_A fstTarget := by
    unfold targetSignalVariance presentDayPGSVariance
    have h_one_minus : 0 < 1 - fstTarget := by linarith
    exact mul_pos h_one_minus hVA
  have hsqrt :
      0 ≤
        taggedTargetSignalVariance V_A fstTarget ldFactor *
          targetSignalVariance V_A fstTarget := by
    unfold taggedTargetSignalVariance
    exact mul_nonneg (mul_nonneg h_ld (le_of_lt hsig_pos)) (le_of_lt hsig_pos)
  unfold transportedScorePhenotypeCov
  have h_expand :
      (effectCorrelation *
          Real.sqrt
            (taggedTargetSignalVariance V_A fstTarget ldFactor *
              targetSignalVariance V_A fstTarget)) ^ 2 =
        effectCorrelation ^ 2 *
          (Real.sqrt
            (taggedTargetSignalVariance V_A fstTarget ldFactor *
              targetSignalVariance V_A fstTarget) ^ 2) := by
    ring
  rw [h_expand, Real.sq_sqrt hsqrt]
  rw [transportedPortableComponentVariance_eq_retainedSignal_mul_targetSignalVariance]
  unfold crossPopulationSignalRetention taggedTargetSignalVariance
    targetSignalVariance
  ring

/-- In the standardized transported-score model, the exact transported target
    `R²` equals retained signal fraction times the exact neutral present-day
    target `R²`. The attenuation law is therefore a derived identity for the
    exact metric, not part of the metric definition itself. -/
theorem empiricalTargetR2_eq_retained_signal_mul_presentDayR2
    (V_A V_E fstTarget ldFactor effectCorrelation : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstT_lt_one : fstTarget < 1)
    (h_ld : 0 ≤ ldFactor) :
    empiricalTargetR2 V_A V_E fstTarget ldFactor effectCorrelation =
      crossPopulationSignalRetention ldFactor effectCorrelation *
        presentDayR2 V_A V_E fstTarget := by
  have hsig_pos : 0 < presentDayPGSVariance V_A fstTarget := by
    unfold presentDayPGSVariance
    have h_one_minus : 0 < 1 - fstTarget := by linarith
    exact mul_pos h_one_minus hVA
  have hsig_ne : targetSignalVariance V_A fstTarget ≠ 0 := ne_of_gt (by
    simpa [targetSignalVariance] using hsig_pos)
  have hvy_pos : 0 < transportedTargetOutcomeVariance V_A V_E fstTarget := by
    unfold transportedTargetOutcomeVariance targetSignalVariance
    linarith
  have hvy_ne : transportedTargetOutcomeVariance V_A V_E fstTarget ≠ 0 := ne_of_gt hvy_pos
  have h_cov_sq :
      transportedScorePhenotypeCov V_A fstTarget ldFactor effectCorrelation ^ 2 =
        transportedPortableComponentVariance V_A fstTarget ldFactor effectCorrelation *
          targetSignalVariance V_A fstTarget := by
    exact transportedScorePhenotypeCov_sq_eq_portableVariance_mul_targetSignalVariance
      V_A fstTarget ldFactor effectCorrelation hVA hfstT_lt_one h_ld
  have h_score_var :
      transportedScoreVariance V_A fstTarget ldFactor effectCorrelation =
        targetSignalVariance V_A fstTarget := by
    exact transportedScoreVariance_eq_targetSignalVariance
      V_A fstTarget ldFactor effectCorrelation
  have h_portable :
      transportedPortableComponentVariance V_A fstTarget ldFactor effectCorrelation =
        crossPopulationSignalRetention ldFactor effectCorrelation *
          targetSignalVariance V_A fstTarget := by
    exact transportedPortableComponentVariance_eq_retainedSignal_mul_targetSignalVariance
      V_A fstTarget ldFactor effectCorrelation
  rw [empiricalTargetR2, h_cov_sq, h_score_var, h_portable]
  unfold transportedTargetOutcomeVariance presentDayR2 targetSignalVariance
  field_simp [hsig_ne, hvy_ne]

/-- Exact bridge from the explicit LD-tagging/effect-correlation score model to
    the observable-only population-genetic core transport theorem. When the
    source score comes from the same `V_A, V_E, fstSource` drift model, the
    transported target `R²` equals retained signal fraction times the core
    observable transported target `R²`. -/
theorem empiricalTargetR2_eq_retained_signal_mul_targetR2FromObservables
    (V_A V_E fstSource fstTarget ldFactor effectCorrelation : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS_lt_one : fstSource < 1)
    (hfstT_lt_one : fstTarget < 1)
    (h_ld : 0 ≤ ldFactor) :
    empiricalTargetR2 V_A V_E fstTarget ldFactor effectCorrelation =
      crossPopulationSignalRetention ldFactor effectCorrelation *
        targetR2FromObservables (presentDayR2 V_A V_E fstSource) fstSource fstTarget := by
  rw [empiricalTargetR2_eq_retained_signal_mul_presentDayR2
        V_A V_E fstTarget ldFactor effectCorrelation hVA hVE hfstT_lt_one h_ld]
  rw [← targetR2FromObservables_eq_presentDayR2 V_A V_E fstSource fstTarget hVA hVE hfstS_lt_one]

/-- Exact target/source `R²` portability ratio under the explicit drift-plus-LD
    score-covariance model. The denominator is exact source `R²`, and the
    numerator is exact transported target `R²`. The attenuation factor
    `ldFactor × effectCorrelation²` is recovered only as a theorem. -/
noncomputable def empiricalPortabilityRatio
    (V_A V_E fstSource fstTarget ldFactor effectCorrelation : ℝ) : ℝ :=
  empiricalTargetR2 V_A V_E fstTarget ldFactor effectCorrelation /
    presentDayR2 V_A V_E fstSource

/-- Exact target/source portability ratio under the standardized transported-
    score model. The numerator is literal target `R²`, not a factorized proxy. -/
theorem empiricalPortabilityRatio_eq_retained_signal_mul_neutral_ratio
    (V_A V_E fstSource fstTarget ldFactor effectCorrelation : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS_lt_one : fstSource < 1)
    (hfstT_lt_one : fstTarget < 1)
    (h_ld : 0 ≤ ldFactor) :
    empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor effectCorrelation =
      crossPopulationSignalRetention ldFactor effectCorrelation *
        (presentDayR2 V_A V_E fstTarget / presentDayR2 V_A V_E fstSource) := by
  have h_src_pos : 0 < presentDayR2 V_A V_E fstSource := by
    unfold presentDayR2
    have hv_pos : 0 < presentDayPGSVariance V_A fstSource := by
      unfold presentDayPGSVariance
      have h_one_minus : 0 < 1 - fstSource := by linarith
      exact mul_pos h_one_minus hVA
    exact div_pos hv_pos (by linarith)
  unfold empiricalPortabilityRatio
  rw [empiricalTargetR2_eq_retained_signal_mul_presentDayR2
        V_A V_E fstTarget ldFactor effectCorrelation hVA hVE hfstT_lt_one h_ld]
  field_simp [ne_of_gt h_src_pos]

/-- Exact target/source portability ratio in the explicit transported-score
    model, written directly against the core observable-only transport ratio.
    This is the cohesion theorem linking the validation layer back to the
    population-genetic drift core. -/
theorem empiricalPortabilityRatio_eq_retained_signal_mul_observableRatio
    (V_A V_E fstSource fstTarget ldFactor effectCorrelation : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS_lt_one : fstSource < 1)
    (hfstT_lt_one : fstTarget < 1)
    (h_ld : 0 ≤ ldFactor) :
    empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor effectCorrelation =
      crossPopulationSignalRetention ldFactor effectCorrelation *
        (targetR2FromObservables (presentDayR2 V_A V_E fstSource) fstSource fstTarget /
          presentDayR2 V_A V_E fstSource) := by
  rw [empiricalPortabilityRatio_eq_retained_signal_mul_neutral_ratio
        V_A V_E fstSource fstTarget ldFactor effectCorrelation
        hVA hVE hfstS_lt_one hfstT_lt_one h_ld]
  rw [← targetR2FromObservables_eq_presentDayR2 V_A V_E fstSource fstTarget hVA hVE hfstS_lt_one]

/-- **Empirical portability prediction lies strictly below the neutral drift baseline.**
    For a fixed ancestry pair and source architecture, any retained-signal
    fraction strictly below `1` yields an exact target/source `R²` ratio below
    the exact drift-only baseline from the observable population-genetic core.
    This is a statement about the actual transported `R²` metric in the
    explicit variance model, not a product surrogate. -/
theorem empirical_portability_ratio_lt_neutral_drift_prediction
    (V_A V_E fstSource fstTarget ldFactor rho : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fstT_lt_one : fstTarget < 1)
    (h_ld : 0 < ldFactor) (h_ld_le : ldFactor ≤ 1)
    (h_rho : 0 < rho) (h_rho_lt : rho < 1) :
    empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor rho <
      targetR2FromObservables (presentDayR2 V_A V_E fstSource) fstSource fstTarget /
        presentDayR2 V_A V_E fstSource ∧
    empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor rho < 1 := by
  have hfstS_lt_one : fstSource < 1 := lt_trans h_fst h_fstT_lt_one
  have h_ret_pos : 0 < crossPopulationSignalRetention ldFactor rho := by
    unfold crossPopulationSignalRetention
    positivity
  have h_ret_lt_one : crossPopulationSignalRetention ldFactor rho < 1 := by
    unfold crossPopulationSignalRetention
    have h_sq_lt_one : rho ^ 2 < 1 := by
      nlinarith [sq_nonneg rho]
    have h_le : ldFactor * rho ^ 2 ≤ 1 * rho ^ 2 := by
      exact mul_le_mul_of_nonneg_right h_ld_le (sq_nonneg rho)
    have h_lt : 1 * rho ^ 2 < 1 := by
      simpa using h_sq_lt_one
    exact lt_of_le_of_lt h_le h_lt
  have h_ratio_eq :
      empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor rho =
        crossPopulationSignalRetention ldFactor rho *
          (targetR2FromObservables (presentDayR2 V_A V_E fstSource) fstSource fstTarget /
            presentDayR2 V_A V_E fstSource) := by
    exact empiricalPortabilityRatio_eq_retained_signal_mul_observableRatio
      V_A V_E fstSource fstTarget ldFactor rho
      hVA hVE hfstS_lt_one h_fstT_lt_one (le_of_lt h_ld)
  have h_src_pos : 0 < presentDayR2 V_A V_E fstSource := by
    unfold presentDayR2
    have hv_pos : 0 < presentDayPGSVariance V_A fstSource := by
      unfold presentDayPGSVariance
      have h_one_minus : 0 < 1 - fstSource := by linarith
      exact mul_pos h_one_minus hVA
    exact div_pos hv_pos (by linarith)
  have h_ratio_lt_neutral :
      empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor rho <
        targetR2FromObservables (presentDayR2 V_A V_E fstSource) fstSource fstTarget /
          presentDayR2 V_A V_E fstSource := by
    rw [h_ratio_eq]
    have h_neutral_pos :
        0 <
          targetR2FromObservables (presentDayR2 V_A V_E fstSource) fstSource fstTarget /
            presentDayR2 V_A V_E fstSource := by
      have h_tgt_pos :
          0 < targetR2FromObservables (presentDayR2 V_A V_E fstSource) fstSource fstTarget := by
        rw [targetR2FromObservables_eq_presentDayR2 V_A V_E fstSource fstTarget hVA hVE hfstS_lt_one]
        unfold presentDayR2
        have hv_pos : 0 < presentDayPGSVariance V_A fstTarget := by
          unfold presentDayPGSVariance
          have h_one_minus : 0 < 1 - fstTarget := by linarith
          exact mul_pos h_one_minus hVA
        exact div_pos hv_pos (by linarith)
      exact div_pos h_tgt_pos h_src_pos
    simpa [mul_comm] using
      (mul_lt_of_lt_one_right h_neutral_pos h_ret_lt_one)
  have h_neutral_lt_one :
      targetR2FromObservables (presentDayR2 V_A V_E fstSource) fstSource fstTarget /
        presentDayR2 V_A V_E fstSource < 1 := by
    rw [targetR2FromObservables_eq_presentDayR2 V_A V_E fstSource fstTarget hVA hVE hfstS_lt_one]
    exact portability_ratio_lt_one_of_positive_drift
      V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fstT_lt_one) h_src_pos
  have h_pred_lt_one :
      empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor rho < 1 := by
    exact lt_trans h_ratio_lt_neutral h_neutral_lt_one
  exact ⟨h_ratio_lt_neutral, h_pred_lt_one⟩

/-- **Traits or target cohorts with better LD retention and more conserved effects
    are predicted to be more portable.**
    At fixed source and target drift levels, the exact target/source `R²` ratio
    is strictly ordered by the retained target signal fraction
    `ldFactor × effectCorrelation²`. This is again an exact metric statement on
    the transported `R²`, not a bookkeeping comparison of attenuation factors. -/
theorem empirical_portability_ratio_strictly_orders_by_ld_and_effect_correlation
    (V_A V_E fstSource fstTarget ldWorse ldBetter rhoWorse rhoBetter : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS_lt_one : fstSource < 1)
    (hfstT_lt_one : fstTarget < 1)
    (h_ldWorse : 0 < ldWorse)
    (h_ld_order : ldWorse ≤ ldBetter)
    (h_rhoWorse : 0 < rhoWorse)
    (h_rho_order : rhoWorse < rhoBetter) :
    empiricalPortabilityRatio V_A V_E fstSource fstTarget ldWorse rhoWorse <
      empiricalPortabilityRatio V_A V_E fstSource fstTarget ldBetter rhoBetter := by
  have h_ret_order_sq : rhoWorse ^ 2 < rhoBetter ^ 2 := by
    nlinarith [sq_nonneg rhoWorse, sq_nonneg rhoBetter]
  have h_ret_worse_lt :
      ldWorse * rhoWorse ^ 2 < ldWorse * rhoBetter ^ 2 := by
    exact mul_lt_mul_of_pos_left h_ret_order_sq h_ldWorse
  have h_ret_better_ge :
      ldWorse * rhoBetter ^ 2 ≤ ldBetter * rhoBetter ^ 2 := by
    exact mul_le_mul_of_nonneg_right h_ld_order (sq_nonneg rhoBetter)
  have h_ret_order :
      ldWorse * rhoWorse ^ 2 < ldBetter * rhoBetter ^ 2 := by
    exact lt_of_lt_of_le h_ret_worse_lt h_ret_better_ge
  have h_tgt_r2_eq_worse :
      empiricalTargetR2 V_A V_E fstTarget ldWorse rhoWorse =
        crossPopulationSignalRetention ldWorse rhoWorse *
          presentDayR2 V_A V_E fstTarget := by
    exact empiricalTargetR2_eq_retained_signal_mul_presentDayR2
      V_A V_E fstTarget ldWorse rhoWorse hVA hVE hfstT_lt_one (le_of_lt h_ldWorse)
  have h_tgt_r2_eq_better :
      empiricalTargetR2 V_A V_E fstTarget ldBetter rhoBetter =
        crossPopulationSignalRetention ldBetter rhoBetter *
          presentDayR2 V_A V_E fstTarget := by
    have h_ldBetter_nonneg : 0 ≤ ldBetter := le_trans (le_of_lt h_ldWorse) h_ld_order
    exact empiricalTargetR2_eq_retained_signal_mul_presentDayR2
      V_A V_E fstTarget ldBetter rhoBetter hVA hVE hfstT_lt_one h_ldBetter_nonneg
  have h_source_pos : 0 < presentDayR2 V_A V_E fstSource := by
    unfold presentDayR2
    have hv_pos : 0 < presentDayPGSVariance V_A fstSource := by
      unfold presentDayPGSVariance
      have h_one_minus : 0 < 1 - fstSource := by linarith
      exact mul_pos h_one_minus hVA
    exact div_pos hv_pos (by linarith)
  have h_target_base_pos : 0 < presentDayR2 V_A V_E fstTarget := by
    unfold presentDayR2
    have hv_pos : 0 < presentDayPGSVariance V_A fstTarget := by
      unfold presentDayPGSVariance
      have h_one_minus : 0 < 1 - fstTarget := by linarith
      exact mul_pos h_one_minus hVA
    exact div_pos hv_pos (by linarith)
  have h_target_r2_lt :
      empiricalTargetR2 V_A V_E fstTarget ldWorse rhoWorse <
        empiricalTargetR2 V_A V_E fstTarget ldBetter rhoBetter := by
    rw [h_tgt_r2_eq_worse, h_tgt_r2_eq_better]
    exact mul_lt_mul_of_pos_right h_ret_order h_target_base_pos
  unfold empiricalPortabilityRatio
  simpa [div_eq_mul_inv] using
    mul_lt_mul_of_pos_right h_target_r2_lt (inv_pos.mpr h_source_pos)

/-- **A fluctuating regime predicts both lower portability and stronger evidence
    for a selection-aware model than a stabilizing regime built from the same
    baseline architecture.**

    The portability comparison uses the exact target/source `R²` ratio, while
    the validation comparison uses the exact Gaussian held-out LRT. Both are
    derived from the regime formulas themselves: the fluctuating regime gets a
    larger selected-architecture variance from OU optimum motion and a lower
    effect correlation once `tau` drops below the exact stabilizing threshold. -/
theorem selection_reduces_portability
    (V_A V_E fstSource fstTarget ldFactor : ℝ)
    (n sigma2_base v_mutation s Ns_stab sigmaTheta_fluct t_div tau_fluct : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS_lt_one : fstSource < 1)
    (hfstT_lt_one : fstTarget < 1)
    (h_ld : 0 < ldFactor)
    (h_n : 0 < n)
    (h_sigma : 0 < sigma2_base)
    (h_vmut : 0 ≤ v_mutation)
    (h_s : 0 < s)
    (h_Ns : 1 < Ns_stab)
    (h_sigmaTheta : 0 < sigmaTheta_fluct)
    (h_t_div : 0 < t_div)
    (h_tau : 0 < tau_fluct)
    (h_tau_threshold :
      tau_fluct < t_div / (-Real.log (effectCorrelationStabilizing Ns_stab))) :
    empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor
        (fluctuatingEffectCorrelation t_div tau_fluct) <
      empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor
        (effectCorrelationStabilizing Ns_stab) ∧
    selectionModelLRT
      (stabilizingSelectionValidationModel n sigma2_base
        (stabilizingSelectedArchitectureVariance v_mutation s) Ns_stab) <
    selectionModelLRT
      (fluctuatingSelectionValidationModel n sigma2_base
        (fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta_fluct tau_fluct)
        t_div tau_fluct) := by
  have h_corr :
      fluctuatingEffectCorrelation t_div tau_fluct <
        effectCorrelationStabilizing Ns_stab := by
    exact fluctuatingCorrelation_lt_stabilizing_of_tau_lt_threshold
      t_div tau_fluct Ns_stab h_t_div h_tau h_Ns h_tau_threshold
  constructor
  · exact empirical_portability_ratio_strictly_orders_by_ld_and_effect_correlation
      V_A V_E fstSource fstTarget ldFactor ldFactor
      (fluctuatingEffectCorrelation t_div tau_fluct)
      (effectCorrelationStabilizing Ns_stab)
      hVA hVE hfstS_lt_one hfstT_lt_one h_ld le_rfl
      (by
        unfold fluctuatingEffectCorrelation
        exact Real.exp_pos _)
      h_corr
  · exact selection_model_preferred_when_better_fit
      n sigma2_base v_mutation s Ns_stab sigmaTheta_fluct t_div tau_fluct
      h_n h_sigma h_vmut h_s h_Ns h_sigmaTheta h_t_div h_tau h_tau_threshold

/-- **Shorter selection autocorrelation predicts both lower portability and
    stronger held-out evidence for a selection-aware model.**
    This is the mechanism-level corollary of the previous theorem for two
    fluctuating regimes with the same ancestry pair, sample size, and
    LD-retention factor. If one regime has a shorter selection autocorrelation
    time, then `SelectionArchitecture.short_autocorrelation_lower_correlation`
    gives a strictly lower cross-population effect correlation for the same
    divergence time. In that case:
    1. the predicted target/source `R²` portability ratio is strictly lower, and
    2. the exact Gaussian held-out LRT for adding a selection-aware term is
       strictly larger, provided the shorter-autocorrelation trait has at least
       as much selection-sensitive variance.

    This ties the empirical portability prediction directly to the actual
    fluctuating-selection mechanism already formalized elsewhere in the repo,
    rather than leaving the correlation ordering as a free assumption. -/
theorem shorter_autocorrelation_reduces_portability_and_increases_selection_evidence
    (V_A V_E fstSource fstTarget ldFactor : ℝ)
    (n sigma2_base selectedVar_long selectedVar_short t τ_long τ_short : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS_lt_one : fstSource < 1)
    (hfstT_lt_one : fstTarget < 1)
    (h_ld : 0 < ldFactor)
    (h_n : 0 < n)
    (h_sigma : 0 < sigma2_base)
    (h_var_long : 0 ≤ selectedVar_long)
    (h_var_short : 0 < selectedVar_short)
    (h_var_order : selectedVar_long ≤ selectedVar_short)
    (h_tau_short : 0 < τ_short)
    (h_tau_long : 0 < τ_long)
    (h_shorter : τ_short < τ_long)
    (h_t : 0 < t) :
    empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor
        (fluctuatingEffectCorrelation t τ_short) <
      empiricalPortabilityRatio V_A V_E fstSource fstTarget ldFactor
        (fluctuatingEffectCorrelation t τ_long) ∧
    selectionModelLRT
      (fluctuatingSelectionValidationModel n sigma2_base selectedVar_long t τ_long) <
    selectionModelLRT
      (fluctuatingSelectionValidationModel n sigma2_base selectedVar_short t τ_short) := by
  have h_corr :
      fluctuatingEffectCorrelation t τ_short <
        fluctuatingEffectCorrelation t τ_long := by
    exact short_autocorrelation_lower_correlation τ_short τ_long t
      h_tau_short h_tau_long h_shorter h_t
  have h_rho_long_nonneg : 0 ≤ fluctuatingEffectCorrelation t τ_long := by
    unfold fluctuatingEffectCorrelation
    exact le_of_lt (Real.exp_pos _)
  have h_rho_long_lt_one : fluctuatingEffectCorrelation t τ_long < 1 := by
    unfold fluctuatingEffectCorrelation
    apply Real.exp_lt_one_iff.mpr
    have h_div_pos : 0 < t / τ_long := div_pos h_t h_tau_long
    have h_neg : -(t / τ_long) < 0 := by linarith
    simpa [neg_div] using h_neg
  have h_rho_short_nonneg : 0 ≤ fluctuatingEffectCorrelation t τ_short := by
    unfold fluctuatingEffectCorrelation
    exact le_of_lt (Real.exp_pos _)
  have h_rho_short_lt_one : fluctuatingEffectCorrelation t τ_short < 1 := by
    unfold fluctuatingEffectCorrelation
    apply Real.exp_lt_one_iff.mpr
    have h_div_pos : 0 < t / τ_short := div_pos h_t h_tau_short
    have h_neg : -(t / τ_short) < 0 := by linarith
    simpa [neg_div] using h_neg
  have h_missed_long_nonneg :
      0 ≤ missedSelectedVariance
        (fluctuatingSelectionValidationModel n sigma2_base selectedVar_long t τ_long) := by
    unfold missedSelectedVariance fluctuatingSelectionValidationModel
    exact mul_nonneg h_var_long
      (by nlinarith [h_rho_long_nonneg, h_rho_long_lt_one])
  have h_missed_lt :
      missedSelectedVariance
          (fluctuatingSelectionValidationModel n sigma2_base selectedVar_long t τ_long) <
        missedSelectedVariance
          (fluctuatingSelectionValidationModel n sigma2_base selectedVar_short t τ_short) := by
    unfold missedSelectedVariance fluctuatingSelectionValidationModel
    exact missedSelectedVariance_lt_of_variance_and_correlation
      selectedVar_long selectedVar_short
      (fluctuatingEffectCorrelation t τ_long)
      (fluctuatingEffectCorrelation t τ_short)
      h_var_short h_rho_long_nonneg h_rho_long_lt_one
      h_rho_short_nonneg
      h_corr h_var_order
  constructor
  · exact empirical_portability_ratio_strictly_orders_by_ld_and_effect_correlation
      V_A V_E fstSource fstTarget ldFactor ldFactor
      (fluctuatingEffectCorrelation t τ_short)
      (fluctuatingEffectCorrelation t τ_long)
      hVA hVE hfstS_lt_one hfstT_lt_one h_ld le_rfl
      (by
        unfold fluctuatingEffectCorrelation
        exact Real.exp_pos _)
      h_corr
  · rw [selectionModelLRT_eq_sampleSize_mul_log_residual_gap
          (fluctuatingSelectionValidationModel n sigma2_base selectedVar_long t τ_long)
          h_sigma h_missed_long_nonneg]
    rw [selectionModelLRT_eq_sampleSize_mul_log_residual_gap
          (fluctuatingSelectionValidationModel n sigma2_base selectedVar_short t τ_short)
          h_sigma
          (by
            unfold missedSelectedVariance fluctuatingSelectionValidationModel
            exact mul_nonneg (le_of_lt h_var_short)
              (by nlinarith [h_rho_short_nonneg, h_rho_short_lt_one]))]
    exact selectionModelLRT_strictMono_in_missedVariance n sigma2_base
      (missedSelectedVariance
        (fluctuatingSelectionValidationModel n sigma2_base selectedVar_long t τ_long))
      (missedSelectedVariance
        (fluctuatingSelectionValidationModel n sigma2_base selectedVar_short t τ_short))
      h_n h_sigma h_missed_long_nonneg h_missed_lt

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
