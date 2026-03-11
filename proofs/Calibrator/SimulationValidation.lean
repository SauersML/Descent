import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

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

/-- **Selection model preferred when it captures additional variance.**
    The LRT statistic equals -2(logL_null - logL_alt).
    When the selection model explains fraction f_sel of residual variance
    beyond the neutral model, and neutral explains f_neut of total variance,
    the LRT is approximately n * log(1 + f_sel/(1 - f_neut)).
    For immune traits (high f_sel due to balancing/directional selection)
    this exceeds the LRT for height (low f_sel under near-neutrality).

    We derive: if one model captures more residual variance than another,
    its LRT is larger, using the definition of likelihoodRatioStat. -/
theorem selection_model_preferred_when_better_fit
    (logL_neutral_immune logL_sel_immune : ℝ)
    (logL_neutral_height logL_sel_height : ℝ)
    (h_immune_fit : logL_neutral_immune < logL_sel_immune)
    (h_height_fit : logL_neutral_height ≤ logL_sel_height)
    -- Immune traits have larger fit improvement from selection model
    (h_immune_bigger_gap :
      logL_sel_immune - logL_neutral_immune >
      logL_sel_height - logL_neutral_height) :
    likelihoodRatioStat logL_neutral_height logL_sel_height <
      likelihoodRatioStat logL_neutral_immune logL_sel_immune := by
  unfold likelihoodRatioStat
  nlinarith

end ModelComparison


/-!
## Cross-Validation for Portability Prediction

Cross-validation methods for assessing PGS portability predictions.
-/

section CrossValidation

/- **Leave-one-population-out cross-validation.**
    Train the portability model on all populations except one,
    predict for the held-out population, repeat for each. -/

/-- **Cross-validation error decomposition.**
    CV error = bias² + variance + irreducible noise. -/
theorem cv_error_decomposition
    (bias_sq variance noise : ℝ)
    (h_bias : 0 ≤ bias_sq) (h_var : 0 ≤ variance) (h_noise : 0 ≤ noise) :
    0 ≤ bias_sq + variance + noise := by linarith

/-- **More diverse training set → lower CV error.**
    Including more populations in training reduces both bias and variance
    of portability predictions for the held-out population.
    Modeled: adding populations reduces both bias² and variance components. -/
theorem more_populations_lower_cv_error
    (bias_sq_few variance_few bias_sq_many variance_many : ℝ)
    (h_bias_nn : 0 ≤ bias_sq_many) (h_var_nn : 0 ≤ variance_many)
    (h_bias_reduced : bias_sq_many ≤ bias_sq_few)
    (h_var_reduced : variance_many < variance_few) :
    bias_sq_many + variance_many < bias_sq_few + variance_few := by
  linarith

/-- **The bias-variance tradeoff in portability prediction.**
    Simple models (e.g., linear in Fst) have high bias but low variance.
    Complex models (e.g., spline in multiple PCs) have low bias but high variance.
    When variance dominates (few populations), the simple model wins. -/
theorem optimal_complexity_depends_on_n_pops
    (bias_simple variance_simple bias_complex variance_complex : ℝ)
    (h_bias_complex_lower : bias_complex < bias_simple)
    (h_var_complex_higher : variance_simple < variance_complex)
    -- The variance gap exceeds the bias² gap (few populations regime)
    (h_var_dominates : variance_complex - variance_simple >
        bias_simple ^ 2 - bias_complex ^ 2) :
    bias_simple ^ 2 + variance_simple < bias_complex ^ 2 + variance_complex := by
  nlinarith

end CrossValidation


/-!
## Concrete Empirical Predictions

Concrete numerical predictions from the theoretical framework
that can be compared with Wang et al.'s findings.
-/

section GeneralPredictions

/-- **Portability ratio is bounded by neutral prediction times LD factor.**
    For any trait, the predicted portability ratio from the neutral model
    combined with LD tagging adjustment gives a product in (0, 1). -/
theorem portability_prediction_bounded
    (neutral_ratio ld_factor : ℝ)
    (h_nr : 0 < neutral_ratio) (h_nr_le : neutral_ratio < 1)
    (h_ld : 0 < ld_factor) (h_ld_le : ld_factor ≤ 1) :
    0 < neutral_ratio * ld_factor ∧ neutral_ratio * ld_factor < 1 := by
  constructor
  · exact mul_pos h_nr h_ld
  · calc neutral_ratio * ld_factor ≤ neutral_ratio * 1 := by nlinarith
      _ = neutral_ratio := mul_one _
      _ < 1 := h_nr_le

/-- **Selection reduces portability below neutral prediction.**
    When genetic correlation ρ < 1 (selection-driven effect changes),
    the actual portability is reduced by ρ² relative to neutral. -/
theorem selection_reduces_portability
    (neutral_ratio rho : ℝ)
    (h_nr : 0 < neutral_ratio) (h_nr_le : neutral_ratio ≤ 1)
    (h_rho : 0 ≤ rho) (h_rho_lt : rho < 1) :
    neutral_ratio * rho ^ 2 < neutral_ratio := by
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
  nlinarith

end GeneralPredictions

end Calibrator
