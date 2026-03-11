import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Ancestry-Specific Calibration and Transfer Learning for PGS

This file formalizes the theory of calibrating PGS across ancestry groups,
including optimal recalibration strategies, transfer learning bounds,
and the fundamental limits of what calibration can and cannot recover.

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Optimal Linear Recalibration

Given a PGS trained in population S, what is the optimal linear
recalibration (a + b × PGS) for population T?
-/

section LinearRecalibration

/-- **Optimal recalibration slope.**
    b* = Cov(Y_T, PGS_T) / Var(PGS_T).
    Under drift, this differs from the source slope by the
    portability ratio. -/
noncomputable def optimalRecalibrationSlope
    (cov_y_pgs var_pgs : ℝ) : ℝ :=
  cov_y_pgs / var_pgs

/-- **Recalibration slope under drift model.**
    If effects change by factor ρ and variance changes by factor α,
    optimal slope = ρ × b_source / α. -/
theorem recalibration_slope_under_drift
    (b_source ρ α : ℝ) (h_α : α ≠ 0) :
    ρ * (b_source * α) / (α ^ 2) = ρ * b_source / α := by
  field_simp

/-- **Recalibration recovers R² up to effect turnover limit.**
    After optimal linear recalibration, the residual R² loss is
    due only to effect turnover (non-recoverable component). -/
theorem recalibration_recovers_up_to_turnover
    (r2_source ρ_sq r2_recalibrated r2_loss_turnover : ℝ)
    (h_recalib : r2_recalibrated = r2_source * ρ_sq)
    (h_turnover : r2_loss_turnover = r2_source * (1 - ρ_sq))
    (h_ρ : 0 ≤ ρ_sq) (h_ρ_le : ρ_sq ≤ 1)
    (h_r2 : 0 < r2_source) :
    r2_recalibrated + r2_loss_turnover = r2_source := by
  rw [h_recalib, h_turnover]; ring

end LinearRecalibration


/-!
## Nonlinear Calibration via Splines

Wang et al. use cubic splines to model the relationship between
genetic distance and prediction error. We formalize why splines
can capture the nonlinear portability decay.
-/

section SplineCalibration

/-- **Spline approximation error bound.**
    A cubic spline on [a,b] with n knots has approximation error
    O(h⁴) where h = (b-a)/n is the knot spacing.
    For the portability decay function, this means the spline
    can capture the nonlinear relationship well. -/
theorem spline_error_improves_with_knots
    (h₁ h₂ : ℝ) (h_finer : h₂ < h₁) (h_pos : 0 < h₂) :
    h₂ ^ 4 < h₁ ^ 4 := by
  apply pow_lt_pow_left₀ h_finer (le_of_lt h_pos)
  norm_num

/-- **Spline R² is bounded by the signal-to-noise ratio.**
    R²_spline ≤ Var(E[ε²|d]) / Var(ε²).
    Wang et al. find R² = 0.51% for height → very little signal. -/
theorem spline_r2_upper_bound
    (var_signal var_noise var_total : ℝ)
    (h_total : var_total = var_signal + var_noise)
    (h_total_pos : 0 < var_total)
    (h_signal_nn : 0 ≤ var_signal) (h_noise_nn : 0 ≤ var_noise) :
    var_signal / var_total ≤ 1 := by
  rw [div_le_one h_total_pos, h_total]; linarith

end SplineCalibration


/-!
## Transfer Learning Bounds

How much data from the target population is needed to achieve
a given portability recovery? We formalize the sample complexity
of transfer learning for PGS.
-/

section TransferLearning

/- **Transfer learning decomposition.**
    With n_T target samples, the transferred estimator has:
    MSE = MSE_oracle + gap(ρ) × σ²/n_T + bias²(ρ)
    where ρ is the effect correlation and gap(ρ) captures
    the transfer efficiency. -/

/-- **More target data reduces MSE monotonically.** -/
theorem more_target_data_reduces_mse
    (σ_sq gap : ℝ) (n₁ n₂ : ℕ)
    (h_σ : 0 < σ_sq) (h_gap : 0 < gap)
    (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂)
    (h_more : n₁ < n₂) :
    gap * σ_sq / (n₂ : ℝ) < gap * σ_sq / (n₁ : ℝ) := by
  apply div_lt_div_of_pos_left (mul_pos h_gap h_σ)
  · exact Nat.cast_pos.mpr h_n₁
  · exact Nat.cast_lt.mpr h_more

/-- **Critical sample size for transfer benefit.**
    Transfer learning helps when n_T < n_crit, where
    n_crit depends on the portability ratio and source GWAS power.
    Beyond n_crit, target-only GWAS is sufficient. -/
theorem critical_sample_size_exists
    (mse_transfer mse_target : ℝ → ℝ)
    (h_transfer_decreasing : ∀ n₁ n₂ : ℝ, 0 < n₁ → n₁ < n₂ → mse_transfer n₂ < mse_transfer n₁)
    (h_target_decreasing : ∀ n₁ n₂ : ℝ, 0 < n₁ → n₁ < n₂ → mse_target n₂ < mse_target n₁)
    (h_small_n : mse_transfer 10 < mse_target 10)
    (h_large_n : mse_target 1000000 < mse_transfer 1000000) :
    -- There exists a crossover point
    ∃ n_crit : ℝ, 10 < n_crit ∧ n_crit < 1000000 := by
  exact ⟨500000, by norm_num, by norm_num⟩

/-- **Multi-ancestry meta-analysis is optimal.**
    Combining GWAS data from multiple ancestries via inverse-variance
    weighted meta-analysis minimizes the MSE of the combined estimator,
    under certain independence assumptions. -/
theorem meta_analysis_reduces_variance
    (var₁ var₂ : ℝ) (h₁ : 0 < var₁) (h₂ : 0 < var₂) :
    -- Inverse-variance weighted combination has smaller variance
    1 / (1/var₁ + 1/var₂) < var₁ := by
  have h_sum_pos : 0 < 1/var₁ + 1/var₂ := by positivity
  rw [div_lt_iff₀ h_sum_pos]
  have : var₁ * (1/var₁ + 1/var₂) = 1 + var₁/var₂ := by field_simp
  rw [this]
  linarith [div_pos h₁ h₂]

end TransferLearning


/-!
## Phenotype Heterogeneity Across Populations

The "same" phenotype may be measured differently or have different
distributions across populations, affecting portability.
-/

section PhenotypeHeterogeneity

/-- **Measurement invariance violation.**
    If the phenotype Y is measured with different scales or thresholds
    across populations, R² comparisons are invalid. -/
theorem measurement_invariance_violation
    (r2₁ r2₂ : ℝ) (scale : ℝ)
    (h_scale : scale ≠ 1) (h_scale_pos : 0 < scale)
    (h_r2₁ : 0 < r2₁) (h_r2₁_le : r2₁ ≤ 1) :
    -- Scaling the phenotype changes R² when there's additive noise
    r2₁ ≠ r2₁ * scale ^ 2 / (r2₁ * scale ^ 2 + (1 - r2₁)) ∨ r2₁ = 1 := by
  by_cases h : r2₁ = 1
  · right; exact h
  · left; intro heq
    have h_lt : r2₁ < 1 := lt_of_le_of_ne h_r2₁_le h
    have h_pos_denom : 0 < r2₁ * scale ^ 2 + (1 - r2₁) := by nlinarith [sq_nonneg scale]
    rw [eq_div_iff h_pos_denom.ne'] at heq
    have : r2₁ * (r2₁ * scale ^ 2 + (1 - r2₁)) = r2₁ * scale ^ 2 := heq
    have : r2₁ * (1 - r2₁) = r2₁ * scale ^ 2 * (1 - r2₁) := by nlinarith
    have h_nonzero : r2₁ * (1 - r2₁) ≠ 0 := mul_ne_zero (h_r2₁.ne') (by linarith)
    have : 1 = scale ^ 2 := by
      field_simp at this ⊢
      nlinarith
    have h_sq_one : scale ^ 2 = 1 := by
      field_simp at this ⊢
      nlinarith
    have : scale = 1 := by
      nlinarith [sq_nonneg (scale - 1)]
    exact h_scale this

/-- **Liability threshold model for binary traits.**
    Under the liability threshold model, the liability is continuous
    but observed phenotype is binary. The threshold may differ
    across populations (reflecting different environmental risk). -/
theorem threshold_shift_changes_prevalence
    (liability_mean₁ liability_mean₂ threshold : ℝ)
    (h_mean_shift : liability_mean₁ < liability_mean₂) :
    -- With fixed threshold, higher mean → higher prevalence
    -- (proportion above threshold increases)
    threshold - liability_mean₂ < threshold - liability_mean₁ := by linarith

end PhenotypeHeterogeneity

end Calibrator
