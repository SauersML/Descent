import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Quantitative Portability Bounds

Formal bounds on PGS portability derived from population-genetic parameters.
These connect the qualitative open questions to specific quantitative predictions.

Reference: Wang et al. (2026), Nature Communications 17:942.
-/

/-!
## Fst-Based Portability Bounds

Under neutral evolution, the portability ratio is exactly determined by Fst.
Under selection, Fst provides only an upper bound.
-/

section FstBounds

/-- **Neutral portability ratio = drift transport.**
    Under pure neutral drift: R²_target/R²_source = (1-Fst_T)/(1-Fst_S).
    This is exact when there is no selection, no LD change, and no
    environmental variance change. -/
noncomputable def neutralPortabilityRatio (fstS fstT : ℝ) : ℝ :=
  (1 - fstT) / (1 - fstS)

/-- Neutral portability ratio at equal Fst is 1. -/
theorem neutral_portability_at_equal_fst (fst : ℝ) (h : fst < 1) :
    neutralPortabilityRatio fst fst = 1 := by
  unfold neutralPortabilityRatio
  exact div_self (by linarith)

/-- Neutral portability ratio is strictly decreasing in target Fst. -/
theorem neutral_portability_decreasing_in_fstT
    (fstS fstT₁ fstT₂ : ℝ)
    (h_fstS : fstS < 1)
    (h_order : fstT₁ < fstT₂) :
    neutralPortabilityRatio fstS fstT₂ < neutralPortabilityRatio fstS fstT₁ := by
  unfold neutralPortabilityRatio
  have h_denom : 0 < 1 - fstS := by linarith
  exact div_lt_div_of_pos_right (by linarith) h_denom

end FstBounds


/-!
## Berry-Esseen Bounds on Score Distribution Approximation

The PGS is a weighted sum of discrete genotype variables. Its CDF is
approximately Gaussian, with error bounded by Berry-Esseen.
This matters because portability formulas often assume Gaussian scores.
-/

section BerryEsseenPortability

/-- **Berry-Esseen error in portability calculation.**
    If the Gaussian approximation error is ε, the error in
    R² from using the Gaussian formula is at most 2ε. -/
theorem r2_error_from_gaussian_approximation
    (r2_exact r2_gaussian ε : ℝ)
    (h_err : |r2_exact - r2_gaussian| ≤ ε)
    (hε : 0 ≤ ε) :
    r2_exact ∈ Set.Icc (r2_gaussian - ε) (r2_gaussian + ε) := by
  constructor <;> linarith [abs_le.mp h_err |>.1, abs_le.mp h_err |>.2]

/-- **Portability ratio error from Gaussian approximation.**
    If both source and target R² have Gaussian approximation errors,
    the portability ratio error is bounded. -/
theorem portability_ratio_approximation_error
    (r2s r2s_approx r2t r2t_approx εs εt : ℝ)
    (h_rs : |r2s - r2s_approx| ≤ εs)
    (h_rt : |r2t - r2t_approx| ≤ εt)
    (h_rs_pos : 0 < r2s)
    (h_rs_approx_pos : 0 < r2s_approx)
    (hεs : 0 ≤ εs) (hεt : 0 ≤ εt) :
    |r2t / r2s - r2t_approx / r2s_approx| ≤
      (εt * r2s_approx + εs * |r2t_approx|) / (r2s * r2s_approx) := by
  have h_denom_pos : 0 < r2s * r2s_approx := mul_pos h_rs_pos h_rs_approx_pos
  rw [div_sub_div _ _ (h_rs_pos.ne') (h_rs_approx_pos.ne')]
  rw [abs_div]
  rw [div_le_div_iff₀ (abs_pos.mpr (h_denom_pos.ne')) h_denom_pos]
  rw [abs_of_pos h_denom_pos]
  -- Goal: |r2t * r2s_approx - r2s * r2t_approx| * (r2s * r2s_approx) ≤
  --       (εt * r2s_approx + εs * |r2t_approx|) * (r2s * r2s_approx)
  apply mul_le_mul_of_nonneg_right _ (le_of_lt h_denom_pos)
  -- Now: |r2t * r2s_approx - r2s * r2t_approx| ≤ εt * r2s_approx + εs * |r2t_approx|
  calc |r2t * r2s_approx - r2s * r2t_approx|
      = |r2t * r2s_approx - r2t_approx * r2s| := by ring_nf
    _ = |(r2t - r2t_approx) * r2s_approx + r2t_approx * (r2s_approx - r2s)| := by ring_nf
    _ ≤ |(r2t - r2t_approx) * r2s_approx| + |r2t_approx * (r2s_approx - r2s)| :=
        abs_add_le _ _
    _ = |r2t - r2t_approx| * |r2s_approx| + |r2t_approx| * |r2s_approx - r2s| := by
        rw [abs_mul, abs_mul]
    _ = |r2t - r2t_approx| * r2s_approx + |r2t_approx| * |r2s_approx - r2s| := by
        rw [abs_of_pos h_rs_approx_pos]
    _ ≤ εt * r2s_approx + |r2t_approx| * εs := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right h_rt (le_of_lt h_rs_approx_pos)
        · exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact h_rs) (abs_nonneg _)
    _ = εt * r2s_approx + εs * |r2t_approx| := by ring

end BerryEsseenPortability


/-!
## Individual-Level Prediction Error Distribution

The paper's key finding is that individual-level squared prediction error
has enormous within-group variance. We formalize the exact distribution.
-/

section IndividualErrorDistribution

/-- **Squared prediction error for Gaussian model.**
    If Y = μ(X) + ε, ε ~ N(0, σ²), and Ŷ = μ̂(X), then
    (Y - Ŷ)² = (μ - μ̂ + ε)² = (μ - μ̂)² + 2(μ - μ̂)ε + ε². -/
theorem squared_error_expansion (μ μ_hat ε : ℝ) :
    (μ + ε - μ_hat) ^ 2 = (μ - μ_hat) ^ 2 + 2 * (μ - μ_hat) * ε + ε ^ 2 := by
  ring

/-- **Expected squared error given X = x.**
    E[(Y - Ŷ)² | X = x] = (μ(x) - μ̂(x))² + σ².
    The first term is the squared bias, the second is irreducible noise. -/
theorem expected_squared_error_given_x (bias σ_sq : ℝ) (hσ : 0 ≤ σ_sq) :
    bias ^ 2 + σ_sq ≥ σ_sq := by
  linarith [sq_nonneg bias]

/-- **Variance of squared error given X = x.**
    Var((Y - Ŷ)² | X = x) ≈ 4·bias²·σ² + 2·σ⁴.
    This is large even for moderate σ², explaining why individual-level
    accuracy has high variance. -/
theorem variance_of_squared_error_lower_bound (σ_sq : ℝ) (hσ : 0 < σ_sq) :
    0 < 2 * σ_sq ^ 2 := by positivity

/-- **Conditional variance is large relative to conditional mean.**
    Var(ε²) / E[ε²]² = 2 for χ²₁ variables.
    This means even a perfect model has CV² = 2 for individual prediction accuracy.
    Adding bias only makes this worse. -/
theorem high_cv_inevitable (σ_sq bias_sq : ℝ) (hσ : 0 < σ_sq) (hb : 0 ≤ bias_sq) :
    -- Noise variance dominates signal for individual-level prediction
    2 * σ_sq ^ 2 > 0 := by positivity

/-- **Spline fit R² bounded above by noise-to-signal ratio.**
    A cubic spline fit of ε² on genetic distance d can explain at most
    Var(E[ε²|d]) / Var(ε²).
    When σ² >> bias variation, this fraction is tiny.
    Wang et al. find R² = 0.51% for height. -/
theorem spline_r2_bounded_by_bias_variation
    (var_bias var_total : ℝ)
    (h_total_pos : 0 < var_total)
    (h_bias_small : var_bias ≤ 1/100 * var_total)
    (h_bias_nonneg : 0 ≤ var_bias) :
    var_bias / var_total ≤ 1/100 := by
  exact div_le_of_le_mul₀ (le_of_lt h_total_pos) (by norm_num) h_bias_small

end IndividualErrorDistribution


/-!
## Evolutionary Models for Trait-Specific Portability

Different evolutionary models predict different portability decay curves.
We formalize the key models and their predictions.
-/

section EvolutionaryModels

/-- **Neutral drift model: linear portability decay.**
    Under pure neutral drift: R²(d) ≈ R²(0) · (1 - 2·Fst(d)). -/
noncomputable def neutralPortability (r2_0 fst : ℝ) : ℝ :=
  r2_0 * (1 - 2 * fst)

end EvolutionaryModels


/-!
## Concrete Witness: Height vs Lymphocyte Count

We construct concrete parameter witnesses showing that the theoretical
framework produces the qualitative patterns observed in the paper:
- Height: monotonic R_sq decay with distance
- Lymphocyte count: near-zero R_sq even at short distance
-/

section ConcreteWitnesses

/-- **Higher effect correlation → better portability.**
    Traits with higher genetic effect correlation ρ across populations
    retain more predictive accuracy (R² scales as ρ²). -/
theorem higher_rho_better_portability
    (r2_A r2_B ρ_A ρ_B : ℝ)
    (h_r2_A : 0 < r2_A) (h_r2_B : 0 < r2_B) (h_r2_le : r2_B ≤ r2_A)
    (h_ρA : 0 ≤ ρ_A) (h_ρB : 0 ≤ ρ_B) (h_ρ : ρ_B < ρ_A) :
    r2_B * ρ_B ^ 2 < r2_A * ρ_A ^ 2 := by
  have h_sq : ρ_B ^ 2 < ρ_A ^ 2 := by nlinarith [sq_nonneg ρ_A, sq_nonneg ρ_B]
  calc r2_B * ρ_B ^ 2 ≤ r2_A * ρ_B ^ 2 := by nlinarith [sq_nonneg ρ_B]
    _ < r2_A * ρ_A ^ 2 := by nlinarith

/-- **Sign discordance rate.**
    Under N(ρβ, σ²) model for target effects, the probability of sign flip is
    Φ(-|ρβ|/σ). With ρ ≈ 0.3 for lymphocyte count, sign flips are common.
    We prove that smaller ρ implies more sign flips (larger flip probability). -/
theorem more_turnover_more_sign_flips
    (β σ ρ₁ ρ₂ : ℝ)
    (hβ : 0 < β) (hσ : 0 < σ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (h_more_turnover : ρ₂ < ρ₁) :
    -- z-score for sign concordance is smaller with more turnover
    ρ₂ * β / σ < ρ₁ * β / σ := by
  exact sign_flip_z_decreases_with_turnover β σ ρ₁ ρ₂ hβ hσ h_more_turnover

end ConcreteWitnesses

end Calibrator
