/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianVarianceJet

assert_below Descent.Decision Descent.Program

/-!
Uniform coordinate bounds for the actual Gaussian log-density derivatives.
The variance interval is fixed before observing the coordinates. Bounds are
explicit polynomials in the coordinate and hold throughout that interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianUniformLogBounds

open GaussianVarianceDensity GaussianVarianceJet

/-- A variance at least one half has a nonnegative reciprocal bounded by two. -/
theorem reciprocal_bounds (a : ℝ) (ha : 1 / 2 ≤ a) : 0 ≤ a⁻¹ ∧ a⁻¹ ≤ 2 := by
  have hpos : 0 < a := by linarith
  refine ⟨(inv_pos.mpr hpos).le, ?_⟩
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) ha
  norm_num [one_div] at hh
  exact hh

/-- First log derivative has a uniform quadratic bound. -/
theorem first_bound (a x : ℝ) (ha : 1 / 2 ≤ a) :
    |logFirst a x| ≤ 1 + 2 * x ^ 2 := by
  obtain ⟨h₀, h₂⟩ := reciprocal_bounds a ha
  have hsq := pow_le_pow_left₀ h₀ h₂ 2
  have hb := abs_add (-a⁻¹ / 2) (x ^ 2 * a⁻¹ ^ 2 / 2)
  simp only [logFirst]
  apply hb.trans
  rw [abs_div, abs_neg, abs_of_nonneg h₀, abs_of_nonneg (by positivity), abs_of_nonneg
    (by positivity : 0 ≤ x ^ 2 * a⁻¹ ^ 2 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg x)]

/-- Second log derivative has a uniform quadratic bound. -/
theorem second_bound (a x : ℝ) (ha : 1 / 2 ≤ a) :
    |logSecond a x| ≤ 2 + 8 * x ^ 2 := by
  obtain ⟨h₀, h₂⟩ := reciprocal_bounds a ha
  have hs := pow_le_pow_left₀ h₀ h₂ 2
  have hc := pow_le_pow_left₀ h₀ h₂ 3
  unfold logSecond
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (by positivity : 0 ≤ a⁻¹ ^ 2 / 2),
    abs_of_nonneg (by positivity : 0 ≤ x ^ 2 * a⁻¹ ^ 3)]
  nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg x)]

/-- Third log derivative has a uniform quadratic bound. -/
theorem third_bound (a x : ℝ) (ha : 1 / 2 ≤ a) :
    |logThird a x| ≤ 8 + 48 * x ^ 2 := by
  obtain ⟨h₀, h₂⟩ := reciprocal_bounds a ha
  have hc := pow_le_pow_left₀ h₀ h₂ 3
  have hq := pow_le_pow_left₀ h₀ h₂ 4
  unfold logThird
  apply (abs_add _ _).trans
  rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ a⁻¹ ^ 3),
    abs_of_nonneg (by positivity : 0 ≤ 3 * x ^ 2 * a⁻¹ ^ 4)]
  nlinarith [mul_le_mul_of_nonneg_left hq (sq_nonneg x)]

/-- All three log derivatives share a single explicit quadratic envelope. -/
theorem common_bound (a x : ℝ) (ha : 1 / 2 ≤ a) :
    |logFirst a x| ≤ 64 * (1 + x ^ 2) ∧
    |logSecond a x| ≤ 64 * (1 + x ^ 2) ∧
    |logThird a x| ≤ 64 * (1 + x ^ 2) := by
  have h₁ := first_bound a x ha
  have h₂ := second_bound a x ha
  have h₃ := third_bound a x ha
  constructor
  · nlinarith [sq_nonneg x]
  constructor <;> nlinarith [sq_nonneg x]

/-- On the chosen variance interval the density itself has a controlled exponential tail. -/
theorem ratio_bound (a x : ℝ) (ha : 1 / 2 ≤ a) (ha' : a ≤ 5 / 4) :
    ratio a x ≤ 2 * Real.exp (x ^ 2 / 10) := by
  have hpos : 0 < a := by linarith
  have hspos : 0 < Real.sqrt a := Real.sqrt_pos.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  have hs : 1 / 2 ≤ Real.sqrt a := by nlinarith
  have hpre := (reciprocal_bounds (Real.sqrt a) hs).2
  have hi : 4 / 5 ≤ a⁻¹ := by
    have hh := one_div_le_one_div_of_le hpos ha'
    norm_num [one_div] at hh
    exact hh
  have he : (1 - a⁻¹) * x ^ 2 / 2 ≤ x ^ 2 / 10 := by
    nlinarith [mul_le_mul_of_nonneg_right hi (sq_nonneg x)]
  exact mul_le_mul hpre (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by norm_num)

end Descent.Portability.GaussianUniformLogBounds
