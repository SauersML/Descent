/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteProductExponential

assert_below Descent.Decision Descent.Program

/-!
Explicit Taylor remainder bounds for real Banach-algebra exponentials. The
certificate is derived from the convergent exponential series and factorial
inequalities, rather than supplied as a hypothesis on the remainder.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ExponentialRemainder

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

noncomputable def remainder (value : A) (order : ℕ) : A :=
  NormedSpace.exp ℝ value -
    ∑ degree ∈ Finset.range order, (Nat.factorial degree : ℝ)⁻¹ • value ^ degree

omit [NormOneClass A] in
theorem remainder_series (value : A) (order : ℕ) :
    remainder value order =
      ∑' degree, (Nat.factorial (degree + order) : ℝ)⁻¹ • value ^ (degree + order) := by
  have hs := (NormedSpace.expSeries_summable' (𝕂 := ℝ) value).sum_add_tsum_nat_add order
  rw [(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) value).tsum_eq] at hs
  unfold remainder
  rw [← hs]
  abel

theorem factorial_product_le (degree order : ℕ) :
    (Nat.factorial degree : ℝ) * Nat.factorial order ≤ Nat.factorial (degree + order) := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (degree + order))
    (Nat.factorial_mul_factorial_dvd_factorial_add degree order)

omit [CompleteSpace A] in
theorem tail_term_bound (value : A) (degree order : ℕ) :
    ‖(Nat.factorial (degree + order) : ℝ)⁻¹ • value ^ (degree + order)‖ ≤
      (‖value‖ ^ order / Nat.factorial order) *
        ((Nat.factorial degree : ℝ)⁻¹ * ‖value‖ ^ degree) := by
  have hfactor : 0 < (Nat.factorial degree : ℝ) * Nat.factorial order := by positivity
  calc
    _ = ‖value ^ (degree + order)‖ / Nat.factorial (degree + order) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [div_eq_mul_inv, mul_comm]
    _ ≤ ‖value‖ ^ (degree + order) / Nat.factorial (degree + order) :=
      div_le_div_of_nonneg_right (norm_pow_le _ _) (by positivity)
    _ ≤ ‖value‖ ^ (degree + order) /
        ((Nat.factorial degree : ℝ) * Nat.factorial order) :=
      div_le_div_of_nonneg_left (by positivity) hfactor (factorial_product_le degree order)
    _ = _ := by rw [pow_add]; ring

/-- The entire tail after `order - 1` is bounded by the first scalar power divided
by its factorial, times the exponential of the operator norm. -/
theorem remainder_norm (value : A) (order : ℕ) :
    ‖remainder value order‖ ≤
      (‖value‖ ^ order / Nat.factorial order) * Real.exp ‖value‖ := by
  rw [remainder_series]
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖value‖).mul_left
    (‖value‖ ^ order / Nat.factorial order)
  rw [← Real.exp_eq_exp_ℝ] at hscalar
  exact tsum_of_norm_bounded hscalar (tail_term_bound value · order)

/-- The second-order remainder has the exact universal `1/6` coefficient. -/
theorem second_order_norm (value : A) :
    ‖NormedSpace.exp ℝ value - (1 + value + (1 / 2 : ℝ) • value ^ 2)‖ ≤
      ‖value‖ ^ 3 / 6 * Real.exp ‖value‖ := by
  have hbound := remainder_norm value 3
  simpa [remainder, Finset.sum_range_succ, Nat.factorial] using hbound

end Descent.Portability.ExponentialRemainder
