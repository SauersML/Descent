/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExponentialRemainder
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
The scalar exponential inequality used in Decision-Directed Portability's
Bernstein bound. It is proved from the convergent exponential series and the
factorial bound, retaining the variance-sensitive quadratic coefficient and
the exact range constant one third.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BernsteinExponentialBound

/-- Every factorial after degree two dominates the required geometric denominator. -/
theorem factorial_geometric_lower (n : ℕ) :
    (2 : ℝ) * 3 ^ n ≤ (Nat.factorial (n + 2) : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n hn =>
    have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hf : (0 : ℝ) ≤ Nat.factorial (n + 2) := by positivity
    calc
      2 * 3 ^ (n + 1) = 3 * (2 * 3 ^ n) := by ring
      _ ≤ 3 * (Nat.factorial (n + 2) : ℝ) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ ≤ ((n : ℝ) + 3) * (Nat.factorial (n + 2) : ℝ) := by nlinarith
      _ = (Nat.factorial (n + 1 + 2) : ℝ) := by
        rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ (n + 2)]
        push_cast
        ring

/-- Each actual exponential-tail term is dominated by a quadratic times a geometric term. -/
theorem tail_term_bound (z : ℝ) (n : ℕ) :
    ‖(Nat.factorial (n + 2) : ℝ)⁻¹ • z ^ (n + 2)‖ ≤
      z ^ 2 / 2 * (|z| / 3) ^ n := by
  calc
    _ = |z| ^ (n + 2) / Nat.factorial (n + 2) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        Real.norm_eq_abs, abs_pow]
      ring
    _ ≤ |z| ^ (n + 2) / (2 * 3 ^ n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_geometric_lower n)
    _ = _ := by
      rw [pow_add, sq_abs, div_pow]
      ring

/-- Summing the proven geometric domination bounds the actual exponential remainder. -/
theorem remainder_bound (z : ℝ) (hz : |z| < 3) :
    |Real.exp z - (1 + z)| ≤ z ^ 2 / (2 * (1 - |z| / 3)) := by
  have hratio : |(|z| / 3)| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hs := (hasSum_geometric_of_abs_lt_one hratio).mul_left (z ^ 2 / 2)
  have hb := tsum_of_norm_bounded hs (tail_term_bound z)
  have he := ExponentialRemainder.remainder_series (A := ℝ) z 2
  have hr : ExponentialRemainder.remainder z 2 = Real.exp z - (1 + z) := by
    simp [ExponentialRemainder.remainder, Finset.sum_range_succ,
      ← Real.exp_eq_exp_ℝ, Nat.factorial]
  rw [← he, hr, Real.norm_eq_abs] at hb
  convert hb using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The one-sided quadratic exponential bound with a fixed admissible range cap. -/
theorem exponential_upper (z a : ℝ) (ha : 0 ≤ a ∧ a < 3) (hz : |z| ≤ a) :
    Real.exp z ≤ 1 + z + z ^ 2 / (2 * (1 - a / 3)) := by
  have hb := remainder_bound z (hz.trans_lt ha.2)
  have hd := le_abs_self (Real.exp z - (1 + z))
  have hc : z ^ 2 / (2 * (1 - |z| / 3)) ≤ z ^ 2 / (2 * (1 - a / 3)) := by
    apply div_le_div_of_nonneg_left (sq_nonneg z) (by linarith)
    linarith
  linarith

end Descent.Portability.BernsteinExponentialBound
