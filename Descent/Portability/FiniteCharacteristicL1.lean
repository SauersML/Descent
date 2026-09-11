/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteAtomicReportMeasure
import Mathlib.Analysis.SpecialFunctions.Exp

assert_below Descent.Decision Descent.Program

/-!
Characteristic functions of two observables on the same finite experiment differ
by at most twice the frequency times their actual L1 distance. This gives a
quantitative certificate for changing the amplitude normalization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteCharacteristicL1

open scoped BigOperators
open HWEInteractionLaw

/-- A global bound on the complex exponential along the imaginary axis. -/
theorem imaginary_exponential_difference (u v : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - Complex.exp ((v : ℂ) * Complex.I)‖ ≤
      2 * |u - v| := by
  have hn (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  by_cases hsmall : |u - v| ≤ 1
  · have hh := Complex.norm_exp_sub_one_le
      (x := ((u - v : ℝ) : ℂ) * Complex.I) (by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, mul_one] using hsmall)
    have he : Complex.exp ((u : ℂ) * Complex.I) - Complex.exp ((v : ℂ) * Complex.I) =
        Complex.exp ((v : ℂ) * Complex.I) *
          (Complex.exp (((u - v : ℝ) : ℂ) * Complex.I) - 1) := by
      rw [mul_sub, ← Complex.exp_add, mul_one]
      congr 1
      congr 1
      push_cast
      ring
    rw [he, norm_mul, hn, one_mul]
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one] using hh
  · have hh := norm_sub_le (Complex.exp ((u : ℂ) * Complex.I))
      (Complex.exp ((v : ℂ) * Complex.I))
    rw [hn, hn] at hh
    linarith

/-- Actual finite characteristic expectations are stable under L1 perturbations. -/
theorem characteristic_difference {α : Type*} [Fintype α]
    (p : FiniteReportLaw α) (z y : α → ℝ) (t : ℝ) :
    ‖complexExpectation p (fun x ↦ Complex.exp ((t * z x : ℝ) * Complex.I)) -
      complexExpectation p (fun x ↦ Complex.exp ((t * y x : ℝ) * Complex.I))‖ ≤
      2 * |t| * p.expectation (fun x ↦ |z x - y x|) := by
  simp only [complexExpectation, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ x, ‖(p.mass x : ℂ) * (Complex.exp ((t * z x : ℝ) * Complex.I) -
        Complex.exp ((t * y x : ℝ) * Complex.I))‖ := norm_sum_le _ _
    _ ≤ ∑ x, p.mass x * (2 * |t * z x - t * y x|) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (p.mass_nonneg x)]
      exact mul_le_mul_of_nonneg_left (imaginary_exponential_difference _ _) (p.mass_nonneg x)
    _ = _ := by
      simp only [← mul_sub, abs_mul, FiniteReportLaw.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end Descent.Portability.FiniteCharacteristicL1
