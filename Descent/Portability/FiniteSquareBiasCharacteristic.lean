/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompensatedCharacteristicKernel
import Descent.Portability.FiniteCharacteristicL1

assert_below Descent.Decision Descent.Program

/-!
The exact finite square-bias identity links a centered original observable to its
compensated characteristic kernel under the actual biased masses. No limiting
characteristic exponent is assumed in this algebraic bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteSquareBiasCharacteristic

open scoped BigOperators
open HWEInteractionLaw CompensatedCharacteristicKernel

/-- Centering removes the linear compensation exactly under the original finite law. -/
theorem centered_compensation {α : Type*} [Fintype α]
    (p : FiniteReportLaw α) (z : α → ℝ) (hz : p.expectation z = 0) (t : ℝ) :
    complexExpectation p (fun x ↦ Complex.exp ((t * z x : ℝ) * Complex.I) - 1 -
      ((t * z x : ℝ) : ℂ) * Complex.I) =
        complexExpectation p (fun x ↦ Complex.exp ((t * z x : ℝ) * Complex.I)) - 1 := by
  have hmass : ∑ x, (p.mass x : ℂ) = 1 := by exact_mod_cast p.mass_sum
  have hmean : ∑ x, (p.mass x : ℂ) * (z x : ℂ) = 0 := by
    exact_mod_cast hz
  have hlinear : ∑ x, (p.mass x : ℂ) * (((t * z x : ℝ) : ℂ) * Complex.I) = 0 := by
    calc
      _ = (t : ℂ) * Complex.I * ∑ x, (p.mass x : ℂ) * (z x : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        push_cast
        ring
      _ = 0 := by rw [hmean, mul_zero]
  simp only [complexExpectation, mul_sub, mul_one, Finset.sum_sub_distrib, hmass, hlinear,
    sub_zero]

/-- The exact identity N(phi(t)-1) = E_Q K_t for any finite square-biased centered law. -/
theorem square_bias_identity {α : Type*} [Fintype α]
    (p q : FiniteReportLaw α) (z : α → ℝ) (N : ℝ)
    (hq : ∀ x, q.mass x = N * p.mass x * z x ^ 2)
    (hz : p.expectation z = 0) (t : ℝ) :
    complexExpectation q (fun x ↦ kernel t (z x)) = (N : ℂ) *
      (complexExpectation p (fun x ↦ Complex.exp ((t * z x : ℝ) * Complex.I)) - 1) := by
  calc
    _ = (N : ℂ) * complexExpectation p (fun x ↦ (z x : ℂ) ^ 2 * kernel t (z x)) := by
      simp only [complexExpectation, hq, Complex.ofReal_mul, Complex.ofReal_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp_rw [quadratic_identity]
      rw [centered_compensation p z hz]

end Descent.Portability.FiniteSquareBiasCharacteristic
