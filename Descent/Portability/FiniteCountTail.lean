/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteAtomicReportMeasure

assert_below Descent.Decision Descent.Program

/-!
Exact count-layer decomposition and a quantitative truncation certificate for
any bounded complex statistic on a finite experiment. The tail is controlled by
the actual first count moment; no independence or moment closure is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteCountTail

open scoped BigOperators
open HWEInteractionLaw

/-- Finite count layers and the remaining tail exactly partition the observable. -/
theorem expectation_decomposition {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (n : α → ℕ) (f : α → ℂ) (R : ℕ) :
    complexExpectation p f =
      (∑ r ∈ Finset.range R, complexExpectation p (fun x ↦ if n x = r then f x else 0)) +
        complexExpectation p (fun x ↦ if R ≤ n x then f x else 0) := by
  have he (x : α) : (∑ r ∈ Finset.range R, if n x = r then f x else 0) +
      (if R ≤ n x then f x else 0) = f x := by
    by_cases hx : n x < R
    · simp [hx, Nat.not_le_of_gt hx]
    · simp [hx, Nat.le_of_not_gt hx]
  unfold complexExpectation
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, ← mul_add, he]

/-- The tail of any bounded complex observable is bounded by the first count moment. -/
theorem tail_bound {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (n : α → ℕ) (f : α → ℂ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B)
    (R : ℕ) (hR : 0 < R) :
    ‖complexExpectation p (fun x ↦ if R ≤ n x then f x else 0)‖ ≤
      (B / (R : ℝ)) * p.expectation (fun x ↦ (n x : ℝ)) := by
  have hr : 0 < (R : ℝ) := by exact_mod_cast hR
  have he (x : α) : ‖if R ≤ n x then f x else 0‖ ≤ (B / (R : ℝ)) * (n x : ℝ) := by
    by_cases hx : R ≤ n x
    · rw [if_pos hx]
      have hc : (R : ℝ) ≤ (n x : ℝ) := by exact_mod_cast hx
      have hh := mul_le_mul_of_nonneg_left hc (div_nonneg hB hr.le)
      rw [div_mul_cancel₀ _ hr.ne'] at hh
      exact (hf x).trans hh
    · rw [if_neg hx, norm_zero]
      positivity
  unfold complexExpectation
  calc
    _ ≤ ∑ x, ‖(p.mass x : ℂ) * (if R ≤ n x then f x else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ x, p.mass x * ((B / (R : ℝ)) * (n x : ℝ)) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (p.mass_nonneg x)]
      exact mul_le_mul_of_nonneg_left (he x) (p.mass_nonneg x)
    _ = _ := by
      simp only [FiniteReportLaw.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- Certified error after keeping only finitely many count layers. -/
theorem truncation_error {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (n : α → ℕ) (f : α → ℂ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B)
    (R : ℕ) (hR : 0 < R) :
    ‖complexExpectation p f -
      ∑ r ∈ Finset.range R, complexExpectation p (fun x ↦ if n x = r then f x else 0)‖ ≤
        (B / (R : ℝ)) * p.expectation (fun x ↦ (n x : ℝ)) := by
  have he := expectation_decomposition p n f R
  rw [he, add_sub_cancel_left]
  exact tail_bound p n f B hB hf R hR

end Descent.Portability.FiniteCountTail
