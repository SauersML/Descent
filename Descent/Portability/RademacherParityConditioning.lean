/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RademacherParityLaw

assert_below Descent.Decision Descent.Program

/-!
Exact conditioning of a nonempty fair-sign row on either product sign. The
conditional law is normalized from parity balance and exposes its characteristic
function as an ordinary transform plus the mixed parity transform.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RademacherParityConditioning

open scoped BigOperators
open HWEInteractionLaw BalancedHWEWeakLimit RademacherArrayWeakLimit RademacherParityLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem parity_factor_bounds (b : Bool) (x : ι → Bool) :
    0 ≤ 1 + signValue b * parity x ∧ 1 + signValue b * parity x ≤ 2 := by
  rcases sq_eq_one_iff.mp (parity_square x) with h | h <;>
    cases b <;> norm_num [signValue, h]

/-- The genuine conditional law, multiplying each accepted row's probability by two. -/
noncomputable def law (b : Bool) : FiniteReportLaw (ι → Bool) where
  mass x := (independentLaw (fun _ : ι ↦ signLaw)).mass x * (1 + signValue b * parity x)
  mass_nonneg x := mul_nonneg (FiniteReportLaw.mass_nonneg _ _) (parity_factor_bounds b x).1
  mass_sum := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, FiniteReportLaw.mass_sum]
    have he : (∑ x : ι → Bool, (independentLaw (fun _ : ι ↦ signLaw)).mass x *
        (signValue b * parity x)) = signValue b *
          (independentLaw (fun _ : ι ↦ signLaw)).expectation parity := by
      simp only [FiniteReportLaw.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [he, parity_mean, mul_zero, add_zero]

/-- The formula is exactly normalized restriction to the selected parity event. -/
theorem law_mass (b : Bool) (x : ι → Bool) :
    (law b).mass x = if parity x = signValue b then
      2 * (independentLaw (fun _ : ι ↦ signLaw)).mass x else 0 := by
  classical
  rcases sq_eq_one_iff.mp (parity_square x) with h | h <;>
    cases b <;> norm_num [law, signValue, h, mul_comm]

/-- Every conditional real statistic is the sum of its ordinary and parity-weighted means. -/
theorem expectation_law (b : Bool) (f : (ι → Bool) → ℝ) :
    (law b).expectation f =
      (independentLaw (fun _ : ι ↦ signLaw)).expectation f + signValue b *
        (independentLaw (fun _ : ι ↦ signLaw)).expectation (fun x ↦ parity x * f x) := by
  simp only [FiniteReportLaw.expectation, law, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Exact complex transform decomposition for the conditional experiment. -/
theorem complexExpectation_law (b : Bool) (f : (ι → Bool) → ℂ) :
    complexExpectation (law b) f =
      complexExpectation (independentLaw (fun _ : ι ↦ signLaw)) f + (signValue b : ℂ) *
        complexExpectation (independentLaw (fun _ : ι ↦ signLaw))
          (fun x ↦ (parity x : ℂ) * f x) := by
  simp only [complexExpectation, law, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  push_cast
  ring

/-- Conditioning on a fair parity event increases any nonnegative expectation by at most two. -/
theorem expectation_law_le_twice (b : Bool) (f : (ι → Bool) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (law b).expectation f ≤ 2 * (independentLaw (fun _ : ι ↦ signLaw)).expectation f := by
  simp only [FiniteReportLaw.expectation, law, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have h := mul_le_mul_of_nonneg_left (parity_factor_bounds b x).2
    ((independentLaw (fun _ : ι ↦ signLaw)).mass_nonneg x)
  have h' := mul_le_mul_of_nonneg_right h (hf x)
  nlinarith

/-- The conditional second moment is bounded by twice the unconditioned row variance. -/
theorem second_moment_bound (b : Bool) (a : ι → ℝ) :
    (law b).expectation (fun x ↦ weightedSum a x ^ 2) ≤ 2 * ∑ i, a i ^ 2 := by
  simpa only [row_second] using expectation_law_le_twice b
    (fun x ↦ weightedSum a x ^ 2) (fun x ↦ sq_nonneg _)

end Descent.Portability.RademacherParityConditioning
