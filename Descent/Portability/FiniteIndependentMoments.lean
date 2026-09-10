/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEInteractionLaw

assert_below Descent.Decision Descent.Program

/-!
Exact first and second moments of a finite sum under an explicitly constructed
independent law. Cross terms are eliminated by the actual product masses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteIndependentMoments

open scoped BigOperators
open HWEInteractionLaw

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Constant observables integrate to their constant value. -/
theorem expectation_const (p : FiniteReportLaw α) (c : ℝ) :
    p.expectation (fun _ ↦ c) = c := by
  rw [FiniteReportLaw.expectation, ← Finset.sum_mul, p.mass_sum, one_mul]

/-- Exact coordinate marginal, obtained from the product law. -/
theorem coordinate_expectation (p : ι → FiniteReportLaw α) (i : ι) (f : α → ℝ) :
    (independentLaw p).expectation (fun x ↦ f (x i)) = (p i).expectation f := by
  have h := expectation_independent_product p (fun j a ↦ if i = j then f a else 1)
  have hfactor : ∀ j, (p j).expectation (fun a ↦ if i = j then f a else 1) =
      if i = j then (p j).expectation f else 1 := by
    intro j
    by_cases hj : i = j <;> simp [hj, expectation_const]
  simpa only [Fintype.prod_ite_eq, hfactor] using h

/-- Distinct coordinates with a centered first factor have zero cross moment. -/
theorem cross_expectation_zero (p : ι → FiniteReportLaw α) (i j : ι) (hij : i ≠ j)
    (f g : α → ℝ) (hf : (p i).expectation f = 0) :
    (independentLaw p).expectation (fun x ↦ f (x i) * g (x j)) = 0 := by
  let factors (k : ι) (a : α) := (if i = k then f a else 1) *
    (if j = k then g a else 1)
  have hprod : ∀ x : ι → α, (∏ k, factors k (x k)) = f (x i) * g (x j) := by
    intro x
    simp only [factors, Finset.prod_mul_distrib, Fintype.prod_ite_eq]
  have h := expectation_independent_product p factors
  simp_rw [hprod] at h
  rw [h]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have heq : factors i = f := by
    funext a
    simp [factors, hij.symm]
  rw [heq, hf]

omit [DecidableEq ι] in
/-- Summing finitely many observables commutes with finite expectation. -/
theorem expectation_sum (p : FiniteReportLaw α) (f : ι → α → ℝ) :
    p.expectation (fun x ↦ ∑ i, f i x) = ∑ i, p.expectation (f i) := by
  simp only [FiniteReportLaw.expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- The mean of the independent sum is the sum of the actual coordinate means. -/
theorem independent_sum_mean (p : ι → FiniteReportLaw α) (f : ι → α → ℝ) :
    (independentLaw p).expectation (fun x ↦ ∑ i, f i (x i)) =
      ∑ i, (p i).expectation (f i) := by
  rw [expectation_sum]
  simp only [coordinate_expectation]

/-- For centered coordinates all off-diagonal terms vanish, leaving exactly
the sum of their second moments. -/
theorem independent_sum_second (p : ι → FiniteReportLaw α) (f : ι → α → ℝ)
    (hf : ∀ i, (p i).expectation (f i) = 0) :
    (independentLaw p).expectation (fun x ↦ (∑ i, f i (x i)) ^ 2) =
      ∑ i, (p i).expectation (fun a ↦ f i a ^ 2) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expectation_sum]
  rw [Finset.sum_eq_single i]
  · exact coordinate_expectation p i (fun a ↦ f i a * f i a)
  · intro j _ hji
    exact cross_expectation_zero p j i hji (f j) (f i) (hf j)
  · intro hnot
    exact (hnot (Finset.mem_univ i)).elim

end Descent.Portability.FiniteIndependentMoments
