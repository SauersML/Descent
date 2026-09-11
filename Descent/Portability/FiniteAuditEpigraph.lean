/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteAuditDesignConvexity
import Descent.Portability.FiniteSlaterMultipliers

assert_below Descent.Decision Descent.Program

/-!
The actual finite-library audit epigraph for Decision-Directed Portability,
Theorem 14. Its variables are the sampling probabilities and the common
variance bound. All convexity and strict feasibility conditions are derived
from the reciprocal audit objective and the supplied labeling budget.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteAuditEpigraph

open FiniteAuditDesign FiniteAuditDesignConvexity
open scoped BigOperators

variable {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]

/-- The audit probability box, with the epigraph coordinate unrestricted. -/
def domain (floor : ι → ℝ) : Set ((ι → ℝ) × ℝ) :=
  {x | ∀ i, x.1 i ∈ Set.Icc (floor i) 1}

/-- The expected-budget constraint and the finite contrast-variance constraints. -/
noncomputable def constraint (a : J → ι → ℝ) (c : ι → ℝ) (B : ℝ) :
    Option J → ((ι → ℝ) × ℝ) → ℝ
  | none, x ↦ spending c x.1 - B
  | some j, x ↦ rowVariance a x.1 j - x.2

/-- The probability box with a free epigraph coordinate is convex. -/
theorem domain_convex (floor : ι → ℝ) : Convex ℝ (domain floor) := by
  have he : domain floor = Set.Icc floor (fun _ ↦ (1 : ℝ)) ×ˢ (Set.univ : Set ℝ) := by
    ext x
    simp [domain, Set.mem_Icc, Pi.le_def, forall_and]
  rw [he]
  exact convex_Icc.prod convex_univ

/-- The epigraph objective is the actual free scalar coordinate and is affine. -/
theorem objective_convex (floor : ι → ℝ) :
    ConvexOn ℝ (domain floor) (fun x : (ι → ℝ) × ℝ ↦ x.2) := by
  refine ⟨domain_convex floor, ?_⟩
  intro x _ y _ α β _ _ _
  exact le_refl _

/-- The actual budget and reciprocal row-variance constraints are convex on the design domain. -/
theorem constraint_convex (a : J → ι → ℝ) (floor c : ι → ℝ) (B : ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) (j : Option J) :
    ConvexOn ℝ (domain floor) (constraint a c B j) := by
  refine ⟨domain_convex floor, ?_⟩
  intro x hx y hy α β hα hβ hsum
  cases j with
  | none =>
    change spending c (α • x.1 + β • y.1) - B ≤
      α * (spending c x.1 - B) + β * (spending c y.1 - B)
    rw [spending_mix]
    have he : α * B + β * B = B := by rw [← add_mul, hsum, one_mul]
    nlinarith
  | some j =>
    have hj : rowVariance a (α • x.1 + β • y.1) j ≤
        α * rowVariance a x.1 j + β * rowVariance a y.1 j := by
      simp only [rowVariance, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ ↦ reciprocal_jensen (a j i) (x.1 i) (y.1 i) α β
        (ha j i) ((hf i).trans_le (hx i).1) ((hf i).trans_le (hy i).1) hα hβ hsum)
    change rowVariance a (α • x.1 + β • y.1) j - (α * x.2 + β * y.2) ≤
      α * (rowVariance a x.1 j - x.2) + β * (rowVariance a y.1 j - y.2)
    nlinarith

/-- A strict expected-budget design supplies every strict epigraph constraint at once. -/
theorem slater_point (a : J → ι → ℝ) (floor c p : ι → ℝ) (B : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (floor i) 1) (hbudget : spending c p < B) :
    ∃ x ∈ domain floor, ∀ j, constraint a c B j x < 0 := by
  refine ⟨(p, worstVariance a p + 1), hp, ?_⟩
  intro j
  cases j with
  | none => exact sub_neg.mpr hbudget
  | some j =>
    change rowVariance a p j - (worstVariance a p + 1) < 0
    linarith [row_le_worst a p j]

end Descent.Portability.FiniteAuditEpigraph
