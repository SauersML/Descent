/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteIndependentMoments
import Mathlib.Topology.ContinuousMap.Bounded.Normed

assert_below Descent.Decision Descent.Program

/-!
Finite independent sums act on bounded continuous observables through powers
of an explicit translation operator. The operator identity is derived from the
full product law, retaining all nonlinear observables of the sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IndependentShiftOperator

open scoped BigOperators BoundedContinuousFunction
open HWEInteractionLaw

abbrev Observable := ℝ →ᵇ ℝ

/-- Translation acts continuously and linearly on bounded continuous observables. -/
noncomputable def translate (c : ℝ) : Observable →L[ℝ] Observable :=
  ({ toFun := fun f : Observable ↦
        f.compContinuous ⟨fun x ↦ x + c, continuous_id.add continuous_const⟩
     map_add' := fun _ _ ↦ by ext x; rfl
     map_smul' := fun _ _ ↦ by ext x; rfl } : Observable →ₗ[ℝ] Observable).mkContinuous 1
    (by
      intro f
      simpa only [one_mul] using
        (BoundedContinuousFunction.norm_compContinuous_le f
          (⟨fun x : ℝ ↦ x + c, continuous_id.add continuous_const⟩ : C(ℝ, ℝ))))

@[simp] theorem translate_apply (c : ℝ) (f : Observable) (x : ℝ) :
    translate c f x = f (x + c) := rfl

/-- One independent summand updates every observable by its actual finite law. -/
noncomputable def shift {α : Type*} [Fintype α] (p : FiniteReportLaw α) (g : α → ℝ) :
    Observable →L[ℝ] Observable := ∑ a, p.mass a • translate (g a)

theorem shift_apply {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (g : α → ℝ) (f : Observable) (x : ℝ) :
    shift p g f x = p.expectation (fun a ↦ f (x + g a)) := by
  simp [shift, FiniteReportLaw.expectation, translate_apply]

/-- Split a sampled row into its first draw and the remaining draws. -/
def splitSample (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun x := (x 0, fun i ↦ x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  right_inv x := by cases x; rfl

/-- The full product law factors over the actual first coordinate and actual remaining row. -/
theorem independent_sum_succ {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (g : α → ℝ) (f : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    (independentLaw (fun _ : Fin (n + 1) ↦ p)).expectation
      (fun sample ↦ f (x + ∑ j, g (sample j))) =
    p.expectation (fun a ↦ (independentLaw (fun _ : Fin n ↦ p)).expectation
      (fun sample ↦ f ((x + g a) + ∑ j, g (sample j)))) := by
  simp only [FiniteReportLaw.expectation, independentLaw, Finset.mul_sum, ← mul_assoc]
  rw [← Fintype.sum_prod_type (fun z : α × (Fin n → α) ↦
    (p.mass z.1 * ∏ j, p.mass (z.2 j)) * f ((x + g z.1) + ∑ j, g (z.2 j)))]
  apply Fintype.sum_equiv (splitSample α n)
  intro sample
  change ((∏ j : Fin (n + 1), p.mass (sample j)) *
    f (x + ∑ j : Fin (n + 1), g (sample j))) =
    (p.mass (sample 0) * ∏ j : Fin n, p.mass (sample j.succ)) *
      f ((x + g (sample 0)) + ∑ j : Fin n, g (sample j.succ))
  rw [Fin.prod_univ_succ, Fin.sum_univ_succ, add_assoc]

/-- Powers of the translation operator equal the full nonlinear finite-sample expectation. -/
theorem shift_pow_sample {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (g : α → ℝ) (f : Observable) (x : ℝ) (n : ℕ) :
    (shift p g ^ n) f x =
      (independentLaw (fun _ : Fin n ↦ p)).expectation
        (fun sample ↦ f (x + ∑ j, g (sample j))) := by
  induction n generalizing x with
  | zero =>
    simp [FiniteReportLaw.expectation, independentLaw]
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, shift_apply, independent_sum_succ]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only
    rw [ih]

end Descent.Portability.IndependentShiftOperator
