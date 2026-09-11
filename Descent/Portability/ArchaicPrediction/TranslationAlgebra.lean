/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.ResponsePanels

assert_below Descent.Decision Descent.Program

/-!
# Centered response uniqueness and commuting lowering operators

Recentring preserves completeness and uniqueness on the binary cube. The
coordinate lowering maps have square zero and commute, giving the finite
translation algebra behind the all-order coefficient formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem centered_multilinear_representation (p : I → ℝ) (f : (I → Bool) → ℝ) :
    ∃! a : Finset I → ℝ, ∀ x,
      MvPolynomial.eval ((fun i => allele (x i)) - p) (responsePolynomial a) = f x := by
  obtain ⟨b, hb, hu⟩ := binary_multilinear_representation f
  refine ⟨transport 0 p b, ?_, ?_⟩
  · intro x
    rw [evaluate_transport, sub_zero, hb]
  · intro a ha
    have he : transport p 0 a = b := by
      apply hu
      intro x
      simpa only [sub_zero] using
        (evaluate_transport p 0 (fun i => allele (x i)) a).trans (ha x)
    have h := congrArg (transport 0 p) he
    simpa only [transport_inverse] using h

/-- Remove a single coordinate from every monomial containing it. -/
noncomputable def lowerCoordinate (i : I) : (Finset I → ℝ) →ₗ[ℝ] (Finset I → ℝ) where
  toFun a S := if i ∈ S then 0 else a (insert i S)
  map_add' a b := by funext S; by_cases hi : i ∈ S <;> simp [hi]
  map_smul' c a := by funext S; by_cases hi : i ∈ S <;> simp [hi]

theorem lowerCoordinate_square_zero (i : I) :
    (lowerCoordinate i).comp (lowerCoordinate i) = 0 := by
  apply LinearMap.ext
  intro a
  funext S
  by_cases hi : i ∈ S <;> simp [lowerCoordinate, hi]

theorem lowerCoordinate_commute (i j : I) :
    (lowerCoordinate i).comp (lowerCoordinate j) =
      (lowerCoordinate j).comp (lowerCoordinate i) := by
  by_cases hij : i = j
  · subst j; rfl
  apply LinearMap.ext
  intro a
  funext S
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [lowerCoordinate, hi, hj, hij, Ne.symm hij, Finset.insert_comm]

end Descent.Portability.ArchaicPrediction
