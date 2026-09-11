/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Factorial
import Descent.Portability.ArchaicPrediction.Moments

assert_below Descent.Decision Descent.Program

/-!
# Complete response panels, assay noise, and truncation

Every binary response has a unique multilinear representation. The low-degree
panel theorem therefore restricts a complete representation, rather than an
assumed basis with unproved completeness. The assay-error calculation uses
explicit second moments; independent centered errors with common variance
are a sufficient special case. It does not assume different recovered
coefficients are independent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
variable {I H J : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype J]

noncomputable def subsetExpansion : (Finset I → ℝ) →ₗ[ℝ] (Finset I → ℝ) where
  toFun := subsetResponse
  map_add' a b := by funext T; simp [subsetResponse, Finset.sum_add_distrib]
  map_smul' c a := by funext T; simp [subsetResponse, Finset.mul_sum]

theorem subsetExpansion_injective : Function.Injective (subsetExpansion (I := I)) := by
  intro a b h
  funext S
  rw [← factorial_recovery a S, ← factorial_recovery b S]
  apply Finset.sum_congr rfl
  intro T _
  rw [show subsetResponse a T = subsetResponse b T from congrFun h T]

theorem complete_response_panel (f : Finset I → ℝ) :
    ∃! a : Finset I → ℝ, ∀ T, subsetResponse a T = f T := by
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl
    (f := subsetExpansion (I := I))).mp subsetExpansion_injective
  obtain ⟨a, ha⟩ := hs f
  refine ⟨a, fun T => congrFun ha T, ?_⟩
  intro b hb
  exact subsetExpansion_injective ((funext hb).trans ha.symm)

/-- Equation (3.1): unique representation on the actual binary cube. -/
theorem binary_multilinear_representation (f : (I → Bool) → ℝ) :
    ∃! a : Finset I → ℝ, ∀ x,
      MvPolynomial.eval (fun i => allele (x i)) (responsePolynomial a) = f x := by
  classical
  obtain ⟨a, ha, hu⟩ := complete_response_panel (fun T : Finset I => f (fun i => decide (i ∈ T)))
  have hr (x : I → Bool) : (fun i => decide (i ∈ Finset.univ.filter (fun j => x j = true))) = x := by
    funext i
    cases hx : x i <;> simp [hx]
  refine ⟨a, ?_, ?_⟩
  · intro x
    have he : (fun i => allele (x i)) =
        (fun i => if i ∈ Finset.univ.filter (fun j => x j = true) then (1 : ℝ) else 0) := by
      funext i
      cases hx : x i <;> simp [hx, allele]
    rw [he, subsetResponse_evaluation, ha, hr]
  · intro b hb
    apply hu b
    intro T
    have h := hb (fun i => decide (i ∈ T))
    have he : (fun i => allele (decide (i ∈ T))) = (fun i => if i ∈ T then (1 : ℝ) else 0) := by
      funext i; by_cases hi : i ∈ T <;> simp [hi, allele]
    rwa [he, subsetResponse_evaluation] at h

/-- The exact squared error of a linear combination of uncorrelated errors. -/
theorem orthogonal_noise_risk [DecidableEq J] (w : H → ℝ) (noise : J → H → ℝ)
    (variance : J → ℝ)
    (hsecond : ∀ i j, weightedMean w (fun h => noise i h * noise j h) =
      if i = j then variance i else 0) (c : J → ℝ) :
    weightedMean w (fun h => (∑ j, c j * noise j h) ^ 2) = ∑ j, c j ^ 2 * variance j := by
  rw [weighted_product_expansion]
  simp_rw [hsecond]
  simp [pow_two]

/-- Equation (4.3), including the exponential cost in the contrast order. -/
theorem factorial_contrast_noise (w : H → ℝ) (noise : Finset I → H → ℝ) (variance : ℝ)
    (hsecond : ∀ S T, weightedMean w (fun h => noise S h * noise T h) =
      if S = T then variance else 0) (S : Finset I) :
    weightedMean w (fun h => (∑ T ∈ S.powerset,
      (-1 : ℝ) ^ (S.card - T.card) * noise T h) ^ 2) = 2 ^ S.card * variance := by
  have h := orthogonal_noise_risk w noise (fun _ => variance) hsecond
    (fun T => if T ⊆ S then (-1 : ℝ) ^ (S.card - T.card) else 0)
  have hp : ∀ n : ℕ, ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    intro n
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hc : (Finset.univ.filter (fun T : Finset I => T ⊆ S)).card = 2 ^ S.card := by
    rw [← powerset_eq_filter, Finset.card_powerset]
  simpa [powerset_eq_filter, Finset.sum_filter, ite_mul, hp,
    ← Finset.sum_filter, hc] using h

/-- Any omitted bounded basis modes give this pointwise truncation budget. -/
theorem bounded_response_tail [DecidableEq J] (c : J → ℝ) (φ : J → ℝ) (keep : Finset J)
    (hφ : ∀ j, |φ j| ≤ 1) :
    |(∑ j, c j * φ j) - ∑ j ∈ keep, c j * φ j| ≤ ∑ j ∈ Finset.univ \ keep, |c j| := by
  classical
  rw [← Finset.sum_sdiff (Finset.subset_univ keep)]
  rw [add_sub_cancel_right]
  calc
    _ ≤ ∑ j ∈ Finset.univ \ keep, |c j * φ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hφ j) (abs_nonneg _)).trans_eq (mul_one _)

/-- Standardized tag error separates target tag error and coefficient-transfer regret. -/
theorem tag_transfer_regret (β ρsource ρtarget : ℝ) :
    β ^ 2 * (1 + ρsource ^ 2 - 2 * ρsource * ρtarget) =
      β ^ 2 * (1 - ρtarget ^ 2) + β ^ 2 * (ρsource - ρtarget) ^ 2 := by ring

/-- A nonzero background rectangle is precisely a changed response contrast. -/
theorem background_rectangle_detects_change (u11 u01 u10 u00 : ℝ) :
    (u11 - u01) - (u10 - u00) ≠ 0 ↔ u11 - u01 ≠ u10 - u00 := sub_ne_zero

end Descent.Portability.ArchaicPrediction
