/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianCovarianceSeparation
import Mathlib.LinearAlgebra.Vandermonde

assert_below Descent.Decision Descent.Program

/-!
Finite covariance mixtures are identified by finitely many projected variance
moments. The projection and Vandermonde nonsingularity are derived from distinct
covariances, with an explicit bound from the permutation-orbit sizes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteCovarianceMoments

open GaussianCovarianceSeparation
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

theorem coefficients_zero (A : I → SymmetricCovariance D) (hA : Function.Injective A)
    (coefficient : I → ℝ)
    (hmoment : ∀ v : D → ℝ, ∀ k < Fintype.card I,
      (∑ i, coefficient i * quadraticValue (A i).val v ^ k) = 0) : coefficient = 0 := by
  classical
  obtain ⟨v, hv⟩ := exists_covariance_separating_vector (fun i ↦ (A i).val)
    (fun i ↦ (A i).property) (fun i j h ↦ hA (Subtype.ext h))
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have he := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (f := fun i : Fin (Fintype.card I) ↦ quadraticValue (A (e i)).val v)
    (v := fun i ↦ coefficient (e i)) (hv.comp e.injective) (fun k ↦ ?_)
  · funext i
    have hh := congrFun he (e.symm i)
    simpa only [e.apply_symm_apply, Pi.zero_apply] using hh
  · rw [Equiv.sum_comp e (fun i ↦ coefficient i * quadraticValue (A i).val v ^ (k : ℕ))]
    exact hmoment v k k.isLt

theorem regroup_counts [DecidableEq J] (index : I → J) (f : J → ℝ) :
    (∑ j, (∑ i, if index i = j then (1 : ℝ) else 0) * f j) = ∑ i, f (index i) := by
  classical
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem orbit_eq_of_variance_moments [DecidableEq D] (A B : SymmetricCovariance D)
    (hmoment : ∀ v : D → ℝ, ∀ k < 2 * Fintype.card (Equiv.Perm D),
      (∑ π : Equiv.Perm D, quadraticValue (permuteCovariance A π).val v ^ k) =
        ∑ π : Equiv.Perm D, quadraticValue (permuteCovariance B π).val v ^ k) :
    ∃ π : Equiv.Perm D, permuteCovariance A π = B := by
  classical
  let s : Finset (SymmetricCovariance D) :=
    Finset.univ.image (permuteCovariance A) ∪ Finset.univ.image (permuteCovariance B)
  let first : Equiv.Perm D → s := fun π ↦
    ⟨permuteCovariance A π, Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨π, by simp, rfl⟩))⟩
  let second : Equiv.Perm D → s := fun π ↦
    ⟨permuteCovariance B π, Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨π, by simp, rfl⟩))⟩
  let coefficient (z : s) : ℝ :=
    (∑ π : Equiv.Perm D, if first π = z then 1 else 0) -
      ∑ π : Equiv.Perm D, if second π = z then 1 else 0
  have hcard : Fintype.card s ≤ 2 * Fintype.card (Equiv.Perm D) := by
    rw [Fintype.card_coe]
    calc
      s.card ≤ (Finset.univ.image (permuteCovariance A)).card +
        (Finset.univ.image (permuteCovariance B)).card := Finset.card_union_le _ _
      _ ≤ Fintype.card (Equiv.Perm D) + Fintype.card (Equiv.Perm D) := by
        exact add_le_add (Finset.card_image_le.trans (by simp))
          (Finset.card_image_le.trans (by simp))
      _ = _ := by ring
  have hc : coefficient = 0 := by
    apply coefficients_zero (fun z : s ↦ z.val) Subtype.val_injective coefficient
    intro v k hk
    simp only [coefficient, sub_mul, Finset.sum_sub_distrib]
    rw [regroup_counts first, regroup_counts second]
    exact sub_eq_zero.mpr (hmoment v k (hk.trans_le hcard))
  have hvalue := congrFun hc (second 1)
  change (∑ π : Equiv.Perm D, if first π = second 1 then (1 : ℝ) else 0) -
      (∑ π : Equiv.Perm D, if second π = second 1 then (1 : ℝ) else 0) = 0 at hvalue
  by_contra hn
  push_neg at hn
  have hfirst : ∀ π, first π ≠ second 1 := by
    intro π h
    have hh := congrArg Subtype.val h
    exact hn π hh
  have hsecond : 0 < (∑ π : Equiv.Perm D, if second π = second 1 then (1 : ℝ) else 0) := by
    apply Finset.sum_pos'
    · intro π _
      split_ifs <;> norm_num
    · exact ⟨1, Finset.mem_univ _, by simp⟩
  simp only [hfirst, if_false, Finset.sum_const_zero, zero_sub] at hvalue
  linarith

end Descent.Portability.FiniteCovarianceMoments
