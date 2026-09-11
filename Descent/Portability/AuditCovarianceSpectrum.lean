/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
The covariance spectrum used in Decision-Directed Portability, Theorem 10.
The largest eigenvalue is obtained from the finite-dimensional spectral
theorem for the actual sum of weighted outer products. Its quadratic-form
bound is derived, and equality is attained in a unit eigenvector direction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AuditCovarianceSpectrum

open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The covariance envelope operator, with normalization already included in the row vectors. -/
noncomputable def covariance (w : ι → ℝ) (u : ι → E) : E →ₗ[ℝ] E :=
  ∑ i, w i • (innerSL ℝ (u i)).toLinearMap.smulRight (u i)

/-- The covariance operator's quadratic form is the sum of the directional variance terms. -/
theorem quadratic (w : ι → ℝ) (u : ι → E) (a : E) :
    inner ℝ a (covariance w u a) = ∑ i, w i * (inner ℝ a (u i)) ^ 2 := by
  simp only [covariance, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (u i) a]
  ring

/-- A sum of real weighted outer products is symmetric. -/
theorem symmetric (w : ι → ℝ) (u : ι → E) : (covariance w u).IsSymmetric := by
  intro a b
  simp only [covariance, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (u i) a]
  ring

/-- Nonnegative marginal variance envelopes produce a positive semidefinite operator. -/
theorem positive (w : ι → ℝ) (u : ι → E) (hw : ∀ i, 0 ≤ w i) :
    (covariance w u).IsPositive := by
  refine ⟨symmetric w u, ?_⟩
  intro a
  change 0 ≤ inner ℝ (covariance w u a) a
  rw [real_inner_comm, quadratic]
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i) (sq_nonneg _))

/-- The actual covariance eigenvalues, in decreasing order. -/
noncomputable def eigenvalues (w : ι → ℝ) (u : ι → E) :
    Fin (Module.finrank ℝ E) → ℝ := (symmetric w u).eigenvalues rfl

/-- An orthonormal eigenbasis of the actual covariance operator. -/
noncomputable def basis (w : ι → ℝ) (u : ι → E) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := (symmetric w u).eigenvectorBasis rfl

/-- The largest covariance eigenvalue, with zero for the zero-dimensional correction space. -/
noncomputable def largest (w : ι → ℝ) (u : ι → E) : ℝ :=
  if h : 0 < Module.finrank ℝ E then eigenvalues w u ⟨0, h⟩ else 0

/-- Every covariance eigenvalue is bounded by the first one. -/
theorem eigenvalue_le_largest (w : ι → ℝ) (u : ι → E)
    (i : Fin (Module.finrank ℝ E)) : eigenvalues w u i ≤ largest w u := by
  have hd : 0 < Module.finrank ℝ E := Nat.zero_lt_of_lt i.isLt
  rw [largest, dif_pos hd]
  exact (symmetric w u).eigenvalues_antitone rfl
    (show (⟨0, hd⟩ : Fin (Module.finrank ℝ E)) ≤ i from Nat.zero_le _)

/-- Positive marginal envelopes make the largest covariance eigenvalue nonnegative. -/
theorem largest_nonneg (w : ι → ℝ) (u : ι → E) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ largest w u := by
  unfold largest
  split_ifs with hd
  · exact (positive w u hw).nonneg_eigenvalues rfl ⟨0, hd⟩
  · exact le_refl 0

/-- The actual covariance quadratic form diagonalizes in its proved eigenbasis. -/
theorem spectral_quadratic (w : ι → ℝ) (u : ι → E) (a : E) :
    inner ℝ a (covariance w u a) = ∑ i, eigenvalues w u i * ((basis w u).repr a i) ^ 2 := by
  rw [← (basis w u).sum_inner_mul_inner a (covariance w u a)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show inner ℝ a (basis w u i) = inner ℝ (basis w u i) a from real_inner_comm _ _,
    ← OrthonormalBasis.repr_apply_apply,
    ← OrthonormalBasis.repr_apply_apply]
  have he := (symmetric w u).eigenvectorBasis_apply_self_apply rfl a i
  change (basis w u).repr (covariance w u a) i =
    eigenvalues w u i * (basis w u).repr a i at he
  rw [he]
  ring

/-- The sum of squared spectral coordinates is the actual squared norm. -/
theorem sum_coordinates_sq (w : ι → ℝ) (u : ι → E) (a : E) :
    (∑ i, ((basis w u).repr a i) ^ 2) = ‖a‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (basis w u).sum_inner_mul_inner a a]
  apply Finset.sum_congr rfl
  intro i _
  rw [show inner ℝ a (basis w u i) = inner ℝ (basis w u i) a from real_inner_comm _ _,
    ← OrthonormalBasis.repr_apply_apply]
  ring

/-- The exact largest-eigenvalue bound used for every audit direction. -/
theorem quadratic_le (w : ι → ℝ) (u : ι → E) (a : E) :
    (∑ i, w i * (inner ℝ a (u i)) ^ 2) ≤ largest w u * ‖a‖ ^ 2 := by
  rw [← quadratic, spectral_quadratic, ← sum_coordinates_sq w u a, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦
    mul_le_mul_of_nonneg_right (eigenvalue_le_largest w u i) (sq_nonneg _))

/-- In nonzero dimension a unit vector attains the stated variance constant. -/
theorem largest_attained (w : ι → ℝ) (u : ι → E) (hd : 0 < Module.finrank ℝ E) :
    ∃ a : E, ‖a‖ = 1 ∧ (∑ i, w i * (inner ℝ a (u i)) ^ 2) = largest w u := by
  let j : Fin (Module.finrank ℝ E) := ⟨0, hd⟩
  refine ⟨basis w u j, (basis w u).orthonormal.1 j, ?_⟩
  rw [← quadratic]
  have he := (symmetric w u).apply_eigenvectorBasis rfl j
  change covariance w u (basis w u j) = eigenvalues w u j • basis w u j at he
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq,
    (basis w u).orthonormal.1 j, one_pow, mul_one, largest, dif_pos hd]

end Descent.Portability.AuditCovarianceSpectrum
