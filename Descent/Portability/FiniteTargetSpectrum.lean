/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AdaptiveLinearMeasurements
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint

assert_below Descent.Decision Descent.Program

/-!
The target spectrum is derived from the self-adjoint Gram operator of the
actual target map. This supplies squared singular values and a norm expansion,
rather than assuming a spectral lower bound for the measurement problem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteTargetSpectrum

open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

noncomputable def gram (L : E →L[ℝ] F) : E →L[ℝ] E := L.adjoint.comp L

theorem gram_symmetric (L : E →L[ℝ] F) : (gram L).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (L.adjoint (L x)) y = inner ℝ x (L.adjoint (L y))
  rw [L.adjoint_inner_left, L.adjoint_inner_right]

/-- Squared singular values, ordered from largest to smallest. -/
noncomputable def squaredSingularValues (L : E →L[ℝ] F) :
    Fin (Module.finrank ℝ E) → ℝ := (gram_symmetric L).eigenvalues rfl

/-- The corresponding right singular basis exists by the finite spectral theorem. -/
noncomputable def rightBasis (L : E →L[ℝ] F) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  (gram_symmetric L).eigenvectorBasis rfl

theorem squaredSingularValues_antitone (L : E →L[ℝ] F) :
    Antitone (squaredSingularValues L) := (gram_symmetric L).eigenvalues_antitone rfl

theorem gram_rightBasis (L : E →L[ℝ] F) (i : Fin (Module.finrank ℝ E)) :
    gram L (rightBasis L i) = squaredSingularValues L i • rightBasis L i :=
  (gram_symmetric L).apply_eigenvectorBasis rfl i

/-- The target norm is exactly the diagonal quadratic form in singular coordinates. -/
theorem target_norm_expansion (L : E →L[ℝ] F) (v : E) :
    ‖L v‖ ^ 2 = ∑ i, squaredSingularValues L i * ((rightBasis L).repr v i) ^ 2 := by
  have hnorm := L.apply_norm_sq_eq_inner_adjoint_right v
  change ‖L v‖ ^ 2 = inner ℝ v (gram L v) at hnorm
  rw [hnorm, ← (rightBasis L).sum_inner_mul_inner v (gram L v)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show inner ℝ v (rightBasis L i) = inner ℝ (rightBasis L i) v from
    real_inner_comm _ _, ← OrthonormalBasis.repr_apply_apply,
    ← OrthonormalBasis.repr_apply_apply]
  have heig := (gram_symmetric L).eigenvectorBasis_apply_self_apply rfl v i
  change (rightBasis L).repr (gram L v) i =
    squaredSingularValues L i * (rightBasis L).repr v i at heig
  rw [heig]
  ring

/-- Every squared singular value is nonnegative, derived from the target norm. -/
theorem squaredSingularValues_nonneg (L : E →L[ℝ] F)
    (i : Fin (Module.finrank ℝ E)) : 0 ≤ squaredSingularValues L i := by
  have hnorm := L.apply_norm_sq_eq_inner_adjoint_right (rightBasis L i)
  change ‖L (rightBasis L i)‖ ^ 2 =
    inner ℝ (rightBasis L i) (gram L (rightBasis L i)) at hnorm
  rw [gram_rightBasis, inner_smul_right,
    real_inner_self_eq_norm_sq, (rightBasis L).orthonormal.1 i, one_pow, mul_one] at hnorm
  rw [← hnorm]
  exact sq_nonneg _

end Descent.Portability.FiniteTargetSpectrum
