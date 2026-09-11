/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.OperatorPositiveCone
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Positive

assert_below Descent.Decision Descent.Program

/-!
Finite-dimensional representation of the operator functional produced by
spectral epigraph separation. Riesz representation constructs an actual
operator W with R(A) = trace(W A). Positivity on the quadratic cone forces
W to be positive semidefinite, and R(identity) is exactly its trace.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PositiveOperatorFunctional

open OperatorPositiveCone
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- The rank-one operator mapping z to its inner product with y times x. -/
noncomputable def rank (x y : E) : E →L[ℝ] E := (innerSL ℝ y).smulRight x

/-- The actual value of the rank-one operator. -/
theorem rank_apply (x y z : E) : rank x y z = inner ℝ y z • x := rfl

/-- Rank-one operators are additive in their output vector. -/
theorem rank_add_left (x y z : E) : rank (x + y) z = rank x z + rank y z := by
  ext v
  simp only [rank_apply, ContinuousLinearMap.add_apply, smul_add]

/-- Rank-one operators are additive in their input functional. -/
theorem rank_add_right (x y z : E) : rank x (y + z) = rank x y + rank x z := by
  ext v
  simp only [rank_apply, ContinuousLinearMap.add_apply, inner_add_left, add_smul]

/-- Rank-one operators are homogeneous in their output vector. -/
theorem rank_smul_left (t : ℝ) (x y : E) : rank (t • x) y = t • rank x y := by
  ext v
  simp only [rank_apply, ContinuousLinearMap.smul_apply, smul_comm t]

/-- Real rank-one operators are homogeneous in their input functional. -/
theorem rank_smul_right (t : ℝ) (x y : E) : rank x (t • y) = t • rank x y := by
  ext v
  simp only [rank_apply, ContinuousLinearMap.smul_apply, inner_smul_left,
    conj_trivial, mul_smul]

/-- Fixing the output vector gives a genuine linear functional of the input vector. -/
noncomputable def rowFunctional (R : (E →L[ℝ] E) →L[ℝ] ℝ) (x : E) : E →ₗ[ℝ] ℝ where
  toFun y := R (rank x y)
  map_add' y z := by rw [rank_add_right, map_add]
  map_smul' t y := by rw [rank_smul_right, map_smul]; rfl

/-- Riesz representation constructs the operator rather than assuming a trace representation. -/
noncomputable def representative (R : (E →L[ℝ] E) →L[ℝ] ℝ) : E →ₗ[ℝ] E where
  toFun x := (InnerProductSpace.toDual ℝ E).symm (rowFunctional R x).toContinuousLinearMap
  map_add' x y := by
    apply ext_inner_right ℝ
    intro z
    rw [inner_add_left, InnerProductSpace.toDual_symm_apply,
      InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
    change R (rank (x + y) z) = R (rank x z) + R (rank y z)
    rw [rank_add_left, map_add]
  map_smul' t x := by
    apply ext_inner_right ℝ
    intro z
    rw [inner_smul_left, InnerProductSpace.toDual_symm_apply,
      InnerProductSpace.toDual_symm_apply]
    change R (rank (t • x) z) = t * R (rank x z)
    rw [rank_smul_left, map_smul, smul_eq_mul]

/-- Pairing with the constructed operator recovers the supplied rank-one functional. -/
theorem representative_pairing (R : (E →L[ℝ] E) →L[ℝ] ℝ) (x y : E) :
    inner ℝ (representative R x) y = R (rank x y) :=
  InnerProductSpace.toDual_symm_apply

/-- The difference of the two transposed rank-one operators has zero quadratic form. -/
theorem rank_skew_quadratic (x y z : E) :
    inner ℝ z ((rank x y - rank y x) z) = 0 := by
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, rank_apply, rank_apply,
    inner_smul_right, inner_smul_right, real_inner_comm x z, real_inner_comm y z]
  ring

/-- Positivity on the quadratic cone annihilates skew directions. -/
theorem rank_symmetry (R : (E →L[ℝ] E) →L[ℝ] ℝ)
    (hR : ∀ A, Nonnegative A → 0 ≤ R A) (x y : E) : R (rank x y) = R (rank y x) := by
  have h₁ := hR (rank x y - rank y x) (fun z ↦ by rw [rank_skew_quadratic])
  have h₂ := hR (rank y x - rank x y) (fun z ↦ by rw [rank_skew_quadratic])
  rw [map_sub] at h₁ h₂
  linarith

/-- The representing operator is genuinely positive semidefinite. -/
theorem representative_positive (R : (E →L[ℝ] E) →L[ℝ] ℝ)
    (hR : ∀ A, Nonnegative A → 0 ≤ R A) : (representative R).IsPositive := by
  constructor
  · intro x y
    rw [representative_pairing, real_inner_comm (representative R y) x,
      representative_pairing]
    exact rank_symmetry R hR x y
  · intro x
    change 0 ≤ inner ℝ (representative R x) x
    rw [representative_pairing]
    apply hR
    intro z
    rw [rank_apply, inner_smul_right, real_inner_comm x z]
    exact mul_self_nonneg _

/-- Every operator is the sum of its actual rank-one basis columns. -/
theorem operator_expansion (A : E →L[ℝ] E) :
    A = ∑ j, rank (A (stdOrthonormalBasis ℝ E j)) (stdOrthonormalBasis ℝ E j) := by
  ext x
  simp only [ContinuousLinearMap.sum_apply, rank_apply]
  calc
    A x = A (∑ j, inner ℝ (stdOrthonormalBasis ℝ E j) x •
        stdOrthonormalBasis ℝ E j) :=
      congrArg A ((stdOrthonormalBasis ℝ E).sum_repr' x).symm
    _ = _ := by simp only [map_sum, map_smul]

/-- The functional equals the trace pairing with its constructed representing operator. -/
theorem trace_representation (R : (E →L[ℝ] E) →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    LinearMap.trace ℝ E ((representative R).comp A.toLinearMap) = R A := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  calc
    _ = ∑ j, R (rank (A (stdOrthonormalBasis ℝ E j)) (stdOrthonormalBasis ℝ E j)) := by
      apply Finset.sum_congr rfl
      intro j _
      change inner ℝ (stdOrthonormalBasis ℝ E j)
        (representative R (A (stdOrthonormalBasis ℝ E j))) = _
      rw [real_inner_comm, representative_pairing]
    _ = R (∑ j, rank (A (stdOrthonormalBasis ℝ E j))
        (stdOrthonormalBasis ℝ E j)) := (map_sum R _ _).symm
    _ = R A := congrArg R (operator_expansion A).symm

/-- The value at the identity is exactly the trace of the constructed operator. -/
theorem representative_trace (R : (E →L[ℝ] E) →L[ℝ] ℝ) :
    LinearMap.trace ℝ E (representative R) = R (ContinuousLinearMap.id ℝ E) := by
  simpa using trace_representation R (ContinuousLinearMap.id ℝ E)

end Descent.Portability.PositiveOperatorFunctional
