/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ControlledCoarseGraining
import Descent.Portability.EvolutionaryObservability

assert_below Descent.Decision Descent.Program

/-!
Finite matrices as continuous operators on supremum-norm observable vectors.
This bridge preserves exponentials and products and exposes the row-sum norm
needed for Markov coarse-graining certificates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix Matrix.Norms.Operator NNReal

namespace Descent.Portability.MatrixOperatorBridge

variable {S T U : Type*} [Fintype S] [Fintype T] [Fintype U]
  [DecidableEq S] [DecidableEq T] [DecidableEq U]

noncomputable def operator (matrix : Matrix S T ℝ) : (T → ℝ) →L[ℝ] (S → ℝ) :=
  LinearMap.toContinuousLinearMap matrix.toLin'

omit [Fintype S] [DecidableEq S] in
@[simp] theorem operator_apply (matrix : Matrix S T ℝ) (vector : T → ℝ) :
    operator matrix vector = matrix *ᵥ vector := rfl

omit [Fintype S] [DecidableEq S] in
@[simp] theorem operator_zero : operator (0 : Matrix S T ℝ) = 0 := by
  ext vector
  simp

@[simp] theorem operator_one : operator (1 : Matrix S S ℝ) = 1 := by
  ext vector
  simp

omit [Fintype S] [DecidableEq S] in
@[simp] theorem operator_add (first second : Matrix S T ℝ) :
    operator (first + second) = operator first + operator second := by
  ext vector
  simp [Matrix.add_mulVec]

omit [Fintype S] [DecidableEq S] in
@[simp] theorem operator_sub (first second : Matrix S T ℝ) :
    operator (first - second) = operator first - operator second := by
  ext vector
  simp [Matrix.sub_mulVec]

omit [Fintype S] [DecidableEq S] in
@[simp] theorem operator_smul (scalar : ℝ) (matrix : Matrix S T ℝ) :
    operator (scalar • matrix) = scalar • operator matrix := by
  ext vector
  simp [Matrix.smul_mulVec]

omit [Fintype S] [DecidableEq S] in
@[simp] theorem operator_mul (first : Matrix S T ℝ) (second : Matrix T U ℝ) :
    operator (first * second) = (operator first).comp (operator second) := by
  ext vector
  simp [Matrix.mulVec_mulVec]

noncomputable def operatorLinear : Matrix S T ℝ →ₗ[ℝ] ((T → ℝ) →L[ℝ] (S → ℝ)) where
  toFun := operator
  map_add' := operator_add
  map_smul' := operator_smul

noncomputable def operatorHom : Matrix S S ℝ →+* ((S → ℝ) →L[ℝ] (S → ℝ)) where
  toFun := operator
  map_zero' := operator_zero
  map_one' := operator_one
  map_add' := operator_add
  map_mul' first second := by rw [operator_mul, ContinuousLinearMap.mul_def]

/-- Matrix exponential and observable-semigroup exponential are the same operator. -/
theorem operator_exp (matrix : Matrix S S ℝ) :
    operator (NormedSpace.exp ℝ matrix) = NormedSpace.exp ℝ (operator matrix) := by
  exact NormedSpace.map_exp ℝ (operatorHom (S := S))
    (operatorLinear (S := S) (T := S)).continuous_of_finiteDimensional matrix

omit [DecidableEq S] in
/-- The operator norm is bounded by the maximum absolute row-sum norm. -/
theorem operator_norm_le (matrix : Matrix S T ℝ) : ‖operator matrix‖ ≤ ‖matrix‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg matrix)
  intro vector
  exact Matrix.linfty_opNorm_mulVec matrix vector

omit [DecidableEq S] in
/-- Each row sum is also bounded by the operator norm: a sign vector attains it. -/
theorem row_abs_sum_le_operator_norm (matrix : Matrix S T ℝ) (source : S) :
    ∑ target, |matrix source target| ≤ ‖operator matrix‖ := by
  let vector : T → ℝ := fun target ↦ if 0 ≤ matrix source target then 1 else -1
  have hvector : ‖vector‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro target
    by_cases h : 0 ≤ matrix source target <;> simp [vector, h]
  have heq : (operator matrix vector) source = ∑ target, |matrix source target| := by
    rw [operator_apply]
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_congr rfl
    intro target _
    by_cases h : 0 ≤ matrix source target
    · simp [vector, h, abs_of_nonneg h]
    · simp [vector, h, abs_of_neg (lt_of_not_ge h)]
  calc
    ∑ target, |matrix source target| = |(operator matrix vector) source| := by
      rw [heq, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)]
    _ ≤ ‖operator matrix vector‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (operator matrix vector) source
    _ ≤ ‖operator matrix‖ * ‖vector‖ := (operator matrix).le_opNorm vector
    _ ≤ ‖operator matrix‖ := mul_le_of_le_one_right (norm_nonneg _) hvector


omit [DecidableEq S] in
/-- The matrix maximum absolute row-sum norm is exactly the observable operator norm. -/
theorem operator_norm_eq (matrix : Matrix S T ℝ) : ‖operator matrix‖ = ‖matrix‖ := by
  apply le_antisymm (operator_norm_le matrix)
  rw [Matrix.linfty_opNorm_def]
  change ((Finset.univ.sup (fun source ↦ ∑ target, ‖matrix source target‖₊) : ℝ≥0) : ℝ) ≤
    (‖operator matrix‖₊ : ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro source _
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using
    row_abs_sum_le_operator_norm matrix source

/-- Markov kernels contract bounded observable differences in supremum norm. -/
theorem markov_operator_norm_le_one (kernel : S → FiniteReportLaw S) :
    ‖operator (InterleavedMutationExponential.kernelMatrix kernel)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro vector
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg vector)).mpr
  intro source
  change |(kernel source).expectation vector| ≤ ‖vector‖
  exact EvolutionaryObservability.expectation_abs_le _ _ _
    (fun target ↦ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm vector target)

end Descent.Portability.MatrixOperatorBridge
