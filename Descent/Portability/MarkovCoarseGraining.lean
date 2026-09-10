/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarkovPoissonLaw

assert_below Descent.Decision Descent.Program

/-!
Computable finite Markov coarse-graining error: the generator defect controls
maximum row-sum error and total variation of the actual aggregated state laws.
Fine and coarse state spaces may have different sizes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix Matrix.Norms.Operator NNReal

namespace Descent.Portability.MarkovCoarseGraining

open MatrixOperatorBridge ControlledCoarseGraining MarkovPoissonLaw
open InterleavedMutationExponential
variable {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

noncomputable def matrixDefect (fine : Matrix S S ℝ) (coarse : Matrix T T ℝ)
    (lift : Matrix S T ℝ) : Matrix S T ℝ := fine * lift - lift * coarse

noncomputable def matrixError (fine : Matrix S S ℝ) (coarse : Matrix T T ℝ)
    (lift : Matrix S T ℝ) (time : ℝ) : Matrix S T ℝ :=
  NormedSpace.exp ℝ (time • fine) * lift - lift * NormedSpace.exp ℝ (time • coarse)

theorem operator_matrixDefect (fine : Matrix S S ℝ) (coarse : Matrix T T ℝ)
    (lift : Matrix S T ℝ) :
    operator (matrixDefect fine coarse lift) =
      defect (operator fine) (operator coarse) (operator lift) := by
  simp [matrixDefect, defect]

theorem operator_matrixError (fine : Matrix S S ℝ) (coarse : Matrix T T ℝ)
    (lift : Matrix S T ℝ) (time : ℝ) :
    operator (matrixError fine coarse lift time) =
      (evolution (operator fine) time).comp (operator lift) -
        (operator lift).comp (evolution (operator coarse) time) := by
  simp [matrixError, evolution, operator_exp]

/-- Every row's total absolute error has the same computable defect certificate. -/
theorem row_error_bound (fine : S → FiniteReportLaw S) (coarse : T → FiniteReportLaw T)
    (fineRate coarseRate : ℝ≥0) (lift : Matrix S T ℝ) (time : ℝ) (htime : 0 ≤ time)
    (source : S) :
    (∑ target, |matrixError (generator fine fineRate) (generator coarse coarseRate)
      lift time source target|) ≤
        time * ‖matrixDefect (generator fine fineRate) (generator coarse coarseRate) lift‖ := by
  apply le_trans (row_abs_sum_le_operator_norm _ source)
  rw [operator_matrixError]
  apply le_trans (contraction_defect_bound _ _ _ time htime
    (evolution_norm_le_one fine fineRate) (evolution_norm_le_one coarse coarseRate))
  rw [← operator_matrixDefect]
  exact mul_le_mul_of_nonneg_left (operator_norm_le _) htime

noncomputable def membership (partition : S → T) : Matrix S T ℝ :=
  fun source target ↦ if partition source = target then 1 else 0

noncomputable def stateLaw (kernel : S → FiniteReportLaw S) (rate : ℝ≥0)
    (time : ℝ) (source : S) : FiniteReportLaw S :=
  poissonLaw kernel (rate * Real.toNNReal time) source

theorem stateLaw_matrix (kernel : S → FiniteReportLaw S) (rate : ℝ≥0)
    (time : ℝ) (htime : 0 ≤ time) :
    kernelMatrix (stateLaw kernel rate time) =
      NormedSpace.exp ℝ (time • generator kernel rate) := by
  change kernelMatrix (poissonLaw kernel (rate * Real.toNNReal time)) = _
  rw [poissonLaw_matrix]
  congr 1
  simp only [generator, smul_smul, NNReal.coe_mul, Real.coe_toNNReal time htime]
  congr 1
  ring

/-- The matrix discrepancy is exactly the discrepancy between two normalized
laws: evolve then aggregate, or aggregate first and use the candidate coarse chain. -/
theorem matrixError_mass_difference (fine : S → FiniteReportLaw S)
    (coarse : T → FiniteReportLaw T) (fineRate coarseRate : ℝ≥0)
    (partition : S → T) (time : ℝ) (htime : 0 ≤ time) (source : S) (target : T) :
    matrixError (generator fine fineRate) (generator coarse coarseRate)
        (membership partition) time source target =
      ((stateLaw fine fineRate time source).pushforward partition).mass target -
        (stateLaw coarse coarseRate time (partition source)).mass target := by
  unfold matrixError
  rw [← stateLaw_matrix fine fineRate time htime, ← stateLaw_matrix coarse coarseRate time htime]
  simp only [Matrix.sub_apply, Matrix.mul_apply, kernelMatrix, membership,
    FiniteReportLaw.pushforward, FiniteReportLaw.bind, FiniteReportLaw.pointMass]
  congr 1
  · apply Finset.sum_congr rfl
    intro state _
    by_cases heq : partition state = target
    · simp [heq]
    · simp [heq, Ne.symm heq]
  · simp

/-- Total variation is at most half the time times the maximum row-sum generator defect. -/
theorem totalVariation_error_bound (fine : S → FiniteReportLaw S)
    (coarse : T → FiniteReportLaw T) (fineRate coarseRate : ℝ≥0)
    (partition : S → T) (time : ℝ) (htime : 0 ≤ time) (source : S) :
    ((stateLaw fine fineRate time source).pushforward partition).totalVariation
        (stateLaw coarse coarseRate time (partition source)) ≤
      time * ‖matrixDefect (generator fine fineRate) (generator coarse coarseRate)
        (membership partition)‖ / 2 := by
  rw [FiniteReportLaw.totalVariation_eq_half_sum_abs]
  have hrow := row_error_bound fine coarse fineRate coarseRate
    (membership partition) time htime source
  simp_rw [matrixError_mass_difference fine coarse fineRate coarseRate partition time htime] at hrow
  exact div_le_div_of_nonneg_right hrow (by norm_num)

/-- Every bounded coarse report inherits the same error certificate. -/
theorem bounded_report_error (fine : S → FiniteReportLaw S)
    (coarse : T → FiniteReportLaw T) (fineRate coarseRate : ℝ≥0)
    (partition : S → T) (time : ℝ) (htime : 0 ≤ time) (source : S)
    (report : T → ℝ) (hreport : FiniteReportLaw.BoundedMetric report) :
    |((stateLaw fine fineRate time source).pushforward partition).expectation report -
        (stateLaw coarse coarseRate time (partition source)).expectation report| ≤
      time * ‖matrixDefect (generator fine fineRate) (generator coarse coarseRate)
        (membership partition)‖ / 2 :=
  (FiniteReportLaw.abs_expectation_sub_le_totalVariation _ _ _ hreport).trans
    (totalVariation_error_bound _ _ _ _ _ _ htime _)



omit [DecidableEq T] in
/-- Centering a bounded scalar report gives the sharp oscillation-times-TV factor. -/
theorem expectation_range_totalVariation (first second : FiniteReportLaw T)
    (report : T → ℝ) (lower upper : ℝ)
    (hreport : ∀ state, lower ≤ report state ∧ report state ≤ upper) :
    |first.expectation report - second.expectation report| ≤
      (upper - lower) * first.totalVariation second := by
  have hcenter : first.expectation report - second.expectation report =
      ∑ state, (first.mass state - second.mass state) * (report state - (lower + upper) / 2) := by
    unfold FiniteReportLaw.expectation
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      first.mass_sum, second.mass_sum]
    ring
  rw [hcenter]
  calc
    |∑ state, (first.mass state - second.mass state) * (report state - (lower + upper) / 2)| ≤
        ∑ state, |(first.mass state - second.mass state) *
          (report state - (lower + upper) / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ state, |first.mass state - second.mass state| * ((upper - lower) / 2) := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply abs_le.mpr
      constructor <;> linarith [(hreport state).1, (hreport state).2]
    _ = (upper - lower) * first.totalVariation second := by
      rw [← Finset.sum_mul, FiniteReportLaw.totalVariation_eq_half_sum_abs]
      ring

/-- The arbitrary bounded-observable certificate, with the report's exact oscillation factor. -/
theorem ranged_report_error (fine : S → FiniteReportLaw S)
    (coarse : T → FiniteReportLaw T) (fineRate coarseRate : ℝ≥0)
    (partition : S → T) (time : ℝ) (htime : 0 ≤ time) (source : S)
    (report : T → ℝ) (lower upper : ℝ) (hwidth : lower ≤ upper)
    (hreport : ∀ state, lower ≤ report state ∧ report state ≤ upper) :
    |((stateLaw fine fineRate time source).pushforward partition).expectation report -
        (stateLaw coarse coarseRate time (partition source)).expectation report| ≤
      (upper - lower) / 2 * time *
        ‖matrixDefect (generator fine fineRate) (generator coarse coarseRate)
          (membership partition)‖ := by
  apply le_trans (expectation_range_totalVariation _ _ report lower upper hreport)
  have hTV := totalVariation_error_bound fine coarse fineRate coarseRate partition time htime source
  calc
    _ ≤ (upper - lower) * (time *
        ‖matrixDefect (generator fine fineRate) (generator coarse coarseRate)
          (membership partition)‖ / 2) := mul_le_mul_of_nonneg_left hTV (sub_nonneg.mpr hwidth)
    _ = _ := by ring

/-- The maximum row-sum certificate for arbitrary conservative finite generator
matrices. Their contraction property is derived through exact uniformization. -/
theorem finite_generator_matrix_bound (fine : FiniteGenerator S) (coarse : FiniteGenerator T)
    (lift : Matrix S T ℝ) (time : ℝ) (htime : 0 ≤ time) :
    ‖matrixError fine.matrix coarse.matrix lift time‖ ≤
      time * ‖matrixDefect fine.matrix coarse.matrix lift‖ := by
  rw [← operator_norm_eq, operator_matrixError]
  apply le_trans (contraction_defect_bound _ _ _ time htime
    (finiteGenerator_evolution_norm_le_one fine) (finiteGenerator_evolution_norm_le_one coarse))
  rw [← operator_matrixDefect, operator_norm_eq]

/-- Arbitrary finite generators inherit the actual-law total-variation certificate. -/
theorem finite_generator_totalVariation_bound (fine : FiniteGenerator S)
    (coarse : FiniteGenerator T) (partition : S → T)
    (time : ℝ) (htime : 0 ≤ time) (source : S) :
    ((stateLaw (normalizedKernel fine) (normalizationRate fine) time source).pushforward
      partition).totalVariation (stateLaw (normalizedKernel coarse) (normalizationRate coarse)
          time (partition source)) ≤
      time * ‖matrixDefect fine.matrix coarse.matrix (membership partition)‖ / 2 := by
  have hbound := totalVariation_error_bound (normalizedKernel fine) (normalizedKernel coarse)
    (normalizationRate fine) (normalizationRate coarse) partition time htime source
  simpa only [normalized_generator] using hbound

end Descent.Portability.MarkovCoarseGraining
