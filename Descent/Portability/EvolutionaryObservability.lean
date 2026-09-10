/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MinimalObservableLaw
import Descent.Portability.InterleavedMutationExponential

assert_below Descent.Decision Descent.Program

/-!
Finite-horizon evolutionary observability: exact forecast loss, the weighted
trajectory operator, and its Gramian on any specified residual state space.
The probabilistic feasibility of a residual ball is a separate assumption in
any sharp minimax application of these algebraic identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix

namespace Descent.Portability.EvolutionaryObservability

open InterleavedMutationExponential
variable {S I T R : Type*} [Fintype S] [Fintype I] [Fintype T] [Fintype R]

noncomputable def gramian (reports : T → Matrix S I ℝ) (weights : T → ℝ) : Matrix S S ℝ :=
  ∑ time, weights time • (reports time * (reports time).transpose)

noncomputable def forecastLoss (reports : T → Matrix S I ℝ) (weights : T → ℝ)
    (difference : S → ℝ) : ℝ :=
  ∑ time, weights time * ∑ report, ((reports time).transpose *ᵥ difference) report ^ 2

/-- The matrix Gramian evaluates the complete weighted trajectory loss. -/
theorem forecastLoss_eq_quadratic (reports : T → Matrix S I ℝ) (weights : T → ℝ)
    (difference : S → ℝ) :
    forecastLoss reports weights difference =
      difference ⬝ᵥ gramian reports weights *ᵥ difference := by
  unfold forecastLoss gramian
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro time _
  rw [Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  have hv : difference ᵥ* reports time = (reports time).transpose *ᵥ difference := by
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rw [hv]
  simp only [dotProduct, pow_two, smul_eq_mul]

/-- Rows are time/report pairs; columns are initial-state directions. -/
noncomputable def trajectoryMatrix (reports : T → Matrix S I ℝ) (weights : T → ℝ) :
    Matrix (T × I) S ℝ :=
  fun output state ↦ Real.sqrt (weights output.1) * reports output.1 state output.2

omit [Fintype S] in
/-- Stacking the square-root-weighted forecasts produces exactly the Gramian. -/
theorem trajectory_gramian (reports : T → Matrix S I ℝ) (weights : T → ℝ)
    (hweights : ∀ time, 0 ≤ weights time) :
    (trajectoryMatrix reports weights).transpose * trajectoryMatrix reports weights =
      gramian reports weights := by
  ext first second
  simp only [Matrix.mul_apply, Matrix.transpose_apply, trajectoryMatrix,
    Fintype.sum_prod_type, gramian, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro time _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro report _
  have hsquare := Real.sq_sqrt (hweights time)
  calc
    _ = Real.sqrt (weights time) ^ 2 *
        (reports time first report * reports time second report) := by ring
    _ = _ := by rw [hsquare]

omit [Fintype R] in
/-- Any residual parametrization composes with the same forecast operator.
For the report's ellipsoid take `residual = Γ^(1/2) Q`. -/
theorem residual_trajectory_gramian (reports : T → Matrix S I ℝ) (weights : T → ℝ)
    (hweights : ∀ time, 0 ≤ weights time) (residual : Matrix S R ℝ) :
    (trajectoryMatrix reports weights * residual).transpose *
        (trajectoryMatrix reports weights * residual) =
      residual.transpose * gramian reports weights * residual := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc, ← trajectory_gramian reports weights hweights]

variable [DecidableEq S]

noncomputable def evolvedReports (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (time : ℕ) : Matrix S I ℝ := kernelMatrix kernel ^ time * reports

omit [Fintype I] in
/-- These are the actual expected reports after `time` evolutionary steps. -/
theorem evolvedReports_expectation (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (time : ℕ) (source : S) (report : I) :
    evolvedReports kernel reports time source report =
      (ExactFiniteHistoryLaw.propagate (FiniteReportLaw.pointMass source)
        (fun _ ↦ kernel) time).expectation (fun state ↦ reports state report) := by
  simp only [evolvedReports, Matrix.mul_apply, FiniteReportLaw.expectation, propagate_mass]

/-- Every power of the evolutionary kernel is again a probability row. -/
noncomputable def powerLaw (kernel : S → FiniteReportLaw S) (time : ℕ) (source : S) :
    FiniteReportLaw S :=
  ExactFiniteHistoryLaw.propagate (FiniteReportLaw.pointMass source) (fun _ ↦ kernel) time

theorem powerLaw_mass (kernel : S → FiniteReportLaw S) (time : ℕ) (source target : S) :
    (powerLaw kernel time source).mass target = (kernelMatrix kernel ^ time) source target :=
  propagate_mass _ _ _ _

omit [DecidableEq S] in
/-- Convex averaging cannot amplify a uniform absolute bound. -/
theorem expectation_abs_le (law : FiniteReportLaw S) (metric : S → ℝ) (bound : ℝ)
    (hbound : ∀ state, |metric state| ≤ bound) : |law.expectation metric| ≤ bound := by
  unfold FiniteReportLaw.expectation
  calc
    |∑ state, law.mass state * metric state| ≤ ∑ state, |law.mass state * metric state| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ state, law.mass state * |metric state| := by
      simp only [abs_mul, abs_of_nonneg (law.mass_nonneg _)]
    _ ≤ ∑ state, law.mass state * bound :=
      Finset.sum_le_sum fun state _ ↦
        mul_le_mul_of_nonneg_left (hbound state) (law.mass_nonneg state)
    _ = bound := by rw [← Finset.sum_mul, law.mass_sum, one_mul]

omit [Fintype I] in
theorem evolvedReports_abs_le (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (bound : I → ℝ)
    (hbound : ∀ state report, |reports state report| ≤ bound report)
    (time : ℕ) (source : S) (report : I) :
    |evolvedReports kernel reports time source report| ≤ bound report := by
  rw [evolvedReports_expectation]
  exact expectation_abs_le _ _ _ (fun state ↦ hbound state report)

end Descent.Portability.EvolutionaryObservability
