/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EvolutionaryObservability
import Descent.Portability.SpectralMeasurementMinimax

assert_below Descent.Decision Descent.Program

/-!
Sharp adaptive measurement design for finite evolutionary forecasts. The complete
residual ball is required to consist of probability laws. Forecasts are built from
those actual laws, while the estimator may output an arbitrary report trajectory.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix

namespace Descent.Portability.EvolutionaryForecastMinimax

open EvolutionaryObservability AdaptiveLinearMeasurements SpectralMeasurementMinimax
open InterleavedMutationExponential

variable {S I T R U V : Type*}
  [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype R] [DecidableEq R]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

noncomputable def euclideanOperator (matrix : Matrix U V ℝ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ U := matrix.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq U] in
@[simp] theorem euclideanOperator_apply (matrix : Matrix U V ℝ) (vector : EuclideanSpace ℝ V) :
    euclideanOperator matrix vector = WithLp.toLp 2 (matrix *ᵥ WithLp.ofLp vector) := rfl

omit [DecidableEq U] in
theorem euclideanOperator_comp (first : Matrix U V ℝ) (second : Matrix V R ℝ) :
    (euclideanOperator first).comp (euclideanOperator second) =
      euclideanOperator (first * second) := by
  ext vector state
  simp only [ContinuousLinearMap.comp_apply, euclideanOperator_apply, WithLp.ofLp_toLp]
  rw [Matrix.mulVec_mulVec]

theorem euclideanOperator_adjoint (matrix : Matrix U V ℝ) :
    (euclideanOperator matrix).adjoint = euclideanOperator matrix.transpose := by
  unfold euclideanOperator
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]

noncomputable def forecastOperator (reports : T → Matrix S I ℝ) (weights : T → ℝ)
    (residual : Matrix S R ℝ) : EuclideanSpace ℝ R →L[ℝ] EuclideanSpace ℝ (T × I) :=
  euclideanOperator (trajectoryMatrix reports weights * residual)

omit [DecidableEq S] in
/-- The actual target Gram operator is the residual observability Gramian. -/
theorem forecastOperator_gram (reports : T → Matrix S I ℝ) (weights : T → ℝ)
    (hweights : ∀ time, 0 ≤ weights time) (residual : Matrix S R ℝ) :
    FiniteTargetSpectrum.gram (forecastOperator reports weights residual) =
      euclideanOperator (residual.transpose * gramian reports weights * residual) := by
  rw [FiniteTargetSpectrum.gram, forecastOperator, euclideanOperator_adjoint,
    euclideanOperator_comp, residual_trajectory_gramian reports weights hweights residual]

omit [DecidableEq S] [DecidableEq I] [DecidableEq T] in
/-- This is the weighted trajectory loss, with its full matrix residual map. -/
theorem forecastOperator_norm (reports : T → Matrix S I ℝ) (weights : T → ℝ)
    (hweights : ∀ time, 0 ≤ weights time) (residual : Matrix S R ℝ)
    (vector : EuclideanSpace ℝ R) :
    ‖forecastOperator reports weights residual vector‖ ^ 2 =
      forecastLoss reports weights (residual *ᵥ WithLp.ofLp vector) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [forecastOperator, euclideanOperator_apply, Real.norm_eq_abs, sq_abs,
    ← Matrix.mulVec_mulVec, Fintype.sum_prod_type, forecastLoss]
  apply Finset.sum_congr rfl
  intro time _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro report _
  have hcoord (direction : S → ℝ) :
      (trajectoryMatrix reports weights *ᵥ direction) (time, report) =
        Real.sqrt (weights time) * ((reports time).transpose *ᵥ direction) report := by
    simp only [Matrix.mulVec, dotProduct, trajectoryMatrix, Matrix.transpose_apply,
      Finset.mul_sum, mul_assoc]
  change (trajectoryMatrix reports weights *ᵥ
    (residual *ᵥ WithLp.ofLp vector)) (time, report) ^ 2 = _
  rw [hcoord, mul_pow, Real.sq_sqrt (hweights time)]

section Translation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [AddCommGroup F]

/-- A known center is added only to the final prediction; adaptive queries are unchanged. -/
def translatePrediction (center : F) : {q : ℕ} → Procedure E F q → Procedure E F q
  | 0, .done prediction => .done (center + prediction)
  | _ + 1, .ask question continuation =>
      .ask question (fun response ↦ translatePrediction center (continuation response))

theorem translatePrediction_run (center : F) {q : ℕ} (procedure : Procedure E F q) (vector : E) :
    (translatePrediction center procedure).run vector = center + procedure.run vector := by
  induction q with
  | zero => cases procedure; rfl
  | succ q ih => cases procedure with
    | ask question continuation => exact ih (continuation (question vector))

end Translation

/-- The probability-simplex condition is imposed on every point of the whole
residual ball. It is not replaced by a condition only at the center. -/
def FeasibleBall (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ) : Prop :=
  ∀ vector : EuclideanSpace ℝ R, ‖vector‖ ≤ radius →
    (∀ state, 0 ≤ center state + (residual *ᵥ WithLp.ofLp vector) state) ∧
      (∑ state, (center state + (residual *ᵥ WithLp.ofLp vector) state)) = 1

noncomputable def initialLaw (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ)
    (hfeasible : FeasibleBall center residual radius) (vector : EuclideanSpace ℝ R)
    (hvector : ‖vector‖ ≤ radius) : FiniteReportLaw S where
  mass state := center state + (residual *ᵥ WithLp.ofLp vector) state
  mass_nonneg state := (hfeasible vector hvector).1 state
  mass_sum := (hfeasible vector hvector).2

/-- The report trajectory is computed by propagating the actual initial law. -/
noncomputable def futureTrajectory (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (times : T → ℕ) (weights : T → ℝ) (initial : FiniteReportLaw S) :
    EuclideanSpace ℝ (T × I) :=
  WithLp.toLp 2 (fun output ↦ Real.sqrt (weights output.1) *
    (initial.bind (powerLaw kernel (times output.1))).expectation
      (fun state ↦ reports state output.2))

omit [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] in
theorem futureTrajectory_matrix (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (times : T → ℕ) (weights : T → ℝ) (initial : FiniteReportLaw S) :
    futureTrajectory kernel reports times weights initial =
      WithLp.toLp 2 (trajectoryMatrix (fun time ↦ evolvedReports kernel reports (times time))
        weights *ᵥ initial.mass) := by
  ext output
  rcases output with ⟨time, report⟩
  change Real.sqrt (weights time) *
    (initial.bind (powerLaw kernel (times time))).expectation (fun state ↦ reports state report) =
      (trajectoryMatrix (fun moment ↦ evolvedReports kernel reports (times moment)) weights *ᵥ
        initial.mass) (time, report)
  rw [FiniteReportLaw.expectation_bind]
  simp only [FiniteReportLaw.expectation, powerLaw_mass, Matrix.mulVec, dotProduct,
    trajectoryMatrix, evolvedReports, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  ring

noncomputable def centerTrajectory (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (times : T → ℕ) (weights : T → ℝ) (center : S → ℝ) : EuclideanSpace ℝ (T × I) :=
  WithLp.toLp 2 (trajectoryMatrix (fun time ↦ evolvedReports kernel reports (times time))
    weights *ᵥ center)

omit [DecidableEq I] [DecidableEq T] in
theorem futureTrajectory_affine (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (times : T → ℕ) (weights : T → ℝ) (center : S → ℝ) (residual : Matrix S R ℝ)
    (radius : ℝ) (hfeasible : FeasibleBall center residual radius)
    (vector : EuclideanSpace ℝ R) (hvector : ‖vector‖ ≤ radius) :
    futureTrajectory kernel reports times weights
        (initialLaw center residual radius hfeasible vector hvector) =
      centerTrajectory kernel reports times weights center +
        forecastOperator (fun time ↦ evolvedReports kernel reports (times time)) weights residual
          vector := by
  rw [futureTrajectory_matrix]
  change WithLp.toLp 2 (_ *ᵥ (center + residual *ᵥ WithLp.ofLp vector)) = _
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  rfl

/-- Sharp design over actual adaptive scalar-query procedures and actual future
law expectations. The radius ball's probability feasibility is essential. The
reported eigenvalues belong to the identified residual observability Gramian. -/
theorem adaptive_forecast_minimax (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (times : T → ℕ) (weights : T → ℝ) (hweights : ∀ time, 0 ≤ weights time)
    (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ) (hradius : 0 ≤ radius)
    (hfeasible : FeasibleBall center residual radius) (queries : ℕ) :
    let target := forecastOperator
      (fun time ↦ evolvedReports kernel reports (times time)) weights residual
    IsLeast {risk : ℝ | ∃ procedure : Procedure (EuclideanSpace ℝ R)
        (EuclideanSpace ℝ (T × I)) queries,
      ∀ vector : EuclideanSpace ℝ R, ∀ hvector : ‖vector‖ ≤ radius,
        ‖futureTrajectory kernel reports times weights
            (initialLaw center residual radius hfeasible vector hvector) -
          procedure.run vector‖ ^ 2 ≤ risk}
      (radius ^ 2 * residualEigenvalue target queries) ∧
    FiniteTargetSpectrum.gram target = euclideanOperator
      (residual.transpose *
        gramian (fun time ↦ evolvedReports kernel reports (times time)) weights * residual) := by
  dsimp only
  let target := forecastOperator
    (fun time ↦ evolvedReports kernel reports (times time)) weights residual
  let base := centerTrajectory kernel reports times weights center
  have hspectral := adaptive_minimax_all_budgets target queries radius hradius
  refine ⟨?_, forecastOperator_gram _ _ hweights residual⟩
  constructor
  · obtain ⟨procedure, hprocedure⟩ := hspectral.1
    refine ⟨translatePrediction base procedure, ?_⟩
    intro vector hvector
    rw [futureTrajectory_affine, translatePrediction_run]
    change ‖base + target vector - (base + procedure.run vector)‖ ^ 2 ≤ _
    simpa only [add_sub_add_left_eq_sub] using hprocedure vector hvector
  · rintro risk ⟨procedure, hprocedure⟩
    apply hspectral.2
    refine ⟨translatePrediction (-base) procedure, ?_⟩
    intro vector hvector
    have h := hprocedure vector hvector
    rw [futureTrajectory_affine] at h
    rw [translatePrediction_run]
    change ‖target vector - (-base + procedure.run vector)‖ ^ 2 ≤ _
    convert h using 1
    congr 2
    dsimp only [target, base]
    abel

end Descent.Portability.EvolutionaryForecastMinimax
