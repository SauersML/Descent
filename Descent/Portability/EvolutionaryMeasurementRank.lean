/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DiscountedForecastMinimax
import Descent.Portability.MeasurementRankLaw

assert_below Descent.Decision Descent.Program

/-!
The exact number of noiseless measurements needed for zero evolutionary forecast
error. The count is the rank of the actual forecast operator on the unidentified
initial directions, and remains sharp over adaptive prediction procedures.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix

namespace Descent.Portability.EvolutionaryMeasurementRank

open EvolutionaryObservability EvolutionaryForecastMinimax AdaptiveLinearMeasurements
open SpectralMeasurementMinimax MeasurementRankLaw

private theorem zero_mem_iff_rank
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (target : E →L[ℝ] F) (queries : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (risks : Set ℝ) (hminimax : IsLeast risks (radius ^ 2 * residualEigenvalue target queries)) :
    0 ∈ risks ↔ targetRank target ≤ queries := by
  constructor
  · intro hzero
    apply (residualEigenvalue_zero_iff target queries).mp
    have hnonneg : 0 ≤ residualEigenvalue target queries := by
      unfold residualEigenvalue
      split_ifs <;> simp [FiniteTargetSpectrum.squaredSingularValues_nonneg]
    have hbound := hminimax.2 hzero
    have hr := sq_pos_of_pos hradius
    nlinarith
  · intro hrank
    have hzero := (residualEigenvalue_zero_iff target queries).mpr hrank
    simpa only [hzero, mul_zero] using hminimax.1

variable {S I T R : Type*} [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] [Fintype R] [DecidableEq R]

/-- An exact budget means a procedure predicts all actual weighted future
expectations correctly throughout the full feasible residual ball. -/
def FiniteExactBudget (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (times : T → ℕ) (weights : T → ℝ) (center : S → ℝ) (residual : Matrix S R ℝ)
    (radius : ℝ) (hfeasible : FeasibleBall center residual radius) (queries : ℕ) : Prop :=
  ∃ procedure : Procedure (EuclideanSpace ℝ R) (EuclideanSpace ℝ (T × I)) queries,
    ∀ vector : EuclideanSpace ℝ R, ∀ hvector : ‖vector‖ ≤ radius,
      ‖futureTrajectory kernel reports times weights
          (initialLaw center residual radius hfeasible vector hvector) - procedure.run vector‖ ^ 2 ≤ 0

theorem finite_exact_budget_iff (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (times : T → ℕ) (weights : T → ℝ) (hweights : ∀ time, 0 ≤ weights time)
    (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ) (hradius : 0 < radius)
    (hfeasible : FeasibleBall center residual radius) (queries : ℕ) :
    FiniteExactBudget kernel reports times weights center residual radius hfeasible queries ↔
      targetRank (forecastOperator
        (fun time ↦ evolvedReports kernel reports (times time)) weights residual) ≤ queries :=
  zero_mem_iff_rank _ queries radius hradius _
    (adaptive_forecast_minimax kernel reports times weights hweights center residual radius
      hradius.le hfeasible queries).1

/-- The finite-horizon minimal exact budget is the actual residual forecast rank. -/
theorem finite_minimal_exact_count (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (times : T → ℕ) (weights : T → ℝ) (hweights : ∀ time, 0 ≤ weights time)
    (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ) (hradius : 0 < radius)
    (hfeasible : FeasibleBall center residual radius) :
    IsLeast {queries : ℕ |
      FiniteExactBudget kernel reports times weights center residual radius hfeasible queries}
      (targetRank (forecastOperator
        (fun time ↦ evolvedReports kernel reports (times time)) weights residual)) := by
  refine ⟨(finite_exact_budget_iff kernel reports times weights hweights center residual radius
    hradius hfeasible _).mpr le_rfl, ?_⟩
  intro queries hqueries
  exact (finite_exact_budget_iff kernel reports times weights hweights center residual radius
    hradius hfeasible queries).mp hqueries

/-- The same rank is computable from the residual finite observability Gramian. -/
theorem finite_rank_from_gramian (reports : T → Matrix S I ℝ) (weights : T → ℝ)
    (hweights : ∀ time, 0 ≤ weights time) (residual : Matrix S R ℝ) :
    targetRank (forecastOperator reports weights residual) =
      Module.finrank ℝ (LinearMap.range
        (euclideanOperator (residual.transpose * gramian reports weights * residual)).toLinearMap) := by
  rw [← gram_rank, forecastOperator_gram reports weights hweights residual]

open DiscountedForecastMinimax

def DiscountedExactBudget (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ)
    (hfeasible : FeasibleBall center residual radius) (queries : ℕ) : Prop :=
  ∃ procedure : Procedure (EuclideanSpace ℝ R) (Trajectory I) queries,
    ∀ vector : EuclideanSpace ℝ R, ∀ hvector : ‖vector‖ ≤ radius,
      ‖lawTrajectory kernel reports discount hnonneg hlt
          (initialLaw center residual radius hfeasible vector hvector) - procedure.run vector‖ ^ 2 ≤ 0

theorem discounted_exact_budget_iff (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ) (hradius : 0 < radius)
    (hfeasible : FeasibleBall center residual radius) (queries : ℕ) :
    DiscountedExactBudget kernel reports discount hnonneg hlt center residual radius hfeasible
        queries ↔ targetRank
      (DiscountedForecastMinimax.forecastOperator kernel reports discount hnonneg hlt residual) ≤
        queries :=
  zero_mem_iff_rank _ queries radius hradius _
    (adaptive_discounted_minimax kernel reports discount hnonneg hlt center residual radius
      hradius.le hfeasible queries).1

/-- The infinite trajectory requires exactly its finite residual image dimension. -/
theorem discounted_minimal_exact_count (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ) (hradius : 0 < radius)
    (hfeasible : FeasibleBall center residual radius) :
    IsLeast {queries : ℕ | DiscountedExactBudget kernel reports discount hnonneg hlt
      center residual radius hfeasible queries}
      (targetRank (DiscountedForecastMinimax.forecastOperator kernel reports discount
        hnonneg hlt residual)) := by
  refine ⟨(discounted_exact_budget_iff kernel reports discount hnonneg hlt center residual radius
    hradius hfeasible _).mpr le_rfl, ?_⟩
  intro queries hqueries
  exact (discounted_exact_budget_iff kernel reports discount hnonneg hlt center residual radius
    hradius hfeasible queries).mp hqueries

theorem discounted_rank_from_gramian (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) (residual : Matrix S R ℝ) :
    targetRank (DiscountedForecastMinimax.forecastOperator kernel reports discount
      hnonneg hlt residual) =
      Module.finrank ℝ (LinearMap.range (euclideanOperator (residual.transpose *
        DiscountedObservability.discountedGramian kernel reports discount * residual)).toLinearMap) := by
  rw [← gram_rank,
    DiscountedForecastMinimax.forecastOperator_gram kernel reports discount hnonneg hlt residual]

end Descent.Portability.EvolutionaryMeasurementRank
