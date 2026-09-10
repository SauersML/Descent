/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

/-!
# Equal joint moments do not determine AUC

Two explicit six-person binary cohorts have identical score/outcome means, variances,
covariance, prevalence, nonzero squared correlation, and Brier score, but AUCs `1/3` and
`2/3`. Predictions in both cohorts use the same increasing affine function of raw score.
This is an exact finite-distribution obstruction, not a demographic realizability theorem.
In particular, a Gaussian moment chart cannot be an unrestricted AUC identity.

The finite expectation uses `FiniteReportLaw`; pair comparisons use the very same
`empiricalAUCComparison` imported by the production cohort evaluator in `DiscriminationLaw`.
Every score vector here has exactly three cases and three controls, so AUC is always defined.
-/

namespace MomentAUCNonidentifiability

/-- The complete first- and second-order joint moment information in centered form. -/
structure JointMoments where
  scoreMean : ℝ
  outcomeMean : ℝ
  scoreVariance : ℝ
  outcomeVariance : ℝ
  predictiveCovariance : ℝ

/-- A uniformly sampled individual from a six-person cohort. -/
noncomputable def cohortLaw : FiniteReportLaw (Fin 6) where
  mass := fun _ ↦ 1 / 6
  mass_nonneg := fun _ ↦ by norm_num
  mass_sum := by norm_num [Fin.sum_univ_succ]

/-- Arithmetic expectation under the uniform finite-cohort law. -/
noncomputable def mean (value : Fin 6 → ℝ) : ℝ := cohortLaw.expectation value

/-- First three individuals are cases; the remaining three are controls. -/
def outcome : Fin 6 → Bool := ![true, true, true, false, false, false]

def outcomeValue (i : Fin 6) : ℝ := if outcome i then 1 else 0

/-- First and second joint moments, retaining score location and outcome prevalence. -/
noncomputable def jointMoments (score : Fin 6 → ℝ) : JointMoments where
  scoreMean := mean score
  outcomeMean := mean outcomeValue
  scoreVariance := cohortLaw.variance score
  outcomeVariance := cohortLaw.variance outcomeValue
  predictiveCovariance := cohortLaw.covariance score outcomeValue

/-- In the first cohort one case outranks all controls. -/
noncomputable def firstScore : Fin 6 → ℝ := ![-1 / 2, -1 / 2, 5 / 2, 0, 0, 0]

/-- In the second cohort two cases outrank all controls. -/
noncomputable def secondScore : Fin 6 → ℝ := ![-3 / 2, 3 / 2, 3 / 2, 0, 0, 0]

/-- The same prediction rule is deployed in both cohorts. -/
noncomputable def prediction (score : ℝ) : ℝ := 1 / 2 + score / 6

theorem first_prediction_mem_unitInterval (i : Fin 6) :
    0 < prediction (firstScore i) ∧ prediction (firstScore i) < 1 := by
  fin_cases i <;> norm_num [prediction, firstScore]

theorem second_prediction_mem_unitInterval (i : Fin 6) :
    0 < prediction (secondScore i) ∧ prediction (secondScore i) < 1 := by
  fin_cases i <;> norm_num [prediction, secondScore]

/-- The exact common joint moment tuple has a strictly positive predictive covariance. -/
noncomputable def commonMoments : JointMoments := ⟨1 / 4, 1 / 2, 17 / 16, 1 / 4, 1 / 8⟩

theorem first_jointMoments : jointMoments firstScore = commonMoments := by
  norm_num [jointMoments, mean, cohortLaw, FiniteReportLaw.expectation,
    FiniteReportLaw.variance, FiniteReportLaw.covariance,
    firstScore, outcome, outcomeValue, commonMoments, Fin.sum_univ_succ]

theorem second_jointMoments : jointMoments secondScore = commonMoments := by
  norm_num [jointMoments, mean, cohortLaw, FiniteReportLaw.expectation,
    FiniteReportLaw.variance, FiniteReportLaw.covariance,
    secondScore, outcome, outcomeValue, commonMoments, Fin.sum_univ_succ]

theorem same_jointMoments : jointMoments firstScore = jointMoments secondScore :=
  first_jointMoments.trans second_jointMoments.symm

/-- Exact Mann--Whitney pair average on the fixed three-case/three-control cohort.
The common prediction rule is applied before every production comparison. -/
noncomputable def auc (score : Fin 6 → ℝ) : ℝ :=
  (∑ caseIndividual, ∑ controlIndividual,
    if outcome caseIndividual && !outcome controlIndividual then
      empiricalAUCComparison (prediction (score caseIndividual))
        (prediction (score controlIndividual))
    else 0) / 9

theorem first_auc : auc firstScore = 1 / 3 := by
  norm_num [auc, empiricalAUCComparison, firstScore, outcome, prediction, Fin.sum_univ_succ]

theorem second_auc : auc secondScore = 2 / 3 := by
  norm_num [auc, empiricalAUCComparison, secondScore, outcome, prediction, Fin.sum_univ_succ]

/-- The general exact finite-law evaluator agrees with the specialized pair average for
every score vector on this fixed, nondegenerate case/control layout. -/
theorem binaryAUC_eq_cohortAUC (score : Fin 6 → ℝ) :
    cohortLaw.binaryAUC (fun i ↦ prediction (score i)) outcome = some (auc score) := by
  norm_num [FiniteReportLaw.binaryAUC, FiniteReportLaw.binaryCaseMass,
    FiniteReportLaw.binaryAUCNumerator, cohortLaw, FiniteReportLaw.expectation,
    auc, outcome, Fin.sum_univ_succ]
  ring

theorem first_exact_auc :
    cohortLaw.binaryAUC (fun i ↦ prediction (firstScore i)) outcome = some (1 / 3) := by
  rw [binaryAUC_eq_cohortAUC, first_auc]

theorem second_exact_auc :
    cohortLaw.binaryAUC (fun i ↦ prediction (secondScore i)) outcome = some (2 / 3) := by
  rw [binaryAUC_eq_cohortAUC, second_auc]

/-- Predicted risk has positive variance in both witnesses, and outcomes are nonconstant. -/
theorem prediction_variances_pos :
    0 < (jointMoments (fun i ↦ prediction (firstScore i))).scoreVariance ∧
    0 < (jointMoments (fun i ↦ prediction (secondScore i))).scoreVariance ∧
    0 < (jointMoments firstScore).outcomeVariance := by
  norm_num [jointMoments, mean, cohortLaw, FiniteReportLaw.expectation,
    FiniteReportLaw.variance, FiniteReportLaw.covariance,
    firstScore, secondScore, outcome, outcomeValue, prediction, Fin.sum_univ_succ]

theorem first_r2 :
    cohortLaw.squaredCorrelation (fun i ↦ prediction (firstScore i)) outcomeValue =
      some (1 / 17) := by
  norm_num [FiniteReportLaw.squaredCorrelation, FiniteReportLaw.variance,
    FiniteReportLaw.covariance, cohortLaw, FiniteReportLaw.expectation,
    firstScore, outcome, outcomeValue, prediction, Fin.sum_univ_succ]

theorem second_r2 :
    cohortLaw.squaredCorrelation (fun i ↦ prediction (secondScore i)) outcomeValue =
      some (1 / 17) := by
  norm_num [FiniteReportLaw.squaredCorrelation, FiniteReportLaw.variance,
    FiniteReportLaw.covariance, cohortLaw, FiniteReportLaw.expectation,
    secondScore, outcome, outcomeValue, prediction, Fin.sum_univ_succ]

/-- Brier loss under the same uniformly weighted cohort and common prediction rule. -/
noncomputable def brier (score : Fin 6 → ℝ) : ℝ :=
  cohortLaw.meanSquaredError (fun i ↦ prediction (score i)) outcomeValue

theorem first_brier : brier firstScore = 23 / 96 := by
  norm_num [brier, FiniteReportLaw.meanSquaredError, cohortLaw, FiniteReportLaw.expectation,
    firstScore, outcome, outcomeValue, prediction, Fin.sum_univ_succ]

theorem second_brier : brier secondScore = 23 / 96 := by
  norm_num [brier, FiniteReportLaw.meanSquaredError, cohortLaw, FiniteReportLaw.expectation,
    secondScore, outcome, outcomeValue, prediction, Fin.sum_univ_succ]

/-- Even exact first/second joint moments cannot produce every defined finite-cohort AUC. -/
theorem no_moments_only_auc_readout :
    ¬ ∃ readout : JointMoments → ℝ,
      ∀ score : Fin 6 → ℝ, auc score = readout (jointMoments score) := by
  rintro ⟨readout, hexact⟩
  have hfirst := hexact firstScore
  have hsecond := hexact secondScore
  rw [first_auc, first_jointMoments] at hfirst
  rw [second_auc, second_jointMoments] at hsecond
  linarith

/-- A bounded adversarial error persists even for approximate moment-only AUC reports. -/
theorem moments_only_auc_error_lower_bound (readout : JointMoments → ℝ) :
    1 / 6 ≤ |auc firstScore - readout (jointMoments firstScore)| ∨
      1 / 6 ≤ |auc secondScore - readout (jointMoments secondScore)| := by
  rw [first_auc, second_auc, first_jointMoments, second_jointMoments]
  by_contra h
  obtain ⟨hfirst, hsecond⟩ := not_or.mp h
  have hfirst := (abs_lt.mp (lt_of_not_ge hfirst)).1
  have hsecond := (abs_lt.mp (lt_of_not_ge hsecond)).2
  linarith

end MomentAUCNonidentifiability

end Descent.Portability
