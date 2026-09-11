/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMeasureQueries
import Descent.Portability.FiniteDiscreteMeasure

assert_below Descent.Decision Descent.Program

/-!
# Source/target portability remains joint: one explicit law

NOTE 2 section 6.2 is titled "Source/target portability remains joint": the queries of the
portability ratio (27) are queries of the joint law of the source and target metrics, not of their
two marginal laws. `PortabilityMeasureQueries.portabilityQueries_eq_sourceTargetLaw` shows that
each query is a functional of the joint law. This module shows that the marginal laws do not
determine the comparison queries, on one explicit population with two reports of mass one half.

`halfLaw` is the uniform law on two reports. Both couplings use the source numerators
`exampleSourceNum = (1/2, 1)` and unit denominators; the target numerators are
`exampleTargetNumFirst = (1, 1/2)` in the first coupling and its reversal
`exampleTargetNumSecond` in the second. `targetMetric_same_marginal` shows that the target metric
has the same law in both couplings, and the source metric is literally the same function. Yet
the probability that the target metric exceeds the source metric is one half in the first
coupling and zero in the second (`targetExceedsMass_first`, `targetExceedsMass_second`), and so
is the conditional probability that (27) exceeds one (`ratioExceedsOneProbability_first`,
`ratioExceedsOneProbability_second`). `sourceTargetLaw_first_ne_second` concludes that the two
joint laws of `(M_s, M_t)` differ, while their marginals agree.

Scope: the example separates the third and fourth queries; the first query, the mean of the
ratio, also differs on it (`2` and `1/2` against `1` and `1`) but is not computed here.

## Empirical status

None. The bodies here are arithmetic on one stipulated two-report law: every statement is an
evaluation of finite sums of the supplied accumulators, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityRemainsJoint

open MeasureTheory PortabilityMeasureQueries

noncomputable section

/-- The uniform law on two reports. -/
def halfLaw : FiniteReportLaw (Fin 2) where
  mass := fun _ ↦ 1 / 2
  mass_nonneg := fun _ ↦ by norm_num
  mass_sum := by norm_num [Fin.sum_univ_two]

/-- The source numerators of the example: one half on the first report and one on the second. -/
def exampleSourceNum : Fin 2 → ℝ := ![1 / 2, 1]

/-- The target numerators of the first coupling: one on the first report and one half on the
second. -/
def exampleTargetNumFirst : Fin 2 → ℝ := ![1, 1 / 2]

/-- The target numerators of the second coupling: the first coupling with the two reports
exchanged. -/
def exampleTargetNumSecond : Fin 2 → ℝ := fun report ↦ exampleTargetNumFirst (Fin.rev report)

/-- Reversal exchanges the two reports. -/
theorem rev_zero_one : Fin.rev (0 : Fin 2) = 1 ∧ Fin.rev (1 : Fin 2) = 0 := ⟨rfl, rfl⟩

/-- The source numerators lie in the admissible range below the unit denominators. -/
theorem exampleSourceNum_nonneg : ∀ report, 0 ≤ exampleSourceNum report := by
  intro report
  fin_cases report <;> norm_num [exampleSourceNum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

/-- The source numerators are at most the unit denominators. -/
theorem exampleSourceNum_le_one : ∀ report, exampleSourceNum report ≤ (1 : Fin 2 → ℝ) report := by
  intro report
  fin_cases report <;> norm_num [exampleSourceNum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

/-- The target numerators of the first coupling are nonnegative. -/
theorem exampleTargetNumFirst_nonneg : ∀ report, 0 ≤ exampleTargetNumFirst report := by
  intro report
  fin_cases report <;> norm_num [exampleTargetNumFirst, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

/-- The target numerators of the first coupling are at most the unit denominators. -/
theorem exampleTargetNumFirst_le_one :
    ∀ report, exampleTargetNumFirst report ≤ (1 : Fin 2 → ℝ) report := by
  intro report
  fin_cases report <;> norm_num [exampleTargetNumFirst, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

/-- The target numerators of the second coupling are nonnegative. -/
theorem exampleTargetNumSecond_nonneg : ∀ report, 0 ≤ exampleTargetNumSecond report :=
  fun report ↦ exampleTargetNumFirst_nonneg (Fin.rev report)

/-- The target numerators of the second coupling are at most the unit denominators. -/
theorem exampleTargetNumSecond_le_one :
    ∀ report, exampleTargetNumSecond report ≤ (1 : Fin 2 → ℝ) report :=
  fun report ↦ exampleTargetNumFirst_le_one (Fin.rev report)

/-- **The marginal law of the target metric is the same in both couplings.** Every observable of
the target metric has the same expectation under the uniform law, because the second coupling only
exchanges the two reports. -/
theorem targetMetric_same_marginal (observable : ℝ → ℝ) :
    ∫ report, observable (exampleTargetNumFirst report / (1 : Fin 2 → ℝ) report)
        ∂FiniteDiscreteMeasure.measure halfLaw =
      ∫ report, observable (exampleTargetNumSecond report / (1 : Fin 2 → ℝ) report)
        ∂FiniteDiscreteMeasure.measure halfLaw := by
  rw [FiniteDiscreteMeasure.integral_observable, FiniteDiscreteMeasure.integral_observable]
  simp only [FiniteReportLaw.expectation, Fin.sum_univ_two, halfLaw, exampleTargetNumSecond,
    rev_zero_one.1, rev_zero_one.2, Pi.one_apply, div_one]
  ring

/-- Every report of the example is in the definedness event of (27). -/
theorem portabilityDomain_example :
    portabilityDomain exampleSourceNum (1 : Fin 2 → ℝ) (1 : Fin 2 → ℝ) = Set.univ := by
  ext report
  fin_cases report <;> norm_num [portabilityDomain, exampleSourceNum, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

/-- **The first coupling.** The probability that the target metric exceeds the source metric is
one half: only the first report has `1/2 < 1`. -/
theorem targetExceedsMass_first :
    targetExceedsMass (FiniteDiscreteMeasure.measure halfLaw) exampleSourceNum 1
      exampleTargetNumFirst 1 = 1 / 2 := by
  classical
  rw [targetExceedsMass, FiniteDiscreteMeasure.real_event]
  norm_num [FiniteReportLaw.expectation, Fin.sum_univ_two, halfLaw, Set.indicator_apply,
    portabilityDomain, exampleSourceNum, exampleTargetNumFirst, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

/-- **The second coupling.** The probability that the target metric exceeds the source metric is
zero: the two metrics are equal on both reports. -/
theorem targetExceedsMass_second :
    targetExceedsMass (FiniteDiscreteMeasure.measure halfLaw) exampleSourceNum 1
      exampleTargetNumSecond 1 = 0 := by
  classical
  rw [targetExceedsMass, FiniteDiscreteMeasure.real_event]
  norm_num [FiniteReportLaw.expectation, Fin.sum_univ_two, halfLaw, Set.indicator_apply,
    portabilityDomain, exampleSourceNum, exampleTargetNumSecond, exampleTargetNumFirst,
    rev_zero_one.1, rev_zero_one.2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **The first coupling, fourth query.** The conditional probability that (27) exceeds one is
one half, because every report is defined. -/
theorem ratioExceedsOneProbability_first :
    ratioExceedsOneProbability (FiniteDiscreteMeasure.measure halfLaw) exampleSourceNum 1
      exampleTargetNumFirst 1 = 1 / 2 := by
  rw [ratioExceedsOneProbability_eq _ _ _ _ _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _), portabilityDomain_example, measureReal_univ_eq_one, inv_one,
    one_mul, targetExceedsMass_first]

/-- **The second coupling, fourth query.** The conditional probability that (27) exceeds one is
zero. -/
theorem ratioExceedsOneProbability_second :
    ratioExceedsOneProbability (FiniteDiscreteMeasure.measure halfLaw) exampleSourceNum 1
      exampleTargetNumSecond 1 = 0 := by
  rw [ratioExceedsOneProbability_eq _ _ _ _ _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _), portabilityDomain_example, measureReal_univ_eq_one, inv_one,
    one_mul, targetExceedsMass_second]

/-- **NOTE 2 §6.2, portability remains joint.** The two couplings give the metric vector
`(M_s, M_t)` different joint laws on the event where both denominators are positive, although the
source metric is the same function and the target metric has the same marginal law. -/
theorem sourceTargetLaw_first_ne_second :
    sourceTargetLaw (FiniteDiscreteMeasure.measure halfLaw) exampleSourceNum 1
        exampleTargetNumFirst 1 exampleSourceNum_nonneg exampleTargetNumFirst_nonneg
        exampleSourceNum_le_one exampleTargetNumFirst_le_one ≠
      sourceTargetLaw (FiniteDiscreteMeasure.measure halfLaw) exampleSourceNum 1
        exampleTargetNumSecond 1 exampleSourceNum_nonneg exampleTargetNumSecond_nonneg
        exampleSourceNum_le_one exampleTargetNumSecond_le_one := by
  intro hequal
  have hfirst := (portabilityQueries_eq_sourceTargetLaw (FiniteDiscreteMeasure.measure halfLaw)
    exampleSourceNum 1 exampleTargetNumFirst 1 (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) exampleSourceNum_nonneg
    exampleTargetNumFirst_nonneg exampleSourceNum_le_one exampleTargetNumFirst_le_one).2.2.1
  have hsecond := (portabilityQueries_eq_sourceTargetLaw (FiniteDiscreteMeasure.measure halfLaw)
    exampleSourceNum 1 exampleTargetNumSecond 1 (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) exampleSourceNum_nonneg
    exampleTargetNumSecond_nonneg exampleSourceNum_le_one exampleTargetNumSecond_le_one).2.2.1
  rw [targetExceedsMass_first, hequal] at hfirst
  rw [targetExceedsMass_second] at hsecond
  rw [← hsecond] at hfirst
  norm_num at hfirst

end

end Descent.Portability.PortabilityRemainsJoint
