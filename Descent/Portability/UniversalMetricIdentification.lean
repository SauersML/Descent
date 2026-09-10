/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Identifiability

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

/-!
# Identifying every metric requires identifying the report law

For an arbitrary finite report space, equality of all bounded metric expectations is
equivalent to equality of the complete report law. Singleton indicators already suffice.
The exact worst discrepancy over metrics taking values in `[0,1]` is total variation,
and an explicit indicator attains it. Thus the result supplies both an identification
criterion and a sharp approximation certificate, without selecting a metric in advance.

The report can include training randomness, the target cohort, source and target metrics,
and a distinguished undefined outcome. A metric of such a report is a fixed function of
that report. This theorem does not construct its law from demographic history, assert that
demography identifies phenotype or training mechanisms, or cover an infinite report space.
In particular, unconditional expectations of bounded report functions are covered;
conditional-on-defined averages require an additional normalization by definedness mass.
-/

variable {Report : Type*} [Fintype Report]

/-- A probability law on the complete finite report of a scoring pipeline. -/
structure FiniteReportLaw (Report : Type*) [Fintype Report] where
  mass : Report → ℝ
  mass_nonneg : ∀ report, 0 ≤ mass report
  mass_sum : ∑ report, mass report = 1

namespace FiniteReportLaw

@[ext] theorem ext {p q : FiniteReportLaw Report}
    (h : ∀ report, p.mass report = q.mass report) : p = q := by
  cases p with
  | mk pmass pnonneg psum =>
    cases q with
    | mk qmass qnonneg qsum =>
      have heq : pmass = qmass := funext h
      subst qmass
      rfl

/-- The expectation of any report metric, with no distributional approximation. -/
noncomputable def expectation (p : FiniteReportLaw Report) (metric : Report → ℝ) : ℝ :=
  ∑ report, p.mass report * metric report

/-- The positive variation of the difference of two probability laws. -/
noncomputable def totalVariation (p q : FiniteReportLaw Report) : ℝ :=
  ∑ report, max (p.mass report - q.mass report) 0

/-- A bounded metric is a report function taking values in the unit interval. -/
def BoundedMetric (metric : Report → ℝ) : Prop :=
  ∀ report, 0 ≤ metric report ∧ metric report ≤ 1

theorem expectation_sub (p q : FiniteReportLaw Report) (metric : Report → ℝ) :
    p.expectation metric - q.expectation metric =
      ∑ report, (p.mass report - q.mass report) * metric report := by
  simp only [expectation, ← Finset.sum_sub_distrib, sub_mul]

theorem expectation_complement (p : FiniteReportLaw Report) (metric : Report → ℝ) :
    p.expectation (fun report ↦ 1 - metric report) = 1 - p.expectation metric := by
  simp only [expectation, mul_sub, mul_one, Finset.sum_sub_distrib, p.mass_sum]

theorem totalVariation_nonneg (p q : FiniteReportLaw Report) :
    0 ≤ p.totalVariation q :=
  Finset.sum_nonneg (fun _ _ ↦ le_max_right _ _)

theorem totalVariation_le_one (p q : FiniteReportLaw Report) :
    p.totalVariation q ≤ 1 := by
  rw [← p.mass_sum]
  apply Finset.sum_le_sum
  intro report _
  exact max_le (sub_le_self _ (q.mass_nonneg report)) (p.mass_nonneg report)

/-- The positive-variation definition agrees exactly with half the `L¹` distance. -/
theorem totalVariation_eq_half_sum_abs (p q : FiniteReportLaw Report) :
    p.totalVariation q = (∑ report, |p.mass report - q.mass report|) / 2 := by
  have hpoint : ∀ report,
      2 * max (p.mass report - q.mass report) 0 =
        |p.mass report - q.mass report| + (p.mass report - q.mass report) := by
    intro report
    by_cases h : 0 ≤ p.mass report - q.mass report
    · rw [max_eq_left h, abs_of_nonneg h]
      ring
    · have hn := le_of_lt (lt_of_not_ge h)
      rw [max_eq_right hn, abs_of_nonpos hn]
      ring
  have hsum : (∑ report, 2 * max (p.mass report - q.mass report) 0) =
      ∑ report, (|p.mass report - q.mass report| + (p.mass report - q.mass report)) :=
    Finset.sum_congr rfl (fun report _ ↦ hpoint report)
  have hzero : (∑ report, (p.mass report - q.mass report)) = 0 := by
    rw [Finset.sum_sub_distrib, p.mass_sum, q.mass_sum, sub_self]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hzero, add_zero] at hsum
  unfold totalVariation
  linarith

/-- Every signed metric discrepancy is bounded by total variation. -/
theorem expectation_sub_le_totalVariation (p q : FiniteReportLaw Report)
    (metric : Report → ℝ) (hmetric : BoundedMetric metric) :
    p.expectation metric - q.expectation metric ≤ p.totalVariation q := by
  rw [expectation_sub]
  apply Finset.sum_le_sum
  intro report _
  obtain ⟨hlo, hhi⟩ := hmetric report
  by_cases hd : 0 ≤ p.mass report - q.mass report
  · rw [max_eq_left hd]
    nlinarith
  · have hn : p.mass report - q.mass report ≤ 0 := le_of_lt (lt_of_not_ge hd)
    rw [max_eq_right hn]
    nlinarith

/-- One certificate controls every bounded metric, including arbitrary nonlinear summaries
of a finite source/target report. -/
theorem abs_expectation_sub_le_totalVariation (p q : FiniteReportLaw Report)
    (metric : Report → ℝ) (hmetric : BoundedMetric metric) :
    |p.expectation metric - q.expectation metric| ≤ p.totalVariation q := by
  have hupper := p.expectation_sub_le_totalVariation q metric hmetric
  have hcomplement : BoundedMetric (fun report ↦ 1 - metric report) := by
    intro report
    obtain ⟨hlo, hhi⟩ := hmetric report
    constructor <;> linarith
  have hlower := p.expectation_sub_le_totalVariation q _ hcomplement
  rw [p.expectation_complement, q.expectation_complement] at hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- The event that attains the maximum discrepancy. Its dependence on the two laws is
necessary: a single prespecified metric can be blind to their difference. -/
noncomputable def separatingMetric (p q : FiniteReportLaw Report) : Report → ℝ :=
  fun report ↦ if q.mass report ≤ p.mass report then 1 else 0

theorem separatingMetric_bounded (p q : FiniteReportLaw Report) :
    BoundedMetric (p.separatingMetric q) := by
  intro report
  unfold separatingMetric
  split_ifs <;> norm_num

theorem separatingMetric_attains (p q : FiniteReportLaw Report) :
    p.expectation (p.separatingMetric q) - q.expectation (p.separatingMetric q) =
      p.totalVariation q := by
  rw [expectation_sub]
  unfold totalVariation separatingMetric
  apply Finset.sum_congr rfl
  intro report _
  split_ifs with h
  · rw [mul_one, max_eq_left (sub_nonneg.mpr h)]
  · rw [mul_zero, max_eq_right (sub_nonpos.mpr (le_of_lt (lt_of_not_ge h)))]

/-- Total variation is the exact optimal uniform error over all unit-interval metrics,
with an attained optimizer rather than only a supremum characterization. -/
theorem all_bounded_metric_errors_le_iff (p q : FiniteReportLaw Report) (error : ℝ) :
    (∀ metric, BoundedMetric metric →
      |p.expectation metric - q.expectation metric| ≤ error) ↔
        p.totalVariation q ≤ error := by
  constructor
  · intro h
    have hw := h (p.separatingMetric q) (p.separatingMetric_bounded q)
    rw [p.separatingMetric_attains q, abs_of_nonneg (p.totalVariation_nonneg q)] at hw
    exact hw
  · intro h metric hmetric
    exact (p.abs_expectation_sub_le_totalVariation q metric hmetric).trans h

/-- Every singleton event is a bounded metric. -/
noncomputable def singletonMetric (selected : Report) : Report → ℝ := by
  classical
  exact fun report ↦ if report = selected then 1 else 0

omit [Fintype Report] in
theorem singletonMetric_bounded (selected : Report) :
    BoundedMetric (singletonMetric selected) := by
  intro report
  unfold singletonMetric
  split_ifs <;> norm_num

theorem expectation_singletonMetric (p : FiniteReportLaw Report) (selected : Report) :
    p.expectation (singletonMetric selected) = p.mass selected := by
  classical
  simp [expectation, singletonMetric]

/-- Singleton indicator expectations alone identify the finite report law. -/
theorem eq_iff_singleton_expectations_eq (p q : FiniteReportLaw Report) :
    p = q ↔ ∀ report,
      p.expectation (singletonMetric report) = q.expectation (singletonMetric report) := by
  constructor
  · rintro rfl report
    rfl
  · intro h
    apply ext
    intro report
    simpa only [expectation_singletonMetric] using h report

/-- No compression preserves all bounded metric expectations unless it preserves the law. -/
theorem eq_iff_all_bounded_expectations_eq (p q : FiniteReportLaw Report) :
    p = q ↔ ∀ metric, BoundedMetric metric → p.expectation metric = q.expectation metric := by
  constructor
  · rintro rfl metric _
    rfl
  · intro h
    apply (eq_iff_singleton_expectations_eq p q).mpr
    intro report
    exact h (singletonMetric report) (singletonMetric_bounded report)

/-- Applied to an observation such as demographic history, the exact all-metric criterion
is identification of the full report distribution. It is a criterion, not an assumption
that demographic history supplies the phenotype or the scoring protocol. -/
theorem identified_iff_all_bounded_metrics_identified
    {Parameter Observation : Type*} (observe : Parameter → Observation)
    (law : Parameter → FiniteReportLaw Report) :
    Core.IdentifiedBy observe law ↔
      ∀ metric, BoundedMetric metric →
        Core.IdentifiedBy observe (fun parameter ↦ (law parameter).expectation metric) := by
  constructor
  · intro h metric _ first second heq
    exact congrArg (fun p ↦ p.expectation metric) (h first second heq)
  · intro h first second heq
    apply (eq_iff_all_bounded_expectations_eq _ _).mpr
    intro metric hmetric
    exact h metric hmetric first second heq

/-- A point mass provides a nonempty concrete law without zero-denominator metric branches. -/
noncomputable def pointMass (selected : Report) : FiniteReportLaw Report := by
  classical
  exact {
    mass := fun report ↦ if report = selected then 1 else 0
    mass_nonneg := by intro report; split_ifs <;> norm_num
    mass_sum := by simp }

/-- Opposite deterministic binary reports attain the largest possible discrepancy: one.
The same singleton metric exhibits the disagreement in their expectations. -/
theorem binary_pointMass_separation :
    (pointMass true).totalVariation (pointMass false) = 1 ∧
      (pointMass true).expectation (singletonMetric true) = 1 ∧
      (pointMass false).expectation (singletonMetric true) = 0 := by
  norm_num [totalVariation, pointMass, expectation, singletonMetric, Fintype.sum_bool]

end FiniteReportLaw

end Descent.Portability
