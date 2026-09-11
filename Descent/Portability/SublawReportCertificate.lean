/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification

assert_below Descent.Decision Descent.Program

/-!
# Positive sublaws certify every bounded report metric at once

An exact computation that enumerates part of a finite report space and stops returns a
positive sublaw: a nonnegative mass vector whose total is at most one and which never
claims more mass on a report than the true report law does. Everything the computation
failed to reach is summarised by one number, the missing mass. This module proves that a
single such certificate bounds the expectation of every metric with values in a fixed
interval, and that it also bounds the conditional expectation on a decidable definedness
event, without any knowledge of where the missing mass sits.

`expectation_bounds` is NOTE 1 equation (24): for a metric with values in `[lower, upper]`
the true expectation lies between the accounted total shifted by `lower` times the missing
mass and the same total shifted by `upper` times the missing mass.
`conditional_expectation_bounds` is the normalized certificate, NOTE 1 equation (25) and
NOTE 2 equation (35). Its algebraic core is `ratio_bounds`, a statement about seven real
numbers with no report space in it, isolated here because the replica-domain certificates
reuse it verbatim. `defined_probability_bounds` is the companion statement that the true
definedness probability lies between the accounted definedness mass and that mass plus the
missing mass.

Sharpness is delivered by construction rather than asserted. `completion` places the whole
missing mass on one chosen report, `dominatedBy_completion` shows the result is a report law
dominating the sublaw, and `endpoints_attained` shows that the two completions choosing a
defined report of minimal, respectively maximal, metric value realize the two endpoints
exactly. No argument using only the sublaw and the value interval can narrow the interval.

Scope: the report space is finite and a certificate is a mass vector, not a measure. How a
sublaw arises is irrelevant here; only domination and the mass deficit are used. The
uniformization route of NOTE 1 equation (26), which produces such sublaws from a finite
generator by truncating a Poisson mixture, is not proved in this module. `truncation` is
the concrete sublaw supplied as a witness: the restriction of a known law to an enumerated
finite set of reports, whose missing mass is exactly the mass left outside that set.

These statements strengthen `FiniteReportLaw.abs_expectation_sub_le_totalVariation` in a
different direction: there one compares two complete laws, here one has only a fragment of
a single law and still certifies every bounded metric and the normalized conditional one.

## Empirical status

None. The bodies here are algebra: every statement is an inequality between finite sums and
ratios of real numbers fixed by the hypotheses, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SublawReportCertificate

variable {Report : Type*} [Fintype Report]

/-- A positive sublaw of a finite report space: a nonnegative mass vector whose total mass is
at most one. It records exactly what a partial exact computation has established. -/
structure ReportSublaw (Report : Type*) [Fintype Report] where
  mass : Report → ℝ
  mass_nonneg : ∀ report, 0 ≤ mass report
  mass_sum_le_one : ∑ report, mass report ≤ 1

namespace ReportSublaw

/-- The mass a sublaw has not accounted for. -/
noncomputable def missingMass (sublaw : ReportSublaw Report) : ℝ :=
  1 - ∑ report, sublaw.mass report

/-- The unaccounted mass of a sublaw is never negative. -/
theorem missingMass_nonneg (sublaw : ReportSublaw Report) : 0 ≤ sublaw.missingMass := by
  have hsum := sublaw.mass_sum_le_one
  simp only [missingMass]
  linarith

/-- A sublaw is dominated by a report law when it never claims more mass on any report than
the law assigns to it. -/
def DominatedBy (sublaw : ReportSublaw Report) (law : FiniteReportLaw Report) : Prop :=
  ∀ report, sublaw.mass report ≤ law.mass report

end ReportSublaw

/-- Enumerating a finite set of reports exactly and stopping there yields a sublaw of the law
being enumerated. -/
noncomputable def truncation [DecidableEq Report] (law : FiniteReportLaw Report)
    (enumerated : Finset Report) : ReportSublaw Report where
  mass := fun report ↦ if report ∈ enumerated then law.mass report else 0
  mass_nonneg := fun report ↦ by
    by_cases hmem : report ∈ enumerated
    · simpa [hmem] using law.mass_nonneg report
    · simp [hmem]
  mass_sum_le_one := by
    rw [← law.mass_sum]
    refine Finset.sum_le_sum fun report _ ↦ ?_
    by_cases hmem : report ∈ enumerated
    · simp [hmem]
    · simpa [hmem] using law.mass_nonneg report

/-- The enumerated fragment of a law is dominated by that law, so the domination hypothesis
of the certificates below is inhabited by an object no stronger than a partial enumeration. -/
theorem truncation_dominatedBy [DecidableEq Report] (law : FiniteReportLaw Report)
    (enumerated : Finset Report) : (truncation law enumerated).DominatedBy law := by
  intro report
  show (if report ∈ enumerated then law.mass report else 0) ≤ law.mass report
  by_cases hmem : report ∈ enumerated
  · simp [hmem]
  · simpa [hmem] using law.mass_nonneg report

/-- The mass an enumeration misses is exactly the mass of the reports it did not reach. -/
theorem truncation_missingMass [DecidableEq Report] (law : FiniteReportLaw Report)
    (enumerated : Finset Report) :
    (truncation law enumerated).missingMass = 1 - ∑ report ∈ enumerated, law.mass report := by
  have hmass : ∑ report, (truncation law enumerated).mass report =
      ∑ report ∈ enumerated, law.mass report := by
    show (∑ report, if report ∈ enumerated then law.mass report else 0) =
      ∑ report ∈ enumerated, law.mass report
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [ReportSublaw.missingMass, hmass]

/-- The mass a dominating report law places beyond what a sublaw accounts for. -/
noncomputable def residual (law : FiniteReportLaw Report) (sublaw : ReportSublaw Report) :
    Report → ℝ :=
  fun report ↦ law.mass report - sublaw.mass report

/-- Under domination the residual weight is nonnegative on every report. -/
theorem residual_nonneg (law : FiniteReportLaw Report) (sublaw : ReportSublaw Report)
    (hdom : sublaw.DominatedBy law) (report : Report) : 0 ≤ residual law sublaw report :=
  sub_nonneg.mpr (hdom report)

/-- Every expectation splits into the part a sublaw accounts for and the residual part. -/
theorem residual_expectation (law : FiniteReportLaw Report) (sublaw : ReportSublaw Report)
    (value : Report → ℝ) :
    ∑ report, residual law sublaw report * value report =
      law.expectation value - ∑ report, sublaw.mass report * value report := by
  simp only [residual, FiniteReportLaw.expectation, sub_mul, Finset.sum_sub_distrib]

/-- The total residual weight is the missing mass, whatever the dominating law. -/
theorem sum_residual (law : FiniteReportLaw Report) (sublaw : ReportSublaw Report) :
    ∑ report, residual law sublaw report = sublaw.missingMass := by
  simp only [residual, ReportSublaw.missingMass, Finset.sum_sub_distrib, law.mass_sum]

/-- A nonnegative weighting of a function whose values lie between `lower` and `upper` has
weighted total between `lower` and `upper` times the total weight. -/
theorem weighted_value_bounds (weight : Report → ℝ) (hweight : ∀ report, 0 ≤ weight report)
    (value : Report → ℝ) (lower upper : ℝ) (hlower : ∀ report, lower ≤ value report)
    (hupper : ∀ report, value report ≤ upper) :
    lower * (∑ report, weight report) ≤ ∑ report, weight report * value report ∧
      ∑ report, weight report * value report ≤ upper * (∑ report, weight report) := by
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun report _ ↦ ?_
    rw [mul_comm lower (weight report)]
    exact mul_le_mul_of_nonneg_left (hlower report) (hweight report)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun report _ ↦ ?_
    rw [mul_comm upper (weight report)]
    exact mul_le_mul_of_nonneg_left (hupper report) (hweight report)

/-- **NOTE 1 equation (24).** One dominated sublaw certifies the expectation of every metric
with values in a fixed interval: the true expectation differs from the accounted total by at
most the missing mass times the width of that interval, and the two shifts are explicit. -/
theorem expectation_bounds (law : FiniteReportLaw Report) (sublaw : ReportSublaw Report)
    (hdom : sublaw.DominatedBy law) (value : Report → ℝ) (lower upper : ℝ)
    (hlower : ∀ report, lower ≤ value report) (hupper : ∀ report, value report ≤ upper) :
    (∑ report, sublaw.mass report * value report) + lower * sublaw.missingMass ≤
        law.expectation value ∧
      law.expectation value ≤
        (∑ report, sublaw.mass report * value report) + upper * sublaw.missingMass := by
  obtain ⟨hlow, hhigh⟩ := weighted_value_bounds (residual law sublaw)
    (residual_nonneg law sublaw hdom) value lower upper hlower hupper
  rw [sum_residual law sublaw] at hlow hhigh
  have hsplit := residual_expectation law sublaw value
  exact ⟨by linarith, by linarith⟩

/-- The real indicator of a decidable definedness event on reports. -/
def definedIndicator (defined : Report → Prop) [DecidablePred defined] : Report → ℝ :=
  fun report ↦ if defined report then 1 else 0

omit [Fintype Report] in
/-- A definedness indicator is nonnegative. -/
theorem definedIndicator_nonneg (defined : Report → Prop) [DecidablePred defined]
    (report : Report) : 0 ≤ definedIndicator defined report := by
  simp only [definedIndicator]
  split_ifs <;> norm_num

omit [Fintype Report] in
/-- A definedness indicator never exceeds one. -/
theorem definedIndicator_le_one (defined : Report → Prop) [DecidablePred defined]
    (report : Report) : definedIndicator defined report ≤ 1 := by
  simp only [definedIndicator]
  split_ifs <;> norm_num

/-- The definedness mass a sublaw has already accounted for. -/
noncomputable def definedMass (sublaw : ReportSublaw Report) (defined : Report → Prop)
    [DecidablePred defined] : ℝ :=
  ∑ report, sublaw.mass report * definedIndicator defined report

/-- The metric total a sublaw has already accounted for on the defined event. -/
noncomputable def definedTotal (sublaw : ReportSublaw Report) (defined : Report → Prop)
    [DecidablePred defined] (value : Report → ℝ) : ℝ :=
  ∑ report, sublaw.mass report * (definedIndicator defined report * value report)

/-- The conditional expectation of a metric given the definedness event, under a report law. -/
noncomputable def conditionalExpectation (law : FiniteReportLaw Report)
    (defined : Report → Prop) [DecidablePred defined] (value : Report → ℝ) : ℝ :=
  law.expectation (fun report ↦ definedIndicator defined report * value report) /
    law.expectation (definedIndicator defined)

/-- The residual definedness weight is the gap between the true definedness probability and
the mass a sublaw accounts for. -/
theorem residual_defined_mass (law : FiniteReportLaw Report) (sublaw : ReportSublaw Report)
    (defined : Report → Prop) [DecidablePred defined] :
    ∑ report, residual law sublaw report * definedIndicator defined report =
      law.expectation (definedIndicator defined) - definedMass sublaw defined := by
  simp only [definedMass]
  exact residual_expectation law sublaw (definedIndicator defined)

/-- The residual metric weight on the defined event is the gap between the true defined total
and the total a sublaw accounts for. -/
theorem residual_defined_total (law : FiniteReportLaw Report) (sublaw : ReportSublaw Report)
    (defined : Report → Prop) [DecidablePred defined] (value : Report → ℝ) :
    ∑ report, residual law sublaw report * definedIndicator defined report * value report =
      law.expectation (fun report ↦ definedIndicator defined report * value report) -
        definedTotal sublaw defined value := by
  have hstep := residual_expectation law sublaw
    (fun report ↦ definedIndicator defined report * value report)
  simp only [definedTotal]
  rw [← hstep]
  exact Finset.sum_congr rfl fun report _ ↦ mul_assoc _ _ _

/-- The residual definedness weight never exceeds the whole missing mass. -/
theorem residual_defined_mass_le (law : FiniteReportLaw Report) (sublaw : ReportSublaw Report)
    (hdom : sublaw.DominatedBy law) (defined : Report → Prop) [DecidablePred defined] :
    ∑ report, residual law sublaw report * definedIndicator defined report ≤
      sublaw.missingMass := by
  rw [← sum_residual law sublaw]
  refine Finset.sum_le_sum fun report _ ↦ ?_
  have hbound := mul_le_mul_of_nonneg_left (definedIndicator_le_one defined report)
    (residual_nonneg law sublaw hdom report)
  simpa using hbound

/-- **NOTE 1, section 5.** The true definedness probability lies between the definedness mass
a dominated sublaw accounts for and that mass increased by the whole missing mass. -/
theorem defined_probability_bounds (law : FiniteReportLaw Report)
    (sublaw : ReportSublaw Report) (hdom : sublaw.DominatedBy law) (defined : Report → Prop)
    [DecidablePred defined] :
    definedMass sublaw defined ≤ law.expectation (definedIndicator defined) ∧
      law.expectation (definedIndicator defined) ≤
        definedMass sublaw defined + sublaw.missingMass := by
  have heq := residual_defined_mass law sublaw defined
  have hnonneg :
      0 ≤ ∑ report, residual law sublaw report * definedIndicator defined report :=
    Finset.sum_nonneg fun report _ ↦ mul_nonneg (residual_nonneg law sublaw hdom report)
      (definedIndicator_nonneg defined report)
  have hle := residual_defined_mass_le law sublaw hdom defined
  constructor <;> linarith

/-- The algebraic core of the normalized certificate. An accounted pair `(total, mass)` with
`0 < mass` is completed by an unknown pair `(extraTotal, extraMass)` whose denominator part
lies in `[0, missing]` and whose numerator part is squeezed by the same value interval that
squeezes the accounted pair. Then the completed ratio lies between the two ratios obtained
by moving the whole missing mass into the denominator at the extreme values. Both ratios
`(total + lower * missing) / (mass + missing)` and `(total + upper * missing) / (mass +
missing)` have positive denominators because `0 < mass` and `0 ≤ missing`. -/
theorem ratio_bounds (lower upper mass total extraMass extraTotal missing : ℝ)
    (hmass : 0 < mass) (hextraNonneg : 0 ≤ extraMass) (hextraLe : extraMass ≤ missing)
    (htotalLower : lower * mass ≤ total) (htotalUpper : total ≤ upper * mass)
    (hextraLower : lower * extraMass ≤ extraTotal)
    (hextraUpper : extraTotal ≤ upper * extraMass) :
    (total + lower * missing) / (mass + missing) ≤
        (total + extraTotal) / (mass + extraMass) ∧
      (total + extraTotal) / (mass + extraMass) ≤
        (total + upper * missing) / (mass + missing) := by
  have hmissing : 0 ≤ missing := le_trans hextraNonneg hextraLe
  have hfull : 0 < mass + missing := by linarith
  have hpart : 0 < mass + extraMass := by linarith
  constructor
  · rw [div_le_div_iff₀ hfull hpart]
    have hcross := mul_le_mul_of_nonpos_right htotalLower
      (by linarith : extraMass - missing ≤ 0)
    have hscaleMass := mul_le_mul_of_nonneg_right hextraLower hmass.le
    have hscaleMissing := mul_le_mul_of_nonneg_right hextraLower hmissing
    nlinarith [hcross, hscaleMass, hscaleMissing]
  · rw [div_le_div_iff₀ hpart hfull]
    have hcross := mul_le_mul_of_nonneg_right htotalUpper
      (by linarith : (0 : ℝ) ≤ missing - extraMass)
    have hscaleMass := mul_le_mul_of_nonneg_right hextraUpper hmass.le
    have hscaleMissing := mul_le_mul_of_nonneg_right hextraUpper hmissing
    nlinarith [hcross, hscaleMass, hscaleMissing]

/-- **NOTE 1 equation (25) and NOTE 2 equation (35).** The normalization-aware certificate:
when a dominated sublaw already accounts for positive definedness mass, the conditional
expectation of a metric with values in `[lower, upper]` given definedness lies between the
two ratios obtained by adding the whole missing mass to the definedness denominator and the
extreme metric values to the numerator. No information about the unreached reports is used
beyond the single number `missingMass`. -/
theorem conditional_expectation_bounds (law : FiniteReportLaw Report)
    (sublaw : ReportSublaw Report) (hdom : sublaw.DominatedBy law) (defined : Report → Prop)
    [DecidablePred defined] (value : Report → ℝ) (lower upper : ℝ)
    (hlower : ∀ report, lower ≤ value report) (hupper : ∀ report, value report ≤ upper)
    (hpos : 0 < definedMass sublaw defined) :
    (definedTotal sublaw defined value + lower * sublaw.missingMass) /
          (definedMass sublaw defined + sublaw.missingMass) ≤
        conditionalExpectation law defined value ∧
      conditionalExpectation law defined value ≤
        (definedTotal sublaw defined value + upper * sublaw.missingMass) /
          (definedMass sublaw defined + sublaw.missingMass) := by
  have hindNonneg := definedIndicator_nonneg defined (Report := Report)
  have hsubWeight : ∀ report, 0 ≤ sublaw.mass report * definedIndicator defined report :=
    fun report ↦ mul_nonneg (sublaw.mass_nonneg report) (hindNonneg report)
  have hresWeight : ∀ report,
      0 ≤ residual law sublaw report * definedIndicator defined report :=
    fun report ↦ mul_nonneg (residual_nonneg law sublaw hdom report) (hindNonneg report)
  obtain ⟨hsubLow, hsubHigh⟩ := weighted_value_bounds
    (fun report ↦ sublaw.mass report * definedIndicator defined report) hsubWeight value
    lower upper hlower hupper
  obtain ⟨hresLow, hresHigh⟩ := weighted_value_bounds
    (fun report ↦ residual law sublaw report * definedIndicator defined report) hresWeight
    value lower upper hlower hupper
  have hmassEq : ∑ report, sublaw.mass report * definedIndicator defined report =
      definedMass sublaw defined := rfl
  have htotalEq :
      ∑ report, sublaw.mass report * definedIndicator defined report * value report =
        definedTotal sublaw defined value :=
    Finset.sum_congr rfl fun report _ ↦ mul_assoc _ _ _
  rw [hmassEq, htotalEq] at hsubLow hsubHigh
  rw [residual_defined_mass law sublaw defined,
    residual_defined_total law sublaw defined value] at hresLow hresHigh
  obtain ⟨hdefLow, hdefHigh⟩ := defined_probability_bounds law sublaw hdom defined
  have hextraNonneg :
      0 ≤ law.expectation (definedIndicator defined) - definedMass sublaw defined := by
    linarith
  have hextraLe :
      law.expectation (definedIndicator defined) - definedMass sublaw defined ≤
        sublaw.missingMass := by
    linarith
  obtain ⟨hlow, hhigh⟩ := ratio_bounds lower upper (definedMass sublaw defined)
    (definedTotal sublaw defined value)
    (law.expectation (definedIndicator defined) - definedMass sublaw defined)
    (law.expectation (fun report ↦ definedIndicator defined report * value report) -
      definedTotal sublaw defined value)
    sublaw.missingMass hpos hextraNonneg hextraLe hsubLow hsubHigh hresLow hresHigh
  have hmiddle :
      (definedTotal sublaw defined value +
          (law.expectation (fun report ↦ definedIndicator defined report * value report) -
            definedTotal sublaw defined value)) /
        (definedMass sublaw defined +
          (law.expectation (definedIndicator defined) - definedMass sublaw defined)) =
        conditionalExpectation law defined value := by
    unfold conditionalExpectation
    ring
  rw [hmiddle] at hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- The completion of a sublaw that assigns the whole missing mass to one chosen report. -/
noncomputable def completion [DecidableEq Report] (sublaw : ReportSublaw Report)
    (target : Report) : FiniteReportLaw Report where
  mass := fun report ↦ sublaw.mass report + if report = target then sublaw.missingMass else 0
  mass_nonneg := fun report ↦ by
    have hbase := sublaw.mass_nonneg report
    have hmissing := sublaw.missingMass_nonneg
    split_ifs <;> linarith
  mass_sum := by
    have hpoint : ∑ report, (if report = target then sublaw.missingMass else 0) =
        sublaw.missingMass := by simp
    rw [Finset.sum_add_distrib, hpoint]
    simp only [ReportSublaw.missingMass]
    ring

/-- Every completion dominates the sublaw it completes, so the domination hypothesis is
inhabited by laws that differ from one another only in where the missing mass went. -/
theorem dominatedBy_completion [DecidableEq Report] (sublaw : ReportSublaw Report)
    (target : Report) : sublaw.DominatedBy (completion sublaw target) := by
  intro report
  have hmissing := sublaw.missingMass_nonneg
  show sublaw.mass report ≤
    sublaw.mass report + if report = target then sublaw.missingMass else 0
  split_ifs <;> linarith

/-- Under a completion, every expectation is the accounted total plus the missing mass
weighted by the metric value at the chosen report. -/
theorem completion_expectation [DecidableEq Report] (sublaw : ReportSublaw Report)
    (target : Report) (value : Report → ℝ) :
    (completion sublaw target).expectation value =
      (∑ report, sublaw.mass report * value report) + value target * sublaw.missingMass := by
  have hmass : ∀ report, (completion sublaw target).mass report =
      sublaw.mass report + if report = target then sublaw.missingMass else 0 := fun _ ↦ rfl
  simp only [FiniteReportLaw.expectation, hmass, add_mul, Finset.sum_add_distrib]
  congr 1
  have hstep : ∀ report ∈ (Finset.univ : Finset Report),
      (if report = target then sublaw.missingMass else 0) * value report =
        if report = target then value target * sublaw.missingMass else 0 := by
    intro report _
    split_ifs with heq
    · rw [heq]; ring
    · ring
  rw [Finset.sum_congr rfl hstep]
  simp

/-- The conditional expectation under a completion that chooses a defined report is the
accounted ratio with the whole missing mass added to the denominator and the chosen report's
metric value times that mass added to the numerator. -/
theorem completion_conditional_expectation [DecidableEq Report] (sublaw : ReportSublaw Report)
    (defined : Report → Prop) [DecidablePred defined] (value : Report → ℝ) (target : Report)
    (htarget : defined target) :
    conditionalExpectation (completion sublaw target) defined value =
      (definedTotal sublaw defined value + value target * sublaw.missingMass) /
        (definedMass sublaw defined + sublaw.missingMass) := by
  have hind : definedIndicator defined target = 1 := by
    simp [definedIndicator, htarget]
  have hnum := completion_expectation sublaw target
    (fun report ↦ definedIndicator defined report * value report)
  have hden := completion_expectation sublaw target (definedIndicator defined)
  simp only [hind, one_mul] at hnum hden
  unfold conditionalExpectation definedTotal definedMass
  rw [hnum, hden]

/-- **Sharpness of NOTE 1 equation (25).** Given a defined report of minimal metric value and
a defined report of maximal metric value, the two completions that place the whole missing
mass on them attain the lower and the upper certificate endpoints exactly. So the interval
of `conditional_expectation_bounds` is the exact range over dominating completions and no
argument using only the sublaw and the value interval can shrink it. -/
theorem endpoints_attained [DecidableEq Report] (sublaw : ReportSublaw Report)
    (defined : Report → Prop) [DecidablePred defined] (value : Report → ℝ) (lower upper : ℝ)
    (leastReport greatestReport : Report) (hleast : defined leastReport)
    (hgreatest : defined greatestReport) (hvalueLeast : value leastReport = lower)
    (hvalueGreatest : value greatestReport = upper) :
    conditionalExpectation (completion sublaw leastReport) defined value =
        (definedTotal sublaw defined value + lower * sublaw.missingMass) /
          (definedMass sublaw defined + sublaw.missingMass) ∧
      conditionalExpectation (completion sublaw greatestReport) defined value =
        (definedTotal sublaw defined value + upper * sublaw.missingMass) /
          (definedMass sublaw defined + sublaw.missingMass) := by
  constructor
  · rw [completion_conditional_expectation sublaw defined value leastReport hleast,
      hvalueLeast]
  · rw [completion_conditional_expectation sublaw defined value greatestReport hgreatest,
      hvalueGreatest]

end Descent.Portability.SublawReportCertificate
