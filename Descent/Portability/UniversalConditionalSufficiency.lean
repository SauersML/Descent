/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification

assert_below Descent.Decision Descent.Program

/-!
# Universal conditional sufficiency of a summary for every report

Pre-outcome information carries a law, and conditional on it the study produces a report
through a specified channel. A proposed summary of that information is sufficient for every
report exactly when the conditional report law is constant along the summary's fibres. This
module proves the three formulations of UPT Theorem 9.1 equivalent in the finite case: every
bounded report statistic has the same conditional expectation along a fibre; the conditional
report laws along a fibre are the same law; and the report is conditionally independent of
the information given the summary. It then proves that the conditional report law is itself
the coarsest sufficient statistic, by showing sufficiency is equivalent to the conditional
law factoring through the summary.

This is UPT Theorem 9.1 restricted to finite information, summary and report spaces. The
manuscript's standard Borel statement, which needs a conditional-law-valued kernel and a
countable determining class, is not formalized here. The equivalence of the first two
formulations is exactly `FiniteReportLaw.eq_iff_all_bounded_expectations_eq`, already proved
in `UniversalMetricIdentification`; the conditional independence formulation and the
coarsest-statistic claim are what is added.

Conditional independence is written without division, as the identity between the product of
the conditional report mass with the summary class probability and the joint mass restricted
to the class. That keeps it meaningful on classes of zero probability rather than assigning
an invented value there. The hypotheses are domain conditions: the information state carries
positive probability wherever a conditional law is compared.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.UniversalConditionalSufficiency

noncomputable section

variable {Info Cls Report : Type*} [Fintype Info] [Fintype Report]

/-- The probability that the summary takes a given value. -/
def classMass [DecidableEq Cls] (prior : FiniteReportLaw Info) (summary : Info → Cls)
    (cls : Cls) : ℝ :=
  ∑ w, if summary w = cls then prior.mass w else 0

/-- The joint mass of a summary value and a report, before any normalization. -/
def classReportMass [DecidableEq Cls] (prior : FiniteReportLaw Info)
    (channel : Info → FiniteReportLaw Report) (summary : Info → Cls) (cls : Cls)
    (report : Report) : ℝ :=
  ∑ w, if summary w = cls then prior.mass w * (channel w).mass report else 0

/-- A summary value actually taken by a state of positive probability has positive
probability. -/
theorem classMass_pos [DecidableEq Cls] (prior : FiniteReportLaw Info)
    (summary : Info → Cls) (w : Info)
    (hw : 0 < prior.mass w) : 0 < classMass prior summary (summary w) := by
  rw [classMass]
  have hnonneg : ∀ v : Info, v ∈ (Finset.univ : Finset Info) →
      0 ≤ (if summary v = summary w then prior.mass v else 0) := by
    intro v _
    by_cases hv : summary v = summary w
    · simpa [hv] using prior.mass_nonneg v
    · simp [hv]
  have hterm := Finset.single_le_sum hnonneg (Finset.mem_univ w)
  rw [if_pos rfl] at hterm
  linarith

/-- UPT Theorem 9.1, the equivalence of its first two formulations: equality of every
bounded report statistic's conditional expectation along a fibre is equality of the
conditional report laws along that fibre. -/
theorem sufficient_iff_bounded_expectations_match (prior : FiniteReportLaw Info)
    (channel : Info → FiniteReportLaw Report) (summary : Info → Cls) :
    (∀ w w', 0 < prior.mass w → 0 < prior.mass w' → summary w = summary w' →
        channel w = channel w') ↔
      ∀ w w', 0 < prior.mass w → 0 < prior.mass w' → summary w = summary w' →
        ∀ metric, FiniteReportLaw.BoundedMetric metric →
          (channel w).expectation metric = (channel w').expectation metric := by
  constructor
  · intro hsuff w w' hw hw' hcls metric hmetric
    exact (FiniteReportLaw.eq_iff_all_bounded_expectations_eq (channel w) (channel w')).1
      (hsuff w w' hw hw' hcls) metric hmetric
  · intro hexp w w' hw hw' hcls
    exact (FiniteReportLaw.eq_iff_all_bounded_expectations_eq (channel w) (channel w')).2
      (hexp w w' hw hw' hcls)

/-- UPT Theorem 9.1, the equivalence with its third formulation: the conditional report laws
are constant along the summary's fibres exactly when the report is conditionally independent
of the information given the summary. -/
theorem sufficient_iff_conditional_independence [DecidableEq Cls]
    (prior : FiniteReportLaw Info)
    (channel : Info → FiniteReportLaw Report) (summary : Info → Cls) :
    (∀ w w', 0 < prior.mass w → 0 < prior.mass w' → summary w = summary w' →
        channel w = channel w') ↔
      ∀ (w : Info) (report : Report), 0 < prior.mass w →
        (channel w).mass report * classMass prior summary (summary w) =
          classReportMass prior channel summary (summary w) report := by
  constructor
  · intro hsuff w report hw
    rw [classMass, classReportMass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    by_cases hv : summary v = summary w
    · rw [if_pos hv, if_pos hv]
      rcases lt_or_eq_of_le (prior.mass_nonneg v) with hpos | hzero
      · rw [hsuff v w hpos hw hv]
        ring
      · rw [← hzero]
        ring
    · rw [if_neg hv, if_neg hv, mul_zero]
  · intro hindep w w' hw hw' hcls
    refine FiniteReportLaw.ext fun report ↦ ?_
    have hw1 := hindep w report hw
    have hw2 := hindep w' report hw'
    rw [hcls] at hw1
    rw [← hw2] at hw1
    have hpos : 0 < classMass prior summary (summary w') := classMass_pos prior summary w' hw'
    exact mul_right_cancel₀ (ne_of_gt hpos) hw1

/-- UPT Theorem 9.1, the coarsest sufficient statistic: a summary is sufficient for every
report exactly when the conditional report law factors through it on the states of positive
probability. The conditional report law is therefore itself sufficient, and every other
sufficient summary determines it. -/
theorem sufficient_iff_channel_factors [Nonempty Report] (prior : FiniteReportLaw Info)
    (channel : Info → FiniteReportLaw Report) (summary : Info → Cls) :
    (∀ w w', 0 < prior.mass w → 0 < prior.mass w' → summary w = summary w' →
        channel w = channel w') ↔
      ∃ decode : Cls → FiniteReportLaw Report,
        ∀ w, 0 < prior.mass w → channel w = decode (summary w) := by
  classical
  constructor
  · intro hsuff
    have hpick : ∀ cls : Cls, ∃ law : FiniteReportLaw Report,
        ∀ w, 0 < prior.mass w → summary w = cls → channel w = law := by
      intro cls
      by_cases hex : ∃ v, 0 < prior.mass v ∧ summary v = cls
      · obtain ⟨v, hv, hvcls⟩ := hex
        exact ⟨channel v, fun w hw hwcls ↦ hsuff w v hw hv (by rw [hwcls, hvcls])⟩
      · refine ⟨FiniteReportLaw.pointMass (Classical.arbitrary Report), fun w hw hwcls ↦ ?_⟩
        exact absurd ⟨w, hw, hwcls⟩ hex
    choose decode hdecode using hpick
    exact ⟨decode, fun w hw ↦ hdecode (summary w) w hw rfl⟩
  · rintro ⟨decode, hdecode⟩ w w' hw hw' hcls
    rw [hdecode w hw, hdecode w' hw', hcls]

end

end Descent.Portability.UniversalConditionalSufficiency
