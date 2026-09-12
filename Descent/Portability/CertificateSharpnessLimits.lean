/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaDomainCertificate
import Descent.Portability.CylinderThresholdCertificate

assert_below Descent.Decision Descent.Program

/-!
# What a certificate can promise: sharpness of (18) and the atomic discretization gap

Two limits NOTE2 places on its certificates.

§5.2, sharpness of (18). Theorem 4 encloses the conditional mean `(L_K + δ_n)/(H_K + δ_d)`
using only the residual constraints `0 ≤ δ_n ≤ δ_d ≤ τ_K`, and its bounds are sharp given only
those constraints. `residualQuotients` is the set of quotients the constraints allow.
`isLeast_residualQuotients` shows that its least element is `L_K/(H_K + τ_K)`, attained at
`δ_n = 0, δ_d = τ_K`, and `isGreatest_residualQuotients` that its greatest element is
`(L_K + τ_K)/(H_K + τ_K)`, attained at `δ_n = δ_d = τ_K`. The finite-law certificate itself is
`ReplicaDomainCertificate.replica_certificate`, with its width in `certificate_width`.

§7.2, the atomic discretization gap. For genuinely continuous reports a finite atomic
discretization does not converge in total variation. `isGreatest_eventGap_of_countable_support`
proves this on any measurable space with measurable singletons: a probability law concentrated
on a countable set and a non-atomic probability law are at event distance one, the greatest
value of `|P(A) - μ(A)|` over measurable events `A`, attained at the support.
`eventGap_eq_one_at_every_resolution` states it for a whole sequence of discretizations.
`CylinderThresholdCertificate.discretization_event_gap` is the fair-bit case on one event.

## Empirical status

None. The bodies here are inequalities between real numbers and between measures of sets, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CertificateSharpnessLimits

open MeasureTheory

/-! ## Sharpness of (18) -/

/-- The conditional means that the residual constraints of NOTE2 §5.2 allow: a retained
numerator `retained` and retained mass `mass`, completed by an unresolved numerator and an
unresolved definedness mass with `0 ≤ δ_n ≤ δ_d ≤ τ`. -/
def residualQuotients (retained mass tolerance : ℝ) : Set ℝ :=
  {quotient | ∃ unresolvedNumerator unresolvedMass : ℝ, 0 ≤ unresolvedNumerator ∧
    unresolvedNumerator ≤ unresolvedMass ∧ unresolvedMass ≤ tolerance ∧
    quotient = (retained + unresolvedNumerator) / (mass + unresolvedMass)}

/-- NOTE2 (18), lower endpoint: given only the residual constraints, the least possible
conditional mean is `L_K/(H_K + τ_K)`, attained at `δ_n = 0, δ_d = τ_K`. -/
theorem isLeast_residualQuotients (retained mass tolerance : ℝ) (hretained : 0 ≤ retained)
    (hmass : 0 < mass) (htolerance : 0 ≤ tolerance) :
    IsLeast (residualQuotients retained mass tolerance) (retained / (mass + tolerance)) := by
  constructor
  · exact ⟨0, tolerance, le_rfl, htolerance, le_rfl, by rw [add_zero]⟩
  · rintro quotient ⟨numerator, massGap, hnum, hnumle, hgap, rfl⟩
    have hpos : 0 < mass + massGap := by linarith
    rw [div_le_div_iff₀ (by linarith) hpos]
    nlinarith [mul_nonneg hretained (sub_nonneg.mpr hgap),
      mul_nonneg hnum (by linarith : (0 : ℝ) ≤ mass + tolerance)]

/-- NOTE2 (18), upper endpoint: given only the residual constraints and `L_K ≤ H_K`, the greatest
possible conditional mean is `(L_K + τ_K)/(H_K + τ_K)`, attained at `δ_n = δ_d = τ_K`. -/
theorem isGreatest_residualQuotients (retained mass tolerance : ℝ) (hle : retained ≤ mass)
    (hmass : 0 < mass) (htolerance : 0 ≤ tolerance) :
    IsGreatest (residualQuotients retained mass tolerance)
      ((retained + tolerance) / (mass + tolerance)) := by
  constructor
  · exact ⟨tolerance, tolerance, htolerance, le_rfl, le_rfl, rfl⟩
  · rintro quotient ⟨numerator, massGap, hnum, hnumle, hgap, rfl⟩
    have hpos : 0 < mass + massGap := by linarith
    rw [div_le_div_iff₀ hpos (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hgap),
      mul_nonneg (sub_nonneg.mpr hnumle) (by linarith : (0 : ℝ) ≤ mass + tolerance)]

/-! ## The atomic discretization gap -/

/-- NOTE2 §7.2: a probability law concentrated on a countable set, in particular any finite
atomic discretization, is at event distance one from every non-atomic probability law: one is
the greatest value of `|P(A) - μ(A)|` over measurable events, attained at the support. -/
theorem isGreatest_eventGap_of_countable_support {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (atomic continuous : Measure α) [IsProbabilityMeasure atomic]
    [IsProbabilityMeasure continuous] [NoAtoms continuous] {support : Set α}
    (hsupport : support.Countable) (hconcentrated : atomic supportᶜ = 0) :
    IsGreatest {gap | ∃ event, MeasurableSet event ∧
      gap = |atomic.real event - continuous.real event|} 1 := by
  have hfull : atomic support = 1 :=
    (prob_compl_eq_zero_iff hsupport.measurableSet).mp hconcentrated
  constructor
  · refine ⟨support, hsupport.measurableSet, ?_⟩
    rw [measureReal_def, measureReal_def, hfull, hsupport.measure_zero continuous]
    simp
  · rintro gap ⟨event, _, rfl⟩
    have hatomicLe : atomic.real event ≤ 1 := measureReal_le_one
    have hcontinuousLe : continuous.real event ≤ 1 := measureReal_le_one
    have hatomicNonneg : 0 ≤ atomic.real event := measureReal_nonneg
    have hcontinuousNonneg : 0 ≤ continuous.real event := measureReal_nonneg
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- NOTE2 §7.2: a sequence of atomic discretizations, each concentrated on a countable set, is
at event distance one from a non-atomic probability law at every resolution. -/
theorem eventGap_eq_one_at_every_resolution {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (atomicAt : ℕ → Measure α)
    [∀ resolution, IsProbabilityMeasure (atomicAt resolution)] (continuous : Measure α)
    [IsProbabilityMeasure continuous] [NoAtoms continuous] (supportAt : ℕ → Set α)
    (hsupport : ∀ resolution, (supportAt resolution).Countable)
    (hconcentrated : ∀ resolution, atomicAt resolution (supportAt resolution)ᶜ = 0)
    (resolution : ℕ) :
    IsGreatest {gap | ∃ event, MeasurableSet event ∧
      gap = |(atomicAt resolution).real event - continuous.real event|} 1 :=
  isGreatest_eventGap_of_countable_support (atomicAt resolution) continuous
    (hsupport resolution) (hconcentrated resolution)

end Descent.Portability.CertificateSharpnessLimits
