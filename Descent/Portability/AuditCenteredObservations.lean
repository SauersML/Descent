/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SharedAuditCompletion

assert_below Descent.Decision Descent.Program

/-!
The actual centered observations used by the audit confidence theorem. Their
mean, second moment, and almost-sure range are derived from the augmented
observation measure. Both requested and unrequested branches are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AuditCenteredObservations

open MeasureTheory ProbabilityTheory AugmentedAuditLaw BoundedAuditCompletion

/-- A weighted centered observation, with the true target mean determined by its outcome law. -/
noncomputable def centered (μ : Measure ℝ) (w z : ℝ) : ℝ := w * (z - ∫ y, y ∂μ)

/-- Centering and applying a fixed contrast coefficient is measurable. -/
theorem centered_measurable (μ : Measure ℝ) (w : ℝ) : Measurable (centered μ w) := by
  unfold centered
  fun_prop

/-- The requested branch belongs to the claimed enlarged observation interval. -/
theorem observed_interval (p q L U y : ℝ) (hp : 0 < p) (hy : y ∈ Set.Icc L U) :
    observed p q y ∈ Set.Icc (observed p q L) (observed p q U) := by
  unfold observed
  constructor
  · exact add_le_add_left (div_le_div_of_nonneg_right (sub_le_sub_right hy.1 q) hp.le) q
  · exact add_le_add_left (div_le_div_of_nonneg_right (sub_le_sub_right hy.2 q) hp.le) q

/-- The unrequested proxy belongs to the same observation interval. -/
theorem proxy_interval (p q L U : ℝ) (hp : 0 < p) (hq : q ∈ Set.Icc L U) :
    q ∈ Set.Icc (observed p q L) (observed p q U) := by
  unfold observed
  constructor
  · have hh : (L - q) / p ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hq.1]) hp.le
    linarith
  · have hh : 0 ≤ (U - q) / p := div_nonneg (by linarith [hq.2]) hp.le
    linarith

/-- The complete audit measure has the stated almost-sure support. -/
theorem audit_support (μ : Measure ℝ) (p q L U : ℝ) (hp : 0 < p)
    (hq : q ∈ Set.Icc L U) (hs : ∀ᵐ y ∂μ, y ∈ Set.Icc L U) :
    ∀ᵐ z ∂auditLaw μ p q, z ∈ Set.Icc (observed p q L) (observed p q U) := by
  unfold auditLaw
  apply ae_add_measure_iff.mpr
  constructor
  · apply Measure.ae_smul_measure
    simpa using proxy_interval p q L U hp hq
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (observed_measurable p q).aemeasurable measurableSet_Icc).mpr
    filter_upwards [hs] with y hy
    exact observed_interval p q L U y hp hy

/-- The mean of a bounded probability law lies in its almost-sure support interval. -/
theorem mean_interval (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ)
    (hs : ∀ᵐ y ∂μ, y ∈ Set.Icc a b) : (∫ y, y ∂μ) ∈ Set.Icc a b := by
  have hi := (memLp_of_bounded hs measurable_id.aestronglyMeasurable 2).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  constructor
  · have hh := integral_mono_ae (integrable_const a) hi (hs.mono fun _ h ↦ h.1)
    simpa using hh
  · have hh := integral_mono_ae hi (integrable_const b) (hs.mono fun _ h ↦ h.2)
    simpa using hh

/-- Centering a bounded observation costs at most the length of its support interval. -/
theorem centered_interval_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ)
    (hs : ∀ᵐ y ∂μ, y ∈ Set.Icc a b) :
    ∀ᵐ y ∂μ, |y - ∫ z, z ∂μ| ≤ b - a := by
  have hm := mean_interval μ a b hs
  filter_upwards [hs] with y hy
  rw [abs_le]
  constructor <;> linarith [hm.1, hm.2, hy.1, hy.2]

/-- The enlarged support interval has exactly width divided by request probability. -/
theorem observation_width (p q L U : ℝ) :
    observed p q U - observed p q L = (U - L) / p := by
  unfold observed
  ring

/-- The true centered audit observation has the manuscript's bounded-increment constant. -/
theorem centered_range (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q L U w : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (hq : q ∈ Set.Icc L U)
    (hs : ∀ᵐ y ∂μ, y ∈ Set.Icc L U) :
    ∀ᵐ z ∂auditLaw μ p q, |centered μ w z| ≤ |w| * (U - L) / p := by
  letI := auditLaw_probability μ p q ⟨hp.1.le, hp.2⟩
  have hi := (memLp_of_bounded hs measurable_id.aestronglyMeasurable 2).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hb := centered_interval_bound (auditLaw μ p q) _ _ (audit_support μ p q L U hp.1 hq hs)
  rw [audit_mean μ p q hp hi, observation_width] at hb
  filter_upwards [hb] with z hz
  unfold centered
  rw [abs_mul]
  have hh := mul_le_mul_of_nonneg_left hz (abs_nonneg w)
  simpa only [mul_div_assoc] using hh

/-- Every centered observation has a finite second moment under its audit law. -/
theorem centered_memLp (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q w : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (hY : MemLp (fun y : ℝ ↦ y) 2 μ) :
    MemLp (centered μ w) 2 (auditLaw μ p q) := by
  letI := auditLaw_probability μ p q ⟨hp.1.le, hp.2⟩
  exact ((audit_memLp μ p q hY).sub (memLp_const _)).const_mul w

/-- The centering uses the prospective outcome mean and is exactly unbiased. -/
theorem centered_mean (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q w : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (hY : MemLp (fun y : ℝ ↦ y) 2 μ) :
    (∫ z, centered μ w z ∂auditLaw μ p q) = 0 := by
  letI := auditLaw_probability μ p q ⟨hp.1.le, hp.2⟩
  have hi := (audit_memLp μ p q hY).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  unfold centered
  rw [integral_const_mul w (fun z ↦ z - ∫ y, y ∂μ),
    integral_sub hi (integrable_const _),
    audit_mean μ p q hp (hY.integrable (by norm_num : (1 : ENNReal) ≤ 2))]
  simp

/-- The actual centered second moment is the coefficient square times the audit variance. -/
theorem centered_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q w : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (hY : MemLp (fun y : ℝ ↦ y) 2 μ) :
    (∫ z, centered μ w z ^ 2 ∂auditLaw μ p q) =
      w ^ 2 * Var[fun z : ℝ ↦ z; auditLaw μ p q] := by
  rw [variance_eq_integral (X := fun z : ℝ ↦ z) measurable_id.aemeasurable,
    audit_mean μ p q hp (hY.integrable (by norm_num : (1 : ENNReal) ≤ 2))]
  simp only [centered, mul_pow, integral_const_mul]

end Descent.Portability.AuditCenteredObservations
