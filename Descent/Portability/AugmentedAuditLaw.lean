/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 4. The law of a single augmented audit
observation is the actual mixture of the unobserved proxy and the affine image
of the outcome law. Its expectation and variance are derived from integrals.
The same construction with a Dirac outcome gives the sampling-only experiment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AugmentedAuditLaw

open MeasureTheory ProbabilityTheory

/-- The reported observation when its outcome is requested. -/
noncomputable def observed (p q y : ℝ) : ℝ := q + (y - q) / p

/-- The law after an independent Bernoulli request with probability `p`. -/
noncomputable def auditLaw (μ : Measure ℝ) (p q : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac q +
    ENNReal.ofReal p • μ.map (observed p q)

/-- The requested-outcome transformation is measurable. -/
theorem observed_measurable (p q : ℝ) : Measurable (observed p q) := by
  unfold observed
  fun_prop

/-- The audit law is a normalized probability measure for every valid request rate. -/
theorem auditLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p q : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : IsProbabilityMeasure (auditLaw μ p q) := by
  constructor
  simp only [auditLaw, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply (observed_measurable p q) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) hp.1]
  norm_num

/-- Integrability under the actual two-branch audit law. -/
theorem audit_integrable (μ : Measure ℝ) (p q : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (hi : Integrable (fun y ↦ f (observed p q y)) μ) :
    Integrable f (auditLaw μ p q) := by
  have hd : Integrable f (Measure.dirac q) := integrable_dirac (by simp)
  have hm : Integrable f (μ.map (observed p q)) :=
    (integrable_map_measure hf.aestronglyMeasurable
      (observed_measurable p q).aemeasurable).mpr hi
  exact (hd.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hm.smul_measure ENNReal.ofReal_ne_top)

/-- Exact integration formula, with both selection branches retained. -/
theorem audit_integral (μ : Measure ℝ) (p q : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun y ↦ f (observed p q y)) μ) :
    (∫ z, f z ∂auditLaw μ p q) = (1 - p) * f q + p * ∫ y, f (observed p q y) ∂μ := by
  have hd : Integrable f (Measure.dirac q) := integrable_dirac (by simp)
  have hm : Integrable f (μ.map (observed p q)) :=
    (integrable_map_measure hf.aestronglyMeasurable
      (observed_measurable p q).aemeasurable).mpr hi
  rw [auditLaw, integral_add_measure (hd.smul_measure ENNReal.ofReal_ne_top)
    (hm.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_map (observed_measurable p q).aemeasurable hf.aestronglyMeasurable,
    integral_dirac]
  simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2), ENNReal.toReal_ofReal hp.1,
    smul_eq_mul]

/-- Finite second moments of the outcome imply finite second moments after requesting it. -/
theorem observed_memLp (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q : ℝ)
    (hY : MemLp (fun y : ℝ ↦ y) 2 μ) : MemLp (observed p q) 2 μ := by
  simpa only [observed, div_eq_mul_inv, mul_comm, Pi.add_apply, Pi.sub_apply] using
    (memLp_const q).add ((hY.sub (memLp_const q)).const_mul p⁻¹)

/-- The augmented observation has a genuine finite second moment. -/
theorem audit_memLp (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q : ℝ)
    (hY : MemLp (fun y : ℝ ↦ y) 2 μ) :
    MemLp (fun z : ℝ ↦ z) 2 (auditLaw μ p q) := by
  apply (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
  exact audit_integrable μ p q (fun z ↦ z ^ 2) (by fun_prop)
    (observed_memLp μ p q hY).integrable_sq

/-- Integration of the requested branch needs only the outcome's first moment. -/
theorem observed_integral (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q : ℝ)
    (hY : Integrable (fun y : ℝ ↦ y) μ) :
    (∫ y, observed p q y ∂μ) = q + ((∫ y, y ∂μ) - q) / p := by
  unfold observed
  have hs : Integrable (fun y ↦ y - q) μ := hY.sub (integrable_const q)
  rw [integral_add (integrable_const q) (hs.div_const p),
    integral_div, integral_sub hY (integrable_const q)]
  simp

/-- An arbitrarily wrong fixed proxy does not bias the augmented audit. -/
theorem audit_mean (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (hY : Integrable (fun y : ℝ ↦ y) μ) :
    (∫ z, z ∂auditLaw μ p q) = ∫ y, y ∂μ := by
  have hi : Integrable (observed p q) μ :=
    (integrable_const q).add ((hY.sub (integrable_const q)).div_const p)
  rw [audit_integral μ p q ⟨hp.1.le, hp.2⟩ (fun z : ℝ ↦ z) measurable_id hi,
    observed_integral μ p q hY]
  field_simp [hp.1.ne']
  ring

/-- An affine second-moment expansion, justified by actual integrability. -/
theorem affine_second (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ)
    (hY : MemLp (fun y : ℝ ↦ y) 2 μ) :
    (∫ y, (a * y + b) ^ 2 ∂μ) =
      a ^ 2 * (∫ y, y ^ 2 ∂μ) + 2 * a * b * (∫ y, y ∂μ) + b ^ 2 := by
  have hi := hY.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have he : (fun y : ℝ ↦ (a * y + b) ^ 2) =
      fun y ↦ a ^ 2 * y ^ 2 + (2 * a * b) * y + b ^ 2 := by
    funext y
    ring
  have hs : Integrable (fun y ↦ a ^ 2 * y ^ 2 + (2 * a * b) * y) μ :=
    (hY.integrable_sq.const_mul _).add (hi.const_mul _)
  rw [he, integral_add hs (integrable_const _),
    integral_add (hY.integrable_sq.const_mul _) (hi.const_mul _)]
  simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul]
  rw [integral_const_mul (2 * a * b) (fun y : ℝ ↦ y)]

/-- The prospective audit variance includes both outcome noise and proxy error. -/
theorem audit_variance (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (hY : MemLp (fun y : ℝ ↦ y) 2 μ) :
    Var[fun z : ℝ ↦ z; auditLaw μ p q] =
      Var[fun y : ℝ ↦ y; μ] / p + (1 / p - 1) * ((∫ y, y ∂μ) - q) ^ 2 := by
  letI := auditLaw_probability μ p q ⟨hp.1.le, hp.2⟩
  have hi := hY.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  rw [variance_eq_sub (audit_memLp μ p q hY), audit_mean μ p q hp hi,
    variance_eq_sub hY]
  simp only [Pi.pow_apply]
  rw [audit_integral μ p q ⟨hp.1.le, hp.2⟩ (fun z ↦ z ^ 2) (by fun_prop)
    (observed_memLp μ p q hY).integrable_sq]
  have he : (fun y ↦ observed p q y ^ 2) =
      fun y ↦ (p⁻¹ * y + q * (1 - p⁻¹)) ^ 2 := by
    funext y
    unfold observed
    congr 1
    ring
  rw [he, affine_second μ p⁻¹ (q * (1 - p⁻¹)) hY]
  field_simp [hp.1.ne']
  ring

/-- Conditioning on a realized outcome removes its prospective phenotype variance. -/
theorem sampling_only_variance (p q y : ℝ) (hp : 0 < p ∧ p ≤ 1) :
    Var[fun z : ℝ ↦ z; auditLaw (Measure.dirac y) p q] =
      (1 / p - 1) * (y - q) ^ 2 := by
  have hY : MemLp (fun z : ℝ ↦ z) 2 (Measure.dirac y) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
      (integrable_dirac (by simp))
  rw [audit_variance (Measure.dirac y) p q hp hY]
  simp

end Descent.Portability.AugmentedAuditLaw
