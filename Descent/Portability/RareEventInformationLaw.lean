/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
The marked and erased Gaussian rare-event experiments. The likelihoods are
explicit Bernoulli mixtures of the actual Gaussian density. Their scores are
derived by differentiation, and their null Fisher information is evaluated
using Gaussian moments. The variance parameter is `v`, corresponding to σ².
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RareEventInformationLaw

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The event probability for each observed Boolean mark. -/
noncomputable def markMass (η : ℝ) (z : Bool) : ℝ := if z then η else 1 - η

/-- Joint density with respect to counting measure on the mark and Lebesgue on outcome. -/
noncomputable def markedDensity (η : ℝ) (v : ℝ≥0) (θ : ℝ) (z : Bool) (y : ℝ) : ℝ :=
  markMass η z * gaussianPDFReal (if z then θ else 0) v y

/-- Marginalizing the unobserved mark gives the erased experiment's actual density. -/
noncomputable def erasedDensity (η : ℝ) (v : ℝ≥0) (θ y : ℝ) : ℝ :=
  (1 - η) * gaussianPDFReal 0 v y + η * gaussianPDFReal θ v y

theorem erasedDensity_eq_sum (η : ℝ) (v : ℝ≥0) (θ y : ℝ) :
    erasedDensity η v θ y = ∑ z : Bool, markedDensity η v θ z y := by
  simp [erasedDensity, markedDensity, markMass, add_comm]

/-- Differentiate the Gaussian density with respect to its mean parameter. -/
theorem gaussianPDFReal_mean_hasDerivAt (v : ℝ≥0) (hv : v ≠ 0) (θ y : ℝ) :
    HasDerivAt (fun t ↦ gaussianPDFReal t v y)
      (((y - θ) / v) * gaussianPDFReal θ v y) θ := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h := (((((hasDerivAt_const θ y).sub (hasDerivAt_id θ)).pow 2).neg).div_const
    (2 * (v : ℝ))).exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  convert h using 1
  dsimp [gaussianPDFReal]
  field_simp
  ring

/-- At the null, erasure makes the density independent of event probability. -/
theorem erasedDensity_null (η : ℝ) (v : ℝ≥0) (y : ℝ) :
    erasedDensity η v 0 y = gaussianPDFReal 0 v y := by
  unfold erasedDensity
  ring

/-- Exact score derivative of the marked log likelihood at the null. -/
theorem marked_log_score (η : ℝ) (hη : 0 < η ∧ η < 1) (v : ℝ≥0)
    (hv : v ≠ 0) (z : Bool) (y : ℝ) :
    HasDerivAt (fun θ ↦ Real.log (markedDensity η v θ z y))
      (if z then y / v else 0) 0 := by
  cases z
  · simpa only [markedDensity, markMass, Bool.false_eq_true, ↓reduceIte] using
      hasDerivAt_const (0 : ℝ) (Real.log ((1 - η) * gaussianPDFReal 0 v y))
  · have h := (gaussianPDFReal_mean_hasDerivAt v hv 0 y).const_mul η
    have hp : η * gaussianPDFReal 0 v y ≠ 0 :=
      mul_ne_zero hη.1.ne' (gaussianPDFReal_pos 0 v y hv).ne'
    have hl := h.log hp
    convert hl using 1
    simp only [↓reduceIte, sub_zero]
    have hpdf := (gaussianPDFReal_pos 0 v y hv).ne'
    have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    field_simp [hη.1.ne', hpdf, hv']

/-- Exact score derivative after the event mark has been erased. -/
theorem erased_log_score (η : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (y : ℝ) :
    HasDerivAt (fun θ ↦ Real.log (erasedDensity η v θ y)) (η * y / v) 0 := by
  have h := (hasDerivAt_const (0 : ℝ) ((1 - η) * gaussianPDFReal 0 v y)).add
    ((gaussianPDFReal_mean_hasDerivAt v hv 0 y).const_mul η)
  have hp : (1 - η) * gaussianPDFReal 0 v y + η * gaussianPDFReal 0 v y ≠ 0 := by
    convert (gaussianPDFReal_pos 0 v y hv).ne' using 1
    ring
  have hl := h.log hp
  convert hl using 1
  have hpdf : gaussianPDFReal 0 v y ≠ 0 := (gaussianPDFReal_pos 0 v y hv).ne'
  have heq : (1 - η) * gaussianPDFReal 0 v y + η * gaussianPDFReal 0 v y =
      gaussianPDFReal 0 v y := by ring
  simp only [Pi.add_apply, sub_zero, zero_add]
  rw [heq]
  field_simp

/-- The centered Gaussian second moment, extracted from its proved variance. -/
theorem gaussian_null_second_moment (v : ℝ≥0) :
    (∫ y : ℝ, y ^ 2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal, sub_zero] using h

theorem gaussian_scaled_second_moment (v : ℝ≥0) (c : ℝ) :
    (∫ y : ℝ, (c * y) ^ 2 ∂gaussianReal 0 v) = c ^ 2 * v := by
  simp only [mul_pow, integral_const_mul, gaussian_null_second_moment]

/-- Exact expectation in the marked Gaussian experiment, retaining the event draw. -/
noncomputable def experimentExpectation (η : ℝ) (v : ℝ≥0) (θ : ℝ)
    (h : Bool → ℝ → ℝ) : ℝ :=
  (1 - η) * (∫ y, h false y ∂gaussianReal 0 v) +
    η * (∫ y, h true y ∂gaussianReal θ v)

/-- Probability measure of the full marked experiment before erasing the mark. -/
noncomputable def experimentLaw (η : ℝ) (v : ℝ≥0) (θ : ℝ) : Measure (Bool × ℝ) :=
  ENNReal.ofReal (1 - η) • (gaussianReal 0 v).map (fun y ↦ (false, y)) +
    ENNReal.ofReal η • (gaussianReal θ v).map (fun y ↦ (true, y))

theorem experimentLaw_probability (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1)
    (v : ℝ≥0) (θ : ℝ) : IsProbabilityMeasure (experimentLaw η v θ) := by
  have hm0 : Measurable (fun y : ℝ ↦ (false, y)) := by fun_prop
  have hm1 : Measurable (fun y : ℝ ↦ (true, y)) := by fun_prop
  constructor
  simp only [experimentLaw, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply hm0 MeasurableSet.univ, Measure.map_apply hm1 MeasurableSet.univ,
    Set.preimage_univ, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hη.2) hη.1]
  norm_num

/-- The explicit mixture expectation is the integral under the actual experiment law. -/
theorem experimentExpectation_eq_integral (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1)
    (v : ℝ≥0) (θ : ℝ) (h : Bool → ℝ → ℝ)
    (hh : Measurable (fun zy : Bool × ℝ ↦ h zy.1 zy.2))
    (h0 : Integrable (h false) (gaussianReal 0 v))
    (h1 : Integrable (h true) (gaussianReal θ v)) :
    experimentExpectation η v θ h =
      ∫ zy, h zy.1 zy.2 ∂experimentLaw η v θ := by
  have hm0 : Measurable (fun y : ℝ ↦ (false, y)) := by fun_prop
  have hm1 : Measurable (fun y : ℝ ↦ (true, y)) := by fun_prop
  have hi0 : Integrable (fun zy : Bool × ℝ ↦ h zy.1 zy.2)
      ((gaussianReal 0 v).map (fun y ↦ (false, y))) :=
    (integrable_map_measure hh.aestronglyMeasurable hm0.aemeasurable).mpr h0
  have hi1 : Integrable (fun zy : Bool × ℝ ↦ h zy.1 zy.2)
      ((gaussianReal θ v).map (fun y ↦ (true, y))) :=
    (integrable_map_measure hh.aestronglyMeasurable hm1.aemeasurable).mpr h1
  rw [experimentLaw, integral_add_measure (hi0.smul_measure ENNReal.ofReal_ne_top)
    (hi1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_map hm0.aemeasurable hh.aestronglyMeasurable,
    integral_map hm1.aemeasurable hh.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr hη.2), ENNReal.toReal_ofReal hη.1,
    smul_eq_mul]
  rfl

/-- Null Fisher information with the event mark observed. -/
theorem marked_fisher_information (η : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    experimentExpectation η v 0 (fun z y ↦ (if z then y / v else 0) ^ 2) = η / v := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hs : (∫ y : ℝ, (y / v) ^ 2 ∂gaussianReal 0 v) = 1 / v := by
    have h := gaussian_scaled_second_moment v (1 / v)
    simp only [one_div, ← div_eq_inv_mul] at h
    rw [h]
    field_simp
  simp [experimentExpectation, hs]
  ring

/-- Null Fisher information when the event mark is hidden. -/
theorem erased_fisher_information (η : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    experimentExpectation η v 0 (fun _ y ↦ (η * y / v) ^ 2) = η ^ 2 / v := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hs : (∫ y : ℝ, (η * y / v) ^ 2 ∂gaussianReal 0 v) = η ^ 2 / v := by
    calc
      _ = ∫ y : ℝ, ((η / v) * y) ^ 2 ∂gaussianReal 0 v := by
        apply integral_congr_ae
        filter_upwards [] with y
        congr 1
        ring
      _ = _ := by rw [gaussian_scaled_second_moment]; field_simp
  simp only [experimentExpectation, hs]
  ring

private theorem gaussian_score_sq_integrable (v : ℝ≥0) (c : ℝ) :
    Integrable (fun y : ℝ ↦ (c * y) ^ 2) (gaussianReal 0 v) := by
  exact ((memLp_id_gaussianReal (μ := 0) (v := v) 2).const_mul c).integrable_sq

/-- Fisher information as the integral of the derived marked log-likelihood score. -/
theorem marked_fisher_integral (η : ℝ) (hη : 0 < η ∧ η < 1)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ zy : Bool × ℝ, (deriv (fun θ ↦ Real.log
      (markedDensity η v θ zy.1 zy.2)) 0) ^ 2 ∂experimentLaw η v 0) = η / v := by
  simp_rw [(marked_log_score η hη v hv _ _).deriv]
  rw [← experimentExpectation_eq_integral η ⟨hη.1.le, hη.2.le⟩ v 0
    (fun z y ↦ (if z then y / v else 0) ^ 2)]
  · exact marked_fisher_information η v hv
  · exact (Measurable.ite ((measurableSet_singleton true).preimage measurable_fst)
      (measurable_snd.div_const _) measurable_const).pow_const 2
  · simp
  · simpa [div_eq_mul_inv, mul_comm] using gaussian_score_sq_integrable v (1 / v)

/-- Erased Fisher information uses the actual marginal outcome measure. -/
theorem erased_fisher_integral (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ y : ℝ, (deriv (fun θ ↦ Real.log (erasedDensity η v θ y)) 0) ^ 2
      ∂(experimentLaw η v 0).map Prod.snd) = η ^ 2 / v := by
  simp_rw [(erased_log_score η v hv _).deriv]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [← experimentExpectation_eq_integral η hη v 0 (fun _ y ↦ (η * y / v) ^ 2)]
  · exact erased_fisher_information η v hv
  · fun_prop
  all_goals
    convert gaussian_score_sq_integrable v (η / v) using 1
    funext y
    ring

/-- Inverse-probability estimation with observed event support is exactly unbiased. -/
theorem marked_estimator_unbiased (η : ℝ) (hη : η ≠ 0) (v : ℝ≥0) (θ : ℝ) :
    experimentExpectation η v θ (fun z y ↦ if z then y / η else 0) = θ := by
  simp [experimentExpectation, integral_div, integral_id_gaussianReal]
  field_simp

/-- Erasing the event does not prevent unbiased estimation when its rate is known. -/
theorem erased_estimator_unbiased (η : ℝ) (hη : η ≠ 0) (v : ℝ≥0) (θ : ℝ) :
    experimentExpectation η v θ (fun _ y ↦ y / η) = θ := by
  simp [experimentExpectation, integral_div, integral_id_gaussianReal]
  field_simp

/-- At the null, the marked unbiased estimator has variance v/η. -/
theorem marked_estimator_null_second_moment (η : ℝ) (hη : η ≠ 0) (v : ℝ≥0) :
    experimentExpectation η v 0 (fun z y ↦ (if z then y / η else 0) ^ 2) = v / η := by
  have hs : (∫ y : ℝ, (y / η) ^ 2 ∂gaussianReal 0 v) = v / η ^ 2 := by
    have h := gaussian_scaled_second_moment v (1 / η)
    simpa [div_eq_mul_inv, mul_comm] using h
  simp [experimentExpectation, hs]
  field_simp

/-- At the null, the erased unbiased estimator has variance v/η². -/
theorem erased_estimator_null_second_moment (η : ℝ) (v : ℝ≥0) :
    experimentExpectation η v 0 (fun _ y ↦ (y / η) ^ 2) = v / η ^ 2 := by
  have hs : (∫ y : ℝ, (y / η) ^ 2 ∂gaussianReal 0 v) = v / η ^ 2 := by
    have h := gaussian_scaled_second_moment v (1 / η)
    simpa [div_eq_mul_inv, mul_comm] using h
  rw [experimentExpectation, hs]
  ring

/-- Partial independent observation of marks interpolates the two derived informations. -/
theorem partial_label_information (η q : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    q * experimentExpectation η v 0 (fun z y ↦ (if z then y / v else 0) ^ 2) +
      (1 - q) * experimentExpectation η v 0 (fun _ y ↦ (η * y / v) ^ 2) =
      (q * η + (1 - q) * η ^ 2) / v := by
  rw [marked_fisher_information η v hv, erased_fisher_information η v hv]
  ring

end Descent.Portability.RareEventInformationLaw
