/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EntropyQuadraticFactor
import Mathlib.InformationTheory.KullbackLeibler.Basic

assert_below Descent.Decision Descent.Program

/-!
Normalized nonnegative densities define actual probability measures. Finite
chi-square integral supplies integrability of the entropy integrand, and the
Radon-Nikodym derivative identifies its integral with Mathlib's KL divergence.
Finiteness is proved explicitly before taking the real value of divergence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DensityRelativeEntropy

open scoped ENNReal
open MeasureTheory InformationTheory EntropyQuadraticFactor

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual measure obtained by changing density relative to the specified reference law. -/
noncomputable def densityLaw (μ : Measure Ω) (r : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (r x))

/-- Integral normalization is exactly normalization of the constructed probability law. -/
theorem densityLaw_probability (μ : Measure Ω) (r : Ω → ℝ)
    (hr : Integrable r μ) (hp : ∀ᵐ x ∂μ, 0 ≤ r x) (hn : (∫ x, r x ∂μ) = 1) :
    IsProbabilityMeasure (densityLaw μ r) := by
  constructor
  rw [densityLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hr hp, hn]
  exact ENNReal.ofReal_one

/-- The real Radon-Nikodym derivative agrees almost surely with the original density. -/
theorem densityLaw_rnDeriv (μ : Measure Ω) [SigmaFinite μ] (r : Ω → ℝ)
    (hr : Measurable r) (hp : ∀ᵐ x ∂μ, 0 ≤ r x) :
    (fun x ↦ ((densityLaw μ r).rnDeriv μ x).toReal) =ᵐ[μ] r := by
  filter_upwards [Measure.rnDeriv_withDensity μ hr.ennreal_ofReal, hp] with x hx hp
  rw [densityLaw, hx, ENNReal.toReal_ofReal hp]

/-- A square-integrable relative density perturbation has an integrable entropy integrand. -/
theorem klFun_integrable_of_square (μ : Measure Ω) (r : Ω → ℝ)
    (hr : AEStronglyMeasurable r μ) (hp : ∀ᵐ x ∂μ, 0 ≤ r x)
    (hs : Integrable (fun x ↦ (r x - 1) ^ 2) μ) : Integrable (fun x ↦ klFun (r x)) μ := by
  apply hs.mono' (continuous_klFun.comp_aestronglyMeasurable hr)
  filter_upwards [hp] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg hx)]
  exact klFun_le_square _ hx

/-- Standard KL divergence equals the finite entropy integral for the constructed density law. -/
theorem densityLaw_klDiv (μ : Measure Ω) [IsProbabilityMeasure μ] (r : Ω → ℝ)
    (hr : Measurable r) (hi : Integrable r μ) (hp : ∀ᵐ x ∂μ, 0 ≤ r x)
    (hn : (∫ x, r x ∂μ) = 1) (hs : Integrable (fun x ↦ (r x - 1) ^ 2) μ) :
    klDiv (densityLaw μ r) μ = ENNReal.ofReal (∫ x, klFun (r x) ∂μ) := by
  letI := densityLaw_probability μ r hi hp hn
  have ha : densityLaw μ r ≪ μ :=
    withDensity_absolutelyContinuous μ (fun x ↦ ENNReal.ofReal (r x))
  rw [klDiv_eq_lintegral_klFun, if_pos ha]
  have he : (∫⁻ x, ENNReal.ofReal (klFun (((densityLaw μ r).rnDeriv μ x).toReal)) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (klFun (r x)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [densityLaw_rnDeriv μ r hr hp] with x hx
    rw [hx]
  rw [he]
  exact (ofReal_integral_eq_lintegral_ofReal
    (klFun_integrable_of_square μ r hr.aestronglyMeasurable hp hs)
    (hp.mono (fun _ hx ↦ klFun_nonneg hx))).symm

/-- The KL divergence is genuinely finite under the square-integrability hypothesis. -/
theorem densityLaw_klDiv_ne_top (μ : Measure Ω) [IsProbabilityMeasure μ] (r : Ω → ℝ)
    (hr : Measurable r) (hi : Integrable r μ) (hp : ∀ᵐ x ∂μ, 0 ≤ r x)
    (hn : (∫ x, r x ∂μ) = 1) (hs : Integrable (fun x ↦ (r x - 1) ^ 2) μ) :
    klDiv (densityLaw μ r) μ ≠ ∞ := by
  rw [densityLaw_klDiv μ r hr hi hp hn hs]
  exact ENNReal.ofReal_ne_top

/-- The real-valued KL identity follows with explicit finiteness already established. -/
theorem densityLaw_klDiv_toReal (μ : Measure Ω) [IsProbabilityMeasure μ] (r : Ω → ℝ)
    (hr : Measurable r) (hi : Integrable r μ) (hp : ∀ᵐ x ∂μ, 0 ≤ r x)
    (hn : (∫ x, r x ∂μ) = 1) (hs : Integrable (fun x ↦ (r x - 1) ^ 2) μ) :
    (klDiv (densityLaw μ r) μ).toReal = ∫ x, klFun (r x) ∂μ := by
  rw [densityLaw_klDiv μ r hr hi hp hn hs, ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae (hp.mono (fun _ hx ↦ klFun_nonneg hx))

end Descent.Portability.DensityRelativeEntropy
