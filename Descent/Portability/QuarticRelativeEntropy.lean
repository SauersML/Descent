/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DensityRelativeEntropy
import Descent.Portability.EntropyDensityExpansion

assert_below Descent.Decision Descent.Program

/-!
The fourth-order asymptotic of the standard KL divergence follows from a
normalized second-order density expansion with square-integrable domination.
The theorem proves eventual finiteness as well as the limit. It is the analytic
bridge needed by the Gaussian order-erasure example; the family-specific
expansion and domination are explicit hypotheses, not claimed completed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.QuarticRelativeEntropy

open scoped Topology ENNReal
open Filter MeasureTheory InformationTheory DensityRelativeEntropy EntropyDensityExpansion

/-- A bound on a nonzero scaled density perturbation bounds its actual square. -/
theorem perturbation_square_bound (r ε H : ℝ) (hε : ε ≠ 0)
    (hH : |(r - 1) / ε ^ 2| ≤ H) : (r - 1) ^ 2 ≤ ε ^ 4 * H ^ 2 := by
  have hs : ((r - 1) / ε ^ 2) ^ 2 ≤ H ^ 2 := by
    have hp := abs_nonneg ((r - 1) / ε ^ 2)
    nlinarith [sq_abs ((r - 1) / ε ^ 2)]
  have he : (r - 1) ^ 2 = ε ^ 4 * ((r - 1) / ε ^ 2) ^ 2 := by
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- The scaled dominating function gives square integrability at each nonzero perturbation. -/
theorem perturbation_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (r H : Ω → ℝ) (ε : ℝ) (hε : ε ≠ 0)
    (hr : AEStronglyMeasurable r μ)
    (hdom : ∀ᵐ x ∂μ, |(r x - 1) / ε ^ 2| ≤ H x)
    (hH : Integrable (fun x ↦ H x ^ 2) μ) :
    Integrable (fun x ↦ (r x - 1) ^ 2) μ := by
  apply (hH.const_mul (ε ^ 4)).mono'
    ((hr.aemeasurable.sub_const 1).pow_const 2).aestronglyMeasurable
  filter_upwards [hdom] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact perturbation_square_bound _ _ _ hε hx

/-- Actual KL divergence is eventually finite and has the derived fourth-order limit. -/
theorem klDiv_quartic_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (r : ℝ → Ω → ℝ) (h H : Ω → ℝ)
    (hmeas : ∀ᶠ ε in 𝓝[≠] 0, Measurable (r ε))
    (hint : ∀ᶠ ε in 𝓝[≠] 0, Integrable (r ε) μ)
    (hpos : ∀ᶠ ε in 𝓝[≠] 0, ∀ᵐ x ∂μ, 0 ≤ r ε x)
    (hnorm : ∀ᶠ ε in 𝓝[≠] 0, (∫ x, r ε x ∂μ) = 1)
    (hdom : ∀ᶠ ε in 𝓝[≠] 0, ∀ᵐ x ∂μ, |(r ε x - 1) / ε ^ 2| ≤ H x)
    (hH : Integrable (fun x ↦ H x ^ 2) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun ε ↦ (r ε x - 1) / ε ^ 2) (𝓝[≠] 0) (𝓝 (h x))) :
    (∀ᶠ ε in 𝓝[≠] 0, klDiv (densityLaw μ (r ε)) μ ≠ ∞) ∧
      Tendsto (fun ε ↦ (klDiv (densityLaw μ (r ε)) μ).toReal / ε ^ 4) (𝓝[≠] 0)
        (𝓝 ((1 / 2 : ℝ) * ∫ x, h x ^ 2 ∂μ)) := by
  have hs : ∀ᶠ ε in 𝓝[≠] 0, Integrable (fun x ↦ (r ε x - 1) ^ 2) μ := by
    filter_upwards [hmeas, hdom, self_mem_nhdsWithin] with ε hm hd hε
    exact perturbation_square_integrable μ _ H ε hε hm.aestronglyMeasurable hd hH
  constructor
  · filter_upwards [hmeas, hint, hpos, hnorm, hs] with ε hm hi hp hn hs
    exact densityLaw_klDiv_ne_top μ _ hm hi hp hn hs
  · have hh := entropy_integral_quartic_limit μ r h H
      (hmeas.mono (fun _ hm ↦ hm.aestronglyMeasurable)) hpos hdom hH hlim
    apply hh.congr'
    filter_upwards [hmeas, hint, hpos, hnorm, hs] with ε hm hi hp hn hs
    rw [densityLaw_klDiv_toReal μ _ hm hi hp hn hs]

end Descent.Portability.QuarticRelativeEntropy
