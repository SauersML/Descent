/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EntropyQuadraticFactor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

assert_below Descent.Decision Descent.Program

/-!
A second-order density expansion with a square-integrable dominating function
implies the fourth-order relative-entropy integrand asymptotic. This analytic
bridge derives the entropy limit rather than assuming its Taylor remainder.
Its density expansion and domination premises must still be established for
any particular Gaussian covariance family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EntropyDensityExpansion

open scoped Topology
open Filter MeasureTheory InformationTheory EntropyQuadraticFactor

/-- Exact scaled entropy factorization at every real perturbation, including zero. -/
theorem scaled_factorization (r ε : ℝ) :
    klFun r / ε ^ 4 = quadraticFactor r * ((r - 1) / ε ^ 2) ^ 2 := by
  rw [klFun_factorization, div_pow, ← pow_mul]
  norm_num
  ring

/-- The second-order relative density coefficient gives the pointwise fourth-order entropy limit. -/
theorem pointwise_quartic_limit (r : ℝ → ℝ) (h : ℝ)
    (hr : Tendsto (fun ε ↦ (r ε - 1) / ε ^ 2) (𝓝[≠] 0) (𝓝 h)) :
    Tendsto (fun ε ↦ klFun (r ε) / ε ^ 4) (𝓝[≠] 0) (𝓝 ((1 / 2 : ℝ) * h ^ 2)) := by
  have he : Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have hh := (continuousAt_id.tendsto : Tendsto (fun ε : ℝ ↦ ε) (𝓝 0) (𝓝 0)).pow 2
    simpa using hh.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hd : Tendsto (fun ε ↦ r ε - 1) (𝓝[≠] 0) (𝓝 0) := by
    have hh := hr.mul he
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_mul_cancel₀ _ (pow_ne_zero _ hε)
  have hto : Tendsto r (𝓝[≠] 0) (𝓝 1) := by
    simpa using hd.add_const 1
  have hh := (quadraticFactor_continuousAt_one.tendsto.comp hto).mul (hr.pow 2)
  simpa only [scaled_factorization, quadraticFactor, if_true] using hh

/-- Global chi-square domination also controls the scaled entropy integrand. -/
theorem scaled_entropy_bound (r ε H : ℝ) (hr : 0 ≤ r) (hH : |(r - 1) / ε ^ 2| ≤ H) :
    ‖klFun r / ε ^ 4‖ ≤ H ^ 2 := by
  rw [scaled_factorization, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (quadraticFactor_bounds r hr).1, abs_of_nonneg (sq_nonneg _)]
  have hs : ((r - 1) / ε ^ 2) ^ 2 ≤ H ^ 2 := by
    have hp := abs_nonneg ((r - 1) / ε ^ 2)
    nlinarith [sq_abs ((r - 1) / ε ^ 2)]
  exact (mul_le_mul_of_nonneg_right (quadraticFactor_bounds r hr).2 (sq_nonneg _)).trans
    (by simpa using hs)

/-- Dominated density coefficients justify the fourth-order integral asymptotic. -/
theorem entropy_integral_quartic_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (r : ℝ → Ω → ℝ) (h H : Ω → ℝ)
    (hmeas : ∀ᶠ ε in 𝓝[≠] 0, AEStronglyMeasurable (r ε) μ)
    (hpos : ∀ᶠ ε in 𝓝[≠] 0, ∀ᵐ x ∂μ, 0 ≤ r ε x)
    (hdom : ∀ᶠ ε in 𝓝[≠] 0, ∀ᵐ x ∂μ, |(r ε x - 1) / ε ^ 2| ≤ H x)
    (hH : Integrable (fun x ↦ H x ^ 2) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun ε ↦ (r ε x - 1) / ε ^ 2) (𝓝[≠] 0) (𝓝 (h x))) :
    Tendsto (fun ε ↦ (∫ x, klFun (r ε x) ∂μ) / ε ^ 4) (𝓝[≠] 0)
      (𝓝 ((1 / 2 : ℝ) * ∫ x, h x ^ 2 ∂μ)) := by
  have hh : Tendsto (fun ε ↦ ∫ x, klFun (r ε x) / ε ^ 4 ∂μ) (𝓝[≠] 0)
      (𝓝 (∫ x, (1 / 2 : ℝ) * h x ^ 2 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ H x ^ 2)
    · filter_upwards [hmeas] with ε hm
      have hh := (continuous_klFun.comp_aestronglyMeasurable hm).aemeasurable.div_const (ε ^ 4)
      exact hh.aestronglyMeasurable
    · filter_upwards [hpos, hdom] with ε hp hd
      filter_upwards [hp, hd] with x hp hd
      exact scaled_entropy_bound _ _ _ hp hd
    · exact hH
    · filter_upwards [hlim] with x hx
      exact pointwise_quartic_limit _ _ hx
  simpa only [integral_div, integral_const_mul] using hh

end Descent.Portability.EntropyDensityExpansion
