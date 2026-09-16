/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarginalAnchor
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

assert_below Descent.Decision Descent.Program

/-!
# The probit link satisfies the anchor's hypotheses

`MarginalAnchor` states the anchoring theorems for any link that is continuous,
strictly increasing, tends to `0` and `1`, and has a derivative.  The marginal-slope
kernels use the probit link, the standard normal distribution function
`Φ = cdf (gaussianReal 0 1)`.  This module supplies its four facts from Mathlib's
Gaussian measure -- `Φ' = φ` by the fundamental theorem of calculus applied to the
density, strict monotonicity from `φ > 0`, continuity from differentiability, the
limits from those of any distribution function -- and states the anchor instances:

* `exists_unique_anchor_probit`: the probit anchoring equation
  `E_p[Φ(a + h(v))] = π` has exactly one solution on any finite declared law.
* `anchor_deriv_eq_probit`: `a' = −E_p[φ h'] / E_p[φ]`.
* `crossInformation_baseline_shape_zero_probit`: the `φ`-weighted cross-information
  between the constant baseline direction and the anchored shape direction is zero.

For the probit link the weight `φ(η)` is the link derivative, not the Bernoulli Fisher
weight `φ(η)² / (Φ(η)(1 − Φ(η)))`; the third statement is the orthogonality of the two
score directions in the link-weighted metric the anchor itself induces.

## Empirical status

None. These are properties of the standard normal distribution function and of the
specified model under a specified law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ProbitAnchor

open Filter Topology MeasureTheory ProbabilityTheory MarginalAnchor

noncomputable section

/-- The probit link: the standard normal distribution function. -/
def probit (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The standard normal density. -/
def normalDensity (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

theorem normalDensity_pos (x : ℝ) : 0 < normalDensity x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

theorem continuous_normalDensity : Continuous normalDensity := by
  unfold normalDensity
  rw [gaussianPDFReal_def]
  fun_prop

theorem integrable_normalDensity : Integrable normalDensity :=
  integrable_gaussianPDFReal 0 1

/-- The probit link is the integral of the density over the lower half-line. -/
theorem probit_eq_integral (x : ℝ) : probit x = ∫ t in Set.Iic x, normalDensity t := by
  unfold probit normalDensity
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Iic fun t _ ↦ (gaussianPDFReal_pos 0 1 t one_ne_zero).le

theorem tendsto_probit_atTop : Tendsto probit atTop (𝓝 1) :=
  tendsto_cdf_atTop (gaussianReal 0 1)

theorem tendsto_probit_atBot : Tendsto probit atBot (𝓝 0) :=
  tendsto_cdf_atBot (gaussianReal 0 1)

/-- **`Φ' = φ`.** -/
theorem hasDerivAt_probit (x : ℝ) : HasDerivAt probit (normalDensity x) x := by
  have hint : ∀ u : ℝ, probit u = probit 0 + ∫ t in (0 : ℝ)..u, normalDensity t := by
    intro u
    rw [probit_eq_integral, probit_eq_integral,
      ← intervalIntegral.integral_Iic_sub_Iic integrable_normalDensity.integrableOn
        integrable_normalDensity.integrableOn]
    ring
  have hfun : probit = fun u ↦ probit 0 + ∫ t in (0 : ℝ)..u, normalDensity t := funext hint
  rw [hfun]
  refine (intervalIntegral.integral_hasDerivAt_right
    integrable_normalDensity.intervalIntegrable
    (continuous_normalDensity.stronglyMeasurableAtFilter _ _)
    continuous_normalDensity.continuousAt).const_add (probit 0)

theorem continuous_probit : Continuous probit :=
  continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_probit x).continuousAt

theorem probit_strictMono : StrictMono probit :=
  strictMono_of_deriv_pos fun x ↦ by
    rw [(hasDerivAt_probit x).deriv]
    exact normalDensity_pos x

variable {V : Type*} [Fintype V]

/-- **The probit anchor exists and is unique** on any finite declared law. -/
theorem exists_unique_anchor_probit (p : FiniteReportLaw V) (h : V → ℝ) {π : ℝ}
    (hπ0 : 0 < π) (hπ1 : π < 1) :
    ∃! a : ℝ, anchoredMean probit p h a = π :=
  exists_unique_anchor continuous_probit probit_strictMono tendsto_probit_atBot
    tendsto_probit_atTop p h hπ0 hπ1

/-- **The probit anchor's derivative** is the negated `φ`-weighted mean of the
predictor-shape derivative. -/
theorem anchor_deriv_eq_probit (p : FiniteReportLaw V) (a : ℝ → ℝ) (h : ℝ → V → ℝ)
    {π θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean probit p (h t) (a t) = π) :
    a' = -(∑ v, p.mass v * normalDensity (a θ + h θ v) * h' v)
      / (∑ v, p.mass v * normalDensity (a θ + h θ v)) :=
  anchor_deriv_eq hasDerivAt_probit normalDensity_pos p a h ha hh hanchor

/-- **Orthogonality of baseline and predictor shape under the probit link**, in the
`φ`-weighted metric the anchor induces. -/
theorem crossInformation_baseline_shape_zero_probit (p : FiniteReportLaw V) (a : ℝ → ℝ)
    (h : ℝ → V → ℝ) {π θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean probit p (h t) (a t) = π) (c : ℝ) :
    crossInformation normalDensity p (fun v ↦ a θ + h θ v) (fun _ ↦ c)
      (fun v ↦ a' + h' v) = 0 :=
  crossInformation_baseline_shape_zero hasDerivAt_probit p a h ha hh hanchor c

end

end Descent.Portability.ProbitAnchor
