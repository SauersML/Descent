/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarginalAnchor
import Descent.Foundations.Probability
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

assert_below Descent.Decision Descent.Program

/-!
# The probit link satisfies the anchor's hypotheses

`MarginalAnchor` states the anchoring theorems for any link that is continuous,
strictly increasing, tends to `0` and `1`, and has a derivative.  The marginal-slope
kernels use the probit link, the corpus's `Foundations.Phi = cdf (gaussianReal 0 1)`,
which `Foundations` already shows continuous and strictly increasing.  This module adds
the two facts it lacks -- the limits, from those of any distribution function, and
`Φ' = φ` with `φ = gaussianPDFReal 0 1`, by the fundamental theorem of calculus applied
to the density -- and states the anchor instances:

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

namespace Descent.Portability.ProbitAnchor

open Filter Topology MeasureTheory ProbabilityTheory MarginalAnchor Foundations

noncomputable section

theorem continuous_gaussianPDFReal_std : Continuous (gaussianPDFReal 0 1) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-- `Φ` is the integral of the standard normal density over the lower half-line. -/
theorem Phi_eq_integral (x : ℝ) : Phi x = ∫ t in Set.Iic x, gaussianPDFReal 0 1 t := by
  unfold Phi
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Iic fun t _ ↦ (gaussianPDFReal_pos 0 1 t one_ne_zero).le

theorem tendsto_Phi_atTop : Tendsto Phi atTop (𝓝 1) :=
  tendsto_cdf_atTop (gaussianReal 0 1)

theorem tendsto_Phi_atBot : Tendsto Phi atBot (𝓝 0) :=
  tendsto_cdf_atBot (gaussianReal 0 1)

/-- **`Φ' = φ`.** -/
theorem hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (gaussianPDFReal 0 1 x) x := by
  have hint : ∀ u : ℝ, Phi u = Phi 0 + ∫ t in (0 : ℝ)..u, gaussianPDFReal 0 1 t := by
    intro u
    rw [Phi_eq_integral, Phi_eq_integral,
      ← intervalIntegral.integral_Iic_sub_Iic (integrable_gaussianPDFReal 0 1).integrableOn
        (integrable_gaussianPDFReal 0 1).integrableOn]
    ring
  have hfun : Phi = fun u ↦ Phi 0 + ∫ t in (0 : ℝ)..u, gaussianPDFReal 0 1 t := funext hint
  rw [hfun]
  exact (intervalIntegral.integral_hasDerivAt_right
    (integrable_gaussianPDFReal 0 1).intervalIntegrable
    (continuous_gaussianPDFReal_std.stronglyMeasurableAtFilter _ _)
    continuous_gaussianPDFReal_std.continuousAt).const_add (Phi 0)

theorem gaussianPDFReal_std_pos (x : ℝ) : 0 < gaussianPDFReal 0 1 x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

variable {V : Type*} [Fintype V]

/-- **The probit anchor exists and is unique** on any finite declared law. -/
theorem exists_unique_anchor_probit (p : FiniteReportLaw V) (h : V → ℝ) {π : ℝ}
    (hπ0 : 0 < π) (hπ1 : π < 1) :
    ∃! a : ℝ, anchoredMean Phi p h a = π :=
  exists_unique_anchor continuous_Phi strictMono_Phi tendsto_Phi_atBot tendsto_Phi_atTop p h
    hπ0 hπ1

/-- **The probit anchor's derivative** is the negated `φ`-weighted mean of the
predictor-shape derivative. -/
theorem anchor_deriv_eq_probit (p : FiniteReportLaw V) (a : ℝ → ℝ) (h : ℝ → V → ℝ)
    {π θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean Phi p (h t) (a t) = π) :
    a' = -(∑ v, p.mass v * gaussianPDFReal 0 1 (a θ + h θ v) * h' v)
      / (∑ v, p.mass v * gaussianPDFReal 0 1 (a θ + h θ v)) :=
  anchor_deriv_eq hasDerivAt_Phi gaussianPDFReal_std_pos p a h ha hh hanchor

/-- **Orthogonality of baseline and predictor shape under the probit link**, in the
`φ`-weighted metric the anchor induces. -/
theorem crossInformation_baseline_shape_zero_probit (p : FiniteReportLaw V) (a : ℝ → ℝ)
    (h : ℝ → V → ℝ) {π θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean Phi p (h t) (a t) = π) (c : ℝ) :
    crossInformation (gaussianPDFReal 0 1) p (fun v ↦ a θ + h θ v) (fun _ ↦ c)
      (fun v ↦ a' + h' v) = 0 :=
  crossInformation_baseline_shape_zero hasDerivAt_Phi p a h ha hh hanchor c

end

end Descent.Portability.ProbitAnchor
