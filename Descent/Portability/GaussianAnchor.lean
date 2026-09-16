/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Conditionals.DriftingConditional

assert_below Descent.Decision Descent.Program

/-!
# The closed-form anchor under a Gaussian conditional law

`MarginalAnchor` defines the intercept by the anchoring equation on any declared law.
When the conditional law of the score is Gaussian the equation has a closed form, and it
is the closed form the marginal-slope kernels implement.  The corpus's
`Conditionals.gaussianAverage_probit` is the standard-normal case,
`E[Φ(α + βz)] = Φ(α / √(1 + β²))`, which is what makes `q` the marginal index when
`z ∣ context ∼ N(0, 1)`.  This module extends it to a conditional law `N(μ, σ²)` with
any mean and variance and reads off the anchored intercept:

* `gaussianAverage_probit_general`:
  `E_{z ∼ N(μ, σ²)}[Φ(α + b z)] = Φ((α + b μ) / √(1 + b² σ²))`.
* `gaussian_anchor_closed_form`: the intercept `α = q √(1 + b² σ²) − b μ` makes the
  anchored mean equal to `Φ(q)`.
* `gaussian_anchor_unique`: no other intercept does.

So a score that is Gaussian but not standard given the context does not break marginal
anchoring; it changes the intercept by exactly `q(√(1 + b²σ²) − √(1 + b²)) − bμ`, and a
fit that uses the standard-normal form for such a score puts that quantity into its
baseline.  Which conditional law holds is not decided here.

Builds on `Conditionals.gaussianAverage_probit`, `Foundations.Phi`,
`Foundations.strictMono_Phi` and Mathlib's Gaussian pushforward lemmas.

## Empirical status

None. A Gaussian integral is an identity; whether a score's conditional law is Gaussian
is a property of data this module does not see.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianAnchor

open MeasureTheory ProbabilityTheory Foundations

noncomputable section

/-- `N(m, v)` is the pushforward of `N(0, 1)` under `u ↦ √v · u + m`. -/
theorem gaussianReal_eq_map_affine (m : ℝ) (v : NNReal) :
    gaussianReal m v = (gaussianReal 0 1).map (fun u ↦ Real.sqrt (v : ℝ) * u + m) := by
  have hsq : (⟨Real.sqrt (v : ℝ) ^ 2, sq_nonneg _⟩ : NNReal) * 1 = v := by
    ext
    simp [Real.sq_sqrt v.coe_nonneg]
  have hscale :=
    gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) (Real.sqrt (v : ℝ))
  rw [mul_zero, hsq] at hscale
  have hshift := gaussianReal_map_add_const (μ := (0 : ℝ)) (v := v) m
  rw [zero_add] at hshift
  rw [← hshift, ← hscale, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **Gaussian averaging under a non-standard conditional law.**
`E_{z ∼ N(m, v)}[Φ(α + b z)] = Φ((α + b m) / √(1 + b² v))`. -/
theorem gaussianAverage_probit_general (α b m : ℝ) (v : NNReal) :
    ∫ z, Phi (α + b * z) ∂(gaussianReal m v)
      = Phi ((α + b * m) / Real.sqrt (1 + b ^ 2 * (v : ℝ))) := by
  have hmeas : Measurable fun u : ℝ ↦ Real.sqrt (v : ℝ) * u + m := by fun_prop
  have hcont : Continuous fun z : ℝ ↦ Phi (α + b * z) :=
    continuous_Phi.comp (by fun_prop : Continuous fun z : ℝ ↦ α + b * z)
  rw [gaussianReal_eq_map_affine m v, integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
  have hre : (fun u ↦ Phi (α + b * (Real.sqrt (v : ℝ) * u + m)))
      = fun u ↦ Phi ((α + b * m) + (b * Real.sqrt (v : ℝ)) * u) := by
    funext u
    congr 1
    ring
  rw [hre, Conditionals.gaussianAverage_probit]
  congr 1
  rw [mul_pow, Real.sq_sqrt v.coe_nonneg]

/-- **The closed-form anchor.**  Under `z ∼ N(m, v)` the intercept `q √(1 + b² v) − b m`
makes the anchored mean equal to `Φ(q)`. -/
theorem gaussian_anchor_closed_form (q b m : ℝ) (v : NNReal) :
    ∫ z, Phi ((q * Real.sqrt (1 + b ^ 2 * (v : ℝ)) - b * m) + b * z) ∂(gaussianReal m v)
      = Phi q := by
  rw [gaussianAverage_probit_general]
  congr 1
  have hpos : 0 < Real.sqrt (1 + b ^ 2 * (v : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  field_simp
  ring

/-- **The closed-form anchor is the only one.**  Any intercept whose anchored mean is
`Φ(q)` under `z ∼ N(m, v)` equals `q √(1 + b² v) − b m`. -/
theorem gaussian_anchor_unique (q b m α : ℝ) (v : NNReal)
    (hα : ∫ z, Phi (α + b * z) ∂(gaussianReal m v) = Phi q) :
    α = q * Real.sqrt (1 + b ^ 2 * (v : ℝ)) - b * m := by
  rw [gaussianAverage_probit_general] at hα
  have hpos : 0 < Real.sqrt (1 + b ^ 2 * (v : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hratio : (α + b * m) / Real.sqrt (1 + b ^ 2 * (v : ℝ)) = q := strictMono_Phi.injective hα
  rw [div_eq_iff hpos.ne'] at hratio
  linarith

/-! ### Only the law of the drive matters -/

/-- **Gaussian averaging through the drive.**  Under any declared law `ν` on any predictor
space, if the genetic drive `g` is Gaussian with mean `m` and variance `s`, then
`E_ν[Φ(α + g)] = Φ((α + m) / √(1 + s))`.  For a vector of scores `z` with drive `bᵀz`
and Gaussian `z`, `m = bᵀμ` and `s = bᵀΣb`; nothing about the individual scores beyond
the law of that one linear combination enters. -/
theorem drive_gaussianAverage {X : Type*} [MeasurableSpace X] (ν : Measure X) (g : X → ℝ)
    (hg : AEMeasurable g ν) (m : ℝ) (s : NNReal) (hlaw : ν.map g = gaussianReal m s)
    (α : ℝ) :
    ∫ x, Phi (α + g x) ∂ν = Phi ((α + m) / Real.sqrt (1 + (s : ℝ))) := by
  have hcont : Continuous fun z : ℝ ↦ Phi (α + 1 * z) :=
    continuous_Phi.comp (by fun_prop : Continuous fun z : ℝ ↦ α + 1 * z)
  have h := gaussianAverage_probit_general α 1 m s
  rw [← hlaw, integral_map hg hcont.aestronglyMeasurable] at h
  simpa using h

/-- **The closed-form anchor through the drive**: `q √(1 + s) − m` anchors a Gaussian drive
of mean `m` and variance `s` at `Φ(q)`. -/
theorem drive_anchor_closed_form {X : Type*} [MeasurableSpace X] (ν : Measure X) (g : X → ℝ)
    (hg : AEMeasurable g ν) (m : ℝ) (s : NNReal) (hlaw : ν.map g = gaussianReal m s) (q : ℝ) :
    ∫ x, Phi ((q * Real.sqrt (1 + (s : ℝ)) - m) + g x) ∂ν = Phi q := by
  rw [drive_gaussianAverage ν g hg m s hlaw]
  congr 1
  have hpos : 0 < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  field_simp
  ring

/-- **And it is the only one.** -/
theorem drive_anchor_unique {X : Type*} [MeasurableSpace X] (ν : Measure X) (g : X → ℝ)
    (hg : AEMeasurable g ν) (m : ℝ) (s : NNReal) (hlaw : ν.map g = gaussianReal m s)
    (q α : ℝ)
    (hα : ∫ x, Phi (α + g x) ∂ν = Phi q) :
    α = q * Real.sqrt (1 + (s : ℝ)) - m := by
  rw [drive_gaussianAverage ν g hg m s hlaw] at hα
  have hpos : 0 < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hratio : (α + m) / Real.sqrt (1 + (s : ℝ)) = q := strictMono_Phi.injective hα
  rw [div_eq_iff hpos.ne'] at hratio
  linarith

end

end Descent.Portability.GaussianAnchor
