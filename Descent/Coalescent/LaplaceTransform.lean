/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.HoldingTime
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The clock's Laplace transform, `E(e^{-θτ}) = d/(d+θ)`

K-G (5.9) computes the transit time's density by way of its Laplace transform,

  `E(e^{-θT}) = ∏_{r≥2} d_r/(d_r + θ)`,

and `Descent.Coalescent.Rates.transitDensityTerm` carries the resulting series.  The factor
being multiplied has never been computed in this corpus: `Descent.Coalescent.HoldingTime`
proves the clock's mass and its first moment, and `Descent.Coalescent.HoldingSecondMoment`
its second, but not its transform.

It is one more integral against the same density, and the same rescaling does it: a holding
time of rate `d` weighted by `e^{-θt}` is a holding time of rate `d + θ` scaled by
`d/(d+θ)`.  So

  `∫ e^{-θt} · d e^{-dt} dt = d/(d+θ)`,

which is `integral_exp_neg_mul_holdDensity`.  The lower-integral form is what an independence
argument over infinitely many clocks needs, and `lintegral_exp_neg_holdMeasure` supplies it.

At `θ = 0` it is the mass, at the derivative in `θ` it is the mean; the file states the first
as a check (`integral_exp_neg_mul_holdDensity_zero`) because a transform that failed to
reduce to the mass at zero would be the wrong transform.

## Main results

- `integral_exp_neg_mul_holdDensity`: **`E(e^{-θτ}) = d/(d+θ)`**, K-G (5.9)'s factor.
- `integral_exp_neg_mul_holdDensity_zero`: at `θ = 0` it is the mass, `1`.
- `lintegral_exp_neg_holdMeasure`: the same as a lower integral.
-/

namespace Coalescent

open MeasureTheory Set

/-- The pointwise identity the transform rests on: weighting a rate-`d` clock by `e^{-θt}`
gives a rate-`(d+θ)` clock scaled by `d/(d+θ)`. -/
theorem exp_neg_mul_holdDensity_eq {d θ : ℝ} (hdθ : 0 < d + θ) (t : ℝ) :
    Real.exp (-(θ * t)) * (d * Real.exp (-(d * t)))
      = (d / (d + θ)) * ((d + θ) * Real.exp (-((d + θ) * t))) := by
  have hne : d + θ ≠ 0 := ne_of_gt hdθ
  have h1 : Real.exp (-(θ * t)) * Real.exp (-(d * t)) = Real.exp (-((d + θ) * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : d / (d + θ) * (d + θ) = d := by field_simp
  calc Real.exp (-(θ * t)) * (d * Real.exp (-(d * t)))
      = d * (Real.exp (-(θ * t)) * Real.exp (-(d * t))) := by ring
    _ = d * Real.exp (-((d + θ) * t)) := by rw [h1]
    _ = (d / (d + θ)) * ((d + θ) * Real.exp (-((d + θ) * t))) := by
        rw [← mul_assoc, h2]

/-- **K-G (5.9)'s factor: `E(e^{-θτ}) = d/(d+θ)`.**  Weighting the clock by `e^{-θt}` turns a
rate-`d` holding time into a rate-`(d+θ)` one, scaled by `d/(d+θ)` -- so the transform is the
ratio of the two rates, which is why the transit time's transform is a product of such
ratios. -/
theorem integral_exp_neg_mul_holdDensity {d θ : ℝ} (hd : 0 < d) (hθ : 0 ≤ θ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * (d * Real.exp (-(d * t))) = d / (d + θ) := by
  have hdθ : 0 < d + θ := by linarith
  have hpt : ∀ t : ℝ, Real.exp (-(θ * t)) * (d * Real.exp (-(d * t)))
      = (d / (d + θ)) * ((d + θ) * Real.exp (-((d + θ) * t))) :=
    fun t ↦ exp_neg_mul_holdDensity_eq hdθ t
  calc ∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * (d * Real.exp (-(d * t)))
      = ∫ t in Ioi (0 : ℝ), (d / (d + θ)) * ((d + θ) * Real.exp (-((d + θ) * t))) := by
        exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ hpt t
    _ = (d / (d + θ)) * ∫ t in Ioi (0 : ℝ), (d + θ) * Real.exp (-((d + θ) * t)) := by
        rw [integral_const_mul]
    _ = d / (d + θ) := by
        rw [integral_holdDensity hdθ, mul_one]

/-- At `θ = 0` the transform is the mass, `1` -- the check that it is the right transform. -/
theorem integral_exp_neg_mul_holdDensity_zero {d : ℝ} (hd : 0 < d) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(0 * t)) * (d * Real.exp (-(d * t))) = 1 := by
  rw [integral_exp_neg_mul_holdDensity hd (le_refl 0), add_zero, div_self (ne_of_gt hd)]

/-- The same as a lower integral, which is the form an argument over infinitely many
independent clocks consumes. -/
theorem lintegral_exp_neg_holdMeasure {d θ : ℝ} (hd : 0 < d) (hθ : 0 ≤ θ) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (-(θ * t))) ∂(holdMeasure d)
      = ENNReal.ofReal (d / (d + θ)) := by
  have hdθ : 0 < d + θ := by linarith
  have hmeas : Measurable (holdDensity d) := by
    unfold holdDensity
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    exact (measurable_const.mul ((measurable_const.mul measurable_id).neg.exp)).ennreal_ofReal
  have hexp : Measurable fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-(θ * t))) :=
    ((measurable_const.mul measurable_id).neg.exp).ennreal_ofReal
  have hint : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-(θ * t)) * (d * Real.exp (-(d * t)))) (Ioi (0 : ℝ)) := by
    have hbase : IntegrableOn
        (fun t : ℝ ↦ (d + θ) * Real.exp (-((d + θ) * t))) (Ioi (0 : ℝ)) :=
      holdDensity_integrable hdθ
    have hscaled : IntegrableOn
        (fun t : ℝ ↦ (d / (d + θ)) * ((d + θ) * Real.exp (-((d + θ) * t)))) (Ioi (0 : ℝ)) :=
      hbase.const_mul _
    refine hscaled.congr_fun ?_ measurableSet_Ioi
    intro t _
    exact (exp_neg_mul_holdDensity_eq hdθ t).symm
  have hnonneg : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ Real.exp (-(θ * t)) * (d * Real.exp (-(d * t))) := by
    filter_upwards with t
    positivity
  have hind : ∀ t : ℝ, holdDensity d t * ENNReal.ofReal (Real.exp (-(θ * t)))
      = (Ioi (0 : ℝ)).indicator
          (fun t ↦ ENNReal.ofReal (Real.exp (-(θ * t)) * (d * Real.exp (-(d * t))))) t := by
    intro t
    unfold holdDensity
    by_cases ht : 0 < t
    · rw [if_pos ht, Set.indicator_of_mem (mem_Ioi.mpr ht),
        ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    · rw [if_neg ht, Set.indicator_of_not_mem (by simpa using le_of_not_lt ht), zero_mul]
  calc ∫⁻ t, ENNReal.ofReal (Real.exp (-(θ * t))) ∂(holdMeasure d)
      = ∫⁻ t, holdDensity d t * ENNReal.ofReal (Real.exp (-(θ * t))) := by
        rw [holdMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeas hexp]
        rfl
    _ = ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(θ * t)) * (d * Real.exp (-(d * t)))) := by
        simp only [hind]
        rw [lintegral_indicator measurableSet_Ioi]
    _ = ENNReal.ofReal
          (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * (d * Real.exp (-(d * t)))) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    _ = ENNReal.ofReal (d / (d + θ)) := by
        rw [integral_exp_neg_mul_holdDensity hd hθ]

end Coalescent

end Descent
