/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderExponentialDraw
import Mathlib.Probability.Distributions.Exponential

assert_below Descent.Decision Descent.Program

/-!
# The laws of the uniform and exponential draws from fair bits

NOTE2 §7.2 represents continuous primitives by a stream of fair random bits.
`CylinderUniformDraw` and `CylinderExponentialDraw` certify expectations of bounded integrands
of the uniform draw and of the exponential draw `-log U`. This module identifies the laws of the
two draws as measures.

`map_uniformDraw` states that the law of the uniform draw under the fair-bit measure is Lebesgue
measure on the open unit interval. Two finite measures on the line agree once they agree on every
half-line `(-∞, a]` (`Measure.ext_of_Iic`). `ramp a n` is the continuous decreasing curve equal
to one left of `a` and to zero right of `a + 1/(n+1)`. Its integral against any finite measure
converges to the mass of the half-line by dominated convergence (`tendsto_integral_ramp`), and
its expectation at the uniform draw is its interval integral by
`integral_uniformDraw_of_antitoneOn`, so both laws give every half-line the same mass.

`map_neg_log_unitInterval` pushes Lebesgue measure on the unit interval forward along
`u ↦ -log u`: the event `-log u ≤ x` is the interval `[e^(-x), 1)`, whose length `1 - e^(-x)` is
the exponential distribution function of rate one. `map_exponentialDraw` is the law of the
exponential draw, the exponential law `expMeasure 1` of Mathlib.

## Empirical status

None. The bodies here are measure theory: the draws are stipulated functions of the bit stream,
and every conclusion follows from the fair-bit law and Lebesgue measure, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderUniformLaw

open MeasureTheory Filter CylinderIntervalCertificate CylinderUniformDraw CylinderExponentialDraw

open scoped ENNReal Topology

noncomputable section

/-! ### Measurability of the draw -/

/-- The truncated draw is measurable, being a function of finitely many bits. -/
theorem measurable_truncatedDraw (stage : ℕ) : Measurable (truncatedDraw stage) := by
  have hfun : truncatedDraw stage =
      fun stream ↦ (fun word ↦ (wordDraw stage word : ℝ)) (prefixOf stream stage) := by
    funext stream
    exact (wordDraw_prefixOf stage stream).symm
  rw [hfun]
  exact measurable_prefix stage fun word ↦ (wordDraw stage word : ℝ)

/-- The uniform draw is measurable, as the pointwise limit of its truncations. -/
theorem measurable_uniformDraw : Measurable uniformDraw :=
  measurable_of_tendsto_metrizable measurable_truncatedDraw
    (tendsto_pi_nhds.mpr tendsto_truncatedDraw)

/-! ### Ramps -/

/-- The ramp at `a` of steepness `n + 1`: one left of `a`, zero right of `a + 1/(n+1)`, and
linear in between. -/
def ramp (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (1 - ((n : ℝ) + 1) * (x - a)))

/-- Ramps are continuous. -/
theorem continuous_ramp (a : ℝ) (n : ℕ) : Continuous (ramp a n) :=
  continuous_const.max
    (continuous_const.min (continuous_const.sub (continuous_const.mul
      (continuous_id.sub continuous_const))))

/-- Ramps are decreasing. -/
theorem antitone_ramp (a : ℝ) (n : ℕ) : Antitone (ramp a n) := fun first second hle ↦ by
  have hscale : ((n : ℝ) + 1) * (first - a) ≤ ((n : ℝ) + 1) * (second - a) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  show max 0 (min 1 (1 - ((n : ℝ) + 1) * (second - a))) ≤
    max 0 (min 1 (1 - ((n : ℝ) + 1) * (first - a)))
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

/-- Ramps take values in the unit interval. -/
theorem norm_ramp_le_one (a : ℝ) (n : ℕ) (x : ℝ) : ‖ramp a n x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (min_le_left _ _)

/-- Ramps converge pointwise to the indicator of the half-line `(-∞, a]`. -/
theorem tendsto_ramp (a x : ℝ) :
    Tendsto (fun n ↦ ramp a n x) atTop (𝓝 ((Set.Iic a).indicator (fun _ ↦ (1 : ℝ)) x)) := by
  by_cases hle : x ≤ a
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hle)]
    refine tendsto_const_nhds.congr fun n ↦ ?_
    have hnonpos : ((n : ℝ) + 1) * (x - a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    show (1 : ℝ) = max 0 (min 1 (1 - ((n : ℝ) + 1) * (x - a)))
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  · rw [Set.indicator_of_notMem (by simpa using hle)]
    have hgap : 0 < x - a := by linarith [not_le.mp hle]
    obtain ⟨count, hcount⟩ := exists_nat_gt (1 / (x - a))
    rw [div_lt_iff₀ hgap] at hcount
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨count, fun n hn ↦ ?_⟩)
    have hcast : (count : ℝ) ≤ n := by exact_mod_cast hn
    have hsteep : 1 ≤ ((n : ℝ) + 1) * (x - a) := by nlinarith
    show (0 : ℝ) = max 0 (min 1 (1 - ((n : ℝ) + 1) * (x - a)))
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]

/-- The integrals of the ramps against a finite measure converge to the mass of the half-line
`(-∞, a]`. -/
theorem tendsto_integral_ramp (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Tendsto (fun n ↦ ∫ x, ramp a n x ∂μ) atTop (𝓝 (μ.real (Set.Iic a))) := by
  have hlimit := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ ↦ (1 : ℝ))
    (fun n ↦ (continuous_ramp a n).aestronglyMeasurable) (integrable_const 1)
    (fun n ↦ ae_of_all _ fun x ↦ norm_ramp_le_one a n x) (ae_of_all _ fun x ↦ tendsto_ramp a x)
  rwa [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one] at hlimit

/-! ### The uniform law -/

/-- NOTE2 §7.2: the law of the uniform draw under the fair-bit measure is Lebesgue measure on the
open unit interval. -/
theorem map_uniformDraw :
    Measure.map uniformDraw bitMeasure = volume.restrict (Set.Ioo (0 : ℝ) 1) := by
  refine Measure.ext_of_Iic _ _ fun a ↦ ?_
  have hintegrals : ∀ n, ∫ x, ramp a n x ∂(Measure.map uniformDraw bitMeasure) =
      ∫ x, ramp a n x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := fun n ↦ by
    rw [integral_map measurable_uniformDraw.aemeasurable
        (continuous_ramp a n).aestronglyMeasurable,
      integral_uniformDraw_of_antitoneOn (ramp a n) ((antitone_ramp a n).antitoneOn _)
        (continuous_ramp a n).continuousOn,
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hfirst := tendsto_integral_ramp (Measure.map uniformDraw bitMeasure) a
  have hsecond := tendsto_integral_ramp (volume.restrict (Set.Ioo (0 : ℝ) 1)) a
  simp only [hintegrals] at hfirst
  have hreal := tendsto_nhds_unique hfirst hsecond
  rw [measureReal_def, measureReal_def] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

/-- Almost every fair-bit stream has its uniform draw strictly inside the unit interval. -/
theorem ae_uniformDraw_mem_Ioo :
    ∀ᵐ stream ∂bitMeasure, uniformDraw stream ∈ Set.Ioo (0 : ℝ) 1 := by
  have hmap : ∀ᵐ u ∂(Measure.map uniformDraw bitMeasure), u ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [map_uniformDraw]
    exact ae_restrict_mem measurableSet_Ioo
  exact ae_of_ae_map measurable_uniformDraw.aemeasurable hmap

/-! ### The exponential law -/

/-- On the open unit interval the event `-log u ≤ x` is the interval `[e^(-x), 1)`. -/
theorem neg_log_preimage_Iic (x : ℝ) :
    (fun u : ℝ ↦ -Real.log u) ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 = Set.Ico (Real.exp (-x)) 1 := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo, Set.mem_Ico]
  constructor
  · rintro ⟨hlog, hpos, hlt⟩
    refine ⟨?_, hlt⟩
    calc Real.exp (-x) ≤ Real.exp (Real.log u) := Real.exp_le_exp.mpr (by linarith)
      _ = u := Real.exp_log hpos
  · rintro ⟨hexp, hlt⟩
    have hpos : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hexp
    refine ⟨?_, hpos, hlt⟩
    have hlog := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at hlog
    linarith

/-- NOTE2 §7.2: the negative logarithm of a uniform point of the unit interval has the
exponential law of rate one. -/
theorem map_neg_log_unitInterval :
    Measure.map (fun u : ℝ ↦ -Real.log u) (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
      ProbabilityTheory.expMeasure 1 := by
  have hmeasurable : Measurable fun u : ℝ ↦ -Real.log u := Real.measurable_log.neg
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  rw [Measure.map_apply hmeasurable measurableSet_Iic,
    Measure.restrict_apply (hmeasurable measurableSet_Iic), neg_log_preimage_Iic, Real.volume_Ico,
    ← ProbabilityTheory.ofReal_cdf (ProbabilityTheory.expMeasure 1) x,
    ProbabilityTheory.cdf_expMeasure_eq zero_lt_one x, one_mul]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
  · rw [if_neg hx, ENNReal.ofReal_zero]
    exact ENNReal.ofReal_eq_zero.mpr (by linarith [Real.add_one_le_exp (-x), not_le.mp hx])

/-- The exponential draw is measurable. -/
theorem measurable_exponentialDraw : Measurable exponentialDraw :=
  Real.measurable_log.neg.comp measurable_uniformDraw

/-- NOTE2 §7.2: the law of the exponential draw under the fair-bit measure is the exponential law
of rate one. -/
theorem map_exponentialDraw :
    Measure.map exponentialDraw bitMeasure = ProbabilityTheory.expMeasure 1 := by
  have hcomp : exponentialDraw = (fun u : ℝ ↦ -Real.log u) ∘ uniformDraw := rfl
  rw [hcomp, ← Measure.map_map Real.measurable_log.neg measurable_uniformDraw, map_uniformDraw,
    map_neg_log_unitInterval]

end

end Descent.Portability.CylinderUniformLaw
