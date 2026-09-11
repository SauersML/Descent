/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEKernelTruncation
import Descent.Portability.CountTailConvergence

assert_below Descent.Decision Descent.Program

/-!
Convergence of the complete original HWE characteristic generator to the absolutely
convergent Poisson-weighted layer series. The proof derives a uniform truncation
certificate from the actual count moment before summing the fixed-layer limits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHierarchyGenerator

open scoped BigOperators Topology NNReal
open Filter MeasureTheory ProbabilityTheory Foundations HWEFixedLayerKernelLimit HWEFixedLayerInputs
open HWEKernelTruncation CountTailConvergence HWEAmplitudeWeakLimit CompensatedCharacteristicKernel
open HWEPolynomialLayerScale

/-- The limiting generator contribution of a single heterozygosity layer. -/
noncomputable def seriesTerm (κ α C t : ℝ) (r : ℕ) : ℂ :=
  (poissonPMFReal (4 * energy κ) r : ℂ) * limitingKernel κ α C r t

/-- The complete count-layer generator, defined by its convergent series. -/
noncomputable def seriesGenerator (κ α C t : ℝ) : ℂ := ∑' r, seriesTerm κ α C t r

/-- Every conditional limiting layer obeys the same global kernel bound. -/
theorem limitingKernel_bound (κ α C t : ℝ) (r : ℕ) :
    ‖limitingKernel κ α C r t‖ ≤ 5 * t ^ 2 / 2 := by
  unfold limitingKernel
  split_ifs
  · simp only [norm_zero]
    positivity
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (div_nonneg (sq_nonneg t) (by norm_num))]
    nlinarith [sq_nonneg t]
  · have hh := norm_integral_le_of_norm_le_const
      (μ := (signedLognormal (energy κ) ((1 / Real.sqrt C) * (-2 * κ) ^ r) : Measure ℝ))
      (f := fun y ↦ kernel t y) (Eventually.of_forall (fun y ↦ value_bound t y))
    simpa using hh

/-- The full layer series is absolutely convergent, by domination with normalized Poisson masses. -/
theorem series_summable (κ α C t : ℝ) : Summable (seriesTerm κ α C t) := by
  apply ((poissonPMFRealSum (4 * energy κ)).summable.mul_right (5 * t ^ 2 / 2)).of_norm_bounded
  intro r
  rw [seriesTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg poissonPMFReal_nonneg]
  exact mul_le_mul_of_nonneg_left (limitingKernel_bound κ α C t r) poissonPMFReal_nonneg

/-- The complete original kernel expectation converges, with all count layers accounted for. -/
theorem full_generator_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ) (hκ : κ ≠ 0)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C)) (t : ℝ) :
    Tendsto (tiltedKernel h h0 h1 N t) atTop (𝓝 (seriesGenerator κ α C t)) := by
  apply tendsto_of_layer_truncation (fun r ↦ contribution h h0 h1 N r t)
    (tiltedKernel h h0 h1 N t) (seriesTerm κ α C t)
    (fun r ↦ original_layer_limit h h0 h1 κ hκ hf N α C hC hN r t)
    (series_summable κ α C t) ((5 * t ^ 2 / 2) * (4 * κ ^ 2 + 1))
  intro R hR
  filter_upwards [eventual_uniform_truncation h h0 h1 κ hf N] with m hm
  have hh := hm R hR t
  convert hh using 1
  ring

end Descent.Portability.HWEHierarchyGenerator
