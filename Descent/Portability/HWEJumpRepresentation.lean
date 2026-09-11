/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWENearBalancedTheorem

assert_below Descent.Decision Descent.Program

/-!
The constructed critical jump law is exactly the report's fair signed mark
c exp(-8K + 2 sqrt(K) Z), with Z standard Gaussian. The affine Gaussian image
and composition of the independent sign construction are proved explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEJumpRepresentation

open scoped NNReal
open MeasureTheory ProbabilityTheory HWEAmplitudeWeakLimit RademacherArrayWeakLimit
open SymmetricImageLaw HWETiltedKernelLaw HWECriticalLimitLaw

/-- Transporting the base law before applying the fair sign is exact composition. -/
theorem pairLaw_map (μ : ProbabilityMeasure ℝ) (f g : C(ℝ, ℝ)) :
    pairLaw (μ.map f.continuous.measurable.aemeasurable) g = pairLaw μ (g.comp f) := by
  apply Subtype.ext
  simp only [pairLaw, blend, ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
  rw [Measure.map_map g.continuous.measurable f.continuous.measurable,
    Measure.map_map (show Measurable (fun x ↦ -g x) by fun_prop) f.continuous.measurable]
  rfl

/-- The Gaussian coordinate whose negative gives the report's log mark. -/
noncomputable def logCoordinateMap (K : ℝ≥0) : C(ℝ, ℝ) :=
  ⟨fun z ↦ (-2 * Real.sqrt (K : ℝ)) * z + 8 * (K : ℝ), by fun_prop⟩

/-- Its actual image of the standard Gaussian has mean 8K and variance 4K. -/
theorem gaussian_coordinate_image (K : ℝ≥0) :
    (centeredGaussian 1).map (logCoordinateMap K).continuous.measurable.aemeasurable =
      (⟨gaussianReal (8 * (K : ℝ)) (4 * K), inferInstance⟩ : ProbabilityMeasure ℝ) := by
  have hv : (⟨(-2 * Real.sqrt (K : ℝ)) ^ 2, sq_nonneg _⟩ : NNReal) = (4 : NNReal) * K := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, NNReal.coe_ofNat, mul_one]
    nlinarith [Real.sq_sqrt K.coe_nonneg]
  have hm : (gaussianReal 0 1).map (fun x ↦ (-2 * Real.sqrt (K : ℝ)) * x) =
      gaussianReal 0 (4 * K) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one, hv]
  have ha := gaussianReal_map_add_const (μ := 0) (v := 4 * K) (8 * (K : ℝ))
  rw [← hm, Measure.map_map (by fun_prop) (by fun_prop), zero_add] at ha
  exact Subtype.ext ha

/-- The exact standard-Gaussian map appearing in the report's signed jump formula. -/
noncomputable def standardMarkMap (K : ℝ≥0) (c : ℝ) : C(ℝ, ℝ) :=
  ⟨fun z ↦ c * Real.exp (-8 * (K : ℝ) + 2 * Real.sqrt (K : ℝ) * z), by fun_prop⟩

/-- No distributional shortcut: the constructed jump mark equals the stated report formula. -/
theorem jumpLaw_standard_representation (K : ℝ≥0) (c : ℝ) :
    jumpLaw K c = pairLaw (centeredGaussian 1) (standardMarkMap K c) := by
  rw [jumpLaw, ← gaussian_coordinate_image, pairLaw_map]
  congr 1
  apply ContinuousMap.ext
  intro x
  change c * Real.exp (-((-2 * Real.sqrt (K : ℝ)) * x + 8 * (K : ℝ))) =
    c * Real.exp (-8 * (K : ℝ) + 2 * Real.sqrt (K : ℝ) * x)
  congr 2
  ring

end Descent.Portability.HWEJumpRepresentation
