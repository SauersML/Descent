/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHierarchyLimitLaw
import Descent.Portability.HWEJumpRepresentation

assert_below Descent.Decision Descent.Program

/-!
The integer hierarchy's actual jump distribution is exactly the report's positive
amplitude times an independent fair sign and standard-Gaussian exponential.
Changing the sign of its deterministic amplitude leaves the probability law unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHierarchyJumpRepresentation

open scoped NNReal
open MeasureTheory ProbabilityTheory HWEHierarchyLimitLaw HWEFixedLayerInputs
open HWECriticalLimitLaw HWETiltedKernelLaw HWEJumpRepresentation SymmetricImageLaw
open RademacherArrayWeakLimit

/-- A fair signed jump law depends only on the absolute value of its deterministic amplitude. -/
theorem jumpLaw_abs (K : ℝ≥0) (c : ℝ) : jumpLaw K |c| = jumpLaw K c := by
  apply Subtype.ext
  change (jumpLaw K |c| : Measure ℝ) = (jumpLaw K c : Measure ℝ)
  apply Measure.ext_of_charFun
  funext t
  simp only [jumpLaw, charFun_pairLaw, ProbabilityMeasure.coe_mk,
    amplitudeMap, ContinuousMap.coe_mk]
  congr 1
  funext x
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc]
  · rw [abs_of_nonpos hc]
    simp only [neg_mul, mul_neg, Real.cos_neg]

/-- Magnitude of the actual layer amplitude in the report's positive-amplitude convention. -/
theorem abs_layerAmplitude (κ C : ℝ) (hC : 0 < C) (r : ℕ) :
    |layerAmplitude κ C r| = (2 * |κ|) ^ r / Real.sqrt C := by
  simp only [layerAmplitude, abs_mul, abs_div, abs_one, abs_pow,
    abs_of_pos (Real.sqrt_pos.mpr hC), abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

/-- The report's explicit deterministic map of its standard Gaussian mark. -/
noncomputable def reportMarkMap (κ C : ℝ) (r : ℕ) : C(ℝ, ℝ) :=
  ⟨fun z ↦ (2 * |κ|) ^ r / Real.sqrt C * Real.exp (-8 * κ ^ 2 + 2 * |κ| * z),
    by fun_prop⟩

/-- Equality of actual probability laws with the report's exact fair-sign lognormal formula. -/
theorem layer_jump_report_representation (κ C : ℝ) (hC : 0 < C) (r : ℕ) :
    jumpLaw (energy κ) (layerAmplitude κ C r) =
      pairLaw (centeredGaussian 1) (reportMarkMap κ C r) := by
  rw [← jumpLaw_abs (energy κ) (layerAmplitude κ C r),
    abs_layerAmplitude κ C hC r, jumpLaw_standard_representation]
  congr 1
  apply ContinuousMap.ext
  intro z
  simp only [standardMarkMap, reportMarkMap, ContinuousMap.coe_mk,
    energy, NNReal.coe_mk, Real.sqrt_sq_eq_abs]

end Descent.Portability.HWEHierarchyJumpRepresentation
