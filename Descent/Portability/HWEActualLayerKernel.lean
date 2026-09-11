/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHomogeneousLayer
import Descent.Portability.HWEPolynomialLayerScale
import Descent.Portability.HWEConditionalKernelLimit

assert_below Descent.Decision Descent.Program

/-!
The original normalized interaction's count-layer contribution is identified
with its binomial probability times the conditional kernel at the derived
polynomial layer scale. This connects the scaling analysis to the actual
finite-genotype characteristic generator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEActualLayerKernel

open scoped BigOperators
open Foundations HWEInteractionLaw HWEHeterozygosityLaw HWEHomogeneousLayer HWEPolynomialLayerScale
open HWEConditionalScaleLimit HWEHomozygoteLimit HWELogCoordinates CompensatedCharacteristicKernel
open BalancedHWEWeakLimit HWECriticalAmplitudeLimit

/-- Exact coefficient identity for the original score normalization, including zero block count. -/
theorem prefactor_scale (h : HardyWeinbergModel) (m N r : ℕ) (hr : r ≤ m) :
    (1 / Real.sqrt (N : ℝ)) * h.standardizedGenotype .het ^ r * Real.sqrt 2 ^ (m - r) =
      layerScale h m N r := by
  have hs : Real.sqrt (2 : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by positivity)
  have he : Real.sqrt (2 : ℝ) ^ m = Real.sqrt 2 ^ r * Real.sqrt 2 ^ (m - r) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  rw [layerScale, intensity, Real.sqrt_div (Nat.cast_nonneg N), sqrt_two_pow,
    one_div_div, div_pow, he]
  symm
  calc
    _ = (Real.sqrt 2 ^ r / Real.sqrt 2 ^ r) *
        ((1 / Real.sqrt (N : ℝ)) * h.standardizedGenotype .het ^ r *
          Real.sqrt 2 ^ (m - r)) := by ring
    _ = _ := by rw [div_self hs, one_mul]

/-- The finite layer's actual amplitude equals the derived scale times its conditional amplitude. -/
theorem actual_layer_amplitude (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (m N r : ℕ) (hr : r ≤ m)
    (b : Fin (m - r) → Bool) :
    layerAmplitude h m r (1 / Real.sqrt (N : ℝ)) b =
      layerScale h m N r * signAmplitude (fun _ : Fin (m - r) ↦ h) b := by
  rw [layerAmplitude, prefactor_scale h m N r hr, signAmplitude,
    normalized_homoVector _ (fun _ ↦ h0) (fun _ ↦ h1)]
  ring

/-- Specializing the actual real layer law preserves its dependent finite sample dimension. -/
theorem real_layer_statistic_fin (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (m r : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    (independentLaw (fun _ : Fin m ↦ squareBiasedLocus h h0 h1)).expectation
      (fun x ↦ if count x = (r : ℝ) then f (c * interaction (fun _ : Fin m ↦ h) x) else 0) =
        ((m.choose r : ℝ) * probability h ^ r * (1 - probability h) ^ (m - r)) *
          (independentLaw (fun _ : Fin (m - r) ↦ signLaw)).expectation
            (fun b ↦ f (layerAmplitude h m r c b)) := by
  exact (homogeneous_layer_statistic (ι := Fin m) h h0 h1 r c f).trans
    (congrArg (fun n : ℕ ↦ ((n.choose r : ℝ) * probability h ^ r *
      (1 - probability h) ^ (n - r)) *
        (independentLaw (fun _ : Fin (n - r) ↦ signLaw)).expectation
          (fun b ↦ f (layerAmplitude h n r c b))) (Fintype.card_fin m))

/-- Complex statistics obey the same actual count-layer decomposition as real statistics. -/
theorem complex_layer_statistic (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (m r : ℕ) (c : ℝ) (f : ℝ → ℂ) :
    complexExpectation (independentLaw (fun _ : Fin m ↦ squareBiasedLocus h h0 h1))
      (fun x ↦ if count x = (r : ℝ) then f (c * interaction (fun _ : Fin m ↦ h) x) else 0) =
        (((m.choose r : ℝ) * probability h ^ r * (1 - probability h) ^ (m - r) : ℝ) : ℂ) *
          complexExpectation (independentLaw (fun _ : Fin (m - r) ↦ signLaw))
            (fun b ↦ f (layerAmplitude h m r c b)) := by
  have hre := real_layer_statistic_fin h h0 h1 m r c (fun z ↦ (f z).re)
  have him := real_layer_statistic_fin h h0 h1 m r c (fun z ↦ (f z).im)
  apply Complex.ext
  · simpa only [complexExpectation, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, apply_ite, Complex.zero_re,
      FiniteReportLaw.expectation, Fintype.card_fin] using
        hre
  · simpa only [complexExpectation, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, apply_ite, Complex.zero_im,
      FiniteReportLaw.expectation, Fintype.card_fin] using
        him

/-- Exact layer contribution to the characteristic generator of the original normalized score. -/
theorem actual_layer_kernel (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (m N r : ℕ) (hr : r ≤ m) (t : ℝ) :
    complexExpectation (independentLaw (fun _ : Fin m ↦ squareBiasedLocus h h0 h1))
      (fun x ↦ if count x = (r : ℝ) then
        kernel t (interaction (fun _ : Fin m ↦ h) x / Real.sqrt (N : ℝ)) else 0) =
          (((m.choose r : ℝ) * probability h ^ r * (1 - probability h) ^ (m - r) : ℝ) : ℂ) *
            complexExpectation (independentLaw (fun _ : Fin (m - r) ↦ signLaw))
              (fun b ↦ kernel t (layerScale h m N r *
                signAmplitude (fun _ : Fin (m - r) ↦ h) b)) := by
  have hh := complex_layer_statistic h h0 h1 m r (1 / Real.sqrt (N : ℝ)) (kernel t)
  simpa only [one_div_mul_eq_div, actual_layer_amplitude h h0 h1 m N r hr] using hh

end Descent.Portability.HWEActualLayerKernel
