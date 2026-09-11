/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHierarchySeries
import Descent.Portability.HWECriticalLimitLaw

assert_below Descent.Decision Descent.Program

/-!
Actual probability laws for the HWE heterozygosity hierarchy. The integer case
uses an independent Gaussian plus a compound-Poisson law of signed lognormal
marks. Its intensity is obtained by undoing the square bias of the surviving
layer, and its characteristic function is the derived full generator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHierarchyLimitLaw

open scoped BigOperators Topology NNReal
open MeasureTheory ProbabilityTheory HWEHierarchySeries HWEHierarchyGenerator
open HWEFixedLayerInputs HWEAmplitudeWeakLimit CompensatedCharacteristicKernel
open HWECriticalLimitLaw HWETiltedKernelLaw SymmetricImageLaw CompoundPoissonMarkLaw
open RademacherArrayWeakLimit

/-- Gaussian variance supplied by count layers strictly above the threshold. -/
noncomputable def tailVariance (κ α : ℝ) : ℝ≥0 :=
  ⟨tailMass (4 * energy κ) α, (tail_bounds _ _).1⟩

/-- The exact finite amplitude of the surviving integer layer. -/
noncomputable def layerAmplitude (κ C : ℝ) (r : ℕ) : ℝ :=
  (1 / Real.sqrt C) * (-2 * κ) ^ r

/-- Original jump intensity recovered from the mass of the square-biased layer. -/
noncomputable def layerIntensity (κ C : ℝ) (r : ℕ) : ℝ≥0 :=
  ⟨poissonPMFReal (4 * energy κ) r * (layerAmplitude κ C r ^ 2)⁻¹ *
    Real.exp (8 * (energy κ : ℝ)),
    mul_nonneg (mul_nonneg poissonPMFReal_nonneg (inv_nonneg.mpr (sq_nonneg _)))
      (Real.exp_pos _).le⟩

/-- The Gaussian law for a threshold without an integer layer. -/
noncomputable def gaussianLaw (κ α : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (tailVariance κ α), inferInstance⟩

/-- The independent Gaussian and original Poisson jump law at an integer threshold. -/
noncomputable def integerLaw (κ C : ℝ) (r : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (tailVariance κ (r : ℝ)) ∗
    compoundMeasure (layerIntensity κ C r) (jumpLaw (energy κ) (layerAmplitude κ C r)),
    inferInstance⟩

/-- The surviving amplitude is nonzero under the report's nondegenerate inputs. -/
theorem layerAmplitude_ne_zero (κ C : ℝ) (hκ : κ ≠ 0) (hC : 0 < C) (r : ℕ) :
    layerAmplitude κ C r ≠ 0 := by
  exact mul_ne_zero (one_div_ne_zero (Real.sqrt_pos.mpr hC).ne')
    (pow_ne_zero _ (mul_ne_zero (by norm_num) hκ))

/-- Undoing square bias identifies the surviving kernel with an actual jump characteristic. -/
theorem signed_kernel_characteristic (K : ℝ≥0) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    (∫ y, kernel t y ∂(signedLognormal K c : Measure ℝ)) =
      (((c ^ 2)⁻¹ * Real.exp (8 * (K : ℝ)) : ℝ) : ℂ) *
        (charFun (jumpLaw K c : Measure ℝ) t - 1) := by
  rw [signedLognormal_pair, integral_pair_kernel]
  simp only [centeredGaussian, ProbabilityMeasure.coe_mk, amplitudeMap, ContinuousMap.coe_mk]
  rw [integral_complex_ofReal, tilted_kernel_integral K c hc t,
    integral_sub (cosine_integrable K c t) (integrable_const 1)]
  rw [jumpLaw, charFun_pairLaw]
  simp only [ProbabilityMeasure.coe_mk, amplitudeMap, ContinuousMap.coe_mk,
    integral_complex_ofReal]
  have hi : (∫ _ : ℝ, (1 : ℝ) ∂gaussianReal (8 * (K : ℝ)) (4 * K)) = 1 := by simp
  rw [hi]
  push_cast
  rfl

/-- Exact characteristic identification of the noninteger Gaussian candidate. -/
theorem charFun_gaussianLaw (κ α C t : ℝ) (hα : ∀ r : ℕ, α ≠ (r : ℝ)) :
    charFun (gaussianLaw κ α : Measure ℝ) t = Complex.exp (seriesGenerator κ α C t) := by
  rw [gaussianLaw, ProbabilityMeasure.coe_mk, charFun_gaussianReal,
    noninteger_generator κ α C t hα]
  simp only [tailVariance, NNReal.coe_mk, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  congr 1
  push_cast
  ring

/-- Exact characteristic identification of the integer Gaussian-plus-jump candidate. -/
theorem charFun_integerLaw (κ C t : ℝ) (hκ : κ ≠ 0) (hC : 0 < C) (r : ℕ) :
    charFun (integerLaw κ C r : Measure ℝ) t =
      Complex.exp (seriesGenerator κ (r : ℝ) C t) := by
  rw [integerLaw, ProbabilityMeasure.coe_mk, charFun_conv, charFun_gaussianReal,
    charFun_compoundMeasure, integer_generator]
  change Complex.exp _ * Complex.exp _ = Complex.exp
    ((tailMass (4 * energy κ) (r : ℝ) : ℂ) * ((-(t ^ 2 / 2) : ℝ) : ℂ) +
      (poissonPMFReal (4 * energy κ) r : ℂ) *
        (∫ y, kernel t y ∂(signedLognormal (energy κ) (layerAmplitude κ C r) : Measure ℝ)))
  rw [signed_kernel_characteristic _ _ (layerAmplitude_ne_zero κ C hκ hC r) t,
    ← Complex.exp_add]
  congr 1
  simp only [tailVariance, layerIntensity, NNReal.coe_mk,
    Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  push_cast
  ring

end Descent.Portability.HWEHierarchyLimitLaw
