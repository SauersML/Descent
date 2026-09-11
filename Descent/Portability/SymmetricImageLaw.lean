/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEAmplitudeWeakLimit
import Descent.Portability.CompensatedCharacteristicKernel

assert_below Descent.Decision Descent.Program

/-!
A fair sign applied independently to a continuous image of a real probability
law. The exact complex integral formula permits characteristic functions and
compensated kernels to be evaluated without assuming symmetry of the original law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SymmetricImageLaw

open scoped Topology BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory BoundedContinuousFunction HWEAmplitudeWeakLimit

/-- Complex bounded tests integrate linearly under the actual convex mixture. -/
theorem integral_blend_complex (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (μ ν : ProbabilityMeasure ℝ) (f : ℝ →ᵇ ℂ) :
    (∫ x, f x ∂(blend w hw0 hw1 μ ν : Measure ℝ)) =
      ((1 - w : ℝ) : ℂ) * (∫ x, f x ∂(μ : Measure ℝ)) +
      (w : ℂ) * (∫ x, f x ∂(ν : Measure ℝ)) := by
  change (∫ x, f x ∂(ENNReal.ofReal (1 - w) • (μ : Measure ℝ) +
    ENNReal.ofReal w • (ν : Measure ℝ))) = _
  rw [integral_add_measure
    ((f.integrable (μ : Measure ℝ)).smul_measure ENNReal.ofReal_ne_top)
    ((f.integrable (ν : Measure ℝ)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (sub_nonneg.mpr hw1),
    ENNReal.toReal_ofReal hw0, Complex.real_smul]

/-- The continuous image multiplied by an independent fair sign. -/
noncomputable def pairLaw (μ : ProbabilityMeasure ℝ) (g : C(ℝ, ℝ)) : ProbabilityMeasure ℝ :=
  blend (1 / 2) (by norm_num) (by norm_num)
    (μ.map g.continuous.measurable.aemeasurable)
    (μ.map (show AEMeasurable (fun x ↦ -g x) _ by fun_prop))

/-- Exact bounded complex test formula for the signed image. -/
theorem integral_pairLaw (μ : ProbabilityMeasure ℝ) (g : C(ℝ, ℝ)) (f : ℝ →ᵇ ℂ) :
    (∫ x, f x ∂(pairLaw μ g : Measure ℝ)) =
      ∫ x, (f (g x) + f (-g x)) / 2 ∂(μ : Measure ℝ) := by
  have hp : Integrable (fun x ↦ f (g x)) (μ : Measure ℝ) :=
    (f.compContinuous g).integrable _
  have hm : Integrable (fun x ↦ f (-g x)) (μ : Measure ℝ) :=
    (f.compContinuous (-g)).integrable _
  rw [pairLaw, integral_blend_complex]
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map g.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map (by fun_prop) f.continuous.aestronglyMeasurable,
    integral_div, integral_add hp hm]
  push_cast
  ring

/-- The elementary fair-sign characteristic identity. -/
theorem paired_character (t u : ℝ) :
    (innerProbChar t u + innerProbChar t (-u)) / 2 = (Real.cos (t * u) : ℂ) := by
  have hh := Complex.two_cos ((t * u : ℝ) : ℂ)
  simp only [← Complex.ofReal_cos] at hh
  change (Complex.exp ((t * u : ℝ) * Complex.I) +
    Complex.exp ((t * (-u) : ℝ) * Complex.I)) / 2 = _
  simp only [mul_neg, Complex.ofReal_neg]
  linear_combination -hh / 2

/-- Every signed-image characteristic function is the actual expected cosine. -/
theorem charFun_pairLaw (μ : ProbabilityMeasure ℝ) (g : C(ℝ, ℝ)) (t : ℝ) :
    charFun (pairLaw μ g : Measure ℝ) t =
      ((∫ x, Real.cos (t * g x) ∂(μ : Measure ℝ)) : ℂ) := by
  rw [charFun_eq_integral_innerProbChar, integral_pairLaw]
  simp only [paired_character, integral_complex_ofReal]

/-- Pairing the compensated kernel cancels its imaginary part exactly. -/
theorem paired_kernel (t u : ℝ) :
    (CompensatedCharacteristicKernel.kernel t u +
      CompensatedCharacteristicKernel.kernel t (-u)) / 2 =
        (CompensatedCharacteristicKernel.realPart t u : ℂ) := by
  simp only [CompensatedCharacteristicKernel.kernel_apply,
    CompensatedCharacteristicKernel.value, CompensatedCharacteristicKernel.realPart,
    CompensatedCharacteristicKernel.imaginaryPart, mul_neg, neg_div, Real.sinc_neg,
    SineCompensator.compensator_neg]
  push_cast
  ring

/-- Exact compensated-kernel integral under the constructed signed image. -/
theorem integral_pair_kernel (μ : ProbabilityMeasure ℝ) (g : C(ℝ, ℝ)) (t : ℝ) :
    (∫ x, CompensatedCharacteristicKernel.kernel t x ∂(pairLaw μ g : Measure ℝ)) =
      ((∫ x, CompensatedCharacteristicKernel.realPart t (g x) ∂(μ : Measure ℝ)) : ℂ) := by
  rw [integral_pairLaw]
  simp only [paired_kernel, integral_complex_ofReal]

end Descent.Portability.SymmetricImageLaw
