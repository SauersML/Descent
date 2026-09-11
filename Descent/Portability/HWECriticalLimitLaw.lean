/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWETiltedKernelLaw
import Descent.Portability.CompoundPoissonMarkLaw
import Descent.Portability.HWECriticalScoreCharacteristic

assert_below Descent.Decision Descent.Program

/-!
An actual probability law for the heterogeneous near-balanced HWE critical window:
an independent Gaussian plus a compound-Poisson sum of fair signed lognormal marks.
Its characteristic function is identified with the generator derived from the
original finite HWE genotype experiment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWECriticalLimitLaw

open scoped BigOperators Topology NNReal MeasureTheory BoundedContinuousFunction
open MeasureTheory ProbabilityTheory HWEAmplitudeWeakLimit HWETiltedKernelLaw
open SymmetricImageLaw CompoundPoissonMarkLaw CompensatedCharacteristicKernel

/-- The Gaussian variance created by square-biased mass collapsing to zero. -/
noncomputable def gaussianVariance (K : ℝ≥0) : ℝ≥0 :=
  ⟨1 - Real.exp (-4 * (K : ℝ)), sub_nonneg.mpr (weight_bounds K).2⟩

/-- The original jump intensity after undoing square bias. -/
noncomputable def jumpIntensity (K : ℝ≥0) (c : ℝ) : ℝ≥0 :=
  ⟨(c ^ 2)⁻¹ * Real.exp (4 * (K : ℝ)), by positivity⟩

/-- Fair signed mark c exp(-X), with X Gaussian of mean 8K and variance 4K. -/
noncomputable def jumpLaw (K : ℝ≥0) (c : ℝ) : ProbabilityMeasure ℝ :=
  pairLaw ⟨gaussianReal (8 * (K : ℝ)) (4 * K), inferInstance⟩ (amplitudeMap c)

/-- Independent Gaussian plus the actual Poisson mixture of independent jump marks. -/
noncomputable def criticalLaw (K : ℝ≥0) (c : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (gaussianVariance K) ∗ compoundMeasure (jumpIntensity K c) (jumpLaw K c),
    inferInstance⟩

/-- The bounded cosine mark test is integrable under its actual shifted Gaussian. -/
theorem cosine_integrable (K : ℝ≥0) (c t : ℝ) :
    Integrable (fun x ↦ Real.cos (t * (c * Real.exp (-x))))
      (gaussianReal (8 * (K : ℝ)) (4 * K)) := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ Real.cos (t * (c * Real.exp (-x)))) (by fun_prop) 1
    (fun x ↦ Real.abs_cos_le_one _)
  exact f.integrable _

/-- Characteristic identification of the fully constructed Gaussian-plus-jump limit law. -/
theorem charFun_criticalLaw (K : ℝ≥0) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    charFun (criticalLaw K c : Measure ℝ) t =
      Complex.exp (∫ y, kernel t y ∂(amplitudeLimit K c : Measure ℝ)) := by
  have hi : (∫ x, Real.cos (t * (c * Real.exp (-x))) - 1
      ∂gaussianReal (8 * (K : ℝ)) (4 * K)) =
        (∫ x, Real.cos (t * (c * Real.exp (-x)))
          ∂gaussianReal (8 * (K : ℝ)) (4 * K)) - 1 := by
    rw [integral_sub (cosine_integrable K c t) (integrable_const 1)]
    simp
  rw [criticalLaw, ProbabilityMeasure.coe_mk, charFun_conv, charFun_gaussianReal,
    charFun_compoundMeasure, jumpLaw, charFun_pairLaw, explicit_kernel_generator K c hc t, hi]
  simp only [ProbabilityMeasure.coe_mk, amplitudeMap, ContinuousMap.coe_mk,
    Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_add]
  congr 1
  simp only [gaussianVariance, jumpIntensity, NNReal.coe_mk]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one,
    Complex.ofReal_ofNat, integral_complex_ofReal]
  ring

end Descent.Portability.HWECriticalLimitLaw
