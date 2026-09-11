/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEConditionalInverseMoment
import Descent.Portability.FiniteEscapingKernel
import Descent.Portability.HWETiltedKernelLaw

assert_below Descent.Decision Descent.Program

/-!
Three compensated-kernel regimes for the actual conditional HWE sign amplitudes:
a finite signed-lognormal contribution at convergent scale, the Gaussian kernel
at vanishing scale, and zero contribution at escaping scale. The escape result
uses the derived reciprocal L1 moment, not an assumed convergence in probability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEConditionalKernelLimit

open scoped BigOperators Topology NNReal BoundedContinuousFunction
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw
open HWEConditionalScaleLimit HWEConditionalInverseMoment FiniteEscapingKernel
open HWEAmplitudeWeakLimit HWETiltedKernelLaw SymmetricImageLaw
open BalancedHWEWeakLimit FiniteL1WeakStability CompensatedCharacteristicKernel

/-- Kernel integrals under the actual conditional report law equal its finite experiment sum. -/
theorem integral_sign_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (c t : ℝ) :
    (∫ y, kernel t y ∂(reportProbability (independentLaw (fun _ : ι ↦ signLaw))
      (fun b ↦ c * signAmplitude h b) : Measure ℝ)) =
        complexExpectation (independentLaw (fun _ : ι ↦ signLaw))
          (fun b ↦ kernel t (c * signAmplitude h b)) := by
  change (∫ y, kernel t y ∂finiteMeasure _ _) = _
  have hi := (kernel t).integrable (finiteMeasure
    (independentLaw (fun _ : ι ↦ signLaw)) (fun b ↦ c * signAmplitude h b))
  rw [finiteMeasure, integral_sum_measure hi]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (FiniteReportLaw.mass_nonneg _ _),
    Complex.real_smul, tsum_fintype, complexExpectation]

/-- The actual conditional generator retains its signed-lognormal contribution at finite scale. -/
theorem finite_scale_kernel_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (a : ℕ → ℝ) (c : ℝ) (ha : Tendsto a atTop (𝓝 c)) (t : ℝ) :
    Tendsto (fun m ↦ complexExpectation (independentLaw (fun _ : Fin (m + 1) ↦ signLaw))
      (fun b ↦ kernel t (a m * signAmplitude (h (m + 1)) b))) atTop
        (𝓝 (∫ y, kernel t y ∂(signedLognormal K c : Measure ℝ))) := by
  have hh := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    (sign_varying_scale_limit h h0 h1 ε hcap hε K hK a c ha) (kernel t)
  simpa only [integral_sign_kernel] using hh

/-- Zero amplitude gives the Gaussian coefficient under the actual limit law. -/
theorem zero_scale_kernel (K : ℝ≥0) (t : ℝ) :
    (∫ y, kernel t y ∂(signedLognormal K 0 : Measure ℝ)) = (-(t ^ 2 / 2) : ℝ) := by
  rw [signedLognormal_pair, integral_pairLaw]
  simp only [amplitudeMap, ContinuousMap.coe_mk, zero_mul, neg_zero, kernel_zero]
  simp

/-- A conditional layer collapsing in amplitude contributes exactly the Gaussian coefficient. -/
theorem collapsing_scale_kernel_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun m ↦ complexExpectation (independentLaw (fun _ : Fin (m + 1) ↦ signLaw))
      (fun b ↦ kernel t (a m * signAmplitude (h (m + 1)) b))) atTop
        (𝓝 ((-(t ^ 2 / 2) : ℝ) : ℂ)) := by
  simpa only [zero_scale_kernel] using finite_scale_kernel_limit h h0 h1 ε hcap hε K hK a 0 ha t

/-- A conditional layer escaping in amplitude disappears from the actual generator expectation. -/
theorem escaping_scale_kernel_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 K))
    (a : ℕ → ℝ) (ha : Tendsto (fun m ↦ |a m|) atTop atTop) (t : ℝ) :
    Tendsto (fun m ↦ complexExpectation (independentLaw (fun _ : Fin m ↦ signLaw))
      (fun b ↦ kernel t (a m * signAmplitude (h m) b))) atTop (𝓝 0) := by
  apply kernel_expectation_limit _ _ _
    (reciprocal_scaled_limit h h0 h1 ε hcap hε K hK a ha) t
  filter_upwards [ha.eventually (eventually_gt_atTop (0 : ℝ))] with m hm
  intro b
  exact mul_ne_zero (abs_pos.mp hm) (signAmplitude_ne_zero (h m) (h0 m) (h1 m) b)

end Descent.Portability.HWEConditionalKernelLimit
