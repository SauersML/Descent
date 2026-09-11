/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEAbsoluteMomentLimit
import Descent.Portability.FiniteL1WeakStability

assert_below Descent.Decision Descent.Program

/-!
The fair-sign amplitude arising from actual HWE conditioning has an exact
absolute first moment and a signed-lognormal weak limit. Convergent changes of
scale preserve that limit by a proved L1 perturbation estimate. These results
supply the finite-amplitude and collapsing regimes of the count-layer analysis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEConditionalScaleLimit

open scoped BigOperators Topology NNReal BoundedContinuousFunction
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw HWEHomozygoteLimit
open HWEHomozygoteConditioning HWEAbsoluteMomentLimit HWEExceptionalAmplitude
open HWEAmplitudeWeakLimit BalancedHWEWeakLimit FiniteL1WeakStability

/-- The normalized amplitude on a realized row of the conditional homozygote signs. -/
noncomputable def signAmplitude {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (b : ι → Bool) : ℝ := normalized h (homoVector b)

/-- Exact absolute first moment under the original conditional sign experiment. -/
theorem sign_absolute_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (independentLaw (fun _ : ι ↦ signLaw)).expectation (fun b ↦ |signAmplitude h b|) =
      Real.sqrt (zeroMass h) / zeroMass h := by
  change (independentLaw (fun _ : ι ↦ signLaw)).expectation
    (fun b ↦ |normalized h (homoVector b)|) = _
  rw [← conditional_expectation h h0 h1 (fun x ↦ |normalized h x|),
    homo_absolute_product h h0 h1, homo_product_sqrt h h0 h1]

/-- The first absolute moment converges to exp(2K), as derived from the conditioning mass. -/
theorem sign_absolute_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 K)) :
    Tendsto (fun m ↦ (independentLaw (fun _ : Fin m ↦ signLaw)).expectation
      (fun b ↦ |signAmplitude (h m) b|)) atTop (𝓝 (Real.exp (2 * K))) := by
  have hz : Tendsto (fun m ↦ zeroMass (h m)) atTop (𝓝 (Real.exp (-4 * K))) := by
    simpa only [HWEHeterozygosityLimit.zero_count_probability, zeroMass] using
      HWEHeterozygosityLimit.zero_count_probability_limit h h0 h1 ε hcap hε K hK
  have he : Real.sqrt (Real.exp (-4 * K)) / Real.exp (-4 * K) = Real.exp (2 * K) := by
    rw [← Real.exp_half, ← Real.exp_sub]
    congr 1
    ring
  simpa only [sign_absolute_moment _ (h0 _) (h1 _), he] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp hz).div hz (Real.exp_ne_zero _)

/-- Bounded-test integral of the actual fair signed lognormal limit. -/
theorem integral_signedLognormal (K : ℝ≥0) (c : ℝ) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(signedLognormal K c : Measure ℝ)) =
      ((∫ x, f (c * Real.exp (-x)) ∂gaussianReal 0 (4 * K)) +
        (∫ x, f (-c * Real.exp (-x)) ∂gaussianReal 0 (4 * K))) / 2 := by
  rw [signedLognormal, integral_blend, integral_lognormal, integral_lognormal]
  ring

/-- Weak limit of the actual conditional fair-sign amplitudes. -/
theorem sign_weak_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (c : ℝ) :
    Tendsto (fun m ↦ reportProbability (independentLaw (fun _ : Fin (m + 1) ↦ signLaw))
      (fun b ↦ c * signAmplitude (h (m + 1)) b)) atTop (𝓝 (signedLognormal K c)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun m ↦ ∫ x, f x ∂finiteMeasure
    (independentLaw (fun _ : Fin (m + 1) ↦ signLaw))
      (fun b ↦ c * signAmplitude (h (m + 1)) b)) atTop
        (𝓝 (∫ x, f x ∂(signedLognormal K c : Measure ℝ)))
  simp only [integral_finiteMeasure, integral_signedLognormal, signAmplitude]
  simpa only [conditional_expectation _ (h0 _) (h1 _)] using
    conditional_amplitude_limit h h0 h1 ε hcap hε K hK f c

/-- Changing normalization is justified by the actual conditional first moment. -/
theorem sign_varying_scale_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (a : ℕ → ℝ) (c : ℝ) (ha : Tendsto a atTop (𝓝 c)) :
    Tendsto (fun m ↦ reportProbability (independentLaw (fun _ : Fin (m + 1) ↦ signLaw))
      (fun b ↦ a m * signAmplitude (h (m + 1)) b)) atTop (𝓝 (signedLognormal K c)) := by
  apply varying_scale_limit _ _ a c ha (Real.exp (2 * (K : ℝ)))
  · exact (sign_absolute_limit h h0 h1 ε hcap hε K hK).comp (tendsto_add_atTop_nat 1)
  · exact sign_weak_limit h h0 h1 ε hcap hε K hK c

end Descent.Portability.HWEConditionalScaleLimit
