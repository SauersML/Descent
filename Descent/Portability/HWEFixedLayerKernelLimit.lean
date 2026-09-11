/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEActualLayerKernel
import Descent.Portability.HWEFixedLayerInputs
import Descent.Portability.HWEPolynomialScaleRegimes

assert_below Descent.Decision Descent.Program

/-!
The actual original-genotype contribution of each fixed heterozygosity layer
has its stated three-regime limit under the report's explicit frequency and
block-count scaling assumptions. Neither conditional amplitude laws nor scale
limits are external premises. Combining all layers remains a separate step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEFixedLayerKernelLimit

open scoped BigOperators Topology NNReal
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw HWEHeterozygosityLaw
open HWEFixedLayerInputs HWEPolynomialLayerScale HWEPolynomialScaleRegimes HWEActualLayerKernel
open HWEConditionalScaleLimit HWEConditionalKernelLimit HWEAmplitudeWeakLimit
open BalancedHWEWeakLimit CompensatedCharacteristicKernel

/-- The conditional contribution selected by the heterozygosity threshold. -/
noncomputable def limitingKernel (κ α C : ℝ) (r : ℕ) (t : ℝ) : ℂ :=
  if (r : ℝ) < α then 0 else if α < (r : ℝ) then ((-(t ^ 2 / 2) : ℝ) : ℂ)
    else ∫ y, kernel t y ∂(signedLognormal (energy κ)
      ((1 / Real.sqrt C) * (-2 * κ) ^ r) : Measure ℝ)

/-- All conditional kernel regimes follow from the original homogeneous model inputs. -/
theorem conditional_layer_kernel_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ) (hκ : κ ≠ 0)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C)) (r : ℕ) (t : ℝ) :
    Tendsto (fun m : ℕ ↦ complexExpectation (independentLaw (fun _ : Fin (m + 1) ↦ signLaw))
      (fun b ↦ kernel t (layerScale (h ((m + 1) + r)) ((m + 1) + r) (N ((m + 1) + r)) r *
        signAmplitude (remaining h r (m + 1)) b))) atTop (𝓝 (limitingKernel κ α C r t)) := by
  by_cases hlo : (r : ℝ) < α
  · simp only [limitingKernel, hlo, if_true]
    have ha := (layerScale_escape h h0 h1 κ hκ hf N α C hC hN r hlo).comp
      (tendsto_add_atTop_nat r)
    have hh := escaping_scale_kernel_limit (remaining h r) (fun m _ ↦ h0 (m + r))
      (fun m _ ↦ h1 (m + r)) (cap h r) (fun m _ ↦ le_refl _) (cap_limit h κ hf r)
      (energy κ : ℝ) (remaining_energy_limit h κ hf r)
      (fun m : ℕ ↦ layerScale (h (m + r)) (m + r) (N (m + r)) r) ha t
    exact hh.comp (tendsto_add_atTop_nat 1)
  by_cases hhi : α < (r : ℝ)
  · simp only [limitingKernel, hlo, hhi, if_false, if_true]
    have ha := (layerScale_collapse h h0 h1 κ hf N α C hC hN r hhi).comp
      ((tendsto_add_atTop_nat r).comp (tendsto_add_atTop_nat 1))
    exact collapsing_scale_kernel_limit (remaining h r) (fun m _ ↦ h0 (m + r))
      (fun m _ ↦ h1 (m + r)) (cap h r) (fun m _ ↦ le_refl _) (cap_limit h κ hf r)
      (energy κ) (remaining_energy_limit h κ hf r) _ ha t
  · have he : α = (r : ℝ) := by linarith
    subst α
    simp only [limitingKernel, lt_self_iff_false, if_false]
    have ha := (layerScale_critical h h0 h1 κ hf N C hC r hN).comp
      ((tendsto_add_atTop_nat r).comp (tendsto_add_atTop_nat 1))
    exact finite_scale_kernel_limit (remaining h r) (fun m _ ↦ h0 (m + r))
      (fun m _ ↦ h1 (m + r)) (cap h r) (fun m _ ↦ le_refl _) (cap_limit h κ hf r)
      (energy κ) (remaining_energy_limit h κ hf r) _ _ ha t

/-- Each actual genotype layer has its Poisson-weighted kernel limit at the original score scale. -/
theorem original_layer_kernel_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ) (hκ : κ ≠ 0)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C)) (r : ℕ) (t : ℝ) :
    Tendsto (fun m : ℕ ↦ complexExpectation
      (independentLaw (fun _ : Fin ((m + 1) + r) ↦ squareBiasedLocus
        (h ((m + 1) + r)) (h0 ((m + 1) + r)) (h1 ((m + 1) + r))))
      (fun x ↦ if count x = (r : ℝ) then kernel t
        (interaction (fun _ : Fin ((m + 1) + r) ↦ h ((m + 1) + r)) x /
          Real.sqrt (N ((m + 1) + r) : ℝ)) else 0)) atTop
            (𝓝 ((poissonPMFReal (4 * energy κ) r : ℂ) * limitingKernel κ α C r t)) := by
  have hw := ((binomial_layer_limit h h0 h1 κ hf r).comp
    ((tendsto_add_atTop_nat r).comp (tendsto_add_atTop_nat 1))).ofReal
  have hk := conditional_layer_kernel_limit h h0 h1 κ hκ hf N α C hC hN r t
  apply (hw.mul hk).congr'
  filter_upwards with m
  have he := actual_layer_kernel (h ((m + 1) + r)) (h0 ((m + 1) + r))
    (h1 ((m + 1) + r)) ((m + 1) + r) (N ((m + 1) + r)) r (by omega) t
  have hd := congrArg (fun n : ℕ ↦
    (((((m + 1) + r).choose r : ℝ) * probability (h ((m + 1) + r)) ^ r *
      (1 - probability (h ((m + 1) + r))) ^ n : ℝ) : ℂ) *
    complexExpectation (independentLaw (fun _ : Fin n ↦ signLaw))
      (fun b ↦ kernel t (layerScale (h ((m + 1) + r)) ((m + 1) + r)
        (N ((m + 1) + r)) r * signAmplitude
          (fun _ : Fin n ↦ h ((m + 1) + r)) b))) (Nat.add_sub_cancel (m + 1) r)
  simpa only [Function.comp_def, Nat.add_sub_cancel, remaining] using (he.trans hd).symm

/-- The original row's finite expected kernel restricted to a specified heterozygosity layer. -/
noncomputable def contribution (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1)
    (N : ℕ → ℕ) (r : ℕ) (t : ℝ) (m : ℕ) : ℂ :=
  complexExpectation (independentLaw (fun _ : Fin m ↦ squareBiasedLocus (h m) (h0 m) (h1 m)))
    (fun x ↦ if count x = (r : ℝ) then
      kernel t (interaction (fun _ : Fin m ↦ h m) x / Real.sqrt (N m : ℝ)) else 0)

/-- The fixed-layer limit on the original unshifted interaction-order sequence. -/
theorem original_layer_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ) (hκ : κ ≠ 0)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C)) (r : ℕ) (t : ℝ) :
    Tendsto (contribution h h0 h1 N r t) atTop
      (𝓝 ((poissonPMFReal (4 * energy κ) r : ℂ) * limitingKernel κ α C r t)) := by
  have hh := original_layer_kernel_limit h h0 h1 κ hκ hf N α C hC hN r t
  change Tendsto (fun m : ℕ ↦ contribution h h0 h1 N r t ((m + 1) + r)) atTop _ at hh
  apply (tendsto_add_atTop_iff_nat (1 + r)).mp
  simpa only [Nat.add_assoc] using hh

end Descent.Portability.HWEFixedLayerKernelLimit
