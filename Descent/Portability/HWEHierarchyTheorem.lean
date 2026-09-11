/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHierarchyCharacteristic
import Descent.Portability.HWEHierarchyLimitLaw
import Descent.Portability.HWENearBalancedTheorem

assert_below Descent.Decision Descent.Program

/-!
Full weak convergence for the original independent HWE score under the report's
homogeneous frequency and polynomial block-count inputs. Noninteger thresholds
give the Poisson-tail Gaussian; integer thresholds give the actual independent
Gaussian and compound-Poisson law constructed from the surviving count layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHierarchyTheorem

open scoped BigOperators Topology NNReal
open Filter MeasureTheory ProbabilityTheory Foundations HWEPolynomialLayerScale
open HWEHierarchyCharacteristic HWEHierarchyLimitLaw HWECriticalScoreCharacteristic
open HWENearBalancedTheorem TightCharacteristicConvergence

/-- The original unshifted score converges to the Gaussian law away from integer thresholds. -/
theorem noninteger_weak_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ) (hκ : κ ≠ 0)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C))
    (hα : ∀ r : ℕ, α ≠ (r : ℝ)) :
    Tendsto (fun m : ℕ ↦ scoreProbability (fun _ : Fin m ↦ h m) (N m)) atTop
      (𝓝 (gaussianLaw κ α)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply weak_convergence_of_tight_characteristic _ (gaussianLaw κ α)
  · have ht := (isTightMeasureSet_singleton (μ := (gaussianLaw κ α : Measure ℝ))).union
      (scores_tight (fun m _ ↦ h m) (fun m _ ↦ h0 m) (fun m _ ↦ h1 m) N)
    simpa only [Set.singleton_union] using ht
  · intro t
    rw [charFun_gaussianLaw κ α C t hα]
    exact hierarchy_characteristic_limit h h0 h1 κ hκ hf N α C hC hN t

/-- The original score converges to the Gaussian-plus-Poisson law at every integer layer. -/
theorem integer_weak_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ) (hκ : κ ≠ 0)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (r : ℕ) (C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) (r : ℝ)) atTop (𝓝 C)) :
    Tendsto (fun m : ℕ ↦ scoreProbability (fun _ : Fin m ↦ h m) (N m)) atTop
      (𝓝 (integerLaw κ C r)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply weak_convergence_of_tight_characteristic _ (integerLaw κ C r)
  · have ht := (isTightMeasureSet_singleton (μ := (integerLaw κ C r : Measure ℝ))).union
      (scores_tight (fun m _ ↦ h m) (fun m _ ↦ h0 m) (fun m _ ↦ h1 m) N)
    simpa only [Set.singleton_union] using ht
  · intro t
    rw [charFun_integerLaw κ C t hκ hC r]
    exact hierarchy_characteristic_limit h h0 h1 κ hκ hf N (r : ℝ) C hC hN t

end Descent.Portability.HWEHierarchyTheorem
