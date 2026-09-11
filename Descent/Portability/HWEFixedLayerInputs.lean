/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHomogeneousFrequencyLimit
import Descent.Portability.HWECountLayerLimit

assert_below Descent.Decision Descent.Program

/-!
The explicit homogeneous frequency experiment supplies all conditional log-budget
and Poisson layer-mass inputs, including after removing a fixed number of loci.
The energy is the actual squared displacement parameter kappa squared.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEFixedLayerInputs

open scoped BigOperators Topology NNReal
open Filter Foundations HWEHomogeneousFrequencyLimit HWEHeterozygosityLaw
open HWECountLayerLimit HWELayerPartition

/-- The limiting frequency energy specified by the homogeneous input. -/
noncomputable def energy (κ : ℝ) : ℝ≥0 := ⟨κ ^ 2, sq_nonneg κ⟩

/-- Remaining homozygous loci in a total row of size n+r. -/
def remaining (h : ℕ → HardyWeinbergModel) (r : ℕ) (n : ℕ) : Fin n → HardyWeinbergModel :=
  fun _ ↦ h (n + r)

/-- Exact displacement cap for that remaining row. -/
noncomputable def cap (h : ℕ → HardyWeinbergModel) (r n : ℕ) : ℝ :=
  |(h (n + r)).altFreq - 1 / 2|

/-- The conditional coordinate cap vanishes from the explicit frequency formula. -/
theorem cap_limit (h : ℕ → HardyWeinbergModel) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ)) (r : ℕ) :
    Tendsto (cap h r) atTop (𝓝 0) := by
  simpa only [cap, abs_zero] using
    ((displacement_limit h κ hf).comp (tendsto_add_atTop_nat r)).abs

/-- The remaining row's actual squared-displacement sum converges to the same energy. -/
theorem remaining_energy_limit (h : ℕ → HardyWeinbergModel) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ)) (r : ℕ) :
    Tendsto (fun m ↦ ∑ i, ((remaining h r m i).altFreq - 1 / 2) ^ 2) atTop
      (𝓝 (energy κ : ℝ)) := remaining_budget_limit h κ hf r

/-- The actual binomial count probability has its exact Poisson layer-mass limit. -/
theorem binomial_layer_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ)) (r : ℕ) :
    Tendsto (fun m : ℕ ↦ (m.choose r : ℝ) * probability (h m) ^ r *
      (1 - probability (h m)) ^ (m - r)) atTop
        (𝓝 (ProbabilityTheory.poissonPMFReal (4 * energy κ) r)) := by
  have hh := layer_mass_limit (remaining h 0) (fun m _ ↦ h0 (m + 0))
    (fun m _ ↦ h1 (m + 0)) (cap h 0) (fun m _ ↦ le_refl _) (cap_limit h κ hf 0)
    (energy κ) (remaining_energy_limit h κ hf 0) r
  simpa only [remaining, Nat.add_zero, homogeneous_count_mass, Fintype.card_fin] using hh

end Descent.Portability.HWEFixedLayerInputs
