/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEFixedLayerKernelLimit
import Descent.Portability.FiniteCountTail

assert_below Descent.Decision Descent.Program

/-!
A uniform count-layer truncation certificate for the original HWE characteristic
generator. Its error is controlled by the actual square-biased heterozygosity
mean, which the explicit frequency formula makes uniformly bounded in the tail.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEKernelTruncation

open scoped BigOperators Topology
open Filter Foundations HWEInteractionLaw HWEHeterozygosityLaw HWELayerPartition
open HWEFixedLayerKernelLimit HWEHomogeneousFrequencyLimit CompensatedCharacteristicKernel

/-- The actual square-biased kernel expectation before splitting into count layers. -/
noncomputable def tiltedKernel (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1)
    (N : ℕ → ℕ) (t : ℝ) (m : ℕ) : ℂ :=
  complexExpectation (independentLaw (fun _ : Fin m ↦ squareBiasedLocus (h m) (h0 m) (h1 m)))
    (fun x ↦ kernel t (interaction (fun _ : Fin m ↦ h m) x / Real.sqrt (N m : ℝ)))

/-- Natural and real count indicators agree on the original genotype support. -/
theorem pattern_count_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → DiploidGenotype) (r : ℕ) :
    (actualPattern x).card = r ↔ count x = (r : ℝ) := by
  rw [count_actualPattern, Nat.cast_inj]

/-- The first count moment is exactly four times the row's squared-frequency budget. -/
theorem count_moment (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (m : ℕ) :
    (independentLaw (fun _ : Fin m ↦ squareBiasedLocus h h0 h1)).expectation
      (fun x ↦ ((actualPattern x).card : ℝ)) = 4 * (m : ℝ) * (h.altFreq - 1 / 2) ^ 2 := by
  simp_rw [← count_actualPattern]
  rw [count_mean (fun _ : Fin m ↦ h) (fun _ ↦ h0) (fun _ ↦ h1)]
  simp only [probability, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A finite, original-experiment error certificate for keeping only the first R count layers. -/
theorem truncation_bound (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1)
    (N : ℕ → ℕ) (t : ℝ) (m R : ℕ) (hR : 0 < R) :
    ‖tiltedKernel h h0 h1 N t m - ∑ r ∈ Finset.range R, contribution h h0 h1 N r t m‖ ≤
      ((5 * t ^ 2 / 2) / (R : ℝ)) * (4 * (m : ℝ) * ((h m).altFreq - 1 / 2) ^ 2) := by
  have hh := FiniteCountTail.truncation_error
    (independentLaw (fun _ : Fin m ↦ squareBiasedLocus (h m) (h0 m) (h1 m)))
    (fun x ↦ (actualPattern x).card)
    (fun x ↦ kernel t (interaction (fun _ : Fin m ↦ h m) x / Real.sqrt (N m : ℝ)))
    (5 * t ^ 2 / 2) (by positivity) (fun x ↦ value_bound t _) R hR
  simpa only [pattern_count_eq, count_moment, tiltedKernel, contribution] using hh

/-- One eventual bound controls every truncation level and frequency simultaneously. -/
theorem eventual_uniform_truncation (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) :
    ∀ᶠ m in atTop, ∀ R : ℕ, 0 < R → ∀ t : ℝ,
      ‖tiltedKernel h h0 h1 N t m - ∑ r ∈ Finset.range R, contribution h h0 h1 N r t m‖ ≤
        ((5 * t ^ 2 / 2) / (R : ℝ)) * (4 * κ ^ 2 + 1) := by
  have hr := (squared_budget_limit h κ hf).const_mul 4
  have hh := hr.eventually (gt_mem_nhds (show 4 * κ ^ 2 < 4 * κ ^ 2 + 1 by linarith))
  filter_upwards [hh] with m hm
  intro R hR t
  have hb := truncation_bound h h0 h1 N t m R hR
  have hc : 4 * (m : ℝ) * ((h m).altFreq - 1 / 2) ^ 2 ≤ 4 * κ ^ 2 + 1 := by
    nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))

end Descent.Portability.HWEKernelTruncation
