/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWECriticalLimitLaw

assert_below Descent.Decision Descent.Program

/-!
The heterogeneous near-balanced HWE critical-window weak limit for the actual
independent genotype score. Finite-score second moments supply tightness, and the
proved characteristic limit identifies the constructed Gaussian-compound-Poisson law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWENearBalancedTheorem

open scoped BigOperators Topology NNReal
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw BalancedHWEWeakLimit
open HWECriticalAmplitudeLimit HWECriticalScoreCharacteristic HWECriticalLimitLaw
open FiniteAtomicReportMeasure SecondMomentTightness TightCharacteristicConvergence

/-- Unit second-moment control also covers rows with no sampled blocks. -/
theorem score_second_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (N : ℕ) :
    (independentLaw (fun _ : Fin N ↦ blockLaw h)).expectation
      (fun x ↦ score h N x ^ 2) ≤ 1 := by
  by_cases hn : N = 0
  · simp [hn, score, HWECriticalGenerator.summand, FiniteReportLaw.expectation]
  · rw [score_second h h0 h1 N (Nat.pos_of_ne_zero hn)]

/-- Tightness follows from the actual score moments for every finite row. -/
theorem scores_tight (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (N : ℕ → ℕ) :
    IsTightMeasureSet (Set.range (fun m ↦
      (scoreProbability (h (m + 1)) (N (m + 1)) : Measure ℝ))) := by
  apply tight_of_second_moment_bound _ 1 zero_le_one
  · intro m
    exact finite_report_integrable _ _ _
  · intro m
    change (∫ x : ℝ, x ^ 2 ∂finiteMeasure _
      (score (h (m + 1)) (N (m + 1)))) ≤ 1
    rw [integral_finite_report]
    exact score_second_bound _ (h0 _) (h1 _) _

/-- At critical intensity r, the original Poisson jump intensity is exactly r exp(4K). -/
theorem critical_jump_intensity (K : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    (jumpIntensity K (1 / Real.sqrt r) : ℝ) = r * Real.exp (4 * (K : ℝ)) := by
  change ((1 / Real.sqrt r) ^ 2)⁻¹ * Real.exp (4 * (K : ℝ)) = _
  rw [one_div, inv_pow, inv_inv, Real.sq_sqrt hr.le]

/-- Full weak limit under the report's heterogeneous near-balanced assumptions.
The limit is the explicitly constructed independent Gaussian and compound-Poisson sum. -/
theorem near_balanced_weak_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (N : ℕ → ℕ) (r : ℝ) (hr : 0 < r)
    (hN : Tendsto (fun m ↦ intensity m (N m)) atTop (𝓝 r)) :
    Tendsto (fun m ↦ scoreProbability (h (m + 1)) (N (m + 1))) atTop
      (𝓝 (criticalLaw K (1 / Real.sqrt r))) := by
  apply weak_convergence_of_tight_characteristic _ (criticalLaw K (1 / Real.sqrt r))
  · have ht := (isTightMeasureSet_singleton
      (μ := (criticalLaw K (1 / Real.sqrt r) : Measure ℝ))).union (scores_tight h h0 h1 N)
    simpa only [Set.singleton_union] using ht
  · intro t
    rw [charFun_criticalLaw K _ (one_div_ne_zero (Real.sqrt_pos.mpr hr).ne') t]
    exact score_characteristic_limit h h0 h1 ε hcap hε K hK N r hr hN t

end Descent.Portability.HWENearBalancedTheorem
