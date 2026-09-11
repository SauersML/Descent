/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHeterozygosityLimit
import Descent.Portability.FiniteAtomicReportMeasure
import Descent.Portability.FirstMomentTightness
import Descent.Portability.PoissonRealCharacteristic
import Descent.Portability.TightCharacteristicConvergence

assert_below Descent.Decision Descent.Program

/-!
Actual weak convergence of the square-biased HWE heterozygosity count to a
Poisson law in the heterogeneous near-balanced window. Tightness follows from
the finite experiment's exact first moment, not an assumed limit theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHeterozygosityWeakLimit

open scoped BigOperators Topology NNReal
open Filter MeasureTheory Foundations HWEInteractionLaw HWEHeterozygosityLaw
open HWEHeterozygosityLimit BalancedHWEWeakLimit FiniteAtomicReportMeasure
open FirstMomentTightness PoissonRealCharacteristic TightCharacteristicConvergence

/-- The real-valued heterozygosity count under its original tilted genotype experiment. -/
noncomputable def countProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) : ProbabilityMeasure ℝ :=
  ⟨finiteMeasure (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))) count,
    inferInstance⟩

/-- The absolute first moment is exactly the sum of tilted success probabilities. -/
theorem count_absolute_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (∫ x : ℝ, |x| ∂(countProbability h h0 h1 : Measure ℝ)) = ∑ i, probability (h i) := by
  change (∫ x : ℝ, |x| ∂finiteMeasure _ count) = _
  rw [integral_finite_report]
  simp_rw [abs_of_nonneg (count_nonneg _)]
  exact count_mean h h0 h1

/-- Convergent intensity supplies tightness of the actual triangular count laws. -/
theorem counts_tight (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (r : ℝ) (hr : Tendsto (fun m ↦ ∑ i, probability (h m i)) atTop (𝓝 r)) :
    IsTightMeasureSet (Set.range (fun m ↦ (countProbability (h m) (h0 m) (h1 m) : Measure ℝ))) := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hr).exists_norm_le
  apply tight_of_first_moment_bound
    (fun m ↦ countProbability (h m) (h0 m) (h1 m)) (max 0 B) (le_max_left _ _)
  · intro m
    exact finite_report_integrable _ _ _
  · intro m
    rw [count_absolute_moment]
    exact ((le_abs_self _).trans (hB _ ⟨m, rfl⟩)).trans (le_max_right _ _)

/-- The full near-balanced count limit, including the degenerate zero-intensity case. -/
theorem poisson_weak_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ))) :
    Tendsto (fun m ↦ countProbability (h m) (h0 m) (h1 m)) atTop
      (𝓝 (poissonProbability (4 * K))) := by
  have hrate : Tendsto (fun m ↦ ∑ i, probability (h m i)) atTop (𝓝 (4 * (K : ℝ))) := by
    simpa only [probability, ← Finset.mul_sum] using hK.const_mul 4
  apply weak_convergence_of_tight_characteristic _ (poissonProbability (4 * K))
  · have ht := (isTightMeasureSet_singleton
      (μ := (poissonProbability (4 * K) : Measure ℝ))).union (counts_tight h h0 h1 _ hrate)
    simpa only [Set.singleton_union] using ht
  · intro t
    change Tendsto (fun m ↦ charFun (finiteMeasure
      (independentLaw (fun i ↦ squareBiasedLocus (h m i) (h0 m i) (h1 m i))) count) t)
      atTop (𝓝 (charFun (poissonReal (4 * K)) t))
    rw [charFun_poisson]
    simpa only [charFun_finite_report, NNReal.coe_mul, NNReal.coe_ofNat] using
      count_characteristic_limit h h0 h1 ε hcap hε K hK t

end Descent.Portability.HWEHeterozygosityWeakLimit
