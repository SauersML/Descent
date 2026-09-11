/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWELayerPartition
import Descent.Portability.HWEHeterozygosityWeakLimit

assert_below Descent.Decision Descent.Program

/-!
Every fixed heterozygosity layer in the original square-biased HWE experiment
has its Poisson limiting mass. A continuous tent test isolates an integer atom,
so the conclusion follows from the proved count weak limit and its actual
integer support, without assuming point-mass convergence from weak convergence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWECountLayerLimit

open scoped BigOperators Topology NNReal BoundedContinuousFunction
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw HWEHeterozygosityLaw
open HWELayerPartition HWEHeterozygosityWeakLimit PoissonRealCharacteristic
open BalancedHWEWeakLimit

/-- A bounded continuous test that isolates one atom on the nonnegative integer support. -/
noncomputable def countTest (r : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ max 0 (1 - |x - (r : ℝ)|))
    (by fun_prop) 1 (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le (by norm_num) (by linarith [abs_nonneg (x - (r : ℝ))]))

/-- Adjacent integer atoms are separated exactly by the tent test. -/
theorem countTest_nat (r k : ℕ) : countTest r (k : ℝ) = if k = r then 1 else 0 := by
  change max 0 (1 - |(k : ℝ) - (r : ℝ)|) = _
  by_cases hk : k = r
  · simp [hk]
  rw [if_neg hk]
  apply max_eq_left
  rcases lt_or_gt_of_ne hk with h | h
  · have hh : (k : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hh : (r : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- On realized genotypes the continuous test is exactly the specified count indicator. -/
theorem countTest_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (x : ι → DiploidGenotype) :
    countTest r (count x) = if count x = (r : ℝ) then 1 else 0 := by
  rw [count_actualPattern, countTest_nat]
  simp only [Nat.cast_inj]

/-- The tent's integral under the actual atomic Poisson law is its specified atom probability. -/
theorem countTest_poisson (r : ℕ) (rate : ℝ≥0) :
    (∫ x, countTest r x ∂poissonReal rate) = poissonPMFReal rate r := by
  have hi := (countTest r).integrable (poissonReal rate)
  rw [poissonReal, integral_sum_measure hi]
  simp only [integral_smul_measure, integral_dirac, countTest_nat,
    ENNReal.toReal_ofReal poissonPMFReal_nonneg, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single r]
  · simp
  · intro k hk
    simp [hk]

/-- Fixed-layer mass convergence derived from the actual heterogeneous HWE count law. -/
theorem layer_mass_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (r : ℕ) :
    Tendsto (fun m ↦
      (independentLaw (fun i ↦ squareBiasedLocus (h m i) (h0 m i) (h1 m i))).expectation
        (fun x ↦ if count x = (r : ℝ) then 1 else 0)) atTop
          (𝓝 (poissonPMFReal (4 * K) r)) := by
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (poisson_weak_limit h h0 h1 ε hcap hε K hK) (countTest r)
  change Tendsto (fun m ↦ ∫ x, countTest r x ∂finiteMeasure
    (independentLaw (fun i ↦ squareBiasedLocus (h m i) (h0 m i) (h1 m i))) count)
      atTop (𝓝 (∫ x, countTest r x ∂poissonReal (4 * K))) at hh
  simpa only [integral_finiteMeasure, countTest_count, countTest_poisson] using hh

end Descent.Portability.HWECountLayerLimit
