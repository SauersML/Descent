/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEExceptionalAmplitude

assert_below Descent.Decision Descent.Program

/-!
Under the report's near-balanced triangular-array assumptions, the part of the
actual square-biased interaction containing a heterozygote vanishes in absolute
first moment. Markov's bound gives vanishing probability at every fixed threshold.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEExceptionalLimit

open scoped BigOperators Topology
open Filter Foundations HWEInteractionLaw HWEHomozygoteLimit HWEAbsoluteLocusLaw
open HWEAbsoluteLocusBounds HWEHeterozygosityLaw HWEExceptionalAmplitude

/-- Exact exceptional absolute first moment of a square-biased HWE block. -/
noncomputable def exceptionalMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) : ℝ :=
  (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
    (fun x ↦ if count x = 0 then 0 else |normalized h x|)

theorem exceptionalMoment_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    0 ≤ exceptionalMoment h h0 h1 := by
  unfold exceptionalMoment FiniteReportLaw.expectation
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (FiniteReportLaw.mass_nonneg _ _) (by dsimp only; split_ifs <;> positivity)

/-- A finite-row quantitative bound expressed only in the original frequencies. -/
theorem finite_row_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (ε : ℝ) (hcap : ∀ i, |(h i).altFreq - 1 / 2| ≤ ε) (hsmall : ε ≤ 1 / 8) :
    exceptionalMoment h h0 h1 ≤ 16 * ε * ∑ i, ((h i).altFreq - 1 / 2) ^ 2 := by
  calc
    _ ≤ ∑ i, heteroMass (h i) := exceptional_bound h h0 h1 (fun i ↦ (hcap i).trans hsmall)
    _ ≤ ∑ i, 16 * ε * ((h i).altFreq - 1 / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact heteroMass_bound _ (h0 i) (h1 i) ε (hcap i) ((hcap i).trans hsmall)
    _ = _ := by rw [Finset.mul_sum]

/-- The full heterozygote-containing component collapses in actual absolute first moment. -/
theorem exceptional_L1_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 K)) :
    Tendsto (fun m ↦ exceptionalMoment (h m) (h0 m) (h1 m)) atTop (𝓝 0) := by
  have hb : Tendsto (fun m ↦ 16 * ε m * ∑ i, ((h m i).altFreq - 1 / 2) ^ 2)
      atTop (𝓝 0) := by simpa using (hε.const_mul 16).mul hK
  apply squeeze_zero' (Eventually.of_forall (fun m ↦ exceptionalMoment_nonneg _ _ _)) ?_ hb
  filter_upwards [hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with m hm
  exact finite_row_bound _ (h0 m) (h1 m) (ε m) (hcap m) hm.le

/-- A deterministic threshold certificate for the actual exceptional event. -/
theorem exceptional_markov {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (r : ℝ) (hr : 0 < r) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x ≠ 0 ∧ r ≤ |normalized h x| then 1 else 0) ≤
        exceptionalMoment h h0 h1 / r := by
  rw [le_div_iff₀ hr]
  unfold exceptionalMoment FiniteReportLaw.expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hc : count x = 0
  · simp [hc]
  · by_cases hz : r ≤ |normalized h x|
    · simpa [hc, hz] using mul_le_mul_of_nonneg_left hz
        (FiniteReportLaw.mass_nonneg _ _)
    · simp [hc, hz, mul_nonneg (FiniteReportLaw.mass_nonneg _ _) (abs_nonneg _)]

end Descent.Portability.HWEExceptionalLimit
