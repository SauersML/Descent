/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHierarchyGenerator

assert_below Descent.Decision Descent.Program

/-!
Exact evaluation of the limiting HWE layer series. Noninteger thresholds retain
only the Gaussian upper tail; an integer threshold retains one additional
signed-lognormal kernel. The tail coefficients are actual Poisson probabilities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHierarchySeries

open scoped BigOperators Topology NNReal
open MeasureTheory ProbabilityTheory HWEHierarchyGenerator HWEFixedLayerKernelLimit
open HWEFixedLayerInputs HWEAmplitudeWeakLimit CompensatedCharacteristicKernel

/-- The mass of a Poisson count strictly above the real threshold. -/
noncomputable def tailMass (rate : ℝ≥0) (α : ℝ) : ℝ :=
  ∑' r : ℕ, if α < (r : ℝ) then poissonPMFReal rate r else 0

/-- The selected upper-tail probability series is summable. -/
theorem tail_summable (rate : ℝ≥0) (α : ℝ) :
    Summable (fun r : ℕ ↦ if α < (r : ℝ) then poissonPMFReal rate r else 0) := by
  apply (poissonPMFRealSum rate).summable.of_norm_bounded
  intro r
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg poissonPMFReal_nonneg]
  · simpa using (poissonPMFReal_nonneg (r := rate) (n := r))

/-- The Gaussian coefficient is a probability between zero and one. -/
theorem tail_bounds (rate : ℝ≥0) (α : ℝ) : 0 ≤ tailMass rate α ∧ tailMass rate α ≤ 1 := by
  constructor
  · apply tsum_nonneg
    intro r
    split_ifs
    · exact poissonPMFReal_nonneg
    · exact le_refl _
  · rw [← (poissonPMFRealSum rate).tsum_eq]
    apply (tail_summable rate α).tsum_le_tsum _ (poissonPMFRealSum rate).summable
    intro r
    split_ifs
    · exact le_refl _
    · exact poissonPMFReal_nonneg

/-- Below zero every Poisson layer contributes its Gaussian variance. -/
theorem tail_of_negative (rate : ℝ≥0) (α : ℝ) (hα : α < 0) : tailMass rate α = 1 := by
  unfold tailMass
  have hh (r : ℕ) : α < (r : ℝ) := lt_of_lt_of_le hα (Nat.cast_nonneg r)
  simp only [hh, if_true]
  exact (poissonPMFRealSum rate).tsum_eq

/-- Summing the Gaussian tail coefficients commutes with their complex scalar factor. -/
theorem gaussian_tail_sum (rate : ℝ≥0) (α t : ℝ) :
    (∑' r : ℕ, ((if α < (r : ℝ) then poissonPMFReal rate r else 0 : ℝ) : ℂ) *
      ((-(t ^ 2 / 2) : ℝ) : ℂ)) =
        (tailMass rate α : ℂ) * ((-(t ^ 2 / 2) : ℝ) : ℂ) := by
  rw [tsum_mul_right, ← Complex.ofReal_tsum]
  rfl

/-- Away from nonnegative integers the generator is exactly Gaussian. -/
theorem noninteger_generator (κ α C t : ℝ) (hα : ∀ r : ℕ, α ≠ (r : ℝ)) :
    seriesGenerator κ α C t =
      (tailMass (4 * energy κ) α : ℂ) * ((-(t ^ 2 / 2) : ℝ) : ℂ) := by
  rw [seriesGenerator, ← gaussian_tail_sum]
  apply tsum_congr
  intro r
  unfold seriesTerm limitingKernel
  rcases lt_or_gt_of_ne (hα r) with hlt | hgt
  · simp [hlt, not_lt.mpr hlt.le]
  · simp [hgt, not_lt.mpr hgt.le]

/-- At an integer threshold only that layer remains as a non-Gaussian kernel. -/
theorem integer_generator (κ C t : ℝ) (r : ℕ) :
    seriesGenerator κ (r : ℝ) C t =
      (tailMass (4 * energy κ) (r : ℝ) : ℂ) * ((-(t ^ 2 / 2) : ℝ) : ℂ) +
      (poissonPMFReal (4 * energy κ) r : ℂ) *
        (∫ y, kernel t y ∂(signedLognormal (energy κ)
          ((1 / Real.sqrt C) * (-2 * κ) ^ r) : Measure ℝ)) := by
  rw [seriesGenerator, (series_summable κ (r : ℝ) C t).tsum_eq_add_tsum_ite r]
  have hh : (∑' n : ℕ, if n = r then 0 else seriesTerm κ (r : ℝ) C t n) =
      (tailMass (4 * energy κ) (r : ℝ) : ℂ) * ((-(t ^ 2 / 2) : ℝ) : ℂ) := by
    rw [← gaussian_tail_sum]
    apply tsum_congr
    intro n
    by_cases hn : n = r
    · subst n
      simp
    · have hne : (n : ℝ) ≠ (r : ℝ) := by exact_mod_cast hn
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [hn, seriesTerm, limitingKernel, hlt, not_lt.mpr hlt.le]
      · simp [hn, seriesTerm, limitingKernel, hgt, not_lt.mpr hgt.le]
  rw [hh]
  simp only [seriesTerm, limitingKernel, lt_self_iff_false, if_false]
  exact add_comm _ _

end Descent.Portability.HWEHierarchySeries
