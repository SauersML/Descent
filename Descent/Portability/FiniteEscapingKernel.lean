/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EscapingCharacteristicKernel
import Descent.Portability.FiniteAtomicReportMeasure

assert_below Descent.Decision Descent.Program

/-!
A linear reciprocal-amplitude bound controls the actual finite expectation of
the compensated characteristic kernel. Vanishing reciprocal L1 moments therefore
make a nonzero-amplitude layer disappear from the characteristic generator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteEscapingKernel

open scoped BigOperators Topology
open Filter HWEInteractionLaw CompensatedCharacteristicKernel EscapingCharacteristicKernel

/-- The global boundedness and the inverse-square estimate imply a linear reciprocal bound. -/
theorem kernel_reciprocal_bound (t y : ℝ) (hy : y ≠ 0) :
    ‖kernel t y‖ ≤ (2 + |t| + 5 * t ^ 2 / 2) * |y⁻¹| := by
  have hp : 0 < |y| := abs_pos.mpr hy
  rw [abs_inv]
  by_cases hh : 1 ≤ |y|
  · have hi : |y|⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hh
    have hi0 : 0 ≤ |y|⁻¹ := inv_nonneg.mpr hp.le
    have hs : (|y|⁻¹) ^ 2 ≤ |y|⁻¹ := by nlinarith
    have hb := kernel_inverse_bound t y hy
    have hn : 0 ≤ 5 * t ^ 2 / 2 * |y|⁻¹ := by positivity
    nlinarith
  · have hi : 1 ≤ |y|⁻¹ := by
      simpa using one_div_le_one_div_of_le hp (le_of_not_ge hh)
    have hb := value_bound t y
    change ‖kernel t y‖ ≤ 5 * t ^ 2 / 2 at hb
    have hc : 0 ≤ 2 + |t| + 5 * t ^ 2 / 2 := by positivity
    have hm := mul_le_mul_of_nonneg_left hi hc
    nlinarith [abs_nonneg t]

/-- Bound the actual characteristic-generator expectation by the finite reciprocal moment. -/
theorem expectation_bound {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (z : α → ℝ) (hz : ∀ x, z x ≠ 0) (t : ℝ) :
    ‖complexExpectation p (fun x ↦ kernel t (z x))‖ ≤
      (2 + |t| + 5 * t ^ 2 / 2) * p.expectation (fun x ↦ |(z x)⁻¹|) := by
  unfold complexExpectation
  calc
    _ ≤ ∑ x, ‖(p.mass x : ℂ) * kernel t (z x)‖ := norm_sum_le _ _
    _ ≤ ∑ x, p.mass x * ((2 + |t| + 5 * t ^ 2 / 2) * |(z x)⁻¹|) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (p.mass_nonneg x)]
      exact mul_le_mul_of_nonneg_left (kernel_reciprocal_bound t (z x) (hz x)) (p.mass_nonneg x)
    _ = _ := by
      simp only [FiniteReportLaw.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- A varying finite layer with vanishing reciprocal moment contributes zero to the generator. -/
theorem kernel_expectation_limit {α : ℕ → Type*} [∀ m, Fintype (α m)]
    (p : (m : ℕ) → FiniteReportLaw (α m)) (z : (m : ℕ) → α m → ℝ)
    (hz : ∀ᶠ m in atTop, ∀ x, z m x ≠ 0)
    (hL1 : Tendsto (fun m ↦ (p m).expectation (fun x ↦ |(z m x)⁻¹|)) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun m ↦ complexExpectation (p m) (fun x ↦ kernel t (z m x))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb : Tendsto (fun m ↦ (2 + |t| + 5 * t ^ 2 / 2) *
      (p m).expectation (fun x ↦ |(z m x)⁻¹|)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hL1.const_mul (2 + |t| + 5 * t ^ 2 / 2)
  apply squeeze_zero' (Eventually.of_forall (fun m ↦ norm_nonneg _)) ?_ hb
  filter_upwards [hz] with m hm
  exact expectation_bound (p m) (z m) hm t

end Descent.Portability.FiniteEscapingKernel
