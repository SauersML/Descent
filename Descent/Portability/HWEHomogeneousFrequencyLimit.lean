/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEPatternAmplitude
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

assert_below Descent.Decision Descent.Program

/-!
The report's explicit homogeneous frequency formula implies the near-balanced
budgets used in the conditional layer limit. Removing any fixed number of loci
preserves that budget. The scaled original heterozygote factor tends to -2 kappa.
The frequency formula is required only eventually, permitting valid initial rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHomogeneousFrequencyLimit

open scoped BigOperators Topology
open Filter Foundations HWEPatternAmplitude

/-- The explicit frequency displacement vanishes. -/
theorem displacement_limit (h : ℕ → HardyWeinbergModel) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ)) :
    Tendsto (fun m : ℕ ↦ (h m).altFreq - 1 / 2) atTop (𝓝 0) := by
  have hs : Tendsto (fun m : ℕ ↦ Real.sqrt (m : ℝ)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh : Tendsto (fun m : ℕ ↦ κ / Real.sqrt (m : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.comp hs).const_mul κ
  apply hh.congr'
  filter_upwards [hf] with m hm
  exact hm.symm

/-- The allele frequency itself converges to one half. -/
theorem frequency_limit (h : ℕ → HardyWeinbergModel) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ)) :
    Tendsto (fun m : ℕ ↦ (h m).altFreq) atTop (𝓝 (1 / 2)) := by
  have hh := (displacement_limit h κ hf).add_const (1 / 2 : ℝ)
  convert hh using 1
  · funext m
    ring
  · norm_num

/-- The exact scaled displacement tends to kappa, including either sign of kappa. -/
theorem scaled_displacement_limit (h : ℕ → HardyWeinbergModel) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ)) :
    Tendsto (fun m : ℕ ↦ Real.sqrt (m : ℝ) * ((h m).altFreq - 1 / 2)) atTop (𝓝 κ) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hf, eventually_ge_atTop 1] with m hm hpos
  have hs : Real.sqrt (m : ℝ) ≠ 0 := by positivity
  rw [hm]
  field_simp

/-- The full row's squared displacement budget is kappa squared. -/
theorem squared_budget_limit (h : ℕ → HardyWeinbergModel) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ)) :
    Tendsto (fun m : ℕ ↦ (m : ℝ) * ((h m).altFreq - 1 / 2) ^ 2) atTop (𝓝 (κ ^ 2)) := by
  have hh := (scaled_displacement_limit h κ hf).pow 2
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using hh

/-- After removing r loci, the remaining signs retain the same limiting log-variance budget. -/
theorem remaining_budget_limit (h : ℕ → HardyWeinbergModel) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ)) (r : ℕ) :
    Tendsto (fun m : ℕ ↦ ∑ _i : Fin m, ((h (m + r)).altFreq - 1 / 2) ^ 2)
      atTop (𝓝 (κ ^ 2)) := by
  have hb := (squared_budget_limit h κ hf).comp (tendsto_add_atTop_nat r)
  have hz := (((displacement_limit h κ hf).comp (tendsto_add_atTop_nat r)).pow 2).const_mul
    (r : ℝ)
  have hh := hb.sub hz
  simp only [Function.comp_def, Nat.cast_add, zero_pow (by decide : 2 ≠ 0), mul_zero,
    sub_zero] at hh
  convert hh using 1
  funext m
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The original scaled heterozygote factor has the required explicit finite limit. -/
theorem heterozygote_factor_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ)) :
    Tendsto (fun m : ℕ ↦ Real.sqrt (m : ℝ) * ((h m).standardizedGenotype .het / Real.sqrt 2))
      atTop (𝓝 (-2 * κ)) := by
  have hp := frequency_limit h κ hf
  have hq : Tendsto (fun m : ℕ ↦ 1 - (h m).altFreq) atTop (𝓝 (1 - 1 / 2 : ℝ)) :=
    tendsto_const_nhds.sub hp
  have hd : Tendsto (fun m : ℕ ↦ Real.sqrt ((h m).altFreq * (1 - (h m).altFreq)))
      atTop (𝓝 (1 / 2)) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp (hp.mul hq) using 1 <;> norm_num
  have he (m : ℕ) : Real.sqrt (m : ℝ) *
      ((h m).standardizedGenotype .het / Real.sqrt 2) =
        -(Real.sqrt (m : ℝ) * ((h m).altFreq - 1 / 2)) /
          Real.sqrt ((h m).altFreq * (1 - (h m).altFreq)) := by
    rw [standardized_heterozygote (h m) (h0 m) (h1 m)]
    have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    field_simp
  have hh := (scaled_displacement_limit h κ hf).neg.div hd (by norm_num : (1 / 2 : ℝ) ≠ 0)
  convert hh using 1
  · funext m
    exact he m
  · ring

end Descent.Portability.HWEHomogeneousFrequencyLimit
