/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEPolynomialLayerScale

assert_below Descent.Decision Descent.Program

/-!
The report's explicit frequency and polynomial block-count assumptions imply
all three deterministic layer-scale regimes. The threshold is the integer
heterozygote count: higher layers collapse, equal layers remain finite, and lower
layers escape in absolute amplitude. No scale-limit hypothesis is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEPolynomialScaleRegimes

open scoped Topology
open Filter Foundations HWEPolynomialLayerScale

/-- Above the polynomial exponent, the actual heterozygosity-layer amplitude scale vanishes. -/
theorem layerScale_collapse (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C))
    (r : ℕ) (hr : α < (r : ℝ)) :
    Tendsto (fun m : ℕ ↦ layerScale (h m) m (N m) r) atTop (𝓝 0) := by
  have hc := coefficient_limit h h0 h1 κ hf N α C hC hN r
  have hp : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ ((α - (r : ℝ)) / 2)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by linarith : 0 < -((α - (r : ℝ)) / 2))).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_neg] using hh
  have hh := hc.mul hp
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventual_factorization h N α C hC hN r] with m hm
  exact hm.symm

/-- At an integer threshold the actual amplitude coefficient converges to its explicit value. -/
theorem layerScale_critical (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (C : ℝ) (hC : 0 < C) (r : ℕ)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) (r : ℝ)) atTop (𝓝 C)) :
    Tendsto (fun m : ℕ ↦ layerScale (h m) m (N m) r) atTop
      (𝓝 ((1 / Real.sqrt C) * (-2 * κ) ^ r)) := by
  apply (coefficient_limit h h0 h1 κ hf N (r : ℝ) C hC hN r).congr'
  filter_upwards [eventual_factorization h N (r : ℝ) C hC hN r] with m hm
  simpa only [sub_self, zero_div, Real.rpow_zero, mul_one] using hm.symm

/-- Below the polynomial exponent, a nonzero frequency displacement forces amplitude escape. -/
theorem layerScale_escape (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ) (hκ : κ ≠ 0)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C))
    (r : ℕ) (hr : (r : ℝ) < α) :
    Tendsto (fun m : ℕ ↦ |layerScale (h m) m (N m) r|) atTop atTop := by
  have hc := (coefficient_limit h h0 h1 κ hf N α C hC hN r).abs
  have hd : 0 < |(1 / Real.sqrt C) * (-2 * κ) ^ r| := by
    exact abs_pos.mpr (mul_ne_zero (one_div_ne_zero (Real.sqrt_ne_zero'.mpr hC))
      (pow_ne_zero _ (mul_ne_zero (by norm_num) hκ)))
  have hp : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ ((α - (r : ℝ)) / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < (α - (r : ℝ)) / 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  apply (hc.pos_mul_atTop hd hp).congr'
  filter_upwards [eventual_factorization h N α C hC hN r] with m hm
  symm
  rw [hm, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

end Descent.Portability.HWEPolynomialScaleRegimes
