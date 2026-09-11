/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHomogeneousFrequencyLimit
import Descent.Portability.HWECriticalAmplitudeLimit

assert_below Descent.Decision Descent.Program

/-!
The actual deterministic amplitude of a homogeneous heterozygosity layer factors
into a convergent coefficient and a power of interaction order. This derives the
scale responsible for the report's integer thresholds from its allele frequencies
and polynomially adjusted block intensity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEPolynomialLayerScale

open scoped Topology
open Filter Foundations HWEHomogeneousFrequencyLimit HWECriticalAmplitudeLimit

/-- The report's polynomially adjusted block intensity. -/
noncomputable def adjustedIntensity (m N : ℕ) (α : ℝ) : ℝ :=
  intensity m N * (m : ℝ) ^ α

/-- Deterministic layer amplitude relative to the conditional homozygous exponential. -/
noncomputable def layerScale (h : HardyWeinbergModel) (m N r : ℕ) : ℝ :=
  (1 / Real.sqrt (intensity m N)) * (h.standardizedGenotype .het / Real.sqrt 2) ^ r

/-- The finite coefficient left after extracting the critical polynomial scale. -/
noncomputable def coefficient (h : HardyWeinbergModel) (m N r : ℕ) (α : ℝ) : ℝ :=
  (1 / Real.sqrt (adjustedIntensity m N α)) *
    (Real.sqrt (m : ℝ) * (h.standardizedGenotype .het / Real.sqrt 2)) ^ r

/-- Exact real-power cancellation generating the threshold exponent. -/
theorem sqrt_power_balance (x α : ℝ) (hx : 0 < x) (r : ℕ) :
    Real.sqrt x ^ r * x ^ ((α - (r : ℝ)) / 2) = x ^ (α / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
    ← Real.rpow_add hx]
  congr 1
  ring

/-- Exact separation of an arbitrary positive block intensity from the layer's power of order. -/
theorem scale_factorization (x I α b : ℝ) (hx : 0 < x) (hI : 0 < I) (r : ℕ) :
    (1 / Real.sqrt I) * b ^ r =
      ((1 / Real.sqrt (I * x ^ α)) * (Real.sqrt x * b) ^ r) *
        x ^ ((α - (r : ℝ)) / 2) := by
  have hs : Real.sqrt (I * x ^ α) = Real.sqrt I * x ^ (α / 2) := by
    rw [Real.sqrt_mul hI.le, Real.sqrt_eq_rpow (x ^ α), ← Real.rpow_mul hx.le]
    congr 1
    congr 1
    ring
  have hsi : Real.sqrt I ≠ 0 := Real.sqrt_ne_zero'.mpr hI
  have hxp : x ^ (α / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  symm
  calc
    _ = (b ^ r / Real.sqrt I) *
        (Real.sqrt x ^ r * x ^ ((α - (r : ℝ)) / 2) / x ^ (α / 2)) := by
      rw [hs, mul_pow]
      field_simp
    _ = _ := by rw [sqrt_power_balance x α hx r, div_self hxp, mul_one]; ring

/-- The original layer scale has the stated exact polynomial factor. -/
theorem layerScale_factorization (h : HardyWeinbergModel) (m N r : ℕ) (α : ℝ)
    (hm : 0 < m) (hI : 0 < intensity m N) :
    layerScale h m N r = coefficient h m N r α * (m : ℝ) ^ ((α - (r : ℝ)) / 2) := by
  exact scale_factorization (m : ℝ) (intensity m N) α
    (h.standardizedGenotype .het / Real.sqrt 2) (by exact_mod_cast hm) hI r

/-- The finite coefficient limit is derived from the report's frequency and block-count inputs. -/
theorem coefficient_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C)) (r : ℕ) :
    Tendsto (fun m : ℕ ↦ coefficient (h m) m (N m) r α) atTop
      (𝓝 ((1 / Real.sqrt C) * (-2 * κ) ^ r)) := by
  have hs : Tendsto (fun m : ℕ ↦ 1 / Real.sqrt (adjustedIntensity m (N m) α))
      atTop (𝓝 (1 / Real.sqrt C)) :=
    tendsto_const_nhds.div (Real.continuous_sqrt.continuousAt.tendsto.comp hN)
      (Real.sqrt_ne_zero'.mpr hC)
  exact hs.mul ((heterozygote_factor_limit h h0 h1 κ hf).pow r)

/-- The factorization holds eventually from a positive limiting adjusted intensity. -/
theorem eventual_factorization (h : ℕ → HardyWeinbergModel) (N : ℕ → ℕ)
    (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C)) (r : ℕ) :
    ∀ᶠ m in atTop, layerScale (h m) m (N m) r =
      coefficient (h m) m (N m) r α * (m : ℝ) ^ ((α - (r : ℝ)) / 2) := by
  filter_upwards [hN.eventually (lt_mem_nhds hC), eventually_ge_atTop 1] with m hm hn
  have hp : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hi : 0 < intensity m (N m) := by
    exact (mul_pos_iff_of_pos_right (Real.rpow_pos_of_pos hp α)).mp hm
  exact layerScale_factorization (h m) m (N m) r α (by omega) hi

end Descent.Portability.HWEPolynomialLayerScale
