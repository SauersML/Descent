/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SmallRealProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

assert_below Descent.Decision Descent.Program

/-!
The heterogeneous infinitesimal Rademacher characteristic product has a Gaussian
limit. The coefficient follows from the exact sinc identity and continuity,
without assuming a triangular-array central limit theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CosineArrayLimit

open scoped BigOperators Topology
open Filter SmallArrayContinuity

/-- Exact quadratic cosine deficit with a continuous coefficient at zero. -/
theorem cosine_deficit (t x : ℝ) :
    1 - Real.cos (t * x) = (t ^ 2 / 2) * x ^ 2 * Real.sinc (t * x / 2) ^ 2 := by
  have hsin : Real.sin (t * x / 2) = Real.sinc (t * x / 2) * (t * x / 2) := by
    by_cases hz : t * x / 2 = 0
    · simp [hz]
    · rw [Real.sinc_of_ne_zero hz, div_mul_cancel₀ _ hz]
  have h := Real.sin_sq_eq_half_sub (x := t * x / 2)
  have he : 2 * (t * x / 2) = t * x := by ring
  rw [he, hsin] at h
  nlinarith

/-- Uniformly small coordinates with convergent variance give the Gaussian cosine product. -/
theorem cosine_product_limit (a : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (ha : ∀ m i, |a m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0))
    (s : ℝ) (hs : Tendsto (fun m ↦ ∑ i, a m i ^ 2) atTop (𝓝 s)) (t : ℝ) :
    Tendsto (fun m ↦ ∏ i, Real.cos (t * a m i)) atTop (𝓝 (Real.exp (-(t ^ 2 * s / 2)))) := by
  let p := fun m i ↦ 1 - Real.cos (t * a m i)
  have hp (m : ℕ) (i : Fin m) : 0 ≤ p m i := sub_nonneg.mpr (Real.cos_le_one _)
  have hcap (m : ℕ) (i : Fin m) : p m i ≤ (t ^ 2 / 2) * ε m ^ 2 := by
    have hsinc : Real.sinc (t * a m i / 2) ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using
        (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr
          (Real.abs_sinc_le_one (t * a m i / 2))
    have heps : 0 ≤ ε m := (abs_nonneg _).trans (ha m i)
    have ha2 : a m i ^ 2 ≤ ε m ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) heps).mpr (ha m i)
    dsimp only [p]
    rw [cosine_deficit]
    calc
      _ ≤ (t ^ 2 / 2) * a m i ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hsinc (by positivity)
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left ha2 (by positivity : 0 ≤ t ^ 2 / 2)
  have hintensity : Tendsto (fun m ↦ ∑ i, p m i) atTop (𝓝 ((t ^ 2 / 2) * s)) := by
    have hg : ContinuousAt (fun x : ℝ ↦ Real.sinc (t * x / 2) ^ 2) 0 := by fun_prop
    have h := weighted_continuous_limit _ hg a (fun m i ↦ a m i ^ 2)
      (fun m i ↦ sq_nonneg _) ε ha hε s hs
    have h' := h.const_mul (t ^ 2 / 2)
    simpa only [mul_zero, zero_div, Real.sinc_zero, one_pow, mul_one, p,
      cosine_deficit, ← Finset.mul_sum, mul_assoc] using h'
  have h := SmallRealProduct.product_limit p hp (fun m ↦ (t ^ 2 / 2) * ε m ^ 2) hcap
    (by simpa only [zero_pow two_ne_zero, mul_zero] using (hε.pow 2).const_mul (t ^ 2 / 2))
    _ hintensity
  have he : -((t ^ 2 / 2) * s) = -(t ^ 2 * s / 2) := by ring
  simpa only [p, sub_sub_cancel, he] using h

end Descent.Portability.CosineArrayLimit
