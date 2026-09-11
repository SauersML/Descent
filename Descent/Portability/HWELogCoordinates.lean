/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RademacherArrayWeakLimit

assert_below Descent.Decision Descent.Program

/-!
The near-balanced HWE log coordinate is derived from the original frequency
displacement. Its maximal magnitude vanishes and its squared total tends to 4K,
so the actual fair-sign log profile has Gaussian variance 4K.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWELogCoordinates

open scoped BigOperators Topology NNReal
open Filter Foundations SmallArrayContinuity RademacherArrayWeakLimit

/-- The centered frequency log coordinate, well defined as a real function. -/
noncomputable def coordinate (δ : ℝ) : ℝ :=
  (1 / 2) * (Real.log (1 / 2 + δ) - Real.log (1 / 2 - δ))

@[simp] theorem coordinate_zero : coordinate 0 = 0 := by simp [coordinate]

/-- On valid HWE frequencies this is exactly the report's one-half log odds. -/
theorem coordinate_frequency (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    coordinate (h.altFreq - 1 / 2) = (1 / 2) * Real.log (h.altFreq / (1 - h.altFreq)) := by
  rw [coordinate, Real.log_div h0.ne' (by linarith)]
  congr 2 <;> congr 1 <;> ring

/-- The coefficient 2 is a derivative calculation, not a supplied approximation. -/
theorem coordinate_derivative : HasDerivAt coordinate 2 0 := by
  have hp := ((hasDerivAt_const (0 : ℝ) (1 / 2 : ℝ)).add (hasDerivAt_id 0)).log
    (by norm_num : (1 / 2 : ℝ) + 0 ≠ 0)
  have hm := ((hasDerivAt_id (0 : ℝ)).const_sub (1 / 2)).log
    (by norm_num : (1 / 2 : ℝ) - 0 ≠ 0)
  convert (hp.sub hm).const_mul (1 / 2) using 1
  norm_num [coordinate]

/-- The differentiated slope factors the coordinate exactly, including δ=0. -/
theorem coordinate_slope (δ : ℝ) : δ * dslope coordinate 0 δ = coordinate δ := by
  simpa only [sub_zero, smul_eq_mul, coordinate_zero] using sub_smul_dslope coordinate 0 δ

theorem coordinate_square (δ : ℝ) :
    coordinate δ ^ 2 = δ ^ 2 * dslope coordinate 0 δ ^ 2 := by
  rw [← coordinate_slope, mul_pow]

/-- Total squared frequency displacement K becomes log-coordinate variance 4K. -/
theorem squared_coordinate_limit (δ : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (hδ : ∀ m i, |δ m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ)
    (hK : Tendsto (fun m ↦ ∑ i, δ m i ^ 2) atTop (𝓝 K)) :
    Tendsto (fun m ↦ ∑ i, coordinate (δ m i) ^ 2) atTop (𝓝 (4 * K)) := by
  have hg : ContinuousAt (fun x ↦ dslope coordinate 0 x ^ 2) 0 :=
    (continuousAt_dslope_same.mpr coordinate_derivative.differentiableAt).pow 2
  have h := weighted_continuous_limit _ hg δ (fun m i ↦ δ m i ^ 2)
    (fun m i ↦ sq_nonneg _) ε hδ hε K hK
  have he : K * (2 : ℝ) ^ 2 = 4 * K := by ring
  simpa only [← coordinate_square, dslope_same, coordinate_derivative.deriv, he] using h

/-- The actual maximum log-coordinate magnitude vanishes uniformly over each row. -/
theorem maximal_coordinate_limit (δ : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (hδ : ∀ m i, |δ m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun m ↦ ‖fun i : Fin m ↦ coordinate (δ m i)‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro r hr
  have hu := uniform_row_continuity coordinate coordinate_derivative.continuousAt
    δ ε hδ hε (r / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hu
  refine ⟨N, fun m hm ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hb : ‖fun i : Fin m ↦ coordinate (δ m i)‖ ≤ r / 2 := by
    apply (pi_norm_le_iff_of_nonneg
      (x := fun i : Fin m ↦ coordinate (δ m i)) (by positivity)).mpr
    intro i
    simpa only [Real.norm_eq_abs, coordinate_zero, sub_zero] using hN m hm i
  linarith

/-- The actual weighted fair-sign log profile converges to N(0,4K). -/
theorem fair_log_profile_limit (δ : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (hδ : ∀ m i, |δ m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, δ m i ^ 2) atTop (𝓝 (K : ℝ))) :
    Tendsto (fun m ↦ rowProbability (fun i ↦ coordinate (δ m i))) atTop
      (𝓝 (centeredGaussian (4 * K))) := by
  apply gaussian_weak_limit _ (fun m ↦ ‖fun i : Fin m ↦ coordinate (δ m i)‖)
  · intro m i
    exact norm_le_pi_norm (fun j : Fin m ↦ coordinate (δ m j)) i
  · exact maximal_coordinate_limit δ ε hδ hε
  · simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      squared_coordinate_limit δ ε hδ hε K hK

end Descent.Portability.HWELogCoordinates
