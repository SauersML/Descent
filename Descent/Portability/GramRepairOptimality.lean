/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GramSafeRepair

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Corollary 13: exact robust optimality in the
original coefficient coordinates, the literal soft-threshold formula, and
the lower certificate in terms of the true oracle signal. Every metric is
derived from the positive-definite Gram matrix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GramRepairOptimality

open Matrix GramSafeRepair

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The explicit update is the manuscript's positive-part shrinkage, including zero signal. -/
theorem soft_threshold (G : Matrix κ κ ℝ) (h : κ → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    repair G h ε = if signal G h = 0 then 0
      else (max 0 (1 - ε / signal G h)) • (G⁻¹ *ᵥ h) := by
  by_cases hz : signal G h = 0
  · rw [if_pos hz, repair, if_pos (by simpa only [hz] using hε)]
  · rw [if_neg hz]
    have hn : 0 < signal G h := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    by_cases hh : signal G h ≤ ε
    · rw [repair, if_pos hh, max_eq_left (by
        have hd : 1 ≤ ε / signal G h := (le_div_iff₀ hn).mpr (by simpa using hh)
        linarith), zero_smul]
    · have hp : 0 ≤ 1 - ε / signal G h := by
        have hd : ε / signal G h ≤ 1 := (div_le_iff₀ hn).mpr (by linarith)
        linarith
      rw [repair, if_neg hh, max_eq_right hp]
      congr 1
      field_simp

/-- The coefficient update attains the exact largest worst-case gain over the confidence ball. -/
theorem robust_optimum (G : Matrix κ κ ℝ) (hG : G.PosDef) (h : κ → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest {v : ℝ | ∃ θ : κ → ℝ, ∀ r, signal G (r - h) ≤ ε → v ≤ gain G θ r}
      (max 0 (signal G h - ε) ^ 2) := by
  constructor
  · exact ⟨repair G h ε, fun r hr ↦ (repair_certificate G hG h r ε hε hr).1⟩
  · rintro v ⟨θ, hθ⟩
    have hopt := SafeRepairGeometry.ball_robust_optimum (toGram G hG (G⁻¹ *ᵥ h)) ε hε
    rw [induced_signal G hG] at hopt
    apply hopt.2
    refine ⟨toGram G hG θ, ?_⟩
    intro s hs
    let r := G *ᵥ (s : κ → ℝ)
    have he : toGram G hG (G⁻¹ *ᵥ r) = s := by
      dsimp [r, toGram]
      exact inverse_normal_equation G hG s
    have hr : signal G (r - h) ≤ ε := by
      rw [← induced_error G hG, he]
      exact hs
    have hh := hθ r hr
    rw [← induced_gain G hG θ r, he] at hh
    exact hh

/-- Insufficient signal gives exactly the baseline coefficient vector. -/
theorem zero_update (G : Matrix κ κ ℝ) (h : κ → ℝ) (ε : ℝ)
    (hh : signal G h ≤ ε) : repair G h ε = 0 := by
  simp only [repair, if_pos hh]

/-- The reported lower gain is itself bounded below by the true signal minus twice uncertainty. -/
theorem certificate_vs_oracle (G : Matrix κ κ ℝ) (hG : G.PosDef) (h r : κ → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hc : signal G (r - h) ≤ ε) :
    max 0 (Real.sqrt (oracle G r) - 2 * ε) ^ 2 ≤ max 0 (signal G h - ε) ^ 2 := by
  have ht := norm_le_norm_add_norm_sub
    (toGram G hG (G⁻¹ *ᵥ h)) (toGram G hG (G⁻¹ *ᵥ r))
  rw [norm_sub_rev (toGram G hG (G⁻¹ *ᵥ h)), induced_error G hG,
    induced_signal G hG, induced_signal G hG] at ht
  have hm : max 0 (Real.sqrt (oracle G r) - 2 * ε) ≤ max 0 (signal G h - ε) := by
    apply max_le_max (le_refl 0)
    change signal G r - 2 * ε ≤ signal G h - ε
    linarith
  exact pow_le_pow_left₀ (le_max_left 0 _) hm 2

end Descent.Portability.GramRepairOptimality
