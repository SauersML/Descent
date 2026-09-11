/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorems 11--13, in whitened repair coordinates.
The gain is a quadratic with an exact oracle. Projection of zero onto a convex
confidence set gives an attained robust optimum. For a confidence ball the
optimizer is explicit, including zero signal and zero radius, and obeys the
four-radius-squared oracle regret bound. Statistical coverage is not assumed
to follow from these deterministic geometric statements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SafeRepairGeometry

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact squared-loss improvement in whitened coordinates. -/
noncomputable def gain (u s : E) : ℝ := 2 * ⟪u, s⟫ - ‖u‖ ^ 2

/-- The explicit conservative repair, with its zero-output regime included. -/
noncomputable def safe (h : E) (ε : ℝ) : E :=
  if ‖h‖ ≤ ε then 0 else ((‖h‖ - ε) / ‖h‖) • h

/-- Completing the square identifies both the oracle and the exact regret. -/
theorem gain_eq_oracle_sub_regret (u s : E) :
    gain u s = ‖s‖ ^ 2 - ‖u - s‖ ^ 2 := by
  rw [norm_sub_sq_real]
  unfold gain
  ring

/-- No correction exceeds the oracle's improvement. -/
theorem gain_le_oracle (u s : E) : gain u s ≤ ‖s‖ ^ 2 := by
  rw [gain_eq_oracle_sub_regret]
  exact sub_le_self _ (sq_nonneg _)

/-- The oracle correction attains the upper bound exactly. -/
theorem gain_self (s : E) : gain s s = ‖s‖ ^ 2 := by
  simp [gain_eq_oracle_sub_regret]

/-- A complete convex confidence set has an attained robustly optimal repair. -/
theorem convex_robust_optimum (C : Set E) (hne : C.Nonempty)
    (hcomplete : IsComplete C) (hc : Convex ℝ C) :
    ∃ u ∈ C, (∀ s ∈ C, ‖u‖ ^ 2 ≤ gain u s) ∧
      IsGreatest {v : ℝ | ∃ a : E, ∀ s ∈ C, v ≤ gain a s} (‖u‖ ^ 2) := by
  obtain ⟨u, hu, hn⟩ := exists_norm_eq_iInf_of_complete_convex hne hcomplete hc (0 : E)
  have hnormal := (norm_eq_iInf_iff_real_inner_le_zero hc hu).mp hn
  have hlower : ∀ s ∈ C, ‖u‖ ^ 2 ≤ gain u s := by
    intro s hs
    have hh := hnormal s hs
    simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hh
    unfold gain
    linarith
  refine ⟨u, hu, hlower, ⟨⟨u, hlower⟩, ?_⟩⟩
  rintro v ⟨a, ha⟩
  exact (ha u hu).trans (gain_le_oracle a u)

/-- A compact convex confidence set satisfies the completeness needed above. -/
theorem compact_robust_optimum (C : Set E) (hne : C.Nonempty)
    (hcompact : IsCompact C) (hc : Convex ℝ C) :
    ∃ u ∈ C, (∀ s ∈ C, ‖u‖ ^ 2 ≤ gain u s) ∧
      IsGreatest {v : ℝ | ∃ a : E, ∀ s ∈ C, v ≤ gain a s} (‖u‖ ^ 2) :=
  convex_robust_optimum C hne hcompact.isComplete hc

/-- Insufficient estimated signal gives exactly zero correction. -/
theorem safe_zero (h : E) (ε : ℝ) (hh : ‖h‖ ≤ ε) : safe h ε = 0 := by
  simp [safe, hh]

/-- The norm of the repair is the positive part of signal minus uncertainty. -/
theorem safe_norm (h : E) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖safe h ε‖ = max 0 (‖h‖ - ε) := by
  by_cases hh : ‖h‖ ≤ ε
  · simp [safe, hh]
  · have hn : 0 < ‖h‖ := lt_of_le_of_lt hε (lt_of_not_ge hh)
    have hd : 0 ≤ (‖h‖ - ε) / ‖h‖ := div_nonneg (by linarith) hn.le
    rw [safe, if_neg hh, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd,
      div_mul_cancel₀ _ hn.ne', max_eq_right (by linarith)]

/-- The computed repair itself belongs to the confidence ball. -/
theorem safe_in_ball (h : E) (ε : ℝ) (hε : 0 ≤ ε) : ‖safe h ε - h‖ ≤ ε := by
  by_cases hh : ‖h‖ ≤ ε
  · simpa [safe, hh] using hh
  · have hn : 0 < ‖h‖ := lt_of_le_of_lt hε (lt_of_not_ge hh)
    have he : safe h ε - h = (-ε / ‖h‖) • h := by
      rw [safe, if_neg hh]
      calc
        _ = (((‖h‖ - ε) / ‖h‖) - 1) • h := by rw [sub_smul, one_smul]
        _ = _ := by congr 1; field_simp; ring
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hε) hn.le)]
    have hc : -(-ε / ‖h‖) * ‖h‖ = ε := by field_simp
    rw [hc]

/-- Cauchy--Schwarz gives a uniform lower gain over the complete confidence ball. -/
theorem ball_gain_lower (u h s : E) (ε : ℝ) (hs : ‖s - h‖ ≤ ε) :
    gain u h - 2 * ε * ‖u‖ ≤ gain u s := by
  have hh := real_inner_le_norm u (h - s)
  have hd : ‖h - s‖ ≤ ε := by simpa only [norm_sub_rev] using hs
  have hb := mul_le_mul_of_nonneg_left hd (norm_nonneg u)
  rw [inner_sub_right] at hh
  unfold gain
  nlinarith

/-- At the explicit repair the robust lower objective equals the claimed certificate. -/
theorem safe_lower_value (h : E) (ε : ℝ) (hε : 0 ≤ ε) :
    gain (safe h ε) h - 2 * ε * ‖safe h ε‖ = max 0 (‖h‖ - ε) ^ 2 := by
  by_cases hh : ‖h‖ ≤ ε
  · simp [safe, hh, gain]
  · have hn : 0 < ‖h‖ := lt_of_le_of_lt hε (lt_of_not_ge hh)
    rw [gain, safe_norm h ε hε, safe, if_neg hh,
      inner_smul_left, real_inner_self_eq_norm_sq, max_eq_right (by linarith)]
    simp only [conj_trivial]
    field_simp [hn.ne']
    ring

/-- Every mean vector covered by the confidence ball gets the certified true gain. -/
theorem safe_gain (h s : E) (ε : ℝ) (hε : 0 ≤ ε) (hs : ‖s - h‖ ≤ ε) :
    max 0 (‖h‖ - ε) ^ 2 ≤ gain (safe h ε) s := by
  rw [← safe_lower_value h ε hε]
  exact ball_gain_lower (safe h ε) h s ε hs

/-- The explicit update solves the entire robust optimization problem, with attainment. -/
theorem ball_robust_optimum (h : E) (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest {v : ℝ | ∃ u : E, ∀ s, ‖s - h‖ ≤ ε → v ≤ gain u s}
      (max 0 (‖h‖ - ε) ^ 2) := by
  refine ⟨⟨safe h ε, fun s hs ↦ safe_gain h s ε hε hs⟩, ?_⟩
  rintro v ⟨u, hu⟩
  have hh := (hu (safe h ε) (safe_in_ball h ε hε)).trans (gain_le_oracle u (safe h ε))
  simpa only [safe_norm h ε hε] using hh

/-- The audit-selected repair has at most four squared radii of oracle regret. -/
theorem safe_oracle_regret (h s : E) (ε : ℝ) (hε : 0 ≤ ε) (hs : ‖s - h‖ ≤ ε) :
    0 ≤ ‖s‖ ^ 2 - gain (safe h ε) s ∧
      ‖s‖ ^ 2 - gain (safe h ε) s ≤ 4 * ε ^ 2 := by
  rw [gain_eq_oracle_sub_regret]
  have hd : ‖safe h ε - s‖ ≤ 2 * ε := by
    have ht := dist_triangle (safe h ε) h s
    simp only [dist_eq_norm] at ht
    have hr := safe_in_ball h ε hε
    have hs' : ‖h - s‖ ≤ ε := by simpa only [norm_sub_rev] using hs
    linarith
  constructor
  · nlinarith [sq_nonneg ‖safe h ε - s‖]
  · have hh := mul_self_le_mul_self (norm_nonneg _) hd
    nlinarith

/-- The same confidence ball gives a two-sided interval for the best possible span gain. -/
theorem oracle_interval (h s : E) (ε : ℝ) (hε : 0 ≤ ε) (hs : ‖s - h‖ ≤ ε) :
    max 0 (‖h‖ - ε) ^ 2 ≤ ‖s‖ ^ 2 ∧ ‖s‖ ^ 2 ≤ (‖h‖ + ε) ^ 2 := by
  constructor
  · exact (safe_gain h s ε hε hs).trans (gain_le_oracle _ _)
  · have hn := norm_le_norm_add_norm_sub h s
    rw [norm_sub_rev h s] at hn
    have hd : ‖s‖ ≤ ‖h‖ + ε := by linarith
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2

end Descent.Portability.SafeRepairGeometry
