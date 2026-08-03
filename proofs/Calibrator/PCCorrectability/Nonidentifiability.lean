/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.PCCorrectability.Geometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Non-identifiability from aggregate differentiation
-/

/-- Aggregate differentiation alone cannot determine PC correctability: at
fixed positive differentiation, sample size, and marker count, two valid
subgroup sizes lie on opposite sides of the spectral threshold whenever the
balanced contrast is detectable. -/
theorem fst_does_not_determine_pc_correctability
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F) :
    bbpProxyThreshold n M < F * n →
      ∃ mBelow mAbove : ℝ,
        0 < mBelow ∧ mBelow < n ∧
        0 < mAbove ∧ mAbove < n ∧
        demographicSpike n F mBelow < bbpProxyThreshold n M ∧
        bbpProxyThreshold n M < demographicSpike n F mAbove := by
  intro hdetectable
  let t := bbpProxyThreshold n M
  have ht : 0 < t := by
    unfold t bbpProxyThreshold
    exact Real.sqrt_pos.2 (div_pos hn hM)
  let mBelow := t / (4 * F)
  let mAbove := n / 2
  have hmBelow_pos : 0 < mBelow := by
    exact div_pos ht (mul_pos (by norm_num) hF)
  have hmBelow_lt : mBelow < n := by
    unfold mBelow
    rw [div_lt_iff₀ (mul_pos (by norm_num) hF)]
    nlinarith [hdetectable]
  have hmAbove_pos : 0 < mAbove := by
    unfold mAbove
    linarith
  have hmAbove_lt : mAbove < n := by
    unfold mAbove
    linarith
  have heffective_below_lt : effectiveSubgroupSize n mBelow < mBelow := by
    unfold effectiveSubgroupSize
    rw [div_lt_iff₀ hn]
    nlinarith
  have hfour_below : 4 * F * mBelow = t := by
    unfold mBelow
    field_simp [hF.ne']
  have hspike_below : demographicSpike n F mBelow < t := by
    unfold demographicSpike
    calc
      4 * F * effectiveSubgroupSize n mBelow < 4 * F * mBelow :=
        mul_lt_mul_of_pos_left heffective_below_lt (mul_pos (by norm_num) hF)
      _ = t := hfour_below
  have hspike_above : t < demographicSpike n F mAbove := by
    have hidentity : demographicSpike n F mAbove = F * n := by
      unfold demographicSpike effectiveSubgroupSize mAbove
      field_simp [hn.ne']
      ring
    rw [hidentity]
    exact hdetectable
  exact ⟨mBelow, mAbove, hmBelow_pos, hmBelow_lt, hmAbove_pos, hmAbove_lt,
    hspike_below, hspike_above⟩

end Calibrator
