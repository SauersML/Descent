/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.PCCorrectability.Threshold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Spectral threshold geometry

This leaf proves the sharp subgroup-size geometry of the scalar threshold
model. It is independent of the correction-model and two-point construction
proofs so edits do not trigger unrelated recompilation.
-/

/-- Among all real subgroup sizes, the effective contrast size is maximized by
the balanced split. -/
theorem effectiveSubgroupSize_le_balanced (n m : ℝ) (hn : 0 < n) :
    effectiveSubgroupSize n m ≤ n / 4 := by
  unfold effectiveSubgroupSize
  rw [div_le_iff₀ hn]
  nlinarith [sq_nonneg (2 * m - n)]

/-- The balanced split attains the sharp effective-size upper bound. -/
theorem effectiveSubgroupSize_balanced (n : ℝ) (hn : 0 < n) :
    effectiveSubgroupSize n (n / 2) = n / 4 := by
  unfold effectiveSubgroupSize
  field_simp [hn.ne']
  ring

/-- For nonnegative differentiation, no subgroup contrast has a larger
rank-one spike than the balanced split. -/
theorem demographicSpike_le_balanced (n F m : ℝ) (hn : 0 < n) (hF : 0 ≤ F) :
    demographicSpike n F m ≤ F * n := by
  unfold demographicSpike
  calc
    4 * F * effectiveSubgroupSize n m ≤ 4 * F * (n / 4) :=
      mul_le_mul_of_nonneg_left (effectiveSubgroupSize_le_balanced n m hn)
        (mul_nonneg (by norm_num) hF)
    _ = F * n := by ring

/-- A valid subgroup can cross the spectral edge exactly when the balanced
contrast crosses it.  Thus `F * n` is the sharp feasibility boundary for
the rank-one demographic model. -/
theorem exists_superthreshold_subgroup_iff_balanced
    (n M F : ℝ) (hn : 0 < n) (hF : 0 ≤ F) :
    (∃ m : ℝ, 0 < m ∧ m < n ∧
        bbpProxyThreshold n M < demographicSpike n F m) ↔
      bbpProxyThreshold n M < F * n := by
  constructor
  · rintro ⟨m, _hm_pos, _hm_lt, hm_detectable⟩
    exact lt_of_lt_of_le hm_detectable (demographicSpike_le_balanced n F m hn hF)
  · intro hbalanced
    refine ⟨n / 2, by linarith, by linarith, ?_⟩
    rw [demographicSpike, effectiveSubgroupSize_balanced n hn]
    convert hbalanced using 1; ring

end Calibrator
