/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
Uniformly small triangular-array arguments may be replaced by zero inside
continuous weighted sums when their nonnegative total weights converge. This
supplies the uniform remainder step in heterogeneous critical-window limits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SmallArrayContinuity

open scoped BigOperators Topology
open Filter

/-- Continuity is uniform over every row whose largest absolute argument vanishes. -/
theorem uniform_row_continuity (g : ℝ → ℝ) (hg : ContinuousAt g 0)
    (a : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (ha : ∀ m i, |a m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m in atTop, ∀ i, |g (a m i) - g 0| ≤ δ := by
  obtain ⟨ρ, hρ, hlocal⟩ := Metric.continuousAt_iff.mp hg δ hδ
  filter_upwards [hε.eventually (gt_mem_nhds hρ)] with m hm
  intro i
  have hai : dist (a m i) 0 < ρ := by
    simpa only [Real.dist_eq, sub_zero] using (ha m i).trans_lt hm
  simpa only [Real.dist_eq] using (hlocal hai).le

/-- A continuous factor at uniformly vanishing arguments can be pulled out of
nonnegative weighted sums, with the limiting total weight retained exactly. -/
theorem weighted_continuous_limit (g : ℝ → ℝ) (hg : ContinuousAt g 0)
    (a w : (m : ℕ) → Fin m → ℝ) (hw : ∀ m i, 0 ≤ w m i)
    (ε : ℕ → ℝ) (ha : ∀ m i, |a m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0))
    (s : ℝ) (hs : Tendsto (fun m ↦ ∑ i, w m i) atTop (𝓝 s)) :
    Tendsto (fun m ↦ ∑ i, w m i * g (a m i)) atTop (𝓝 (s * g 0)) := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hs).exists_norm_le
  let C := max 0 B
  have hC : 0 ≤ C := le_max_left _ _
  have htotal (m : ℕ) : ∑ i, w m i ≤ C :=
    ((le_abs_self _).trans (hB _ ⟨m, rfl⟩)).trans (le_max_right _ _)
  have herror : Tendsto (fun m ↦ (∑ i, w m i * g (a m i)) -
      (∑ i, w m i) * g 0) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro δ hδ
    have hCp : 0 < C + 1 := by linarith
    have hsmall := uniform_row_continuity g hg a ε ha hε (δ / (C + 1))
      (div_pos hδ hCp)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
    refine ⟨N, fun m hm ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, Finset.sum_mul, ← Finset.sum_sub_distrib]
    have hbound : |∑ i, (w m i * g (a m i) - w m i * g 0)| ≤ C * (δ / (C + 1)) := by
      calc
        _ ≤ ∑ i, |w m i * g (a m i) - w m i * g 0| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, w m i * |g (a m i) - g 0| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← mul_sub, abs_mul, abs_of_nonneg (hw m i)]
        _ ≤ ∑ i, w m i * (δ / (C + 1)) :=
          Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hN m hm i) (hw m i))
        _ ≤ C * (δ / (C + 1)) := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (htotal m) (div_nonneg hδ.le hCp.le)
    apply hbound.trans_lt
    have hid : (C + 1) * (δ / (C + 1)) = δ := mul_div_cancel₀ _ hCp.ne'
    have hp : 0 < δ / (C + 1) := div_pos hδ hCp
    nlinarith
  have hmain := hs.mul_const (g 0)
  simpa only [sub_add_cancel, zero_add] using herror.add hmain

end Descent.Portability.SmallArrayContinuity
