/-
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
-/
import Descent.PCCorrectability.Geometry

namespace Descent

/-!
# Sharp design criteria

These results eliminate the square root and subgroup-size nuisance parameter
from the rank-one threshold model.  They are exact consequences of the model,
not an asymptotic approximation beyond the BBP proxy already isolated in
`Threshold`.
-/

/-- The balanced contrast crosses the spectral edge exactly when the
dimensionless information product `M F² n` exceeds one. -/
theorem balanced_superthreshold_iff_information
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F) :
    bbpProxyThreshold n M < F * n ↔ 1 < M * F ^ 2 * n := by
  have hratio : 0 < n / M := div_pos hn hM
  have hedge : 0 < bbpProxyThreshold n M := by
    exact Real.sqrt_pos.2 hratio
  have hbalanced : 0 < F * n := by positivity
  have hedge_sq : bbpProxyThreshold n M ^ 2 = n / M := by
    unfold bbpProxyThreshold
    exact Real.sq_sqrt (le_of_lt hratio)
  constructor
  · intro hcross
    have hsquares : bbpProxyThreshold n M ^ 2 < (F * n) ^ 2 :=
      (sq_lt_sq₀ (le_of_lt hedge) (le_of_lt hbalanced)).2 hcross
    rw [hedge_sq] at hsquares
    have hcleared : n < M * (F * n) ^ 2 := by
      simpa [mul_comm] using (div_lt_iff₀ hM).1 hsquares
    nlinarith [hn]
  · intro hinformation
    have hcleared : n < M * (F * n) ^ 2 := by
      nlinarith [hn]
    have hsquares : bbpProxyThreshold n M ^ 2 < (F * n) ^ 2 := by
      rw [hedge_sq]
      exact (div_lt_iff₀ hM).2 (by simpa [mul_comm] using hcleared)
    exact (sq_lt_sq₀ (le_of_lt hedge) (le_of_lt hbalanced)).1 hsquares

/-- A detectable valid subgroup exists exactly above the sharp information
boundary `M F² n = 1`. -/
theorem exists_superthreshold_subgroup_iff_information
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F) :
    (∃ m : ℝ, 0 < m ∧ m < n ∧
        bbpProxyThreshold n M < demographicSpike n F m) ↔
      1 < M * F ^ 2 * n := by
  exact (exists_superthreshold_subgroup_iff_balanced n M F hn (le_of_lt hF)).trans
    (balanced_superthreshold_iff_information n M F hn hM hF)

/-- Calculator form of the sharp boundary: the effective marker count must
exceed `1 / (F² n)`. -/
theorem exists_superthreshold_subgroup_iff_marker_requirement
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F) :
    (∃ m : ℝ, 0 < m ∧ m < n ∧
        bbpProxyThreshold n M < demographicSpike n F m) ↔
      1 / (F ^ 2 * n) < M := by
  rw [exists_superthreshold_subgroup_iff_information n M F hn hM hF]
  have hdenominator : 0 < F ^ 2 * n := mul_pos (sq_pos_of_pos hF) hn
  rw [div_lt_iff₀ hdenominator]
  ring_nf

/-- Equivalent calculator form: the sample size must exceed
`1 / (M F²)`. -/
theorem exists_superthreshold_subgroup_iff_sample_requirement
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F) :
    (∃ m : ℝ, 0 < m ∧ m < n ∧
        bbpProxyThreshold n M < demographicSpike n F m) ↔
      1 / (M * F ^ 2) < n := by
  rw [exists_superthreshold_subgroup_iff_information n M F hn hM hF]
  have hdenominator : 0 < M * F ^ 2 := mul_pos hM (sq_pos_of_pos hF)
  rw [div_lt_iff₀ hdenominator]
  ring_nf

/-- The balanced subgroup maximizes the signed correctability margin over all
real subgroup sizes. -/
theorem pcCorrectabilityMargin_le_balanced
    (n M F m : ℝ) (hn : 0 < n) (hF : 0 ≤ F) :
    pcCorrectabilityMargin n M F m ≤
      pcCorrectabilityMargin n M F (n / 2) := by
  unfold pcCorrectabilityMargin
  apply sub_le_sub_right
  calc
    demographicSpike n F m ≤ F * n :=
      demographicSpike_le_balanced n F m hn hF
    _ = demographicSpike n F (n / 2) := by
      unfold demographicSpike
      rw [effectiveSubgroupSize_balanced n hn]
      ring

end Descent
