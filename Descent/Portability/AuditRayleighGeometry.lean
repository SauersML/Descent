/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AuditCovarianceSpectrum

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, the spectral audit geometry of Theorem 14.
The actual covariance eigenvalue is the attained largest quadratic form on
the unit ball, including a zero-dimensional repair space. A finite coefficient
perturbation bound supplies continuity for the spectral design objective.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AuditRayleighGeometry

open AuditCovarianceSpectrum
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A unit-ball quadratic form is bounded by the actual largest covariance eigenvalue. -/
theorem unit_quadratic_le (w : ι → ℝ) (u : ι → E) (hw : ∀ i, 0 ≤ w i)
    (a : E) (ha : ‖a‖ ≤ 1) :
    (∑ i, w i * (inner ℝ a (u i)) ^ 2) ≤ largest w u := by
  have hh := quadratic_le w u a
  have hn : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  exact hh.trans (by nlinarith [largest_nonneg w u hw])

/-- The maximum over the unit ball is attained, also when the repair space has dimension zero. -/
theorem unit_attained (w : ι → ℝ) (u : ι → E) :
    ∃ a : E, ‖a‖ ≤ 1 ∧ (∑ i, w i * (inner ℝ a (u i)) ^ 2) = largest w u := by
  by_cases hd : 0 < Module.finrank ℝ E
  · obtain ⟨a, ha, he⟩ := largest_attained w u hd
    exact ⟨a, ha.le, he⟩
  · refine ⟨0, by simp, ?_⟩
    simp [largest, hd]

/-- Bounding all unit-ball quadratic forms bounds the actual largest eigenvalue. -/
theorem largest_le_iff (w : ι → ℝ) (u : ι → E) (hw : ∀ i, 0 ≤ w i) (M : ℝ) :
    largest w u ≤ M ↔ ∀ a : E, ‖a‖ ≤ 1 → (∑ i, w i * (inner ℝ a (u i)) ^ 2) ≤ M := by
  constructor
  · intro h a ha
    exact (unit_quadratic_le w u hw a ha).trans h
  · intro h
    obtain ⟨a, ha, he⟩ := unit_attained w u
    rw [← he]
    exact h a ha

/-- Unit directions have squared coordinate leverage bounded by the row's squared norm. -/
theorem inner_sq_le (a v : E) (ha : ‖a‖ ≤ 1) : (inner ℝ a v) ^ 2 ≤ ‖v‖ ^ 2 := by
  have hh : |inner ℝ a v| ≤ ‖v‖ := by
    calc
      |inner ℝ a v| ≤ ‖a‖ * ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) a v
      _ ≤ ‖v‖ := by nlinarith [norm_nonneg v]
  have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg v)).mpr hh
  simpa only [sq_abs] using hs

/-- A one-sided eigenvalue perturbation bound from the actual coefficient differences. -/
theorem largest_sub_le (w v : ι → ℝ) (u : ι → E) (hv : ∀ i, 0 ≤ v i) :
    largest w u - largest v u ≤ ∑ i, |w i - v i| * ‖u i‖ ^ 2 := by
  obtain ⟨a, ha, he⟩ := unit_attained w u
  have hvq := unit_quadratic_le v u hv a ha
  have hd : (∑ i, w i * (inner ℝ a (u i)) ^ 2) -
      (∑ i, v i * (inner ℝ a (u i)) ^ 2) ≤ ∑ i, |w i - v i| * ‖u i‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = (w i - v i) * (inner ℝ a (u i)) ^ 2 := by ring
      _ ≤ |w i - v i| * (inner ℝ a (u i)) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ |w i - v i| * ‖u i‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (inner_sq_le a (u i) ha) (abs_nonneg _)
  rw [he] at hd
  linarith

/-- The spectral objective changes by at most the weighted absolute coefficient perturbation. -/
theorem largest_difference (w v : ι → ℝ) (u : ι → E)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) :
    |largest w u - largest v u| ≤ ∑ i, |w i - v i| * ‖u i‖ ^ 2 := by
  have h₁ := largest_sub_le w v u hv
  have h₂ := largest_sub_le v w u hw
  simp only [abs_sub_comm (v _) (w _)] at h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

/-- Continuous nonnegative coefficients produce a continuous actual covariance eigenvalue. -/
theorem largest_continuousOn {A : Type*} [TopologicalSpace A] (S : Set A)
    (w : A → ι → ℝ) (u : ι → E) (hw : ∀ x ∈ S, ∀ i, 0 ≤ w x i)
    (hc : ∀ i, ContinuousOn (fun x ↦ w x i) S) :
    ContinuousOn (fun x ↦ largest (w x) u) S := by
  intro x hx
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hcont : ContinuousOn (fun y ↦ ∑ i, |w y i - w x i| * ‖u i‖ ^ 2) S := by
    apply continuousOn_finset_sum
    intro i _
    exact (((hc i).sub continuousOn_const).abs).mul continuousOn_const
  have ht : Filter.Tendsto (fun y ↦ ∑ i, |w y i - w x i| * ‖u i‖ ^ 2)
      (nhdsWithin x S) (nhds 0) := by simpa using (hcont x hx).tendsto
  apply squeeze_zero' (Filter.Eventually.of_forall (fun y ↦ norm_nonneg _)) ?_ ht
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa only [Real.norm_eq_abs] using largest_difference (w y) (w x) u (hw y hy) (hw x hx)

end Descent.Portability.AuditRayleighGeometry
