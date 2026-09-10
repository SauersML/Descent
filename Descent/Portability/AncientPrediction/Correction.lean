/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
# Population correction geometry

Theorem 6 of *Ancient DNA for Modern Polygenic Prediction*. The quadratic form
is an uncentered feature second moment. No ancient demographic model is assumed
correct in this module. Finite populations permit one shared strictly positive
step; positive semidefiniteness is enough, including redundant features.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncientPrediction

open scoped BigOperators RealInnerProductSpace

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype G] [Nonempty G]

/-- A symmetric second-moment bilinear form, with its positivity obligation. -/
structure FeatureMoment (E : Type*) [AddCommGroup E] [Module ℝ E] where
  form : E →ₗ[ℝ] E →ₗ[ℝ] ℝ
  symmetric : ∀ x y, form x y = form y x
  nonneg : ∀ x, 0 ≤ form x x

/-- Exact MSE change in the affine correction class. -/
def riskChange (u : E) (V : FeatureMoment E) (α : E) : ℝ :=
  V.form α α - 2 * ⟪u, α⟫

/-- A finite shared step exists whenever every linear term points toward the
residual. This does not require nonsingular second moments. -/
theorem exists_common_step (u : G → E) (V : G → FeatureMoment E)
    (d : E) (hd : ∀ g, 0 < ⟪u g, d⟫) :
    ∃ t : ℝ, 0 < t ∧ ∀ g, riskChange (u g) (V g) (t • d) < 0 := by
  classical
  let b : G → ℝ := fun g => ⟪u g, d⟫ / ((V g).form d d + 1)
  have hb : ∀ g, 0 < b g := fun g =>
    div_pos (hd g) (by linarith [(V g).nonneg d])
  let t := Finset.univ.inf' Finset.univ_nonempty b
  have ht : 0 < t := (Finset.lt_inf'_iff _).mpr (fun g _ => hb g)
  refine ⟨t, ht, fun g => ?_⟩
  have hle : t ≤ b g := Finset.inf'_le b (Finset.mem_univ g)
  have hmul : t * ((V g).form d d + 1) ≤ ⟪u g, d⟫ :=
    (le_div_iff₀ (by linarith [(V g).nonneg d])).mp hle
  have hlin : t * (V g).form d d - 2 * ⟪u g, d⟫ < 0 := by linarith [hd g]
  have := mul_neg_of_pos_of_neg ht hlin
  simpa [riskChange, map_smul, inner_smul_right, mul_add, mul_sub, mul_assoc,
    mul_left_comm, mul_comm] using this

/-- Strict improvement and a common strict residual-correlation direction are
exactly equivalent. The converse uses positivity of actual feature moments. -/
theorem common_improvement_iff_direction (u : G → E) (V : G → FeatureMoment E) :
    (∃ α, ∀ g, riskChange (u g) (V g) α < 0) ↔
      ∃ d, ∀ g, 0 < ⟪u g, d⟫ := by
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, fun g => ?_⟩
    have := hα g
    have := (V g).nonneg α
    unfold riskChange at *
    linarith
  · rintro ⟨d, hd⟩
    obtain ⟨t, _, ht⟩ := exists_common_step u V d hd
    exact ⟨t • d, ht⟩

/-- Separation from the finite residual-correlation hull. The closest hull
point itself supplies a direction, including in an ambient Hilbert space. -/
theorem direction_iff_origin_not_mem_hull (u : G → E) :
    (∃ d, ∀ g, 0 < ⟪u g, d⟫) ↔ 0 ∉ convexHull ℝ (Set.range u) := by
  constructor
  · rintro ⟨d, hd⟩ hzero
    have hc : Convex ℝ {x : E | 0 < ⟪x, d⟫} := by
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq, inner_add_left, real_inner_smul_left] at *
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have : b = 1 := by linarith
        simp [this, hy]
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
    have hs : Set.range u ⊆ {x : E | 0 < ⟪x, d⟫} := by
      rintro x ⟨g, rfl⟩
      exact hd g
    have := convexHull_min hs hc hzero
    simp at this
  · intro hz
    have hne : (convexHull ℝ (Set.range u)).Nonempty :=
      (Set.range_nonempty u).mono (subset_convexHull ℝ _)
    have hcompact := (Set.finite_range u).isCompact_convexHull
    obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne
      hcompact.isComplete (convex_convexHull ℝ _) (0 : E)
    have hproj := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ _) hv).mp hmin
    have hv0 : v ≠ 0 := fun he => hz (he ▸ hv)
    have hsq : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr hv0
    refine ⟨v, fun g => ?_⟩
    have hg := hproj (u g) (subset_convexHull ℝ _ (Set.mem_range_self g))
    simp only [zero_sub, inner_neg_left, inner_sub_right] at hg
    rw [real_inner_comm] at hg
    linarith

/-- Theorem 6: the exact common-benefit obstruction for the affine dictionary. -/
theorem common_improvement_iff_origin_not_mem_hull (u : G → E)
    (V : G → FeatureMoment E) :
    (∃ α, ∀ g, riskChange (u g) (V g) α < 0) ↔
      0 ∉ convexHull ℝ (Set.range u) :=
  (common_improvement_iff_direction u V).trans (direction_iff_origin_not_mem_hull u)

omit [Nonempty G] in
/-- A population-mixture witness ruling out strict improvement. -/
theorem conflict_certificate (u : G → E) (V : G → FeatureMoment E)
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hw1 : ∑ g, w g = 1)
    (hcancel : ∑ g, w g • u g = 0) (α : E) :
    ∃ g, 0 ≤ riskChange (u g) (V g) α := by
  by_contra h
  push_neg at h
  have hsum : (∑ g, w g * riskChange (u g) (V g) α) < 0 := by
    have hpos : ∃ g, 0 < w g := by
      by_contra hn
      push_neg at hn
      have he : ∀ g, w g = 0 := fun g => le_antisymm (hn g) (hw g)
      simp [he] at hw1
    obtain ⟨g, hg⟩ := hpos
    exact Finset.sum_neg' (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw i) (h i).le)
      ⟨g, Finset.mem_univ g, mul_neg_of_pos_of_neg hg (h g)⟩
  have hinner : (∑ g, w g * ⟪u g, α⟫) = 0 := by
    simpa [sum_inner, inner_smul_left] using congrArg (fun x => ⟪x, α⟫) hcancel
  have hquad : 0 ≤ ∑ g, w g * (V g).form α α :=
    Finset.sum_nonneg fun g _ => mul_nonneg (hw g) ((V g).nonneg α)
  simp only [riskChange, mul_sub, Finset.sum_sub_distrib] at hsum
  have he : (∑ g, w g * (2 * ⟪u g, α⟫)) = 2 * ∑ g, w g * ⟪u g, α⟫ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [he, hinner] at hsum
  linarith

end Descent.Portability.AncientPrediction
