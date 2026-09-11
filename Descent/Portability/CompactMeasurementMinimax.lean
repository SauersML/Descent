/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompactSingularSequence
import Mathlib.Analysis.InnerProductSpace.PiL2

assert_below Descent.Decision Descent.Program

/-!
Exact deterministic adaptive measurement error for a compact target operator
between complete Hilbert spaces, with no finite-dimensional ambient assumption.
The singular sequence and attaining questions are constructed by compact deflation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompactMeasurementMinimax

open scoped BigOperators
open CompactSingularSequence AdaptiveLinearMeasurements

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Before the residual vanishes, all leading directions form an orthonormal family. -/
theorem prefix_orthonormal (L : E →L[ℝ] F) (hc : IsCompactOperator L) (q : ℕ)
    (hq : (residual L hc q).1 ≠ 0) :
    Orthonormal ℝ (fun i : Fin (q + 1) ↦ direction L hc i) := by
  constructor
  · intro i
    apply leading_unit
    intro hi
    have hbound := residual_norm_antitone L hc (show (i : ℕ) ≤ q by omega)
    change ‖(residual L hc q).1‖ ≤ ‖(residual L hc i).1‖ at hbound
    rw [hi, norm_zero] at hbound
    exact hq (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))
  · intro i j hij
    have hne : (i : ℕ) ≠ j := fun h ↦ hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · rw [real_inner_comm]
      exact directions_orthogonal L hc i j h
    · exact directions_orthogonal L hc j i h

noncomputable def prefixSpace (L : E →L[ℝ] F) (hc : IsCompactOperator L) (q : ℕ) :
    Submodule ℝ E := Submodule.span ℝ (Set.range (fun i : Fin (q + 1) ↦ direction L hc i))

instance prefixSpace_finite (L : E →L[ℝ] F) (hc : IsCompactOperator L) (q : ℕ) :
    FiniteDimensional ℝ (prefixSpace L hc q) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem prefixSpace_finrank (L : E →L[ℝ] F) (hc : IsCompactOperator L) (q : ℕ)
    (hq : (residual L hc q).1 ≠ 0) : Module.finrank ℝ (prefixSpace L hc q) = q + 1 := by
  simpa only [prefixSpace, Fintype.card_fin] using
    finrank_span_eq_card (prefix_orthonormal L hc q hq).linearIndependent

/-- Parseval on the finite leading span follows directly from its orthonormal generators. -/
theorem prefix_parseval (L : E →L[ℝ] F) (hc : IsCompactOperator L) (q : ℕ)
    (hq : (residual L hc q).1 ≠ 0) (x : prefixSpace L hc q) :
    (∑ i : Fin (q + 1), (inner ℝ (direction L hc i) (x : E)) ^ 2) = ‖x‖ ^ 2 := by
  classical
  let v := fun i : Fin (q + 1) ↦ direction L hc i
  have hon : Orthonormal ℝ v := prefix_orthonormal L hc q hq
  let P : E →L[ℝ] E := ∑ i, (innerSL ℝ (v i)).smulRight (v i)
  have hP (i : Fin (q + 1)) : P (v i) = v i := by
    simp only [P, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply, orthonormal_iff_ite.mp hon]
    simp
  have hspan : prefixSpace L hc q ≤
      LinearMap.ker (P - ContinuousLinearMap.id ℝ E).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    change P (v i) - v i = 0
    rw [hP, sub_self]
  have hPx : P (x : E) = (x : E) := sub_eq_zero.mp (hspan x.property)
  have hnorm : ‖x‖ ^ 2 = inner ℝ (x : E) (P (x : E)) := by
    rw [hPx, real_inner_self_eq_norm_sq]
    rfl
  rw [hnorm]
  simp only [P, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (x : E) (v i)]
  ring

/-- The first q+1 directions all remain visible at the q-th residual singular scale. -/
theorem prefix_visible (L : E →L[ℝ] F) (hc : IsCompactOperator L) (q : ℕ)
    (hq : (residual L hc q).1 ≠ 0) (x : prefixSpace L hc q) :
    ‖(residual L hc q).1‖ * ‖x‖ ≤ ‖L (x : E)‖ := by
  have he := energy_decomposition L hc (q + 1) (x : E)
  have hsum : ‖(residual L hc q).1‖ ^ 2 * ‖x‖ ^ 2 ≤
      ∑ i ∈ Finset.range (q + 1),
        ‖(residual L hc i).1‖ ^ 2 * (inner ℝ (direction L hc i) (x : E)) ^ 2 := by
    rw [← prefix_parseval L hc q hq x, Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range (fun i ↦ ‖(residual L hc i).1‖ ^ 2 *
        (inner ℝ (direction L hc i) (x : E)) ^ 2) (q + 1)]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (residual_norm_antitone L hc (show (i : ℕ) ≤ q by omega))
  have hnonneg := sq_nonneg ‖(residual L hc (q + 1)).1 (x : E)‖
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  nlinarith

/-- Sharp minimax error over all adaptive procedures, including zero targets and zero radius. -/
theorem adaptive_minimax (L : E →L[ℝ] F) (hc : IsCompactOperator L)
    (q : ℕ) (radius : ℝ) (hr : 0 ≤ radius) :
    IsLeast {risk : ℝ | ∃ procedure : Procedure E F q, UniformRisk procedure L radius risk}
      (radius ^ 2 * ‖(residual L hc q).1‖ ^ 2) := by
  refine ⟨⟨spectralProcedure L hc q, spectralProcedure_risk L hc q radius⟩, ?_⟩
  rintro risk ⟨procedure, h⟩
  by_cases hq : (residual L hc q).1 = 0
  · simp only [hq, norm_zero, zero_pow two_ne_zero, mul_zero]
    exact (sq_nonneg _).trans (h 0 (by simpa using hr))
  · exact adaptive_lower_of_subspace procedure L (prefixSpace L hc q)
      (by rw [prefixSpace_finrank L hc q hq]; omega)
      ‖(residual L hc q).1‖ radius risk (norm_nonneg _) hr
      (prefix_visible L hc q hq) h

end Descent.Portability.CompactMeasurementMinimax
