/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteTargetSpectrum

assert_below Descent.Decision Descent.Program

/-!
The finite target spectrum determines the exact error of optimal noiseless
linear measurements. The lower bound applies to actual adaptive procedures;
the upper bound is attained by measuring the leading right singular coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralMeasurementMinimax

open FiniteTargetSpectrum AdaptiveLinearMeasurements
open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

noncomputable def coordinate (L : E →L[ℝ] F) (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  innerSL ℝ (rightBasis L i)

theorem coordinate_repr (L : E →L[ℝ] F) (i : Fin (Module.finrank ℝ E)) (v : E) :
    coordinate L i v = (rightBasis L).repr v i :=
  ((rightBasis L).repr_apply_apply v i).symm

theorem coordinate_basis (L : E →L[ℝ] F) (i j : Fin (Module.finrank ℝ E)) :
    coordinate L i (rightBasis L j) = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (rightBasis L).orthonormal i j

theorem coordinate_norm (L : E →L[ℝ] F) (v : E) :
    (∑ i, (coordinate L i v) ^ 2) = ‖v‖ ^ 2 := by
  change (∑ i, (inner ℝ (rightBasis L i) v) ^ 2) = ‖v‖ ^ 2
  simpa only [Real.norm_eq_abs, sq_abs] using (rightBasis L).sum_sq_norm_inner_right v

theorem target_coordinates (L : E →L[ℝ] F) (v : E) :
    ‖L v‖ ^ 2 = ∑ i, squaredSingularValues L i * (coordinate L i v) ^ 2 := by
  simp only [coordinate_repr, target_norm_expansion]

noncomputable def truncatedParameter (L : E →L[ℝ] F) (q : ℕ)
    (hq : q ≤ Module.finrank ℝ E) (v : E) : E :=
  ∑ j : Fin q, coordinate L (j.castLE hq) v • rightBasis L (j.castLE hq)

theorem coordinate_prefix (L : E →L[ℝ] F) (q : ℕ) (hq : q ≤ Module.finrank ℝ E)
    (v : E) (i : Fin (Module.finrank ℝ E)) :
    coordinate L i (truncatedParameter L q hq v) = if i.val < q then coordinate L i v else 0 := by
  simp only [truncatedParameter, map_sum, map_smul, coordinate_basis, smul_eq_mul]
  by_cases hi : i.val < q
  · rw [if_pos hi]
    let j : Fin q := ⟨i.val, hi⟩
    have hj : j.castLE hq = i := Fin.ext rfl
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro k _ hkj
      have hne : i ≠ k.castLE hq := by
        intro he
        apply hkj
        apply Fin.ext
        exact (congrArg Fin.val he).symm
      simp [hne]
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    have hne : i ≠ j.castLE hq := by
      intro he
      have hv := congrArg Fin.val he
      have hj := j.isLt
      change i.val = j.val at hv
      omega
    simp [hne]

noncomputable def leadingProcedure (L : E →L[ℝ] F) (q : ℕ)
    (hq : q ≤ Module.finrank ℝ E) : Procedure E F q :=
  Procedure.fixed (fun j ↦ coordinate L (j.castLE hq))
    (fun responses ↦ ∑ j, responses j • L (rightBasis L (j.castLE hq)))

theorem leadingProcedure_run (L : E →L[ℝ] F) (q : ℕ) (hq : q ≤ Module.finrank ℝ E) (v : E) :
    (leadingProcedure L q hq).run v = L (truncatedParameter L q hq v) := by
  simp only [leadingProcedure, Procedure.fixed_run, truncatedParameter, map_sum, map_smul]

theorem leadingProcedure_upper (L : E →L[ℝ] F) (q : ℕ) (hq : q < Module.finrank ℝ E)
    (radius : ℝ) :
    UniformRisk (leadingProcedure L q hq.le) L radius
      (radius ^ 2 * squaredSingularValues L ⟨q, hq⟩) := by
  intro v hv
  rw [leadingProcedure_run, ← map_sub, target_coordinates]
  have hcoordinate (i : Fin (Module.finrank ℝ E)) :
      coordinate L i (v - truncatedParameter L q hq.le v) =
        if i.val < q then 0 else coordinate L i v := by
    rw [map_sub, coordinate_prefix]
    split_ifs <;> simp
  simp_rw [hcoordinate]
  calc
    _ ≤ ∑ i, squaredSingularValues L ⟨q, hq⟩ * (coordinate L i v) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · simp only [zero_pow two_ne_zero, mul_zero]
        exact mul_nonneg (squaredSingularValues_nonneg L _) (sq_nonneg _)
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact squaredSingularValues_antitone L (by simpa using Nat.le_of_not_gt hi)
    _ = squaredSingularValues L ⟨q, hq⟩ * ‖v‖ ^ 2 := by
      rw [← Finset.mul_sum, coordinate_norm]
    _ ≤ radius ^ 2 * squaredSingularValues L ⟨q, hq⟩ := by
      have hs := mul_self_le_mul_self (norm_nonneg v) hv
      have hm := mul_le_mul_of_nonneg_left hs (squaredSingularValues_nonneg L ⟨q, hq⟩)
      nlinarith

noncomputable def prefixSpan (L : E →L[ℝ] F) (q : ℕ) (hq : q ≤ Module.finrank ℝ E) :
    Submodule ℝ E := Submodule.span ℝ (Set.range (fun j : Fin q ↦ rightBasis L (j.castLE hq)))

theorem prefixSpan_finrank (L : E →L[ℝ] F) (q : ℕ) (hq : q ≤ Module.finrank ℝ E) :
    Module.finrank ℝ (prefixSpan L q hq) = q := by
  have hi : LinearIndependent ℝ (fun j : Fin q ↦ rightBasis L (j.castLE hq)) :=
    (rightBasis L).toBasis.linearIndependent.comp (fun j : Fin q ↦ j.castLE hq)
      (fun i j h ↦ Fin.ext (congrArg (fun k : Fin (Module.finrank ℝ E) ↦ k.val) h))
  simpa only [prefixSpan, Fintype.card_fin] using finrank_span_eq_card hi

theorem coordinate_prefixSpan (L : E →L[ℝ] F) (q : ℕ) (hq : q ≤ Module.finrank ℝ E)
    (v : prefixSpan L q hq) (i : Fin (Module.finrank ℝ E)) (hi : q ≤ i.val) :
    coordinate L i v = 0 := by
  have hs : prefixSpan L q hq ≤ LinearMap.ker (coordinate L i).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    change coordinate L i (rightBasis L (j.castLE hq)) = 0
    rw [coordinate_basis, if_neg]
    intro he
    have hh := congrArg Fin.val he
    have hj := j.isLt
    change i.val = j.val at hh
    omega
  exact hs v.property

theorem prefixSpan_visible (L : E →L[ℝ] F) (q : ℕ) (hq : q < Module.finrank ℝ E)
    (v : prefixSpan L (q + 1) hq) :
    Real.sqrt (squaredSingularValues L ⟨q, hq⟩) * ‖v‖ ≤ ‖L v‖ := by
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  change (Real.sqrt (squaredSingularValues L ⟨q, hq⟩) * ‖(v : E)‖) ^ 2 ≤ ‖L v‖ ^ 2
  rw [mul_pow, Real.sq_sqrt (squaredSingularValues_nonneg L _), target_coordinates,
    ← coordinate_norm L (v : E), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val ≤ q
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact squaredSingularValues_antitone L hi
  · rw [coordinate_prefixSpan L (q + 1) hq v i (by omega)]
    simp

theorem adaptive_spectral_lower (L : E →L[ℝ] F) (q : ℕ) (hq : q < Module.finrank ℝ E)
    (procedure : Procedure E F q) (radius risk : ℝ) (hr : 0 ≤ radius)
    (h : UniformRisk procedure L radius risk) :
    radius ^ 2 * squaredSingularValues L ⟨q, hq⟩ ≤ risk := by
  have hh := adaptive_lower_of_subspace procedure L (prefixSpan L (q + 1) hq)
    (by rw [prefixSpan_finrank]; omega)
    (Real.sqrt (squaredSingularValues L ⟨q, hq⟩)) radius risk (Real.sqrt_nonneg _) hr
    (prefixSpan_visible L q hq) h
  rwa [Real.sq_sqrt (squaredSingularValues_nonneg L _)] at hh

/-- Sharp optimization over all deterministic adaptive procedures, with the
attaining procedure and the adversarial query-null direction both constructed. -/
theorem adaptive_minimax (L : E →L[ℝ] F) (q : ℕ) (hq : q < Module.finrank ℝ E)
    (radius : ℝ) (hr : 0 ≤ radius) :
    IsLeast {risk : ℝ | ∃ procedure : Procedure E F q, UniformRisk procedure L radius risk}
      (radius ^ 2 * squaredSingularValues L ⟨q, hq⟩) := by
  refine ⟨⟨leadingProcedure L q hq.le, leadingProcedure_upper L q hq radius⟩, ?_⟩
  rintro risk ⟨procedure, h⟩
  exact adaptive_spectral_lower L q hq procedure radius risk hr h

theorem truncatedParameter_full (L : E →L[ℝ] F) (v : E) :
    truncatedParameter L (Module.finrank ℝ E) le_rfl v = v := by
  simpa only [truncatedParameter, Fin.castLE_refl, coordinate_repr] using
    (rightBasis L).sum_repr v

theorem leadingProcedure_full (L : E →L[ℝ] F) (radius : ℝ) :
    UniformRisk (leadingProcedure L (Module.finrank ℝ E) le_rfl) L radius 0 := by
  intro v _
  rw [leadingProcedure_run, truncatedParameter_full, sub_self, norm_zero]
  norm_num

/-- Padding by zero-valued linear questions represents every budget above the
dimension without altering the prediction of the original procedure. -/
def pad {q : ℕ} (procedure : Procedure E F q) : (extra : ℕ) → Procedure E F (q + extra)
  | 0 => procedure
  | extra + 1 => .ask 0 (fun _ ↦ pad procedure extra)

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem pad_run {q : ℕ} (procedure : Procedure E F q) (extra : ℕ) (v : E) :
    (pad procedure extra).run v = procedure.run v := by
  induction extra with
  | zero => rfl
  | succ extra ih => exact ih

theorem full_budget_achievable (L : E →L[ℝ] F) (q : ℕ) (hq : Module.finrank ℝ E ≤ q)
    (radius : ℝ) : ∃ procedure : Procedure E F q, UniformRisk procedure L radius 0 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hq
  refine ⟨pad (leadingProcedure L (Module.finrank ℝ E) le_rfl) extra, ?_⟩
  intro v hv
  rw [pad_run]
  exact leadingProcedure_full L radius v hv

noncomputable def residualEigenvalue (L : E →L[ℝ] F) (q : ℕ) : ℝ :=
  if hq : q < Module.finrank ℝ E then squaredSingularValues L ⟨q, hq⟩ else 0

/-- The exact spectral minimax law includes every budget, zero radius, and
zero-dimensional or rank-deficient target maps. -/
theorem adaptive_minimax_all_budgets (L : E →L[ℝ] F) (q : ℕ) (radius : ℝ)
    (hr : 0 ≤ radius) :
    IsLeast {risk : ℝ | ∃ procedure : Procedure E F q, UniformRisk procedure L radius risk}
      (radius ^ 2 * residualEigenvalue L q) := by
  by_cases hq : q < Module.finrank ℝ E
  · simpa only [residualEigenvalue, dif_pos hq] using adaptive_minimax L q hq radius hr
  · simp only [residualEigenvalue, dif_neg hq, mul_zero]
    refine ⟨full_budget_achievable L q (Nat.le_of_not_gt hq) radius, ?_⟩
    rintro risk ⟨procedure, h⟩
    have hh := h 0 (by simpa only [norm_zero] using hr)
    exact (sq_nonneg _).trans hh

end Descent.Portability.SpectralMeasurementMinimax
