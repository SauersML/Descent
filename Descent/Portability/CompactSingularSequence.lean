/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompactTargetDeflation

assert_below Descent.Decision Descent.Program

/-!
Successive leading directions of an actual compact target operator. Deflation
constructs the residuals, proves their decreasing norms and nested kernels, and
provides an executable mathematical query procedure for every finite budget.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompactSingularSequence

open scoped BigOperators
open CompactTargetDirection CompactTargetDeflation AdaptiveLinearMeasurements

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A leading singular direction, with zero chosen after the target is exhausted. -/
noncomputable def leading (L : E →L[ℝ] F) (hc : IsCompactOperator L) : E := by
  classical
  exact if h : L = 0 then 0 else Classical.choose (exists_leading_direction L hc h)

theorem leading_zero (hc : IsCompactOperator (0 : E →L[ℝ] F)) : leading 0 hc = 0 := by
  simp [leading]

theorem leading_spec (L : E →L[ℝ] F) (hc : IsCompactOperator L) :
    ‖leading L hc‖ ≤ 1 ∧ ‖L (leading L hc)‖ = ‖L‖ ∧
      L.adjoint (L (leading L hc)) = ‖L‖ ^ 2 • leading L hc := by
  classical
  by_cases hL : L = 0
  · subst L
    simp [leading_zero]
  · have h := Classical.choose_spec (exists_leading_direction L hc hL)
    simpa only [leading, dif_neg hL] using And.intro h.1.le h.2

theorem leading_unit (L : E →L[ℝ] F) (hc : IsCompactOperator L) (hL : L ≠ 0) :
    ‖leading L hc‖ = 1 := by
  simpa only [leading, dif_neg hL] using
    (Classical.choose_spec (exists_leading_direction L hc hL)).1

/-- The compact residual after a finite number of leading scalar measurements. -/
noncomputable def residual (L : E →L[ℝ] F) (hc : IsCompactOperator L) :
    ℕ → {R : E →L[ℝ] F // IsCompactOperator R}
  | 0 => ⟨L, hc⟩
  | n + 1 =>
    let R := residual L hc n
    ⟨deflate R.1 (leading R.1 R.2), compact_deflate R.1 R.2 _⟩

noncomputable def direction (L : E →L[ℝ] F) (hc : IsCompactOperator L) (n : ℕ) : E :=
  leading (residual L hc n).1 (residual L hc n).2

@[simp] theorem residual_zero (L : E →L[ℝ] F) (hc : IsCompactOperator L) :
    (residual L hc 0).1 = L := rfl

theorem residual_succ (L : E →L[ℝ] F) (hc : IsCompactOperator L) (n : ℕ) :
    (residual L hc (n + 1)).1 = deflate (residual L hc n).1 (direction L hc n) := rfl

theorem direction_spec (L : E →L[ℝ] F) (hc : IsCompactOperator L) (n : ℕ) :
    ‖direction L hc n‖ ≤ 1 ∧ ‖(residual L hc n).1 (direction L hc n)‖ =
      ‖(residual L hc n).1‖ ∧ (residual L hc n).1.adjoint
        ((residual L hc n).1 (direction L hc n)) =
          ‖(residual L hc n).1‖ ^ 2 • direction L hc n :=
  leading_spec _ _

/-- Residual singular values decrease, including after finite-rank termination. -/
theorem residual_norm_antitone (L : E →L[ℝ] F) (hc : IsCompactOperator L) :
    Antitone (fun n ↦ ‖(residual L hc n).1‖) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [residual_succ]
  exact norm_deflate_le _ _ (direction_spec L hc n).2.1 (direction_spec L hc n).2.2

theorem residual_annihilates_direction (L : E →L[ℝ] F) (hc : IsCompactOperator L)
    (i j : ℕ) (hij : i < j) : (residual L hc j).1 (direction L hc i) = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [residual_succ]
    by_cases he : i = j
    · subst i
      by_cases hR : (residual L hc j).1 = 0
      · simp [hR]
      · exact deflate_self _ _ (leading_unit _ _ hR)
    · exact kernel_preserved _ _ _ (direction_spec L hc j).2.2 (ih (by omega))

/-- Every newly measured direction is orthogonal to all previously measured directions. -/
theorem directions_orthogonal (L : E →L[ℝ] F) (hc : IsCompactOperator L)
    (i j : ℕ) (hij : i < j) : inner ℝ (direction L hc j) (direction L hc i) = 0 := by
  by_cases hR : (residual L hc j).1 = 0
  · simp [direction, hR, leading_zero]
  · have h := singular_cross (residual L hc j).1 (direction L hc j)
      (direction L hc i) (direction_spec L hc j).2.2
    rw [residual_annihilates_direction L hc i j hij, inner_zero_right] at h
    exact (mul_eq_zero.mp h.symm).resolve_left
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hR))

/-- Exact energy decomposition through any finite number of measured directions. -/
theorem energy_decomposition (L : E →L[ℝ] F) (hc : IsCompactOperator L) (q : ℕ) (x : E) :
    ‖L x‖ ^ 2 =
      (∑ i ∈ Finset.range q, ‖(residual L hc i).1‖ ^ 2 * (inner ℝ (direction L hc i) x) ^ 2) +
        ‖(residual L hc q).1 x‖ ^ 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have he := energy_identity (residual L hc q).1 (direction L hc q) x
      (direction_spec L hc q).2.1 (direction_spec L hc q).2.2
    rw [Finset.sum_range_succ, residual_succ, he]
    linarith

/-- The prediction made by all measured coordinates, without a spectral-series assumption. -/
theorem residual_decomposition (L : E →L[ℝ] F) (hc : IsCompactOperator L)
    (q : ℕ) (x : E) :
    (residual L hc q).1 x = L x - ∑ i ∈ Finset.range q,
      inner ℝ (direction L hc i) x • (residual L hc i).1 (direction L hc i) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [residual_succ, deflate_apply, ih, Finset.sum_range_succ]
    abel

/-- A genuine fixed sequence of `q` scalar questions with its explicit decoder. -/
noncomputable def spectralProcedure (L : E →L[ℝ] F) (hc : IsCompactOperator L) (q : ℕ) :
    Procedure E F q :=
  .fixed (fun i ↦ innerSL ℝ (direction L hc i))
    (fun responses ↦ ∑ i : Fin q, responses i • (residual L hc i).1 (direction L hc i))

theorem spectralProcedure_residual (L : E →L[ℝ] F) (hc : IsCompactOperator L)
    (q : ℕ) (x : E) : L x - (spectralProcedure L hc q).run x = (residual L hc q).1 x := by
  rw [spectralProcedure, Procedure.fixed_run, residual_decomposition]
  change L x - (∑ i : Fin q, inner ℝ (direction L hc i) x •
    (residual L hc i).1 (direction L hc i)) = _
  rw [Fin.sum_univ_eq_sum_range (fun i ↦
    inner ℝ (direction L hc i) x • (residual L hc i).1 (direction L hc i)) q]

/-- A finite measurement budget achieves the norm of the actual remaining compact operator. -/
theorem spectralProcedure_risk (L : E →L[ℝ] F) (hc : IsCompactOperator L)
    (q : ℕ) (radius : ℝ) :
    UniformRisk (spectralProcedure L hc q) L radius (radius ^ 2 * ‖(residual L hc q).1‖ ^ 2) := by
  intro x hx
  rw [spectralProcedure_residual]
  have h := ((residual L hc q).1.le_opNorm x).trans
    (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  nlinarith

end Descent.Portability.CompactSingularSequence
