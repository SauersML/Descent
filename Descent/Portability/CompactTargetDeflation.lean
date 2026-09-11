/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompactTargetDirection
import Descent.Portability.AdaptiveLinearMeasurements

assert_below Descent.Decision Descent.Program

/-!
Removing a leading compact singular direction gives another compact operator.
The exact energy identity records the information recovered by the corresponding
scalar measurement, and the residual norm controls its complete prediction error.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompactTargetDeflation

open CompactTargetDirection AdaptiveLinearMeasurements

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Remove the domain component measured along `v`. -/
noncomputable def deflate (L : E →L[ℝ] F) (v : E) : E →L[ℝ] F :=
  L.comp (ContinuousLinearMap.id ℝ E - (innerSL ℝ v).smulRight v)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem deflate_apply (L : E →L[ℝ] F) (v x : E) :
    deflate L v x = L x - inner ℝ v x • L v := by
  simp [deflate]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Compactness survives removal of a measured direction. -/
theorem compact_deflate (L : E →L[ℝ] F) (hcompact : IsCompactOperator L) (v : E) :
    IsCompactOperator (deflate L v) :=
  hcompact.comp_clm _

/-- A Gram eigenvector determines every cross term in target space. -/
theorem singular_cross (L : E →L[ℝ] F) (v x : E)
    (hgram : L.adjoint (L v) = ‖L‖ ^ 2 • v) :
    inner ℝ (L v) (L x) = ‖L‖ ^ 2 * inner ℝ v x := by
  rw [← L.adjoint_inner_left, hgram, real_inner_smul_left]

/-- The removed scalar coordinate accounts for exactly its singular-value energy. -/
theorem energy_identity (L : E →L[ℝ] F) (v x : E)
    (hmax : ‖L v‖ = ‖L‖) (hgram : L.adjoint (L v) = ‖L‖ ^ 2 • v) :
    ‖deflate L v x‖ ^ 2 = ‖L x‖ ^ 2 - ‖L‖ ^ 2 * (inner ℝ v x) ^ 2 := by
  have hcross : inner ℝ (L x) (L v) = ‖L‖ ^ 2 * inner ℝ v x := by
    rw [real_inner_comm]
    exact singular_cross L v x hgram
  rw [deflate_apply, norm_sub_sq_real, inner_smul_right, hcross, norm_smul,
    Real.norm_eq_abs, hmax, mul_pow, sq_abs]
  ring

/-- Taking out the leading direction cannot increase the operator norm. -/
theorem norm_deflate_le (L : E →L[ℝ] F) (v : E)
    (hmax : ‖L v‖ = ‖L‖) (hgram : L.adjoint (L v) = ‖L‖ ^ 2 • v) :
    ‖deflate L v‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  have he := energy_identity L v x hmax hgram
  have hb := L.le_opNorm x
  have hp := mul_nonneg (sq_nonneg ‖L‖) (sq_nonneg (inner ℝ v x))
  have hn := norm_nonneg (deflate L v x)
  have hx := norm_nonneg (L x)
  nlinarith

omit [CompleteSpace E] [CompleteSpace F] in
/-- A unit direction is annihilated by its own deflation. -/
theorem deflate_self (L : E →L[ℝ] F) (v : E) (hv : ‖v‖ = 1) :
    deflate L v v = 0 := by
  rw [deflate_apply, real_inner_self_eq_norm_sq, hv]
  simp

/-- Previously invisible inputs stay invisible after removing a leading direction. -/
theorem kernel_preserved (L : E →L[ℝ] F) (v x : E)
    (hgram : L.adjoint (L v) = ‖L‖ ^ 2 • v) (hx : L x = 0) :
    deflate L v x = 0 := by
  by_cases hL : L = 0
  · simp [hL]
  have hcross := singular_cross L v x hgram
  rw [hx, inner_zero_right] at hcross
  have hs : ‖L‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hL)
  have hvx : inner ℝ v x = 0 := (mul_eq_zero.mp hcross.symm).resolve_left hs
  simp [hx, hvx]

/-- The actual one-question prediction procedure records this singular coordinate. -/
noncomputable def leadingQuery (L : E →L[ℝ] F) (v : E) : Procedure E F 1 :=
  .ask (innerSL ℝ v) (fun response ↦ .done (response • L v))

omit [CompleteSpace E] [CompleteSpace F] in
theorem leadingQuery_residual (L : E →L[ℝ] F) (v x : E) :
    L x - (leadingQuery L v).run x = deflate L v x := by
  simp [leadingQuery, Procedure.run]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Its worst-case squared error is bounded by the actual deflated operator norm. -/
theorem leadingQuery_risk (L : E →L[ℝ] F) (v : E) (radius : ℝ) :
    UniformRisk (leadingQuery L v) L radius (radius ^ 2 * ‖deflate L v‖ ^ 2) := by
  intro x hx
  rw [leadingQuery_residual]
  have h := (deflate L v).le_opNorm x
  have h' := mul_le_mul_of_nonneg_left hx (norm_nonneg (deflate L v))
  have hs := mul_self_le_mul_self (norm_nonneg _) (h.trans h')
  nlinarith

end Descent.Portability.CompactTargetDeflation
