/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TargetUncertainty
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

assert_below Descent.Decision Descent.Program

/-!
A nonzero compact target operator between Hilbert spaces has a leading right
singular direction. Compactness yields a convergent image subsequence; a Gram
residual bound lifts it to a convergent maximizing sequence in the domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompactTargetDirection

open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem gram_residual_bound (L : E →L[ℝ] F) (v : E) (hv : ‖v‖ ≤ 1) :
    ‖L.adjoint (L v) - ‖L‖ ^ 2 • v‖ ^ 2 ≤ ‖L‖ ^ 2 * (‖L‖ ^ 2 - ‖L v‖ ^ 2) := by
  have ha : ‖L.adjoint (L v)‖ ≤ ‖L‖ * ‖L v‖ := by
    simpa only [LinearIsometryEquiv.norm_map] using L.adjoint.le_opNorm (L v)
  have hasq := mul_self_le_mul_self (norm_nonneg _) ha
  have hvsq := mul_self_le_mul_self (norm_nonneg _) hv
  have hcross : inner ℝ (L.adjoint (L v)) v = ‖L v‖ ^ 2 := by
    rw [L.adjoint_inner_left, real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, inner_smul_right, hcross, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  have hmul := mul_le_mul_of_nonneg_left hvsq (sq_nonneg (‖L‖ ^ 2))
  nlinarith

omit [CompleteSpace E] [CompleteSpace F] in
theorem maximizing_sequence (L : E →L[ℝ] F) :
    ∃ u : ℕ → E, (∀ n, ‖u n‖ ≤ 1) ∧ Tendsto (fun n ↦ ‖L (u n)‖) atTop (𝓝 ‖L‖) := by
  have he (n : ℕ) : ∃ v : E, ‖v‖ < 1 ∧ ‖L‖ - 1 / ((n : ℝ) + 1) < ‖L v‖ :=
    L.exists_lt_apply_of_lt_opNorm (by
      have hn : 0 < (n : ℝ) + 1 := by positivity
      exact sub_lt_self _ (one_div_pos.mpr hn))
  choose u hu hl using he
  refine ⟨u, fun n ↦ (hu n).le, ?_⟩
  have hlo : Tendsto (fun n : ℕ ↦ ‖L‖ - 1 / ((n : ℝ) + 1)) atTop (𝓝 ‖L‖) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n ↦ (hl n).le) (fun n ↦ L.unit_le_opNorm _ (hu n).le)

theorem maximizing_sequence_residual (L : E →L[ℝ] F) (u : ℕ → E)
    (hu : ∀ n, ‖u n‖ ≤ 1) (hmax : Tendsto (fun n ↦ ‖L (u n)‖) atTop (𝓝 ‖L‖)) :
    Tendsto (fun n ↦ L.adjoint (L (u n)) - ‖L‖ ^ 2 • u n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n ↦ ‖L‖ ^ 2 * (‖L‖ ^ 2 - ‖L (u n)‖ ^ 2)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n ↦ ‖L‖ ^ 2 * (‖L‖ ^ 2 - ‖L (u n)‖ ^ 2))
        atTop (𝓝 (‖L‖ ^ 2 * (‖L‖ ^ 2 - ‖L‖ ^ 2))) :=
      (tendsto_const_nhds (x := ‖L‖ ^ 2)).mul
        ((tendsto_const_nhds (x := ‖L‖ ^ 2)).sub (hmax.pow 2))
    simpa only [sub_self, mul_zero] using hh
  have hs := squeeze_zero (fun n ↦ sq_nonneg ‖L.adjoint (L (u n)) - ‖L‖ ^ 2 • u n‖)
    (fun n ↦ gram_residual_bound L (u n) (hu n)) ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

theorem maximizer_is_singular (L : E →L[ℝ] F) (v : E) (hv : ‖v‖ ≤ 1)
    (hmax : ‖L v‖ = ‖L‖) : L.adjoint (L v) = ‖L‖ ^ 2 • v := by
  have h := gram_residual_bound L v hv
  rw [hmax, sub_self, mul_zero] at h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (L.adjoint (L v) - ‖L‖ ^ 2 • v)]

/-- Compactness supplies a genuine leading singular vector, rather than an
assumed spectral decomposition or an assumed norm-attainment certificate. -/
theorem exists_leading_direction (L : E →L[ℝ] F) (hcompact : IsCompactOperator L)
    (hne : L ≠ 0) :
    ∃ v : E, ‖v‖ = 1 ∧ ‖L v‖ = ‖L‖ ∧ L.adjoint (L v) = ‖L‖ ^ 2 • v := by
  have hs : 0 < ‖L‖ := norm_pos_iff.mpr hne
  have hs2 : ‖L‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hs)
  obtain ⟨u, hu, hmax⟩ := maximizing_sequence L
  have hres := maximizing_sequence_residual L u hu hmax
  obtain ⟨K, hK, himage⟩ :=
    (show IsCompactOperator L.toLinearMap from hcompact).image_closedBall_subset_compact 1
  obtain ⟨w, _, φ, hφ, hw⟩ := hK.tendsto_subseq
    (x := fun n ↦ L (u n)) (fun n ↦ himage ⟨u n, by simpa using hu n, rfl⟩)
  let v := (‖L‖ ^ 2)⁻¹ • L.adjoint w
  have hadjoint : Tendsto (fun n ↦ L.adjoint (L (u (φ n)))) atTop (𝓝 (L.adjoint w)) :=
    (L.adjoint.continuous.tendsto w).comp hw
  have hvlimit : Tendsto (fun n ↦ u (φ n)) atTop (𝓝 v) := by
    have hh := (hadjoint.sub (hres.comp hφ.tendsto_atTop)).const_smul (‖L‖ ^ 2)⁻¹
    simpa only [Function.comp_apply, sub_zero, sub_sub_cancel, smul_smul,
      inv_mul_cancel₀ hs2, one_smul] using hh
  have hvnorm : ‖v‖ ≤ 1 := le_of_tendsto hvlimit.norm (Eventually.of_forall (fun n ↦ hu (φ n)))
  have hLv : ‖L v‖ = ‖L‖ := tendsto_nhds_unique
    ((L.continuous.tendsto v).comp hvlimit).norm (hmax.comp hφ.tendsto_atTop)
  have hvone : ‖v‖ = 1 := by
    have hh := L.le_opNorm v
    rw [hLv] at hh
    nlinarith
  exact ⟨v, hvone, hLv, maximizer_is_singular L v hvnorm hLv⟩

end Descent.Portability.CompactTargetDirection
