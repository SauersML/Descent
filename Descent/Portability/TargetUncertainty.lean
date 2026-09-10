/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

assert_below Descent.Decision Descent.Program

/-!
Sharp target uncertainty for the image of a Hilbert ball. The minimax lower
bound is derived from opposite feasible points and the operator norm, without
assuming a singular vector or norm attainment. This also covers zero radius,
a zero operator, and an empty residual direction space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TargetUncertainty

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A uniform squared target-error bound for a fixed prediction on a residual ball. -/
def UniformBound (L : E →L[ℝ] F) (radius : ℝ) (prediction : F) (risk : ℝ) : Prop :=
  ∀ v : E, ‖v‖ ≤ radius → ‖L v - prediction‖ ^ 2 ≤ risk

/-- Predicting the center attains the operator-norm upper bound. -/
theorem center_upper_bound (L : E →L[ℝ] F) (radius : ℝ) :
    UniformBound L radius 0 (radius ^ 2 * ‖L‖ ^ 2) := by
  intro v hv
  simp only [sub_zero]
  have hnorm : ‖L v‖ ≤ ‖L‖ * radius :=
    (L.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have hs := mul_self_le_mul_self (norm_nonneg (L v)) hnorm
  nlinarith

/-- The two-point parallelogram lower bound, for any common prediction. -/
theorem two_point_lower (u prediction : F) (risk : ℝ)
    (hplus : ‖u - prediction‖ ^ 2 ≤ risk)
    (hminus : ‖-u - prediction‖ ^ 2 ≤ risk) : ‖u‖ ^ 2 ≤ risk := by
  have hother : ‖u + prediction‖ ^ 2 ≤ risk := by
    rw [show -u - prediction = -(u + prediction) by abel, norm_neg] at hminus
    exact hminus
  have hparallelogram := parallelogram_law_with_norm ℝ u prediction
  nlinarith [sq_nonneg ‖prediction‖]

/-- Opposite residual vectors remove every prediction-dependent cross term. -/
theorem opposite_points_lower (L : E →L[ℝ] F) (radius : ℝ) (prediction : F) (risk : ℝ)
    (h : UniformBound L radius prediction risk) (v : E) (hv : ‖v‖ ≤ radius) :
    ‖L v‖ ^ 2 ≤ risk := by
  apply two_point_lower (L v) prediction risk (h v hv)
  simpa only [map_neg] using h (-v) (by simpa only [norm_neg] using hv)

/-- Every prediction incurs at least the squared operator radius. Norm
attainment and finite dimensionality are unnecessary for this sharp bound. -/
theorem uniform_bound_lower (L : E →L[ℝ] F) (radius : ℝ) (hr : 0 ≤ radius)
    (prediction : F) (risk : ℝ) (h : UniformBound L radius prediction risk) :
    radius ^ 2 * ‖L‖ ^ 2 ≤ risk := by
  have hzero := h 0 (by simpa only [norm_zero] using hr)
  have hrisk : 0 ≤ risk := (sq_nonneg _).trans hzero
  by_cases hrzero : radius = 0
  · simpa only [hrzero, zero_pow two_ne_zero, zero_mul] using hrisk
  have hrpos : 0 < radius := lt_of_le_of_ne hr (Ne.symm hrzero)
  have hnorm : ‖L‖ ≤ Real.sqrt risk / radius := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro v hv
    have hscaled := opposite_points_lower L radius prediction risk h (radius • v) (by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hv, mul_one, le_refl])
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at hscaled
    have hsqrt : radius * ‖L v‖ ≤ Real.sqrt risk :=
      (Real.le_sqrt (by positivity) hrisk).mpr hscaled
    exact (le_div_iff₀ hrpos).mpr (by simpa only [mul_comm] using hsqrt)
  have hmul : radius * ‖L‖ ≤ Real.sqrt risk := by
    have hm := (le_div_iff₀ hrpos).mp hnorm
    simpa only [mul_comm] using hm
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ radius * ‖L‖) hmul
  nlinarith [Real.sq_sqrt hrisk]

/-- Exact minimax squared target radius, expressed as the least achievable
uniform risk. This is an optimization theorem over all real predictions. -/
theorem minimax_radius (L : E →L[ℝ] F) (radius : ℝ) (hr : 0 ≤ radius) :
    IsLeast {risk : ℝ | ∃ prediction : F, UniformBound L radius prediction risk}
      (radius ^ 2 * ‖L‖ ^ 2) := by
  refine ⟨⟨0, center_upper_bound L radius⟩, ?_⟩
  rintro risk ⟨prediction, h⟩
  exact uniform_bound_lower L radius hr prediction risk h

/-- Adding the known target center preserves the sharp radius and identifies
the center prediction as a minimax decision. -/
theorem affine_minimax_radius (L : E →L[ℝ] F) (center : F) (radius : ℝ) (hr : 0 ≤ radius) :
    IsLeast {risk : ℝ | ∃ prediction : F, ∀ v : E, ‖v‖ ≤ radius →
      ‖center + L v - prediction‖ ^ 2 ≤ risk} (radius ^ 2 * ‖L‖ ^ 2) := by
  refine ⟨⟨center, ?_⟩, ?_⟩
  · intro v hv
    simpa only [add_sub_cancel_left, sub_zero] using center_upper_bound L radius v hv
  · rintro risk ⟨prediction, h⟩
    apply uniform_bound_lower L radius hr (prediction - center) risk
    intro v hv
    convert h v hv using 1
    congr 2
    abel

end Descent.Portability.TargetUncertainty
