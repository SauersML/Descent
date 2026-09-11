/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SafeRepairGeometry
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 21. The actual orthogonal
projection onto a fixed correction subspace attains its oracle gain.
For nested spans, the difference of oracle gains is exactly the squared
norm of the projection onto the additional orthogonal directions. The
residualization operator uses only the two specified subspaces.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NestedRepairSpans

open SafeRepairGeometry
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Only the component of the residual lying in a correction span can affect its gains. -/
theorem gain_projection (V : Submodule ℝ E) (d e : E) (hd : d ∈ V) :
    gain d e = gain d (V.starProjection e) := by
  have hh := V.starProjection_inner_eq_zero e d hd
  rw [inner_sub_left, real_inner_comm d e, real_inner_comm d (V.starProjection e)] at hh
  unfold gain
  linarith

/-- The actual projection is an attaining correction, and bounds every correction in the span. -/
theorem oracle_attained (V : Submodule ℝ E) (e : E) :
    gain (V.starProjection e) e = ‖V.starProjection e‖ ^ 2 ∧
      IsGreatest {v : ℝ | ∃ d ∈ V, gain d e = v} (‖V.starProjection e‖ ^ 2) := by
  have he : gain (V.starProjection e) e = ‖V.starProjection e‖ ^ 2 := by
    rw [gain_projection V _ e (V.starProjection_apply_mem e), gain_self]
  refine ⟨he, ⟨⟨V.starProjection e, V.starProjection_apply_mem e, he⟩, ?_⟩⟩
  rintro v ⟨d, hd, rfl⟩
  rw [gain_projection V d e hd]
  exact gain_le_oracle _ _

/-- Residualizing a vector in the larger span produces precisely an allowed new direction. -/
theorem residualized_mem (V U : Submodule ℝ E) (hVU : V ≤ U) (x : E) (hx : x ∈ U) :
    x - V.starProjection x ∈ U ⊓ Vᗮ :=
  ⟨U.sub_mem hx (hVU (V.starProjection_apply_mem x)), V.sub_starProjection_mem_orthogonal x⟩

/-- The difference of the two fitted residuals lies in the newly available orthogonal span. -/
theorem projection_difference_mem (V U : Submodule ℝ E) (hVU : V ≤ U) (e : E) :
    U.starProjection e - V.starProjection e ∈ U ⊓ Vᗮ := by
  refine ⟨U.sub_mem (U.starProjection_apply_mem e) (hVU (V.starProjection_apply_mem e)), ?_⟩
  apply (V.mem_orthogonal' _).mpr
  intro v hv
  have hU := U.starProjection_inner_eq_zero e v (hVU hv)
  have hV := V.starProjection_inner_eq_zero e v hv
  rw [inner_sub_left] at hU hV ⊢
  linarith

/-- The new-direction fit is the actual orthogonal projection onto the additional span. -/
theorem projection_difference (V U : Submodule ℝ E) (hVU : V ≤ U) (e : E) :
    (U ⊓ Vᗮ).starProjection e = U.starProjection e - V.starProjection e := by
  apply (U ⊓ Vᗮ).eq_starProjection_of_mem_of_inner_eq_zero
    (projection_difference_mem V U hVU e)
  intro w hw
  have hU := U.starProjection_inner_eq_zero e w hw.1
  have hV := V.inner_right_of_mem_orthogonal (V.starProjection_apply_mem e) hw.2
  rw [inner_sub_left] at hU
  rw [inner_sub_left, inner_sub_left]
  linarith

/-- Expanding the correction span adds exactly its squared orthogonal residual signal. -/
theorem oracle_increment (V U : Submodule ℝ E) (hVU : V ≤ U) (e : E) :
    ‖U.starProjection e‖ ^ 2 - ‖V.starProjection e‖ ^ 2 =
      ‖(U ⊓ Vᗮ).starProjection e‖ ^ 2 := by
  rw [projection_difference V U hVU e, norm_sub_sq_real]
  have hh := V.inner_right_of_mem_orthogonal (V.starProjection_apply_mem e)
    (projection_difference_mem V U hVU e).2
  rw [inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_comm (U.starProjection e) (V.starProjection e)] at hh
  linarith

/-- No new signal is obtained exactly when the residual is orthogonal to all new directions. -/
theorem no_increment_iff (V U : Submodule ℝ E) (hVU : V ≤ U) (e : E) :
    ‖U.starProjection e‖ ^ 2 = ‖V.starProjection e‖ ^ 2 ↔ e ∈ (U ⊓ Vᗮ)ᗮ := by
  rw [← sub_eq_zero, oracle_increment V U hVU e, sq_eq_zero_iff, norm_eq_zero]
  exact (U ⊓ Vᗮ).starProjection_apply_eq_zero_iff

end Descent.Portability.NestedRepairSpans
