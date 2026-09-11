/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SafeRepairGeometry
import Mathlib.LinearAlgebra.Matrix.PosDef

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Corollary 13 in the original coefficient
coordinates. A positive-definite Gram matrix induces the actual inner product
used to instantiate the robust repair theorem. The norm is derived as the
square root of the inverse quadratic form; no whitening or gain identity is
supplied as an assumption. All matrix dimensions, including zero, are allowed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GramSafeRepair

open Matrix
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The oracle gain of the chosen Gram geometry. -/
noncomputable def oracle (G : Matrix ι ι ℝ) (r : ι → ℝ) : ℝ := r ⬝ᵥ (G⁻¹ *ᵥ r)

/-- The magnitude of the whitened repair signal, expressed without choosing a square root matrix. -/
noncomputable def signal (G : Matrix ι ι ℝ) (r : ι → ℝ) : ℝ := Real.sqrt (oracle G r)

/-- Squared-error improvement in the original coefficient coordinates. -/
noncomputable def gain (G : Matrix ι ι ℝ) (θ r : ι → ℝ) : ℝ :=
  2 * (θ ⬝ᵥ r) - θ ⬝ᵥ (G *ᵥ θ)

/-- The conservative update with the manuscript's zero-signal convention. -/
noncomputable def repair (G : Matrix ι ι ℝ) (r : ι → ℝ) (ε : ℝ) : ι → ℝ :=
  if signal G r ≤ ε then 0 else ((signal G r - ε) / signal G r) • (G⁻¹ *ᵥ r)

/-- Positive definiteness makes the actual matrix inverse solve the normal equation. -/
theorem normal_equation (G : Matrix ι ι ℝ) (hG : G.PosDef) (r : ι → ℝ) :
    G *ᵥ (G⁻¹ *ᵥ r) = r := by
  rw [mulVec_mulVec, mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne'), one_mulVec]

/-- The reverse normal equation makes the coefficient/mean correspondence onto. -/
theorem inverse_normal_equation (G : Matrix ι ι ℝ) (hG : G.PosDef) (u : ι → ℝ) :
    G⁻¹ *ᵥ (G *ᵥ u) = u := by
  rw [mulVec_mulVec, nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hG.det_pos.ne'), one_mulVec]

section InducedGeometry

variable (G : Matrix ι ι ℝ) (hG : G.PosDef)

local instance : NormedAddCommGroup (ι → ℝ) := Matrix.NormedAddCommGroup.ofMatrix hG
local instance : InnerProductSpace ℝ (ι → ℝ) := Matrix.InnerProductSpace.ofMatrix hG

/-- The induced inner product is the Gram quadratic geometry itself. -/
theorem induced_inner (u v : ι → ℝ) : ⟪u, v⟫ = u ⬝ᵥ (G *ᵥ v) := by
  change (G *ᵥ v) ⬝ᵥ star u = u ⬝ᵥ (G *ᵥ v)
  simp only [star_trivial]
  exact dotProduct_comm _ _

/-- The induced squared norm is exactly the Gram quadratic form. -/
theorem induced_norm_sq (u : ι → ℝ) : ‖u‖ ^ 2 = u ⬝ᵥ (G *ᵥ u) := by
  rw [← real_inner_self_eq_norm_sq, induced_inner]

/-- The inverse quadratic signal equals the actual norm of the oracle coefficient. -/
theorem induced_signal (r : ι → ℝ) : ‖G⁻¹ *ᵥ r‖ = signal G r := by
  have he : ‖G⁻¹ *ᵥ r‖ ^ 2 = oracle G r := by
    rw [induced_norm_sq G hG, normal_equation G hG]
    exact dotProduct_comm _ _
  rw [signal, ← he, Real.sqrt_sq (norm_nonneg _)]

/-- The whitened gain theorem agrees exactly with the original matrix gain. -/
theorem induced_gain (u r : ι → ℝ) :
    SafeRepairGeometry.gain u (G⁻¹ *ᵥ r) = gain G u r := by
  rw [SafeRepairGeometry.gain, induced_inner G hG, normal_equation G hG,
    induced_norm_sq G hG]
  rfl

/-- The coefficient error norm is exactly the specified inverse quadratic confidence metric. -/
theorem induced_error (r h : ι → ℝ) :
    ‖G⁻¹ *ᵥ r - G⁻¹ *ᵥ h‖ = signal G (r - h) := by
  rw [← mulVec_sub, induced_signal G hG]

/-- The abstract ball optimizer is precisely the explicit coefficient update. -/
theorem induced_repair (h : ι → ℝ) (ε : ℝ) :
    SafeRepairGeometry.safe (G⁻¹ *ᵥ h) ε = repair G h ε := by
  simp only [SafeRepairGeometry.safe, induced_signal G hG, repair]

end InducedGeometry

/-- A positive-definite Gram matrix has a nonnegative oracle gain. -/
theorem oracle_nonneg (G : Matrix ι ι ℝ) (hG : G.PosDef) (r : ι → ℝ) :
    0 ≤ oracle G r := by
  exact hG.inv.posSemidef.dotProduct_mulVec_nonneg r

/-- The reported repair has its exact gain certificate and its oracle-regret bound. -/
theorem repair_certificate (G : Matrix ι ι ℝ) (hG : G.PosDef) (h r : ι → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hr : signal G (r - h) ≤ ε) :
    max 0 (signal G h - ε) ^ 2 ≤ gain G (repair G h ε) r ∧
      0 ≤ oracle G r - gain G (repair G h ε) r ∧
      oracle G r - gain G (repair G h ε) r ≤ 4 * ε ^ 2 := by
  letI : NormedAddCommGroup (ι → ℝ) := Matrix.NormedAddCommGroup.ofMatrix hG
  letI : InnerProductSpace ℝ (ι → ℝ) := Matrix.InnerProductSpace.ofMatrix hG
  have hc : ‖G⁻¹ *ᵥ r - G⁻¹ *ᵥ h‖ ≤ ε := by rw [induced_error G hG]; exact hr
  have hl := SafeRepairGeometry.safe_gain (G⁻¹ *ᵥ h) (G⁻¹ *ᵥ r) ε hε hc
  have hb := SafeRepairGeometry.safe_oracle_regret (G⁻¹ *ᵥ h) (G⁻¹ *ᵥ r) ε hε hc
  rw [induced_repair G hG, induced_gain G hG, induced_signal G hG] at hl
  rw [induced_repair G hG, induced_gain G hG, induced_norm_sq G hG,
    normal_equation G hG, dotProduct_comm (G⁻¹ *ᵥ r) r] at hb
  exact ⟨hl, hb⟩

/-- The audit also certifies how much any repair in the same span could accomplish. -/
theorem oracle_interval (G : Matrix ι ι ℝ) (hG : G.PosDef) (h r : ι → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hr : signal G (r - h) ≤ ε) :
    max 0 (signal G h - ε) ^ 2 ≤ oracle G r ∧
      oracle G r ≤ (signal G h + ε) ^ 2 := by
  letI : NormedAddCommGroup (ι → ℝ) := Matrix.NormedAddCommGroup.ofMatrix hG
  letI : InnerProductSpace ℝ (ι → ℝ) := Matrix.InnerProductSpace.ofMatrix hG
  have hc : ‖G⁻¹ *ᵥ r - G⁻¹ *ᵥ h‖ ≤ ε := by rw [induced_error G hG]; exact hr
  have hh := SafeRepairGeometry.oracle_interval (G⁻¹ *ᵥ h) (G⁻¹ *ᵥ r) ε hε hc
  rw [induced_signal G hG, induced_norm_sq G hG, normal_equation G hG,
    dotProduct_comm (G⁻¹ *ᵥ r) r] at hh
  exact hh

end Descent.Portability.GramSafeRepair
