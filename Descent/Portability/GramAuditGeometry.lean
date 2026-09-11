/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DecisionLossContrasts
import Descent.Portability.SpectralAuditConfidence

assert_below Descent.Decision Descent.Program

/-!
The coordinate bridge for Decision-Directed Portability, Theorems 10--13.
The actual audit estimate is mapped into the Gram-induced Hilbert space.
Its error norm is derived as the inverse quadratic confidence metric, so the
statistical confidence theorem and the repair theorem concern the same
random estimate and the same target residual correlations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GramAuditGeometry

open MeasureTheory Matrix GramSafeRepair DecisionLossContrasts
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The Gram space has precisely the finite dimension of the correction coefficients. -/
noncomputable instance gramFinite (G : Matrix κ κ ℝ) (hG : G.PosDef) :
    FiniteDimensional ℝ (GramSpace G hG) := inferInstanceAs (FiniteDimensional ℝ (κ → ℝ))

/-- The net dimension is the actual number of independent correction columns. -/
theorem gram_finrank (G : Matrix κ κ ℝ) (hG : G.PosDef) :
    Module.finrank ℝ (GramSpace G hG) = Fintype.card κ := by
  change Module.finrank ℝ (κ → ℝ) = Fintype.card κ
  simp

/-- The residual-correlation estimator, computed from the observed augmented outcomes. -/
noncomputable def estimate (w f : ι → ℝ) (φ : ι → κ → ℝ) (z : ι → ℝ) : κ → ℝ :=
  ∑ i, (w i * (z i - f i)) • φ i

/-- Whitened and normalized coefficient rows, represented in the equivalent Gram geometry. -/
noncomputable def rows (G : Matrix κ κ ℝ) (hG : G.PosDef)
    (w : ι → ℝ) (φ : ι → κ → ℝ) (i : ι) : GramSpace G hG :=
  toGram G hG (w i • (G⁻¹ *ᵥ φ i))

/-- The vector audit error is the inverse-Gram transform of the actual residual estimate error. -/
theorem error_vector (μ : ι → Measure ℝ) (G : Matrix κ κ ℝ) (hG : G.PosDef)
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (z : ι → ℝ) :
    VectorAuditConfidence.error μ (rows G hG w φ) z =
      toGram G hG (G⁻¹ *ᵥ (estimate w f φ z - residual μ w f φ)) := by
  change (∑ i, (z i - ∫ y, y ∂μ i) • (w i • (G⁻¹ *ᵥ φ i))) =
    G⁻¹ *ᵥ ((∑ i, (w i * (z i - f i)) • φ i) -
      ∑ i, (w i * ((∫ y, y ∂μ i) - f i)) • φ i)
  rw [mulVec_sub, mulVec_sum, mulVec_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mulVec_smul, mulVec_smul, ← sub_smul, smul_smul]
  congr 1
  ring

/-- The confidence norm is exactly the inverse quadratic metric used by the safe repair. -/
theorem error_norm (μ : ι → Measure ℝ) (G : Matrix κ κ ℝ) (hG : G.PosDef)
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (z : ι → ℝ) :
    ‖VectorAuditConfidence.error μ (rows G hG w φ) z‖ =
      signal G (residual μ w f φ - estimate w f φ z) := by
  rw [error_vector μ G hG w f φ z, mulVec_sub, toGram_sub, norm_sub_rev,
    induced_error G hG]

/-- Row norms are the exact leverage terms of the inverse Gram matrix. -/
theorem row_norm (G : Matrix κ κ ℝ) (hG : G.PosDef)
    (w : ι → ℝ) (φ : ι → κ → ℝ) (i : ι) :
    ‖rows G hG w φ i‖ = |w i| * signal G (φ i) := by
  change ‖w i • toGram G hG (G⁻¹ *ᵥ φ i)‖ = _
  rw [norm_smul, Real.norm_eq_abs, induced_signal G hG]

end Descent.Portability.GramAuditGeometry
