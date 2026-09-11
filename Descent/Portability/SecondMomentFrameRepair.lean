/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SecondMomentAuditConfidence
import Descent.Portability.CertifiedFrameRepair

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 24, connected to the actual
audit-selected frame prediction. The trace radius is computed from fixed
features, known inclusion probabilities and justified residual second-moment
bounds. It certifies expected gain and oracle regret without fourth moments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SecondMomentFrameRepair

open MeasureTheory DecisionLossContrasts GramSafeRepair GramAuditGeometry
open SharedAuditCompletion CertifiedFrameRepair

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]

/-- The second-moment confidence radius in the exact inverse-Gram metric. -/
noncomputable def auditRadius (w : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (p e : ι → ℝ) (δ : ℝ) : ℝ :=
  Real.sqrt (SecondMomentAuditConfidence.traceBound p e (rows (gram w φ) hG w φ) / δ)

/-- The same estimate used in the fitted correction has the stated confidence radius. -/
theorem estimate_confidence (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (p q e : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (he : ∀ i, (∫ y, (y - q i) ^ 2 ∂μ i) ≤ e i ^ 2) :
    (frameLaw μ p q).real {z | auditRadius w φ hG p e δ <
      signal (gram w φ) (residual μ w f φ - estimate w f φ z)} ≤ δ := by
  have hh := SecondMomentAuditConfidence.confidence μ p q e (rows (gram w φ) hG w φ)
    δ hδ hp hY he
  simpa only [auditRadius, error_norm μ (gram w φ) hG w f φ] using hh

/-- Actual gain, regret and oracle-value claims hold jointly with finite-sample confidence. -/
theorem false_certificate_probability
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (p q e : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (he : ∀ i, (∫ y, (y - q i) ^ 2 ∂μ i) ≤ e i ^ 2) :
    (frameLaw μ p q).real {z | ¬ Certificate μ w f φ (auditRadius w φ hG p e δ) z} ≤ δ := by
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  apply le_trans (measureReal_mono (show
    {z | ¬ Certificate μ w f φ (auditRadius w φ hG p e δ) z} ⊆
    {z | auditRadius w φ hG p e δ <
      signal (gram w φ) (residual μ w f φ - estimate w f φ z)} from ?_))
    (estimate_confidence μ w f φ hG p q e δ hδ hp hY he)
  intro z hz
  change auditRadius w φ hG p e δ <
    signal (gram w φ) (residual μ w f φ - estimate w f φ z)
  apply lt_of_not_ge
  intro hc
  exact hz (certificate_on_event μ w f φ hG _ z hY (Real.sqrt_nonneg _) hc)

/-- In particular, the probability of negative expected frame gain is at most the audit budget. -/
theorem harm_probability (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (p q e : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (he : ∀ i, (∫ y, (y - q i) ^ 2 ∂μ i) ≤ e i ^ 2) :
    (frameLaw μ p q).real {z | improvement μ w f φ (auditRadius w φ hG p e δ) z < 0} ≤ δ := by
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  apply le_trans (measureReal_mono (show
    {z | improvement μ w f φ (auditRadius w φ hG p e δ) z < 0} ⊆
    {z | ¬ Certificate μ w f φ (auditRadius w φ hG p e δ) z} from ?_))
    (false_certificate_probability μ w f φ hG p q e δ hδ hp hY he)
  intro z hz hc
  have hnonneg := (sq_nonneg _).trans hc.1
  exact (not_lt.mpr hnonneg) hz

end Descent.Portability.SecondMomentFrameRepair
