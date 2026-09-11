/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GramAuditGeometry

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, the actual audit-to-repair guarantee.
The registered frame, features, proxies and request probabilities determine
one radius. The observed audit determines the continuous repair. Under the
specified independent bounded outcome laws, the probability of any false
reported gain, regret or oracle upper certificate is at most delta.
This is a statement about expected frame loss, not individual realized loss.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CertifiedFrameRepair

open MeasureTheory Matrix GramSafeRepair DecisionLossContrasts GramAuditGeometry
open SharedAuditCompletion

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]

/-- The numerical radius determined before revealing the audit outcomes. -/
noncomputable def auditRadius (w : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (L U p q lo hi : ι → ℝ) (δ : ℝ) : ℝ :=
  SpectralAuditConfidence.confidenceRadius L U p q lo hi (rows (gram w φ) hG w φ) δ

/-- The actual frame-risk improvement of the audit-selected repair. -/
noncomputable def improvement (μ : ι → Measure ℝ) (w f : ι → ℝ) (φ : ι → κ → ℝ)
    (ε : ℝ) (z : ι → ℝ) : ℝ :=
  frameRisk μ w f - frameRisk μ w (predict f φ (repair (gram w φ) (estimate w f φ z) ε))

/-- Joint reported claims: gain, oracle regret and the remaining value of this correction span. -/
def Certificate (μ : ι → Measure ℝ) (w f : ι → ℝ) (φ : ι → κ → ℝ)
    (ε : ℝ) (z : ι → ℝ) : Prop :=
  max 0 (signal (gram w φ) (estimate w f φ z) - ε) ^ 2 ≤ improvement μ w f φ ε z ∧
    0 ≤ oracle (gram w φ) (residual μ w f φ) - improvement μ w f φ ε z ∧
    oracle (gram w φ) (residual μ w f φ) - improvement μ w f φ ε z ≤ 4 * ε ^ 2 ∧
    oracle (gram w φ) (residual μ w f φ) ≤
      (signal (gram w φ) (estimate w f φ z) + ε) ^ 2

/-- The reported radius is nonnegative on the valid audit design domain. -/
theorem auditRadius_nonneg (w : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (L U p q lo hi : ι → ℝ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i) (hLU : ∀ i, L i ≤ U i) :
    0 ≤ auditRadius w φ hG L U p q lo hi δ := by
  unfold auditRadius SpectralAuditConfidence.confidenceRadius
  apply mul_nonneg (by norm_num)
  apply BernsteinTailBound.radius_nonneg
  · exact SpectralAuditConfidence.range_nonneg L U p _ hLU hp
  · exact (FiniteAuditConfidence.confidence_exponent_pos _ (by positivity) δ hδ).le

/-- The probability guarantee concerns the same estimate used in the deployed correction. -/
theorem estimate_confidence (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (L U p q lo hi : ι → ℝ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    (frameLaw μ p q).real {z | auditRadius w φ hG L U p q lo hi δ <
      signal (gram w φ) (residual μ w f φ - estimate w f φ z)} ≤ δ := by
  have hh := SpectralAuditConfidence.confidence μ L U p q lo hi
    (rows (gram w φ) hG w φ) δ hδ hp hq hs hband
  simpa only [auditRadius, error_norm μ (gram w φ) hG w f φ] using hh

/-- On the confidence event all reported claims concern actual expected frame losses. -/
theorem certificate_on_event (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef) (ε : ℝ) (z : ι → ℝ)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) (hε : 0 ≤ ε)
    (hc : signal (gram w φ) (residual μ w f φ - estimate w f φ z) ≤ ε) :
    Certificate μ w f φ ε z := by
  have hg := repair_certificate (gram w φ) hG (estimate w f φ z) (residual μ w f φ) ε hε hc
  have ho := oracle_interval (gram w φ) hG (estimate w f φ z) (residual μ w f φ) ε hε hc
  unfold Certificate improvement
  rw [frame_gain μ w f φ _ hY]
  exact ⟨hg.1, hg.2.1, hg.2.2, ho.2⟩

/-- End-to-end finite-sample safety for the actual continuous audit-selected repair. -/
theorem false_certificate_probability
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (L U p q lo hi : ι → ℝ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    (frameLaw μ p q).real {z | ¬ Certificate μ w f φ
      (auditRadius w φ hG L U p q lo hi δ) z} ≤ δ := by
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  have hε := auditRadius_nonneg w φ hG L U p q lo hi δ hδ
    (fun i ↦ (hp i).1) (fun i ↦ (hq i).1.trans (hq i).2)
  have hY (i : ι) := memLp_of_bounded (hs i) measurable_id.aestronglyMeasurable 2
  apply le_trans (measureReal_mono (show {z | ¬ Certificate μ w f φ
    (auditRadius w φ hG L U p q lo hi δ) z} ⊆
    {z | auditRadius w φ hG L U p q lo hi δ <
      signal (gram w φ) (residual μ w f φ - estimate w f φ z)} from ?_))
    (estimate_confidence μ w f φ hG L U p q lo hi δ hδ hp hq hs hband)
  intro z hz
  change auditRadius w φ hG L U p q lo hi δ <
    signal (gram w φ) (residual μ w f φ - estimate w f φ z)
  apply lt_of_not_ge
  intro hc
  exact hz (certificate_on_event μ w f φ hG _ z hY hε hc)

end Descent.Portability.CertifiedFrameRepair
