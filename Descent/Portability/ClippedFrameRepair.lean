/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CertifiedFrameRepair

assert_below Descent.Decision Descent.Program

/-!
The bounded-prediction consequence of Decision-Directed Portability,
Corollary 13. Clipping a fitted prediction to the actual outcome support
cannot increase pointwise or expected squared loss. Thus the audit's
improvement certificate survives clipping, in particular to [0,1] for a
binary outcome. Optimality over the linear span is not asserted for clipping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ClippedFrameRepair

open MeasureTheory AuditVarianceGeometry DecisionLossContrasts GramSafeRepair
open GramAuditGeometry CertifiedFrameRepair SharedAuditCompletion
open scoped BigOperators

/-- Projection onto the outcome interval can only decrease squared prediction loss. -/
theorem pointwise_loss (L U y f : ℝ) (hy : y ∈ Set.Icc L U) :
    (y - clip L U f) ^ 2 ≤ (y - f) ^ 2 := by
  have hh := clip_normal L U f y hy
  nlinarith [sq_nonneg (f - clip L U f)]

/-- Both genuine expected losses exist, and clipping decreases the expected loss. -/
theorem expected_loss (μ : Measure ℝ) [IsProbabilityMeasure μ] (L U f : ℝ)
    (hs : ∀ᵐ y ∂μ, y ∈ Set.Icc L U) :
    (∫ y, (y - clip L U f) ^ 2 ∂μ) ≤ ∫ y, (y - f) ^ 2 ∂μ := by
  have hY := memLp_of_bounded hs measurable_id.aestronglyMeasurable 2
  have hc : Integrable (fun y : ℝ ↦ (y - clip L U f) ^ 2) μ :=
    (hY.sub (memLp_const (clip L U f))).integrable_sq
  have hf : Integrable (fun y : ℝ ↦ (y - f) ^ 2) μ :=
    (hY.sub (memLp_const f)).integrable_sq
  apply integral_mono_ae hc hf
  filter_upwards [hs] with y hy
  exact pointwise_loss L U y f hy

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Expected risk decreases under support clipping on any nonnegatively weighted frame. -/
theorem frame_loss (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w L U f : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i)) :
    frameRisk μ w (fun i ↦ clip (L i) (U i) (f i)) ≤ frameRisk μ w f := by
  unfold frameRisk
  exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left
    (expected_loss (μ i) (L i) (U i) (f i) (hs i)) (hw i))

/-- The probability of a false gain certificate is still at most delta after support clipping. -/
theorem false_gain_probability [Nonempty ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef) (hw : ∀ i, 0 ≤ w i)
    (L U p q lo hi : ι → ℝ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    (frameLaw μ p q).real {z | frameRisk μ w f - frameRisk μ w
      (fun i ↦ clip (L i) (U i) (predict f φ
        (repair (gram w φ) (estimate w f φ z) (auditRadius w φ hG L U p q lo hi δ)) i)) <
      max 0 (signal (gram w φ) (estimate w f φ z) - auditRadius w φ hG L U p q lo hi δ) ^ 2}
      ≤ δ := by
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  apply le_trans (measureReal_mono (show _ ⊆ {z | ¬ Certificate μ w f φ
    (auditRadius w φ hG L U p q lo hi δ) z} from ?_))
    (false_certificate_probability μ w f φ hG L U p q lo hi δ hδ hp hq hs hband)
  intro z hz hc
  have hh := frame_loss μ w L U
    (predict f φ (repair (gram w φ) (estimate w f φ z) (auditRadius w φ hG L U p q lo hi δ)))
    hw hs
  have hg := hc.1
  unfold improvement at hg
  exact not_lt_of_ge (hg.trans (sub_le_sub_left hh _)) hz

end Descent.Portability.ClippedFrameRepair
