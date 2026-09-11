/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralMinimaxAuditDesign
import Descent.Portability.CertifiedFrameRepair

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, the spectral cap-search-to-repair theorem.
One allocation is chosen from the registered target frame and support/mean
bands, before any target outcome law or labels are supplied. Its actual
vector confidence radius is within the requested factor of every feasible
allocation. Under each compatible outcome law, the continuous repair's
actual frame-gain, oracle-regret, and oracle-upper certificates fail with
probability at most the declared error budget.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OptimizedFrameRepairAudit

open MeasureTheory Matrix AuditVarianceGeometry FiniteAuditDesign
open DecisionLossContrasts GramAuditGeometry CertifiedFrameRepair SharedAuditCompletion

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]

/-- Range-aware spectral allocation and actual continuous-repair safety hold for the same audit. -/
theorem design_exists (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (L U lo hi floor c : ι → ℝ) (B δ rate : ℝ)
    (hδ : 0 < δ ∧ δ < 1) (hrate : 1 < rate) (hf : ∀ i, 0 < floor i)
    (hb : ∀ i, L i ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ U i)
    (hranges : ∀ i, 0 < SpectralMinimaxAuditDesign.rowRange L U (rows (gram w φ) hG w φ) i)
    (hne : ∃ p, Feasible floor c B p) :
    ∃ p : ι → ℝ, Feasible floor c B p ∧
      (∀ r, Feasible floor c B r →
        auditRadius w φ hG L U p (fun i ↦ proxy (L i) (U i) (lo i) (hi i)) lo hi δ ≤
          rate * auditRadius w φ hG L U r
            (fun i ↦ proxy (L i) (U i) (lo i) (hi i)) lo hi δ) ∧
      ∀ μ : ι → Measure ℝ, (∀ i, IsProbabilityMeasure (μ i)) →
        (∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i)) →
        (∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) →
        (frameLaw μ p (fun i ↦ proxy (L i) (U i) (lo i) (hi i))).real
          {z | ¬ Certificate μ w f φ
            (auditRadius w φ hG L U p
              (fun i ↦ proxy (L i) (U i) (lo i) (hi i)) lo hi δ) z} ≤ δ := by
  obtain ⟨p, hp, happrox, _⟩ := SpectralMinimaxAuditDesign.design_exists L U lo hi floor c
    (rows (gram w φ) hG w φ) B δ rate hδ hrate hf hb hranges hne
  refine ⟨p, hp, happrox, ?_⟩
  intro μ hprob hs hm
  letI (i : ι) : IsProbabilityMeasure (μ i) := hprob i
  have hq (i : ι) : proxy (L i) (U i) (lo i) (hi i) ∈ Set.Icc (L i) (U i) := by
    have hh := clip_mem (lo i) (hi i) ((L i + U i) / 2) (hb i).2.1
    exact ⟨(hb i).1.trans hh.1, hh.2.trans (hb i).2.2⟩
  exact false_certificate_probability μ w f φ hG L U p _ lo hi δ hδ
    (fun i ↦ ⟨(hf i).trans_le (hp.1 i).1, (hp.1 i).2⟩) hq hs hm

end Descent.Portability.OptimizedFrameRepairAudit
