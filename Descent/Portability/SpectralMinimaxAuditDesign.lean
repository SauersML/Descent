/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralRangeAuditDesign
import Descent.Portability.MinimaxAuditDesignLaw
import Descent.Portability.SpectralAuditConfidence

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 16 connected to Theorem 10. The
minimax-proxy audit covariance equals the spectral reciprocal objective,
and the optimized row ranges equal the actual increment ranges. The
allocation is selected before the target outcome law is supplied and
certifies every compatible independent bounded-outcome audit law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralMinimaxAuditDesign

open MeasureTheory AuditVarianceGeometry MinimaxAuditDesignLaw FiniteAuditDesign
open SharedAuditCompletion
open scoped BigOperators

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Registered norm-based row ranges, including any normalization in the correction vectors. -/
noncomputable def rowRange (L U : ι → ℝ) (u : ι → E) (i : ι) : ℝ := ‖u i‖ * (U i - L i)

/-- Valid support and honest mean bands give nonnegative actual minimax variance coefficients. -/
theorem kappa_nonneg (L U lo hi : ι → ℝ)
    (hb : ∀ i, L i ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ U i) (i : ι) :
    0 ≤ kappa L U lo hi i := by
  have hq := clip_mem (lo i) (hi i) ((L i + U i) / 2) (hb i).2.1
  have hl : L i ≤ proxy (L i) (U i) (lo i) (hi i) := (hb i).1.trans hq.1
  have hu : proxy (L i) (U i) (lo i) (hi i) ≤ U i := hq.2.trans (hb i).2.2
  exact mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)

/-- The actual minimax-proxy covariance eigenvalue is precisely the design objective. -/
theorem variance_identity (L U p lo hi : ι → ℝ) (u : ι → E)
    (hp : ∀ i, 0 < p i) (hb : ∀ i, lo i ≤ hi i) :
    SpectralAuditConfidence.variance L U p (fun i ↦ proxy (L i) (U i) (lo i) (hi i)) lo hi u =
      SpectralAuditDesign.objective (kappa L U lo hi) u p := by
  unfold SpectralAuditConfidence.variance SpectralAuditDesign.objective
  congr 1
  funext i
  exact proxy_envelope_value (L i) (U i) (p i) (lo i) (hi i) (hp i) (hb i)

/-- The norm-range maximum in the confidence theorem is exactly the optimized range objective. -/
theorem range_identity (L U p : ι → ℝ) (u : ι → E) :
    SpectralAuditConfidence.range L U p u = AuditRangeCaps.maxRange (rowRange L U u) p := rfl

/-- The complete vector confidence radius agrees with the optimized spectral range-aware radius. -/
theorem radius_identity (L U p lo hi : ι → ℝ) (u : ι → E) (δ : ℝ)
    (hp : ∀ i, 0 < p i) (hb : ∀ i, lo i ≤ hi i) :
    SpectralAuditConfidence.confidenceRadius L U p
      (fun i ↦ proxy (L i) (U i) (lo i) (hi i)) lo hi u δ =
      SpectralRangeAuditDesign.fullRadius (kappa L U lo hi) (rowRange L U u) p u
        (Real.log (2 * (5 ^ Module.finrank ℝ E : ℕ) / δ)) := by
  unfold SpectralAuditConfidence.confidenceRadius SpectralRangeAuditDesign.fullRadius
    ContinuousAuditCapSearch.designRadius
  rw [variance_identity L U p lo hi u hp hb, range_identity]

/-- The selected design has the factor guarantee and valid confidence for every compatible law. -/
theorem design_exists (L U lo hi floor c : ι → ℝ) (u : ι → E) (B δ rate : ℝ)
    (hδ : 0 < δ ∧ δ < 1) (hrate : 1 < rate) (hf : ∀ i, 0 < floor i)
    (hb : ∀ i, L i ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ U i)
    (hranges : ∀ i, 0 < rowRange L U u i) (hne : ∃ p, Feasible floor c B p) :
    ∃ p : ι → ℝ, Feasible floor c B p ∧
      (∀ r, Feasible floor c B r →
        SpectralAuditConfidence.confidenceRadius L U p
          (fun i ↦ proxy (L i) (U i) (lo i) (hi i)) lo hi u δ ≤
        rate * SpectralAuditConfidence.confidenceRadius L U r
          (fun i ↦ proxy (L i) (U i) (lo i) (hi i)) lo hi u δ) ∧
      ∀ μ : ι → Measure ℝ, (∀ i, IsProbabilityMeasure (μ i)) →
        (∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i)) →
        (∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) →
        (frameLaw μ p (fun i ↦ proxy (L i) (U i) (lo i) (hi i))).real
          {z | SpectralAuditConfidence.confidenceRadius L U p
            (fun i ↦ proxy (L i) (U i) (lo i) (hi i)) lo hi u δ <
            ‖VectorAuditConfidence.error μ u z‖} ≤ δ := by
  have hx := (FiniteAuditConfidence.confidence_exponent_pos
    (5 ^ Module.finrank ℝ E) (by positivity) δ hδ).le
  obtain ⟨p, hp, happrox⟩ := SpectralRangeAuditDesign.design_exists (kappa L U lo hi)
    floor c (rowRange L U u) u B (Real.log (2 * (5 ^ Module.finrank ℝ E : ℕ) / δ)) rate
    (kappa_nonneg L U lo hi hb) hf hranges hx hrate hne
  have hpos (i : ι) := (hf i).trans_le (hp.1 i).1
  refine ⟨p, hp, ?_, ?_⟩
  · intro r hr
    rw [radius_identity L U p lo hi u δ hpos (fun i ↦ (hb i).2.1),
      radius_identity L U r lo hi u δ (fun i ↦ (hf i).trans_le (hr.1 i).1)
        (fun i ↦ (hb i).2.1)]
    exact happrox r hr
  · intro μ hprob hs hm
    letI (i : ι) : IsProbabilityMeasure (μ i) := hprob i
    have hq (i : ι) : proxy (L i) (U i) (lo i) (hi i) ∈ Set.Icc (L i) (U i) := by
      have hh := clip_mem (lo i) (hi i) ((L i + U i) / 2) (hb i).2.1
      exact ⟨(hb i).1.trans hh.1, hh.2.trans (hb i).2.2⟩
    exact SpectralAuditConfidence.confidence μ L U p _ lo hi u δ hδ
      (fun i ↦ ⟨hpos i, (hp.1 i).2⟩) hq hs hm

end Descent.Portability.SpectralMinimaxAuditDesign
