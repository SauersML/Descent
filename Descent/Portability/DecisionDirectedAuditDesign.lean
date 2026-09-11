/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MinimaxAuditDesignLaw

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, the finite-library design-to-audit theorem.
A finite geometric search selects an allocation within the prescribed factor
of the best full confidence radius, under the actual expected labeling
budget. That one allocation is certified simultaneously for every independent
outcome-law family compatible with the registered support and mean bands.
The allocation is therefore chosen without using the unknown target means.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DecisionDirectedAuditDesign

open MeasureTheory AuditVarianceGeometry FiniteAuditDesign AuditRangeCaps
open RangeAwareAuditSearch MinimaxAuditDesignLaw SharedAuditCompletion IndependentContrastLaw

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- One design has the cap-search guarantee and valid confidence for every compatible target law. -/
theorem design_exists (K : ℕ) [NeZero K] (L U lo hi floor c : ι → ℝ)
    (w : Fin K → ι → ℝ) (B δ rate : ℝ) (hδ : 0 < δ ∧ δ < 1) (hrate : 1 < rate)
    (hf : ∀ i, 0 < floor i) (hb : ∀ i, L i ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ U i)
    (hranges : ∀ i, 0 < ranges L U w i) (hne : ∃ p, Feasible floor c B p) :
    ∃ p : ι → ℝ, Feasible floor c B p ∧
      (∀ r, Feasible floor c B r →
        fullRadius (coefficients L U lo hi w) (ranges L U w) p (Real.log (2 * K / δ)) ≤
          rate * fullRadius (coefficients L U lo hi w) (ranges L U w) r
            (Real.log (2 * K / δ))) ∧
      ∀ μ : ι → Measure ℝ, (∀ i, IsProbabilityMeasure (μ i)) →
        (∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i)) →
        (∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) →
        (frameLaw μ p (fun i ↦ proxy (L i) (U i) (lo i) (hi i))).real
          {z | ∃ j, fullRadius (coefficients L U lo hi w) (ranges L U w) p
            (Real.log (2 * K / δ)) < |contrast (w j) z - ∑ i, w j i * ∫ y, y ∂μ i|} ≤ δ := by
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hx := (FiniteAuditConfidence.confidence_exponent_pos K hK δ hδ).le
  obtain ⟨N, cap, hcap, p, hp, _hmin, happrox⟩ := finite_search_exists
    (coefficients L U lo hi w) floor c (ranges L U w) B (Real.log (2 * K / δ)) rate
    hf hranges hx hrate hne
  have hlow : 0 < lowerCap (ranges L U w) :=
    maxRange_pos _ (fun _ ↦ 1) hranges (fun _ ↦ by norm_num)
  have hinterval : lowerCap (ranges L U w) ≤ upperCap floor (ranges L U w) := by
    obtain ⟨r, hr⟩ := hne
    have hh := range_interval floor c (ranges L U w) r B hf (fun i ↦ (hranges i).le) hr
    exact hh.1.trans hh.2
  have hcpos : 0 < cap := hlow.trans_le
    (GeometricAuditCaps.grid_mem_interval _ _ rate N hlow.le hinterval hrate.le cap hcap).1
  have hpf := ((capped_feasible_iff floor c (ranges L U w) p B cap hf hcpos).mp hp).1
  refine ⟨p, hpf, happrox, ?_⟩
  intro μ hprob hs hm
  letI (i : ι) : IsProbabilityMeasure (μ i) := hprob i
  exact common_confidence K μ L U p lo hi w δ hδ
    (fun i ↦ ⟨(hf i).trans_le (hpf.1 i).1, (hpf.1 i).2⟩) hb hs hm

end Descent.Portability.DecisionDirectedAuditDesign
