/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ContinuousAuditCapSearch
import Descent.Portability.SpectralAuditDesign

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 16 for the actual spectral audit
criterion. The objective includes both the largest covariance eigenvalue
and the maximum observation range, with the vector-net factor two retained.
The global optimum exists, optimizing over range caps is exact, and a finite
geometric cap search has the stated multiplicative approximation guarantee.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralRangeAuditDesign

open FiniteAuditDesign AuditRangeCaps GeometricAuditCaps RangeAwareAuditSearch
open SpectralAuditDesign BernsteinTailBound

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The full vector confidence radius in actual spectral covariance and row-range coordinates. -/
noncomputable def fullRadius (κ h p : ι → ℝ) (u : ι → E) (x : ℝ) : ℝ :=
  2 * ContinuousAuditCapSearch.designRadius (objective κ u) h p x

/-- The full spectral radius is continuous on the registered positive-floor budget set. -/
theorem radius_continuous (κ floor c h : ι → ℝ) (u : ι → E) (B x : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) :
    ContinuousOn (fun p ↦ fullRadius κ h p u x) {p | Feasible floor c B p} :=
  continuousOn_const.mul (ContinuousAuditCapSearch.radius_continuous (objective κ u)
    floor c h B x hf (SpectralAuditDesign.objective_continuous κ floor c u B hκ hf))

/-- The best attainable full spectral confidence radius has an actual feasible minimizer. -/
theorem radius_minimum (κ floor c h : ι → ℝ) (u : ι → E) (B x : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i)
    (hne : {p | Feasible floor c B p}.Nonempty) :
    ∃ p, Feasible floor c B p ∧
      IsMinOn (fun q ↦ fullRadius κ h q u x) {q | Feasible floor c B q} p :=
  (FiniteAuditDesignConvexity.feasible_compact floor c B).exists_isMinOn hne
    (radius_continuous κ floor c h u B x hκ hf)

/-- Every capped spectral subproblem remains convex in its actual sampling probabilities. -/
theorem capped_convex (κ floor c h : ι → ℝ) (u : ι → E) (B m : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) :
    ConvexOn ℝ {p | Feasible (cappedFloor floor h m) c B p} (objective κ u) :=
  SpectralAuditDesign.objective_convex κ (cappedFloor floor h m) c u B hκ
    (fun i ↦ (hf i).trans_le (le_max_left _ _))

/-- Optimizing the actual eigenvalue at the optimal range cap preserves the exact full optimum. -/
theorem exact_cap_reduction (κ floor c h p : ι → ℝ) (u : ι → E) (B x : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hh : ∀ i, 0 < h i) (hx : 0 ≤ x)
    (hp : Feasible floor c B p)
    (hopt : IsMinOn (fun q ↦ fullRadius κ h q u x) {q | Feasible floor c B q} p) :
    ∃ q, Feasible (cappedFloor floor h (maxRange h p)) c B q ∧
      IsMinOn (objective κ u) {r | Feasible (cappedFloor floor h (maxRange h p)) c B r} q ∧
      2 * radius (maxRange h p) (objective κ u q) x = fullRadius κ h p u x ∧
      fullRadius κ h q u x = fullRadius κ h p u x := by
  have hmin : IsMinOn (fun q ↦ ContinuousAuditCapSearch.designRadius (objective κ u) h q x)
      {q | Feasible floor c B q} p := by
    intro q hq
    have hh := hopt hq
    change fullRadius κ h p u x ≤ fullRadius κ h q u x at hh
    unfold fullRadius at hh
    change ContinuousAuditCapSearch.designRadius (objective κ u) h p x ≤
      ContinuousAuditCapSearch.designRadius (objective κ u) h q x
    linarith
  obtain ⟨q, hq, hqmin, he, he'⟩ := ContinuousAuditCapSearch.exact_cap_reduction
    (objective κ u) floor c h p B x hf hh hx
    (SpectralAuditDesign.objective_continuous κ floor c u B hκ hf) hp hmin
  exact ⟨q, hq, hqmin, congrArg (fun z : ℝ ↦ 2 * z) he,
    congrArg (fun z : ℝ ↦ 2 * z) he'⟩

/-- A finite geometric search over actual capped spectral optimizers achieves the radius factor. -/
theorem finite_search_exists (κ floor c h : ι → ℝ) (u : ι → E) (B x rate : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hh : ∀ i, 0 < h i)
    (hx : 0 ≤ x) (hrate : 1 < rate) (hne : ∃ p, Feasible floor c B p) :
    ∃ N : ℕ, ∃ cap ∈ grid (lowerCap h) (upperCap floor h) rate N, ∃ q,
      Feasible (cappedFloor floor h cap) c B q ∧
      IsMinOn (objective κ u) {p | Feasible (cappedFloor floor h cap) c B p} q ∧
      ∀ p, Feasible floor c B p → fullRadius κ h q u x ≤ rate * fullRadius κ h p u x := by
  obtain ⟨N, cap, hcap, q, hq, hmin, happrox⟩ := ContinuousAuditCapSearch.finite_search_exists
    (objective κ u) floor c h B x rate hf hh hx hrate
    (SpectralAuditDesign.objective_continuous κ floor c u B hκ hf) hne
  refine ⟨N, cap, hcap, q, hq, hmin, ?_⟩
  intro p hp
  have hh := mul_le_mul_of_nonneg_left (happrox p hp) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [fullRadius, mul_left_comm 2 rate] using hh

/-- The design returned by cap search is feasible and competes with every allowed audit. -/
theorem design_exists (κ floor c h : ι → ℝ) (u : ι → E) (B x rate : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hh : ∀ i, 0 < h i)
    (hx : 0 ≤ x) (hrate : 1 < rate) (hne : ∃ p, Feasible floor c B p) :
    ∃ q, Feasible floor c B q ∧
      ∀ p, Feasible floor c B p → fullRadius κ h q u x ≤ rate * fullRadius κ h p u x := by
  obtain ⟨N, cap, _, q, hq, _, happrox⟩ := finite_search_exists κ floor c h u B x rate
    hκ hf hh hx hrate hne
  exact ⟨q, ContinuousAuditCapSearch.capped_subset floor c h B cap hq, happrox⟩

end Descent.Portability.SpectralRangeAuditDesign
