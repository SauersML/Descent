/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteAuditConfidence

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Corollary 19. After the actual audit, any subset
of the registered affine requirements may be claimed, provided each claimed
lower confidence bound is nonnegative. The probability of any false claim is
at most the original error budget, despite this post-audit selection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AuditSelectionSafety

open MeasureTheory ProbabilityTheory SharedAuditCompletion IndependentContrastLaw
open FiniteAuditConfidence BernsteinTailBound
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Data-dependent selection of certified requirements preserves the original failure bound. -/
theorem certified_selection (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p q lo hi : ι → ℝ) (K : ℕ) (hK : 0 < K) (w : Fin K → ι → ℝ)
    (a : Fin K → ℝ) (selected : (ι → ℝ) → Fin K → Prop) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i)
    (hcert : ∀ z j, selected z j → 0 ≤ a j + contrast (w j) z -
      radius (rangeBound L U p (w j)) (varianceBound L U p q lo hi (w j))
        (Real.log (2 * K / δ))) :
    (frameLaw μ p q).real {z | ∃ j, selected z j ∧
      a j + (∑ i, w j i * ∫ y, y ∂μ i) < 0} ≤ δ := by
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  have hb := finite_library_exact_range μ L U p q lo hi K hK w δ hδ hp hq hs hband
  apply le_trans (measureReal_mono _) hb
  rintro z ⟨j, hj, ht⟩
  refine ⟨j, ?_⟩
  apply lt_abs.mpr
  left
  have hc := hcert z j hj
  linarith

end Descent.Portability.AuditSelectionSafety
