/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BernsteinConfidence

assert_below Descent.Decision Descent.Program

/-!
The one-sided Bernstein bound used by Decision-Directed Portability's
hard-budget guard. Strict exceedance is retained so the zero-variance case
has probability zero even when the bound itself is zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BernsteinUpperConfidence

open MeasureTheory ProbabilityTheory BernsteinTailBound BernsteinConfidence
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One-sided Bernstein with no positive-variance assumption or zero-threshold pathology. -/
theorem bernstein_upper (X : ι → Ω → ℝ) (s : Finset ι)
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (M v x : ℝ)
    (hM : 0 ≤ M) (hx : 0 < x)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0)
    (hv : (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    μ.real {ω | radius M v x < ∑ i ∈ s, X i ω} ≤ Real.exp (-x) := by
  have hv₀ : 0 ≤ v :=
    (Finset.sum_nonneg (fun i _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))).trans hv
  rcases eq_or_lt_of_le hv₀ with hvzero | hvpos
  · subst v
    have hz := zero_second_moment_sum X s hm M hb hv
    have he : {ω | radius M 0 x < ∑ i ∈ s, X i ω} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hz] with ω hω
      apply propext
      change (radius M 0 x < ∑ i ∈ s, X i ω) ↔ False
      rw [hω]
      exact iff_false_intro (not_lt.mpr (radius_nonneg M 0 x hM hx.le))
    rw [measureReal_congr he, measureReal_empty]
    exact (Real.exp_pos _).le
  · apply le_trans (measureReal_mono (show {ω | radius M v x < ∑ i ∈ s, X i ω} ⊆
      {ω | radius M v x ≤ ∑ i ∈ s, X i ω} from fun _ h ↦ h.le))
      (one_sided X s hi hm M v x hM hvpos hx hb hmean hv)

end Descent.Portability.BernsteinUpperConfidence
