/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BernsteinTailBound

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Lemma 8 in full, including zero variance.
When the sum of actual second moments is zero, every observation is zero
almost surely; no division by a vanishing variance is used. Otherwise the
proved MGF and Chernoff calculation give the stated two-sided radius.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BernsteinConfidence

open MeasureTheory ProbabilityTheory BernsteinMomentBound BernsteinTailBound
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Zero total second moment forces every term, hence the whole sum, to vanish almost surely. -/
theorem zero_second_moment_sum (X : ι → Ω → ℝ) (s : Finset ι)
    (hm : ∀ i, Measurable (X i)) (M : ℝ)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hv : (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) ≤ 0) :
    ∀ᵐ ω ∂μ, (∑ i ∈ s, X i ω) = 0 := by
  have hz (i : ι) (his : i ∈ s) : ∀ᵐ ω ∂μ, X i ω = 0 := by
    have he : (∫ ω, X i ω ^ 2 ∂μ) = 0 := by
      apply le_antisymm
      · exact (Finset.single_le_sum (fun j _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) his).trans hv
      · exact integral_nonneg (fun _ ↦ sq_nonneg _)
    have hsq := (integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg (X i ω))
      (bounded_memLp (X i) M (hm i) (hb i his)).integrable_sq).mp he
    filter_upwards [hsq] with ω hω
    exact sq_eq_zero_iff.mp hω
  filter_upwards [(Filter.eventually_all_finset s).mpr hz] with ω hω
  exact Finset.sum_eq_zero hω

/-- The exact finite-sample Bernstein inequality, with its actual variance-zero case included. -/
theorem bernstein (X : ι → Ω → ℝ) (s : Finset ι)
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (M v x : ℝ)
    (hM : 0 ≤ M) (hx : 0 < x)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0)
    (hv : (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    μ.real {ω | radius M v x < |∑ i ∈ s, X i ω|} ≤ 2 * Real.exp (-x) := by
  have hv₀ : 0 ≤ v :=
    (Finset.sum_nonneg (fun i _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))).trans hv
  rcases eq_or_lt_of_le hv₀ with hvzero | hvpos
  · subst v
    have hz := zero_second_moment_sum X s hm M hb hv
    have he : {ω | radius M 0 x < |∑ i ∈ s, X i ω|} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hz] with ω hω
      apply propext
      change (radius M 0 x < |∑ i ∈ s, X i ω|) ↔ False
      rw [hω, abs_zero]
      exact iff_false_intro (not_lt.mpr (radius_nonneg M 0 x hM hx.le))
    rw [measureReal_congr he, measureReal_empty]
    positivity
  · exact two_sided_positive X s hi hm M v x hM hvpos hx hb hmean hv

end Descent.Portability.BernsteinConfidence
