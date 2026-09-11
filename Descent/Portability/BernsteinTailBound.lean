/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BernsteinMomentBound
import Mathlib.MeasureTheory.Measure.Real

assert_below Descent.Decision Descent.Program

/-!
The positive-variance Bernstein tail bound, derived by applying Chernoff to the
actual joint MGF and evaluating an admissible tilt. The stated radius is
sqrt(2 v x) + 2 M x / 3, retaining the manuscript's constants. The zero-variance
case is handled separately by its actual almost-sure degeneracy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BernsteinTailBound

open MeasureTheory ProbabilityTheory BernsteinMomentBound
open scoped BigOperators

/-- The variance-sensitive radius stated in Decision-Directed Portability. -/
noncomputable def radius (M v x : ℝ) : ℝ := Real.sqrt (2 * v * x) + 2 * M * x / 3

/-- The radius is nonnegative on the statistical parameter domain. -/
theorem radius_nonneg (M v x : ℝ) (hM : 0 ≤ M) (hx : 0 ≤ x) : 0 ≤ radius M v x := by
  unfold radius
  positivity

/-- With a positive variance bound and confidence exponent, the radius is strictly positive. -/
theorem radius_pos (M v x : ℝ) (hM : 0 ≤ M) (hv : 0 < v) (hx : 0 < x) :
    0 < radius M v x := by
  unfold radius
  have hs : 0 < Real.sqrt (2 * v * x) := Real.sqrt_pos.mpr (by positivity)
  have hm : 0 ≤ 2 * M * x / 3 := by positivity
  linarith

/-- Substitution of the reported radius satisfies the exact Chernoff quadratic inequality. -/
theorem radius_quadratic (M v x : ℝ) (hM : 0 ≤ M) (hv : 0 ≤ v) (hx : 0 ≤ x) :
    2 * x * (v + M * radius M v x / 3) ≤ radius M v x ^ 2 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * v * x)
  have hn : 0 ≤ M * x * Real.sqrt (2 * v * x) := by positivity
  unfold radius
  nlinarith

/-- Exact value of the chosen exponential tilt, before substituting the confidence radius. -/
theorem tilt_identity (M v a : ℝ) (hv : 0 < v) (hd : 0 < v + M * a / 3) :
    -(a / (v + M * a / 3)) * a +
      (a / (v + M * a / 3)) ^ 2 * v /
        (2 * (1 - (a / (v + M * a / 3)) * M / 3)) =
      -a ^ 2 / (2 * (v + M * a / 3)) := by
  have he : 1 - (a / (v + M * a / 3)) * M / 3 = v / (v + M * a / 3) := by
    field_simp [hd.ne']
    ring
  rw [he]
  field_simp [hv.ne', hd.ne']
  ring

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The one-sided Bernstein bound under the actual independent observation law. -/
theorem one_sided (X : ι → Ω → ℝ) (s : Finset ι)
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (M v x : ℝ)
    (hM : 0 ≤ M) (hvpos : 0 < v) (hx : 0 < x)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0)
    (hv : (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    μ.real {ω | radius M v x ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-x) := by
  let a := radius M v x
  let d := v + M * a / 3
  let t := a / d
  have ha : 0 < a := radius_pos M v x hM hvpos hx
  have hd : 0 < d := by dsimp [d]; positivity
  have ht : 0 ≤ t := (div_pos ha hd).le
  have htM : t * M < 3 := by
    change a / d * M < 3
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    dsimp [d]
    nlinarith
  have hint : Integrable (fun ω ↦ Real.exp (t * ∑ i ∈ s, X i ω)) μ := by
    have hh := hi.integrable_exp_mul_sum hm
      (fun i his ↦ exponential_integrable (X i) M t (hm i) (hb i his) ht)
    simpa only [Finset.sum_apply] using hh
  have hc := measure_ge_le_exp_mul_mgf (X := fun ω ↦ ∑ i ∈ s, X i ω) a ht hint
  have hmgf := independent_sum_mgf_le X s hi hm M v t hM hb hmean hv ht htM
  calc
    μ.real {ω | a ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-t * a) *
        Real.exp (t ^ 2 * v / (2 * (1 - t * M / 3))) :=
      hc.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le)
    _ = Real.exp (-a ^ 2 / (2 * d)) := by
      rw [← Real.exp_add]
      congr 1
      exact tilt_identity M v a hvpos hd
    _ ≤ Real.exp (-x) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ (by positivity : 0 < 2 * d)]
      have hh := radius_quadratic M v x hM hvpos.le hx.le
      change 2 * x * d ≤ a ^ 2 at hh
      nlinarith

/-- Negating the actual observations supplies the other tail; the union gives the factor two. -/
theorem two_sided_positive (X : ι → Ω → ℝ) (s : Finset ι)
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (M v x : ℝ)
    (hM : 0 ≤ M) (hvpos : 0 < v) (hx : 0 < x)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0)
    (hv : (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    μ.real {ω | radius M v x < |∑ i ∈ s, X i ω|} ≤ 2 * Real.exp (-x) := by
  have hpos := one_sided X s hi hm M v x hM hvpos hx hb hmean hv
  have hni : iIndepFun (fun i ω ↦ -X i ω) μ :=
    hi.comp (fun _ y ↦ -y) (fun _ ↦ measurable_neg)
  have hnb (i : ι) (his : i ∈ s) : ∀ᵐ ω ∂μ, |-X i ω| ≤ M := by
    simpa only [abs_neg] using hb i his
  have hnm (i : ι) (his : i ∈ s) : (∫ ω, -X i ω ∂μ) = 0 := by
    rw [integral_neg, hmean i his, neg_zero]
  have hnv : (∑ i ∈ s, ∫ ω, (-X i ω) ^ 2 ∂μ) ≤ v := by
    simpa only [neg_sq] using hv
  have hneg := one_sided (fun i ω ↦ -X i ω) s hni (fun i ↦ (hm i).neg)
    M v x hM hvpos hx hnb hnm hnv
  simp only [Finset.sum_neg_distrib] at hneg
  have he : {ω | radius M v x < |∑ i ∈ s, X i ω|} ⊆
      {ω | radius M v x ≤ ∑ i ∈ s, X i ω} ∪
        {ω | radius M v x ≤ -(∑ i ∈ s, X i ω)} := by
    intro ω hω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  have hh := (measureReal_mono he).trans (measureReal_union_le (μ := μ) _ _)
  linarith

end Descent.Portability.BernsteinTailBound
