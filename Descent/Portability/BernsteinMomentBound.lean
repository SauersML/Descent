/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BernsteinExponentialBound
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

assert_below Descent.Decision Descent.Program

/-!
The variance-sensitive moment-generating-function bound for actual bounded
centered observations. Boundedness supplies integrability and second moments.
Finite independent sums use the proved product identity for their joint MGF;
the exponential control is derived rather than assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BernsteinMomentBound

open MeasureTheory ProbabilityTheory BernsteinExponentialBound
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Bounded observations have the second moments required by Bernstein's variance term. -/
theorem bounded_memLp (X : Ω → ℝ) (M : ℝ) (hm : Measurable X)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ M) : MemLp X 2 μ := by
  apply memLp_of_bounded (a := -M) (b := M) _ hm.aestronglyMeasurable
  filter_upwards [hb] with ω hω
  exact abs_le.mp hω

/-- The exponential is integrable under the actual bounded observation law. -/
theorem exponential_integrable (X : Ω → ℝ) (M t : ℝ) (hm : Measurable X)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ M) (ht : 0 ≤ t) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
  apply (integrable_const (Real.exp (t * M))).mono' (by fun_prop)
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hω) ht)

/-- The exact one-observation Bernstein MGF bound using its actual second moment. -/
theorem centered_mgf_bound (X : Ω → ℝ) (M t : ℝ) (hM : 0 ≤ M)
    (hm : Measurable X) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ M)
    (hmean : (∫ ω, X ω ∂μ) = 0) (ht : 0 ≤ t) (htM : t * M < 3) :
    mgf X μ t ≤ Real.exp (t ^ 2 * (∫ ω, X ω ^ 2 ∂μ) / (2 * (1 - t * M / 3))) := by
  let c := t ^ 2 / (2 * (1 - t * M / 3))
  have h₂ := bounded_memLp X M hm hb
  have h₁ := h₂.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hlin : Integrable (fun ω ↦ 1 + t * X ω) μ :=
    (integrable_const 1).add (h₁.const_mul t)
  have hquad : Integrable (fun ω ↦ c * X ω ^ 2) μ := h₂.integrable_sq.const_mul c
  have hpoint : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤ 1 + t * X ω + c * X ω ^ 2 := by
    filter_upwards [hb] with ω hω
    have hz : |t * X ω| ≤ t * M := by
      rw [abs_mul, abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hω ht
    have hh := exponential_upper (t * X ω) (t * M) ⟨mul_nonneg ht hM, htM⟩ hz
    convert hh using 1
    dsimp [c]
    ring
  calc
    mgf X μ t ≤ ∫ ω, 1 + t * X ω + c * X ω ^ 2 ∂μ :=
      integral_mono_ae (exponential_integrable X M t hm hb ht) (hlin.add hquad) hpoint
    _ = 1 + c * ∫ ω, X ω ^ 2 ∂μ := by
      rw [integral_add hlin hquad, integral_add (integrable_const 1) (h₁.const_mul t),
        integral_const_mul t X, integral_const_mul c (fun ω ↦ X ω ^ 2), hmean]
      simp
    _ ≤ Real.exp (c * ∫ ω, X ω ^ 2 ∂μ) := by
      simpa only [add_comm] using Real.add_one_le_exp (c * ∫ ω, X ω ^ 2 ∂μ)
    _ = _ := by congr 1; dsimp [c]; ring

/-- The actual independent-sum MGF is controlled by the sum of second moments. -/
theorem independent_sum_mgf (X : ι → Ω → ℝ) (s : Finset ι)
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (M t : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0) (ht : 0 ≤ t) (htM : t * M < 3) :
    mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t ≤
      Real.exp (t ^ 2 * (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) / (2 * (1 - t * M / 3))) := by
  have he : (∑ i ∈ s, X i) = (fun ω ↦ ∑ i ∈ s, X i ω) := by funext ω; simp
  rw [← he, hi.mgf_sum hm]
  calc
    (∏ i ∈ s, mgf (X i) μ t) ≤
        ∏ i ∈ s, Real.exp (t ^ 2 * (∫ ω, X i ω ^ 2 ∂μ) / (2 * (1 - t * M / 3))) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg (fun _ ↦ (Real.exp_pos _).le)
      · intro i his
        exact centered_mgf_bound (X i) M t hM (hm i) (hb i his) (hmean i his) ht htM
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum, Finset.sum_div]

/-- A supplied upper bound on the sum of second moments yields the stated MGF envelope. -/
theorem independent_sum_mgf_le (X : ι → Ω → ℝ) (s : Finset ι)
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (M v t : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = 0)
    (hv : (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) (ht : 0 ≤ t) (htM : t * M < 3) :
    mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t ≤
      Real.exp (t ^ 2 * v / (2 * (1 - t * M / 3))) := by
  apply (independent_sum_mgf X s hi hm M t hM hb hmean ht htM).trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (sq_nonneg _))
    (by linarith)

end Descent.Portability.BernsteinMomentBound
