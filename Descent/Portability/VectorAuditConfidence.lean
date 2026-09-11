/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteNetConfidence

assert_below Descent.Decision Descent.Program

/-!
The actual vector-valued target audit in Decision-Directed Portability,
Theorem 10. Coefficient vectors include frame normalization and whitening.
Scalar audit tails imply a confidence ball uniformly over the entire fixed
repair span; the direction is not selected using an uncorrected scalar bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.VectorAuditConfidence

open MeasureTheory SharedAuditCompletion IndependentContrastLaw FiniteAuditConfidence
open BernsteinTailBound
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual vector estimation error under the augmented audit law. -/
noncomputable def error (μ : ι → Measure ℝ) (u : ι → E) (z : ι → ℝ) : E :=
  ∑ i, (z i - ∫ y, y ∂μ i) • u i

/-- Every directional error is the corresponding scalar contrast error. -/
theorem directional_error (μ : ι → Measure ℝ) (u : ι → E) (z : ι → ℝ) (a : E) :
    inner ℝ a (error μ u z) =
      contrast (fun i ↦ inner ℝ a (u i)) z - ∑ i, inner ℝ a (u i) * ∫ y, y ∂μ i := by
  simp only [error, inner_sum, inner_smul_right, contrast, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Enlarging a variance envelope enlarges the stated Bernstein radius. -/
theorem radius_mono_variance (M v₁ v₂ x : ℝ) (hx : 0 ≤ x) (hv : v₁ ≤ v₂) :
    radius M v₁ x ≤ radius M v₂ x := by
  unfold radius
  apply add_le_add_right
  apply Real.sqrt_le_sqrt
  nlinarith

/-- A unit-ball direction has no more range than the norm-based row contribution. -/
theorem directional_range (a u : E) (ha : ‖a‖ ≤ 1) (L U p : ℝ)
    (hLU : L ≤ U) (hp : 0 < p) :
    |inner ℝ a u| * (U - L) / p ≤ ‖u‖ * (U - L) / p := by
  have hh : |inner ℝ a u| ≤ ‖u‖ := by
    calc
      |inner ℝ a u| ≤ ‖a‖ * ‖u‖ := by simpa only [Real.norm_eq_abs] using norm_inner_le_norm a u
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg u)
      _ = ‖u‖ := one_mul _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hLU)) hp.le

/-- Actual audit confidence, given a bound on its explicitly computed directional covariance. -/
theorem vector_confidence (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p q lo hi : ι → ℝ) (u : ι → E) (M v δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i)
    (hM : 0 ≤ M) (hcap : ∀ i, ‖u i‖ * (U i - L i) / p i ≤ M)
    (hv : ∀ a : E, ‖a‖ ≤ 1 → varianceBound L U p q lo hi
      (fun i ↦ inner ℝ a (u i)) ≤ v) :
    (frameLaw μ p q).real {z | 2 * radius M v
      (Real.log (2 * (5 ^ Module.finrank ℝ E : ℕ) / δ)) < ‖error μ u z‖} ≤ δ := by
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  let x := Real.log (2 * (5 ^ Module.finrank ℝ E : ℕ) / δ)
  have hx : 0 < x := confidence_exponent_pos _ (by positivity) δ hδ
  apply FiniteNetConfidence.norm_confidence (frameLaw μ p q) (error μ u)
    (radius M v x) δ (radius_nonneg M v x hM hx.le) hδ.1
  intro a ha
  have ht := contrast_tail μ L U p q lo hi (fun i ↦ inner ℝ a (u i)) M x hp hq hs hband hM
    (fun i ↦ (directional_range a (u i) ha (L i) (U i) (p i)
      ((hq i).1.trans (hq i).2) (hp i).1).trans (hcap i)) hx
  have hr := radius_mono_variance M _ v x hx.le (hv a ha)
  apply le_trans (measureReal_mono (show {z | radius M v x < |inner ℝ a (error μ u z)|} ⊆
    {z | radius M (varianceBound L U p q lo hi (fun i ↦ inner ℝ a (u i))) x <
      |contrast (fun i ↦ inner ℝ a (u i)) z - ∑ i, inner ℝ a (u i) * ∫ y, y ∂μ i|} from ?_)) ht
  intro z hz
  rw [directional_error] at hz
  exact lt_of_le_of_lt hr hz

end Descent.Portability.VectorAuditConfidence
