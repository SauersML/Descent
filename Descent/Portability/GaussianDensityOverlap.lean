/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianProductDensity

assert_below Descent.Decision Descent.Program

/-!
Exact second-order overlap integrals for the actual Gaussian density ratios.
Multiplying two ratios gives a scalar times another normalized Gaussian ratio.
This proves integrability and the overlap value, rather than assuming a
square-integrable density expansion in the order-erasure experiment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianDensityOverlap

open MeasureTheory ProbabilityTheory GaussianVarianceDensity GaussianProductDensity
open scoped BigOperators

/-- Precision of the Gaussian obtained after multiplying two variance ratios. -/
noncomputable def precision (a b : ℝ) : ℝ := a⁻¹ + b⁻¹ - 1

/-- The exact overlap coefficient of the two normalized Gaussian density ratios. -/
noncomputable def overlap (a b : ℝ) : ℝ :=
  Real.sqrt ((precision a b)⁻¹) / (Real.sqrt a * Real.sqrt b)

/-- Positive overlap precision gives a positive normalizing coefficient. -/
theorem overlap_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < precision a b) :
    0 < overlap a b := by
  exact div_pos (Real.sqrt_pos.mpr (inv_pos.mpr ht))
    (mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb))

/-- The product of actual density ratios is another Gaussian ratio times its overlap. -/
theorem ratio_mul (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < precision a b) :
    ratio a x * ratio b x = overlap a b * ratio (precision a b)⁻¹ x := by
  have he : (1 - a⁻¹) * x ^ 2 / 2 + (1 - b⁻¹) * x ^ 2 / 2 =
      (1 - ((precision a b)⁻¹)⁻¹) * x ^ 2 / 2 := by
    simp only [inv_inv, precision]
    ring
  have hv : Real.sqrt ((precision a b)⁻¹) ≠ 0 :=
    (Real.sqrt_pos.mpr (inv_pos.mpr ht)).ne'
  have hsa := (Real.sqrt_pos.mpr ha).ne'
  have hsb := (Real.sqrt_pos.mpr hb).ne'
  unfold ratio overlap
  rw [show (Real.sqrt a)⁻¹ * Real.exp ((1 - a⁻¹) * x ^ 2 / 2) *
      ((Real.sqrt b)⁻¹ * Real.exp ((1 - b⁻¹) * x ^ 2 / 2)) =
      ((Real.sqrt a)⁻¹ * (Real.sqrt b)⁻¹) *
        Real.exp ((1 - a⁻¹) * x ^ 2 / 2 + (1 - b⁻¹) * x ^ 2 / 2) by
          rw [Real.exp_add]
          ring, he]
  field_simp [hv, hsa, hsb]

/-- The overlap is an actual integrable product under the reference Gaussian law. -/
theorem ratio_mul_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < precision a b) :
    Integrable (fun x ↦ ratio a x * ratio b x) (gaussianReal 0 1) := by
  simp_rw [ratio_mul a b _ ha hb ht]
  exact (ratio_integrable _ (inv_pos.mpr ht)).const_mul _

/-- Exact integration of the product of two actual Gaussian density ratios. -/
theorem ratio_mul_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < precision a b) :
    (∫ x, ratio a x * ratio b x ∂gaussianReal 0 1) = overlap a b := by
  simp_rw [ratio_mul a b _ ha hb ht]
  rw [integral_const_mul, ratio_integral _ (inv_pos.mpr ht), mul_one]

/-- Variances below two satisfy the exact positive-precision condition for a squared ratio. -/
theorem square_precision_pos (a : ℝ) (ha : 0 < a) (ha₂ : a < 2) :
    0 < precision a a := by
  have hi : 1 / 2 < a⁻¹ := by
    rw [inv_eq_one_div]
    exact one_div_lt_one_div_of_lt ha ha₂
  unfold precision
  linarith

/-- The actual Gaussian variance ratio has a finite squared integral below variance two. -/
theorem ratio_sq_integrable (a : ℝ) (ha : 0 < a) (ha₂ : a < 2) :
    Integrable (fun x ↦ ratio a x ^ 2) (gaussianReal 0 1) := by
  simpa only [pow_two] using ratio_mul_integrable a a ha ha (square_precision_pos a ha ha₂)

/-- The squared integral has the same exact overlap value, with no numerical approximation. -/
theorem ratio_sq_integral (a : ℝ) (ha : 0 < a) (ha₂ : a < 2) :
    (∫ x, ratio a x ^ 2 ∂gaussianReal 0 1) = overlap a a := by
  simpa only [pow_two] using ratio_mul_integral a a ha ha (square_precision_pos a ha ha₂)

variable {ι : Type*} [Fintype ι]

/-- Finite-product Gaussian overlaps are integrable under the actual product reference law. -/
theorem product_overlap_integrable (a b : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (ht : ∀ i, 0 < precision (a i) (b i)) :
    Integrable (fun x ↦ productRatio a x * productRatio b x)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) := by
  simp only [productRatio, ← Finset.prod_mul_distrib]
  exact Integrable.fintype_prod (fun i ↦ ratio_mul_integrable _ _ (ha i) (hb i) (ht i))

/-- The full overlap integral factors into the derived scalar Gaussian overlap values. -/
theorem product_overlap_integral (a b : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (ht : ∀ i, 0 < precision (a i) (b i)) :
    (∫ x, productRatio a x * productRatio b x
      ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) = ∏ i, overlap (a i) (b i) := by
  simp only [productRatio, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun i x ↦ ratio (a i) x * ratio (b i) x)]
  exact Finset.prod_congr rfl (fun i _ ↦ ratio_mul_integral _ _ (ha i) (hb i) (ht i))

/-- Any two positive variances below two have an integrable overlap. -/
theorem precision_pos_of_lt_two (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ha₂ : a < 2) (hb₂ : b < 2) : 0 < precision a b := by
  have h₁ := square_precision_pos a ha ha₂
  have h₂ := square_precision_pos b hb hb₂
  unfold precision at *
  linarith

/-- Exact squared distance between product density ratios under the reference Gaussian law. -/
theorem product_distance_sq (a b : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (ha₂ : ∀ i, a i < 2) (hb₂ : ∀ i, b i < 2) :
    (∫ x, (productRatio a x - productRatio b x) ^ 2
      ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) =
      (∏ i, overlap (a i) (a i)) + (∏ i, overlap (b i) (b i)) -
        2 * ∏ i, overlap (a i) (b i) := by
  have haa (i : ι) := square_precision_pos (a i) (ha i) (ha₂ i)
  have hbb (i : ι) := square_precision_pos (b i) (hb i) (hb₂ i)
  have hab (i : ι) := precision_pos_of_lt_two (a i) (b i) (ha i) (hb i) (ha₂ i) (hb₂ i)
  have hi₁ := product_overlap_integrable a a ha ha haa
  have hi₂ := product_overlap_integrable b b hb hb hbb
  have hi₃ := product_overlap_integrable a b ha hb hab
  calc
    _ = ∫ x, productRatio a x * productRatio a x + productRatio b x * productRatio b x -
        2 * (productRatio a x * productRatio b x)
        ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ ↦ by ring)
    _ = _ := by
      have hsub := integral_sub (hi₁.add hi₂) (hi₃.const_mul 2)
      simp only [Pi.add_apply] at hsub
      rw [hsub, integral_add hi₁ hi₂,
        integral_const_mul, product_overlap_integral a a ha ha haa,
        product_overlap_integral b b hb hb hbb, product_overlap_integral a b ha hb hab]

end Descent.Portability.GaussianDensityOverlap
