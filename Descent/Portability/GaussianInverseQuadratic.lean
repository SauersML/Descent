/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RatioSourceDegeneracy
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi

assert_below Descent.Decision Descent.Program

/-!
Gaussian inverse-quadratic integrability from fractional absolute moments.
These results provide the analytic part of the aligned covariance-ratio branch;
coordinate and covariance hypotheses are stated explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianInverseQuadratic

open MeasureTheory ProbabilityTheory GaussianEffectPortabilityLaw Set
open scoped ENNReal NNReal

/-- Absolute fractional moments, including negative exponents above minus one,
remain integrable against a Gaussian density on the whole real line. -/
theorem abs_rpow_exp_integrable (p b : ℝ) (hp : -1 < p) (hb : 0 < b) :
    Integrable (fun x : ℝ ↦ |x| ^ p * Real.exp (-b * x ^ 2)) := by
  have hpos : IntegrableOn (fun x : ℝ ↦ |x| ^ p * Real.exp (-b * x ^ 2)) (Ioi 0) := by
    apply (integrableOn_rpow_mul_exp_neg_mul_sq hb hp).congr_fun _ measurableSet_Ioi
    intro x hx
    simp only [abs_of_pos (show 0 < x from hx)]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iio, neg_zero] using hpos

theorem gaussian_abs_rpow_integrable (p : ℝ) (hp : -1 < p) :
    Integrable (fun x : ℝ ↦ |x| ^ p) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall (fun _ ↦ gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]
  have hi := (abs_rpow_exp_integrable p (1 / 2) hp (by norm_num)).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert hi using 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [show -(x ^ 2) / (2 : ℝ) = -(1 / 2) * x ^ 2 by ring]
  ring

variable {K : Type*} [Fintype K]

/-- Independence yields integrability of all finite products whose individual
coordinate exponents exceed minus one. -/
theorem gaussian_product_rpow_integrable (exponent : K → ℝ)
    (he : ∀ k, -1 < exponent k) :
    Integrable (fun x : K → ℝ ↦ ∏ k, |x k| ^ exponent k) (effectLaw K) := by
  exact Integrable.fintype_prod (fun k ↦ gaussian_abs_rpow_integrable (exponent k) (he k))

/-- Coordinate hyperplanes have zero probability under the product Gaussian. -/
theorem ae_coordinates_nonzero : ∀ᵐ x : K → ℝ ∂effectLaw K, ∀ k, x k ≠ 0 := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  apply ae_all_iff.mpr
  intro k
  rw [ae_iff]
  change Measure.pi (fun _ : K ↦ gaussianReal 0 1) {x | ¬ x k ≠ 0} = 0
  simp only [not_not]
  exact Measure.pi_eval_preimage_null (fun _ : K ↦ gaussianReal 0 1) (measure_singleton 0)

/-- Multiplying by a coordinate square preserves integrability of the
fractional-product majorant: it raises one exponent by two. -/
theorem gaussian_square_product_integrable (exponent : K → ℝ)
    (he : ∀ k, -1 < exponent k) (j : K) :
    Integrable (fun x : K → ℝ ↦ x j ^ 2 * ∏ k, |x k| ^ exponent k) (effectLaw K) := by
  classical
  let shifted := fun k ↦ exponent k + if k = j then (2 : ℝ) else 0
  have hs : ∀ k, -1 < shifted k := by
    intro k
    dsimp [shifted]
    split_ifs <;> linarith [he k]
  apply (gaussian_product_rpow_integrable shifted hs).congr
  filter_upwards [ae_coordinates_nonzero (K := K)] with x hx
  have heq (k : K) : |x k| ^ shifted k =
      |x k| ^ exponent k * (if k = j then x k ^ 2 else 1) := by
    dsimp [shifted]
    by_cases hk : k = j
    · simp only [hk, ite_true, Real.rpow_add (abs_pos.mpr (hx j)), Real.rpow_two, sq_abs]
    · simp only [hk, ite_false, add_zero, mul_one]
  simp_rw [heq]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem gaussian_sumSquares_product_integrable (exponent : K → ℝ)
    (he : ∀ k, -1 < exponent k) :
    Integrable (fun x : K → ℝ ↦ (∑ j, x j ^ 2) * ∏ k, |x k| ^ exponent k) (effectLaw K) := by
  simp only [Finset.sum_mul]
  exact integrable_finset_sum _ (fun j _ ↦ gaussian_square_product_integrable exponent he j)

/-- A denominator that dominates a product of coordinate powers below one has
an integrable reciprocal even after multiplication by quadratic-growth data.
The coordinate-hyperplane exceptional set is explicitly removed almost surely. -/
theorem quotient_integrable_of_product_lower (numerator denominator : (K → ℝ) → ℝ)
    (hnum : Measurable numerator) (hden : Measurable denominator)
    (exponent : K → ℝ) (he : ∀ k, exponent k < 1)
    (scale bound : ℝ) (hscale : 0 < scale) (hbound : 0 ≤ bound)
    (hlower : ∀ x, scale * (∏ k, |x k| ^ exponent k) ≤ denominator x)
    (hupper : ∀ x, |numerator x| ≤ bound * (1 + ∑ k, x k ^ 2)) :
    Integrable (fun x ↦ numerator x / denominator x) (effectLaw K) := by
  have hnegative : ∀ k, -1 < -exponent k := fun k ↦ by linarith [he k]
  have hi := ((gaussian_product_rpow_integrable (fun k ↦ -exponent k) hnegative).add
    (gaussian_sumSquares_product_integrable (fun k ↦ -exponent k) hnegative)).const_mul
      (bound / scale)
  apply hi.mono' (hnum.div hden).aestronglyMeasurable
  filter_upwards [ae_coordinates_nonzero (K := K)] with x hx
  have hprod : 0 < ∏ k, |x k| ^ exponent k := by
    apply Finset.prod_pos
    intro k _
    exact Real.rpow_pos_of_pos (abs_pos.mpr (hx k)) _
  have hdenPos : 0 < denominator x := (mul_pos hscale hprod).trans_le (hlower x)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenPos]
  calc
    |numerator x| / denominator x ≤ (bound * (1 + ∑ k, x k ^ 2)) / denominator x :=
      div_le_div_of_nonneg_right (hupper x) hdenPos.le
    _ ≤ (bound * (1 + ∑ k, x k ^ 2)) / (scale * ∏ k, |x k| ^ exponent k) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hscale hprod) (hlower x)
    _ = bound / scale * ((∏ k, |x k| ^ (-exponent k)) +
        (∑ j, x j ^ 2) * ∏ k, |x k| ^ (-exponent k)) := by
      simp_rw [Real.rpow_neg (abs_nonneg _)]
      rw [Finset.prod_inv_distrib]
      field_simp

end Descent.Portability.GaussianInverseQuadratic
