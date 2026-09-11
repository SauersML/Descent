/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianVarianceDensity
import Mathlib.MeasureTheory.Integral.Pi

assert_below Descent.Decision Descent.Program

/-!
Finite products of the explicit variance ratios give the actual independent
Gaussian experiment with the specified coordinate variances. Normalization and
the full measure identity are proved, including equality on arbitrary measurable
rectangles. This is the diagonal-coordinate input to covariance perturbations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianProductDensity

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory GaussianVarianceDensity DensityRelativeEntropy

variable {ι : Type*} [Fintype ι]

/-- The concrete density ratio of a finite independent Gaussian variance experiment. -/
noncomputable def productRatio (a : ι → ℝ) (x : ι → ℝ) : ℝ := ∏ i, ratio (a i) (x i)

/-- The product ratio is positive at every data vector. -/
theorem productRatio_pos (a : ι → ℝ) (ha : ∀ i, 0 < a i) (x : ι → ℝ) :
    0 < productRatio a x := by
  exact Finset.prod_pos (fun i _ ↦ ratio_pos _ _ (ha i))

/-- Continuity of the actual finite-product density. -/
theorem productRatio_continuous (a : ι → ℝ) : Continuous (productRatio a) := by
  unfold productRatio
  exact continuous_finset_prod _ (fun i _ ↦ (ratio_continuous (a i)).comp (continuous_apply i))

/-- Integrability follows from the actual independent Gaussian coordinate laws. -/
theorem productRatio_integrable (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Integrable (productRatio a) (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) :=
  Integrable.fintype_prod (fun i ↦ ratio_integrable (a i) (ha i))

/-- Normalization of the full density follows from exact coordinate normalization. -/
theorem productRatio_integral (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x, productRatio a x ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) = 1 := by
  unfold productRatio
  rw [integral_fintype_prod_eq_prod]
  simp only [ratio_integral _ (ha _), Finset.prod_const_one]

/-- The real set integral of a coordinate ratio is the actual Gaussian event probability. -/
theorem coordinate_set_integral (a : ℝ) (ha : 0 < a) (s : Set ℝ) (hs : MeasurableSet s) :
    ENNReal.ofReal (∫ x in s, ratio a x ∂gaussianReal 0 1) = gaussianReal 0 ⟨a, ha.le⟩ s := by
  rw [← densityLaw_eq_gaussian a ha, densityLaw, withDensity_apply _ hs]
  exact ofReal_integral_eq_lintegral_ofReal (ratio_integrable a ha).restrict
    (Filter.Eventually.of_forall (fun x ↦ (ratio_pos a x ha).le))

/-- The complete density construction equals the actual product Gaussian probability measure. -/
theorem densityLaw_eq_productGaussian (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    densityLaw (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) (productRatio a) =
      Measure.pi (fun i ↦ gaussianReal 0 ⟨a i, (ha i).le⟩) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [densityLaw, withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (productRatio_integrable a ha).restrict
      (Filter.Eventually.of_forall (fun x ↦ (productRatio_pos a ha x).le)),
    Measure.restrict_pi_pi]
  change ENNReal.ofReal (∫ x, ∏ i, ratio (a i) (x i)
    ∂Measure.pi (fun i ↦ (gaussianReal 0 1).restrict (s i))) = _
  rw [integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ integral_nonneg
      (fun x ↦ (ratio_pos (a i) x (ha i)).le))]
  apply Finset.prod_congr rfl
  intro i _
  exact coordinate_set_integral (a i) (ha i) (s i) (hs i)

end Descent.Portability.GaussianProductDensity
