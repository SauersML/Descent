/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompoundPoissonMoments
import Descent.Portability.BoundedConvolutionMoments
import Descent.Portability.GaussianHermiteLaw

assert_below Descent.Decision Descent.Program

/-!
Actual moments of an independent Gaussian plus centered compound-Poisson sum.
Both the infinite mixture and the convolution have proved absolute integrability.
The fourth cumulant is evaluated using the full probability law's integrals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianCompoundMoments

open scoped BigOperators NNReal MeasureTheory
open MeasureTheory ProbabilityTheory CompoundPoissonMarkLaw CompoundPoissonMoments
open CompoundPoissonIntegrability BoundedConvolutionMoments GaussianPolynomialMoments

/-- Finite absolute moments through order four for the independent Gaussian-plus-jump law. -/
theorem gaussian_compound_power_integrable (v r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (n : ℕ) (hn : n ≤ 4) :
    Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 v ∗ compoundMeasure r μ) :=
  convolution_power_integrable ⟨gaussianReal 0 v, inferInstance⟩
    (compoundProbability r μ) n (fun k _ ↦ GaussianHermiteLaw.integrable_power v k)
    (fun k hk ↦ compound_power_integrable r μ hμ hm k (hk.trans hn))

/-- General binomial moment identity, with the required integrability derived from the marks. -/
theorem gaussian_compound_power_integral (v r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (n : ℕ) (hn : n ≤ 4) :
    (∫ x : ℝ, x ^ n ∂(gaussianReal 0 v ∗ compoundMeasure r μ)) =
      ∑ k ∈ Finset.range (n + 1), (∫ x : ℝ, x ^ k ∂gaussianReal 0 v) *
        (∫ x : ℝ, x ^ (n - k) ∂compoundMeasure r μ) * (n.choose k : ℝ) :=
  convolution_power_integral ⟨gaussianReal 0 v, inferInstance⟩
    (compoundProbability r μ) n (fun k _ ↦ GaussianHermiteLaw.integrable_power v k)
    (fun k hk ↦ compound_power_integrable r μ hμ hm k (hk.trans hn))

/-- The complete Gaussian-plus-jump law is centered. -/
theorem gaussian_compound_mean (v r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    (∫ x : ℝ, x ∂(gaussianReal 0 v ∗ compoundMeasure r μ)) = 0 := by
  simpa [Finset.sum_range_succ, compound_mean r μ hμ hm] using
    gaussian_compound_power_integral v r μ hμ hm 1 (by norm_num)

/-- Variance contributions add under the actual independent convolution. -/
theorem gaussian_compound_second (v r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v ∗ compoundMeasure r μ)) =
      (v : ℝ) + (r : ℝ) * (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) := by
  have hh := gaussian_compound_power_integral v r μ hμ hm 2 (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.choose, compound_mean r μ hμ hm,
    compound_second r μ hμ hm, second_moment] at hh
  rw [hh]
  ring

/-- The fourth moment includes the Gaussian-pair and cross-pair contributions. -/
theorem gaussian_compound_fourth (v r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v ∗ compoundMeasure r μ)) =
      3 * ((v : ℝ) + (r : ℝ) * (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ))) ^ 2 +
        (r : ℝ) * (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) := by
  have hh := gaussian_compound_power_integral v r μ hμ hm 4 (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.choose, compound_mean r μ hμ hm,
    compound_second r μ hμ hm, compound_fourth r μ hμ hm,
    second_moment, fourth_moment] at hh
  rw [hh]
  ring

/-- Gaussian noise contributes zero to the full distribution's fourth cumulant. -/
theorem gaussian_compound_fourth_cumulant (v r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v ∗ compoundMeasure r μ)) -
      3 * (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v ∗ compoundMeasure r μ)) ^ 2 =
        (r : ℝ) * (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) := by
  rw [gaussian_compound_fourth v r μ hμ hm, gaussian_compound_second v r μ hμ hm]
  ring

end Descent.Portability.GaussianCompoundMoments
