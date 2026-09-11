/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompoundPoissonIntegrability

assert_below Descent.Decision Descent.Program

/-!
The mean, variance, and fourth cumulant of a centered compound-Poisson law are
computed from its actual count mixture. Absolute integrability justifies exchanging
the infinite mixture and each integral. No moment identity is supplied as input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompoundPoissonMoments

open scoped BigOperators NNReal MeasureTheory
open MeasureTheory ProbabilityTheory CompoundPoissonMarkLaw MarkSumMoments
open PoissonMomentSeries CompoundPoissonIntegrability

/-- An actual Poisson sum of centered independent marks is centered. -/
theorem compound_mean (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    (∫ x : ℝ, x ∂compoundMeasure r μ) = 0 := by
  have hi : Integrable (fun x : ℝ ↦ x) (compoundMeasure r μ) := by
    simpa only [pow_one] using compound_power_integrable r μ hμ hm 1 (by norm_num)
  rw [compoundMeasure, integral_sum_measure hi]
  simp only [integral_smul_measure, markSum_mean μ hμ hm, smul_zero, tsum_zero]

/-- The compound second moment is intensity times the actual mark second moment. -/
theorem compound_second (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    (∫ x : ℝ, x ^ 2 ∂compoundMeasure r μ) =
      (r : ℝ) * (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) := by
  have hi := compound_power_integrable r μ hμ hm 2 (by norm_num)
  rw [compoundMeasure, integral_sum_measure hi]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal poissonPMFReal_nonneg,
    smul_eq_mul, markSum_second μ hμ hm, ← mul_assoc]
  exact ((poisson_first r).mul_right (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ))).tsum_eq

/-- All diagonal and paired contributions to the compound fourth moment. -/
theorem compound_fourth (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    (∫ x : ℝ, x ^ 4 ∂compoundMeasure r μ) =
      (r : ℝ) * (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) +
        3 * (r : ℝ) ^ 2 * (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) ^ 2 := by
  have hi := compound_fourth_integrable r μ hμ hm
  rw [compoundMeasure, integral_sum_measure hi]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal poissonPMFReal_nonneg,
    smul_eq_mul, markSum_fourth μ hμ hm]
  convert (poisson_quadratic r (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ))
    (3 * (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) ^ 2)).tsum_eq using 1
  · congr 1
    funext k
    ring
  · ring

/-- The fourth cumulant is proved from the full law's second and fourth integrals. -/
theorem compound_fourth_cumulant (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    (∫ x : ℝ, x ^ 4 ∂compoundMeasure r μ) -
      3 * (∫ x : ℝ, x ^ 2 ∂compoundMeasure r μ) ^ 2 =
        (r : ℝ) * (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) := by
  rw [compound_fourth r μ hμ hm, compound_second r μ hμ hm]
  ring

end Descent.Portability.CompoundPoissonMoments
