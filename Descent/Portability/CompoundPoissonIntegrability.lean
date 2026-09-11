/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarkSumMoments
import Descent.Portability.PoissonMomentSeries

assert_below Descent.Decision Descent.Program

/-!
Fourth-moment integrability for the actual infinite Poisson mixture is obtained
from a convergent series of absolute integrals. Lower powers are dominated by
one plus the fourth power. Thus subsequent moment calculations concern finite
Lebesgue integrals, not formal sums or the default value of a divergent integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompoundPoissonIntegrability

open scoped BigOperators NNReal MeasureTheory
open MeasureTheory ProbabilityTheory CompoundPoissonMarkLaw MarkSumMoments PoissonMomentSeries

/-- A summable family of absolute integrals proves integrability on a countable measure sum. -/
theorem integrable_measure_sum (μ : ℕ → Measure ℝ) (f : ℝ → ℝ)
    (hf : StronglyMeasurable f) (hi : ∀ k, Integrable f (μ k))
    (hs : Summable (fun k ↦ ∫ x, ‖f x‖ ∂μ k)) : Integrable f (Measure.sum μ) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_sum_measure]
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ integral_nonneg (fun x ↦ norm_nonneg _)) hs]
  exact ENNReal.ofReal_lt_top

/-- A finite fourth moment controls all powers required for mean, variance, and kurtosis. -/
theorem power_integrable_of_fourth (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x ^ 4) μ) (n : ℕ) (hn : n ≤ 4) :
    Integrable (fun x : ℝ ↦ x ^ n) μ := by
  apply ((integrable_const (1 : ℝ)).add hi).mono' (by fun_prop)
  filter_upwards with x
  simp only [Real.norm_eq_abs, abs_pow]
  have hx : |x| ^ 4 = x ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 4)]
  by_cases hh : |x| ≤ 1
  · have hpow : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg x) hh
    have h4 : 0 ≤ x ^ 4 := by positivity
    dsimp
    linarith
  · have hpow : |x| ^ n ≤ |x| ^ 4 := pow_le_pow_right₀ (le_of_not_ge hh) hn
    dsimp
    rw [hx] at hpow
    linarith

/-- Fourth powers are integrable for the constructed Poisson mixture of centered marks. -/
theorem compound_fourth_integrable (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    Integrable (fun x : ℝ ↦ x ^ 4) (compoundMeasure r μ) := by
  apply integrable_measure_sum _ _ (continuous_id.pow 4).stronglyMeasurable
  · intro k
    exact (markSum_power_integrable μ hμ k 4).smul_measure ENNReal.ofReal_ne_top
  · have hn (x : ℝ) : ‖x ^ 4‖ = x ^ 4 := Real.norm_of_nonneg (by positivity)
    simp only [id_eq, hn, integral_smul_measure, ENNReal.toReal_ofReal poissonPMFReal_nonneg,
      smul_eq_mul, markSum_fourth μ hμ hm]
    convert (poisson_quadratic r (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ))
      (3 * (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) ^ 2)).summable using 1
    funext k
    ring

/-- All powers through four of the actual compound law have finite absolute integrals. -/
theorem compound_power_integrable (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (n : ℕ) (hn : n ≤ 4) :
    Integrable (fun x : ℝ ↦ x ^ n) (compoundMeasure r μ) :=
  power_integrable_of_fourth _ (compound_fourth_integrable r μ hμ hm) n hn

end Descent.Portability.CompoundPoissonIntegrability
