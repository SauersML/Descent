/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ConvolutionPolynomialMoments

assert_below Descent.Decision Descent.Program

/-!
Moments through a specified finite order of the actual convolution of two probability
measures are the binomial sums of their moments. Integrability of the convolution powers is
proved from integrability of the factor powers on the product experiment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BoundedConvolutionMoments

open scoped BigOperators MeasureTheory
open MeasureTheory

/-- Every term of the binomial expansion is integrable on the independent product law. -/
theorem add_power_integrable (μ ν : ProbabilityMeasure ℝ) (n : ℕ)
    (hμ : ∀ k : ℕ, k ≤ n → Integrable (fun x : ℝ ↦ x ^ k) (μ : Measure ℝ))
    (hν : ∀ k : ℕ, k ≤ n → Integrable (fun x : ℝ ↦ x ^ k) (ν : Measure ℝ)) :
    Integrable (fun z : ℝ × ℝ ↦ (z.1 + z.2) ^ n)
      ((μ : Measure ℝ).prod (ν : Measure ℝ)) := by
  simp_rw [add_pow]
  apply integrable_finset_sum
  intro k hk
  exact ((hμ k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).mul_prod
    (hν (n - k) (Nat.sub_le _ _))).mul_const (n.choose k : ℝ)

/-- Actual convolution powers are integrable, rather than merely formal moments. -/
theorem convolution_power_integrable (μ ν : ProbabilityMeasure ℝ) (n : ℕ)
    (hμ : ∀ k : ℕ, k ≤ n → Integrable (fun x : ℝ ↦ x ^ k) (μ : Measure ℝ))
    (hν : ∀ k : ℕ, k ≤ n → Integrable (fun x : ℝ ↦ x ^ k) (ν : Measure ℝ)) :
    Integrable (fun x : ℝ ↦ x ^ n) ((μ : Measure ℝ) ∗ (ν : Measure ℝ)) := by
  rw [Measure.conv]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  exact add_power_integrable μ ν n hμ hν

/-- Exact binomial moment law for an actual independent sum. -/
theorem convolution_power_integral (μ ν : ProbabilityMeasure ℝ) (n : ℕ)
    (hμ : ∀ k : ℕ, k ≤ n → Integrable (fun x : ℝ ↦ x ^ k) (μ : Measure ℝ))
    (hν : ∀ k : ℕ, k ≤ n → Integrable (fun x : ℝ ↦ x ^ k) (ν : Measure ℝ)) :
    (∫ x : ℝ, x ^ n ∂((μ : Measure ℝ) ∗ (ν : Measure ℝ))) =
      ∑ k ∈ Finset.range (n + 1),
        (∫ x : ℝ, x ^ k ∂(μ : Measure ℝ)) *
        (∫ x : ℝ, x ^ (n - k) ∂(ν : Measure ℝ)) * (n.choose k : ℝ) := by
  rw [Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [add_pow]
  rw [integral_finset_sum _ (fun k hk ↦
    ((hμ k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).mul_prod
      (hν (n - k) (Nat.sub_le _ _))).mul_const (n.choose k : ℝ))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_mul_const, integral_prod_mul (fun x : ℝ ↦ x ^ k)
    (fun x : ℝ ↦ x ^ (n - k))]

end Descent.Portability.BoundedConvolutionMoments
