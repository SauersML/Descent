/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ConvolutionPolynomialMoments

assert_below Descent.Decision Descent.Program

/-!
The actual k-fold independent sum of centered marks has mean zero, second moment
k m2, and fourth moment k m4 + 3 k(k-1) m2^2. Integrability is proved for every
power before the convolution moment identities are applied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MarkSumMoments

open scoped BigOperators MeasureTheory
open MeasureTheory CompoundPoissonMarkLaw ConvolutionPolynomialMoments

/-- Integer moments of every finite convolution law are integrable. -/
theorem markSum_power_integrable (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ)) (k n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (markSum μ k) := by
  induction k generalizing n with
  | zero => exact integrable_dirac (by simp)
  | succ k ih =>
    exact convolution_power_integrable μ ⟨markSum μ k, inferInstance⟩ hμ ih n

/-- A finite sum of the actual centered marks remains centered. -/
theorem markSum_mean (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (k : ℕ) :
    (∫ x : ℝ, x ∂markSum μ k) = 0 := by
  induction k with
  | zero => simp [markSum]
  | succ k ih =>
    have hh := convolution_power_integral μ ⟨markSum μ k, inferInstance⟩ hμ
      (markSum_power_integrable μ hμ k) 1
    simpa [Finset.sum_range_succ, hm, ih, markSum] using hh

/-- Exact second moment of the finite centered mark sum. -/
theorem markSum_second (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (k : ℕ) :
    (∫ x : ℝ, x ^ 2 ∂markSum μ k) =
      (k : ℝ) * (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) := by
  induction k with
  | zero => simp [markSum]
  | succ k ih =>
    have hh := convolution_power_integral μ ⟨markSum μ k, inferInstance⟩ hμ
      (markSum_power_integrable μ hμ k) 2
    simp only [ProbabilityMeasure.coe_mk] at hh
    norm_num [Finset.sum_range_succ, hm, markSum_mean μ hμ hm k, ih] at hh
    change (∫ x : ℝ, x ^ 2 ∂((μ : Measure ℝ) ∗ markSum μ k)) = _
    rw [hh]
    push_cast
    ring

/-- Exact fourth moment, with every mixed contribution from the product law accounted for. -/
theorem markSum_fourth (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) (μ : Measure ℝ))
    (hm : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) (k : ℕ) :
    (∫ x : ℝ, x ^ 4 ∂markSum μ k) =
      (k : ℝ) * (∫ x : ℝ, x ^ 4 ∂(μ : Measure ℝ)) +
        3 * (k : ℝ) * ((k : ℝ) - 1) * (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) ^ 2 := by
  induction k with
  | zero => simp [markSum]
  | succ k ih =>
    have hh := convolution_power_integral μ ⟨markSum μ k, inferInstance⟩ hμ
      (markSum_power_integrable μ hμ k) 4
    simp only [ProbabilityMeasure.coe_mk] at hh
    norm_num [Finset.sum_range_succ, Nat.choose, hm, markSum_mean μ hμ hm k,
      markSum_second μ hμ hm k, ih] at hh
    change (∫ x : ℝ, x ^ 4 ∂((μ : Measure ℝ) ∗ markSum μ k)) = _
    rw [hh]
    push_cast
    ring

end Descent.Portability.MarkSumMoments
