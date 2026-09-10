/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWEGaussianCharacteristic
import Descent.Portability.TightCharacteristicConvergence
import Descent.Portability.SecondMomentTightness
import Descent.Portability.FiniteAtomicReportMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

assert_below Descent.Decision Descent.Program

/-!
The balanced high-intensity HWE phase converges weakly to the actual standard
Gaussian probability measure. Tightness follows from the exact normalized row
moments, with the exceptional order-zero row included in the finite bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWEGaussianWeakLimit

open scoped Topology BoundedContinuousFunction
open Filter MeasureTheory ProbabilityTheory HWEInteractionLaw BalancedHWEInteraction
open BalancedHWEWeakLimit BalancedHWEVanishingLaw BalancedHWEGaussianCharacteristic
open TightCharacteristicConvergence SecondMomentTightness FiniteAtomicReportMeasure

/-- The actual standard Gaussian probability measure. -/
noncomputable def standardGaussian : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- Every sequence of normalized balanced rows is tight, with no intensity limit assumed. -/
theorem normalized_rows_tight (N : ℕ → ℕ) :
    IsTightMeasureSet (Set.range (fun m ↦
      (rowProbability m (N m) (unitAmplitude m (N m)) : Measure ℝ))) := by
  let B := 1 + |(rowLaw 0 (N 0)).expectation
    (fun sample ↦ rowScore (unitAmplitude 0 (N 0)) sample ^ 2)|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply tight_of_second_moment_bound
    (fun m ↦ rowProbability m (N m) (unitAmplitude m (N m))) B hB
  · intro m
    exact finite_report_integrable _ _ _
  · intro m
    change (∫ x : ℝ, x ^ 2 ∂finiteMeasure (rowLaw m (N m))
      (rowScore (unitAmplitude m (N m)))) ≤ B
    rw [integral_finite_report]
    by_cases hm : m = 0
    · subst m
      have h := le_abs_self ((rowLaw 0 (N 0)).expectation
        (fun sample ↦ rowScore (unitAmplitude 0 (N 0)) sample ^ 2))
      dsimp [B]
      linarith
    · by_cases hn : N m = 0
      · rw [hn]
        simpa only [rowScore, Finset.univ_eq_empty, Finset.sum_empty, zero_pow (by decide : 2 ≠ 0),
          FiniteReportLaw.expectation, mul_zero, Finset.sum_const_zero] using hB
      · rw [normalized_second_moment m (N m) (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)]
        dsimp [B]
        linarith [abs_nonneg ((rowLaw 0 (N 0)).expectation
          (fun sample ↦ rowScore (unitAmplitude 0 (N 0)) sample ^ 2))]

/-- The full Gaussian weak phase of the original normalized balanced HWE interaction statistic. -/
theorem normalized_gaussian_weak_limit (N : ℕ → ℕ)
    (hr : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop atTop) :
    Tendsto (fun m ↦ rowProbability m (N m) (unitAmplitude m (N m))) atTop
      (nhds standardGaussian) := by
  apply weak_convergence_of_tight_characteristic _ standardGaussian
  · have h := (isTightMeasureSet_singleton (μ := (standardGaussian : Measure ℝ))).union
      (normalized_rows_tight N)
    simpa only [Set.singleton_union] using h
  · intro t
    have hnormal : charFun (gaussianReal 0 1) t =
        ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [charFun_gaussianReal]
      simp only [NNReal.coe_one, Complex.ofReal_zero, Complex.ofReal_one,
        mul_zero, zero_mul, zero_sub, one_mul,
        Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_pow, Complex.ofReal_ofNat]
    change Tendsto (fun m ↦ charFun (finiteMeasure (rowLaw m (N m))
      (rowScore (unitAmplitude m (N m)))) t) atTop (nhds (charFun (gaussianReal 0 1) t))
    rw [hnormal]
    simpa only [charFun_finite_report] using gaussian_characteristic_limit N hr t

end Descent.Portability.BalancedHWEGaussianWeakLimit
