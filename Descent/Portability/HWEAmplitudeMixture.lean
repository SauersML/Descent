/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEExceptionalLimit
import Descent.Portability.FiniteL1BoundedTests

assert_below Descent.Decision Descent.Program

/-!
Complete bounded-continuous-test limit for the actual square-biased HWE amplitude
under near balance: an atom at zero and a fair signed lognormal component. Both
the mixing weight and the disappearance of heterozygote amplitudes are derived
from the original genotype law and frequency assumptions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEAmplitudeMixture

open scoped BigOperators Topology NNReal BoundedContinuousFunction
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw
open HWEHomozygoteLimit HWEExceptionalLimit HWEHeterozygosityLaw

/-- Keep the original amplitude only on the heterozygote-containing event. -/
noncomputable def exceptionalAmplitude {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (c : ℝ) (x : ι → DiploidGenotype) : ℝ :=
  if count x = 0 then 0 else c * normalized h x

/-- Exact L1 magnitude after masking and rescaling. -/
theorem exceptional_absolute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (c : ℝ) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ |exceptionalAmplitude h c x|) = |c| * exceptionalMoment h h0 h1 := by
  simp only [exceptionalMoment, FiniteReportLaw.expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hc : count x = 0 <;> simp [exceptionalAmplitude, hc, abs_mul, mul_left_comm]

/-- All bounded continuous tests see the masked exceptional amplitude converge to zero. -/
theorem exceptional_test_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 K))
    (f : ℝ →ᵇ ℝ) (c : ℝ) :
    Tendsto (fun m ↦
      (independentLaw (fun i ↦ squareBiasedLocus (h m i) (h0 m i) (h1 m i))).expectation
        (fun x ↦ f (exceptionalAmplitude (h m) c x))) atTop (𝓝 (f 0)) := by
  apply FiniteL1BoundedTests.test_limit
  simpa only [exceptional_absolute, mul_zero] using
    (exceptional_L1_limit h h0 h1 ε hcap hε K hK).const_mul |c|

/-- Exact event decomposition for the actual unmasked amplitude statistic. -/
theorem amplitude_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (f : ℝ → ℝ) (c : ℝ) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ f (c * normalized h x)) =
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x = 0 then f (c * normalized h x) else 0) +
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ f (exceptionalAmplitude h c x)) - f 0 *
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x = 0 then 1 else 0) := by
  simp only [FiniteReportLaw.expectation, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hc : count x = 0 <;> simp [exceptionalAmplitude, hc] <;> ring

/-- Full tilted amplitude limit: zero atom plus the derived fair signed lognormal component. -/
theorem amplitude_mixture_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (f : ℝ →ᵇ ℝ) (c : ℝ) :
    Tendsto (fun m ↦
      (independentLaw (fun i ↦ squareBiasedLocus (h (m + 1) i)
        (h0 (m + 1) i) (h1 (m + 1) i))).expectation
        (fun x ↦ f (c * normalized (h (m + 1)) x))) atTop
      (𝓝 ((1 - Real.exp (-4 * (K : ℝ))) * f 0 + Real.exp (-4 * (K : ℝ)) *
        (((∫ x, f (c * Real.exp (-x)) ∂gaussianReal 0 (4 * K)) +
        (∫ x, f (-c * Real.exp (-x)) ∂gaussianReal 0 (4 * K))) / 2))) := by
  have hh := component_amplitude_limit h h0 h1 ε hcap hε K hK f c
  have he := (exceptional_test_limit h h0 h1 ε hcap hε K hK f c).comp
    (tendsto_add_atTop_nat 1)
  have hz := (HWEHeterozygosityLimit.zero_count_probability_limit h h0 h1 ε hcap hε K hK).comp
    (tendsto_add_atTop_nat 1)
  have hc := (hh.add he).sub (hz.const_mul (f 0))
  simp only [Function.comp_def, ← amplitude_decomposition] at hc
  convert hc using 1 <;> congr 1 <;> ring

end Descent.Portability.HWEAmplitudeMixture
