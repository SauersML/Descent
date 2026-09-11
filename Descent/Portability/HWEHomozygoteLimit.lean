/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHomozygoteAmplitude

assert_below Descent.Decision Descent.Program

/-!
The actual square-biased HWE interaction, conditioned on no heterozygotes and
normalized by its balanced magnitude, converges to a fair signed lognormal law.
Both the conditional law and its unnormalized mixture weight are derived here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHomozygoteLimit

open scoped BigOperators Topology NNReal BoundedContinuousFunction
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw
open HWEHomozygoteConditioning HWEHomozygoteAmplitude HWELogCoordinates
open BalancedHWEWeakLimit RademacherArrayWeakLimit RademacherParityLaw

/-- Normalize the original interaction by its balanced homozygote magnitude. -/
noncomputable def normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (x : ι → DiploidGenotype) : ℝ :=
  interaction h x / Real.sqrt 2 ^ Fintype.card ι

theorem normalized_homoVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (b : ι → Bool) :
    normalized h (homoVector b) = parity b *
      Real.exp (-weightedSum (fun i ↦ coordinate ((h i).altFreq - 1 / 2)) b) := by
  rw [normalized, interaction_homoVector h h0 h1, mul_assoc]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (Real.sqrt_pos.mpr (by norm_num)).ne')

/-- A bounded continuous amplitude test pulled back to the Gaussian coordinate. -/
noncomputable def amplitudeTest (f : ℝ →ᵇ ℝ) (c : ℝ) (b : Bool) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨fun x ↦ c * signValue b * Real.exp (-x), by fun_prop⟩

theorem test_parity (f : ℝ →ᵇ ℝ) (c : ℝ) {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (b : ι → Bool) :
    f (c * (parity b * Real.exp (-weightedSum a b))) =
      if parity b = 1 then amplitudeTest f c true (weightedSum a b)
        else amplitudeTest f c false (weightedSum a b) := by
  rcases sq_eq_one_iff.mp (parity_square b) with h | h <;>
    norm_num [h, amplitudeTest, signValue, mul_assoc]

/-- Actual conditional bounded-test convergence to an independent fair sign times exp(N(0,4K)). -/
theorem conditional_amplitude_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (f : ℝ →ᵇ ℝ) (c : ℝ) :
    Tendsto (fun m ↦
      (independentLaw (fun i ↦ squareBiasedLocus (h (m + 1) i)
        (h0 (m + 1) i) (h1 (m + 1) i))).expectation
        (fun x ↦ if HWEHeterozygosityLaw.count x = 0
          then f (c * normalized (h (m + 1)) x) else 0) / zeroMass (h (m + 1))) atTop
      (𝓝 (((∫ x, f (c * Real.exp (-x)) ∂gaussianReal 0 (4 * K)) +
        (∫ x, f (-c * Real.exp (-x)) ∂gaussianReal 0 (4 * K))) / 2)) := by
  let a := fun m (i : Fin m) ↦ coordinate ((h m i).altFreq - 1 / 2)
  have hc := RademacherJointLimit.joint_observable_limit a
    (fun m ↦ ‖a m‖) (fun m i ↦ norm_le_pi_norm (a m) i)
    (maximal_coordinate_limit _ ε hcap hε) (4 * K)
    (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      squared_coordinate_limit _ ε hcap hε K hK) (amplitudeTest f c)
  simp only [conditional_expectation _ (h0 _) (h1 _),
    normalized_homoVector _ (h0 _) (h1 _), test_parity]
  simpa only [amplitudeTest, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, signValue, if_true, Bool.false_eq_true, if_false,
    mul_one, mul_neg_one] using hc

/-- The zero-heterozygote component carries precisely its limiting mass exp(-4K). -/
theorem component_amplitude_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (f : ℝ →ᵇ ℝ) (c : ℝ) :
    Tendsto (fun m ↦
      (independentLaw (fun i ↦ squareBiasedLocus (h (m + 1) i)
        (h0 (m + 1) i) (h1 (m + 1) i))).expectation
        (fun x ↦ if HWEHeterozygosityLaw.count x = 0
          then f (c * normalized (h (m + 1)) x) else 0)) atTop
      (𝓝 (Real.exp (-4 * (K : ℝ)) *
        (((∫ x, f (c * Real.exp (-x)) ∂gaussianReal 0 (4 * K)) +
        (∫ x, f (-c * Real.exp (-x)) ∂gaussianReal 0 (4 * K))) / 2))) := by
  have hz : Tendsto (fun m ↦ zeroMass (h m)) atTop (𝓝 (Real.exp (-4 * (K : ℝ)))) := by
    simpa only [HWEHeterozygosityLimit.zero_count_probability, zeroMass] using
      HWEHeterozygosityLimit.zero_count_probability_limit h h0 h1 ε hcap hε K hK
  have hc := conditional_amplitude_limit h h0 h1 ε hcap hε K hK f c
  have hh := (hz.comp (tendsto_add_atTop_nat 1)).mul hc
  have he (m : ℕ) (v : ℝ) : zeroMass (h (m + 1)) * (v / zeroMass (h (m + 1))) = v :=
    mul_div_cancel₀ v (zeroMass_pos _ (h0 _) (h1 _)).ne'
  simpa only [Function.comp_def, he] using hh

end Descent.Portability.HWEHomozygoteLimit
