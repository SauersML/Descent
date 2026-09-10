/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWECounterexample
import Descent.Portability.BanachEulerExponential
import Descent.Portability.IndependentShiftOperator
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.NormedSpace

assert_below Descent.Decision Descent.Program

/-!
The critical HWE array converges for every bounded continuous observable, using
norm convergence of the actual transition operators. The limiting operator is
the compound-Poisson exponential of the fair-sign translation kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWEOperatorLimit

open scoped BigOperators BoundedContinuousFunction Topology
open Filter Foundations HWEInteractionLaw BalancedHWEInteraction IndependentShiftOperator

abbrev Operator := Observable →L[ℝ] Observable

noncomputable local instance : NormedRing Operator := ContinuousLinearMap.toNormedRing
local instance : IsTopologicalRing Operator :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- One fair unit jump, acting on the requested observable. -/
noncomputable def jump : Operator := (1 / 2 : ℝ) • (translate 1 + translate (-1))

theorem jump_apply (f : Observable) (x : ℝ) :
    jump f x = (f (x + 1) + f (x - 1)) / 2 := by
  simp [jump, sub_eq_add_neg, div_eq_mul_inv, mul_comm]
  ring

/-- The actual balanced block law equals a lazy fair-sign jump operator. -/
theorem block_shift_eq (m : ℕ) (hm : 0 < m) :
    shift (blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness)) blockCode =
      1 + (1 / 2 : ℝ) ^ m • (jump - 1) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  ext f x
  rw [shift_apply, blockCode_law (fun z ↦ f (x + z))]
  simp only [Fintype.card_fin, add_zero, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sub_apply,
    smul_eq_mul, jump_apply]
  rw [sub_eq_add_neg x 1]
  ring

/-- Norm convergence of the complete HWE transition operator at critical scaling. -/
theorem critical_operator_limit :
    Tendsto (fun m : ℕ ↦
      (shift (blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness)) blockCode) ^ (2 ^ m))
      atTop (nhds (NormedSpace.exp ℝ (jump - 1))) := by
  have h := (BanachEulerExponential.euler_tends_exp (jump - 1)).comp
    (Nat.tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ)))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  rw [block_shift_eq m hm]
  have hp : (1 / 2 : ℝ) ^ m = ((2 ^ m : ℕ) : ℝ)⁻¹ := by
    rw [Nat.cast_pow, Nat.cast_ofNat,
      show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  simp only [Function.comp_apply, hp]

/-- Evaluate a full operator at the requested bounded observable and starting value. -/
noncomputable def observer (f : Observable) (x : ℝ) : Operator →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp (ContinuousLinearMap.apply ℝ Observable f)

@[simp] theorem observer_apply (f : Observable) (x : ℝ) (T : Operator) :
    observer f x T = T f x := rfl

/-- Convergence of every bounded continuous test observable of the actual HWE statistic. -/
theorem critical_bounded_observable_limit (f : Observable) :
    Tendsto (fun m : ℕ ↦ (rowLaw m (2 ^ m)).expectation
      (fun sample ↦ f (rowScore 1 sample))) atTop
      (nhds ((NormedSpace.exp ℝ (jump - 1)) f 0)) := by
  have h := (observer f 0).continuous.tendsto (NormedSpace.exp ℝ (jump - 1))
    |>.comp critical_operator_limit
  convert h using 1
  funext m
  dsimp only [Function.comp_apply]
  rw [observer_apply, shift_pow_sample]
  simp only [rowLaw, rowScore, one_mul, zero_add]

/-- Removing the identity from the jump generator supplies the Poisson normalization. -/
theorem exponential_generator :
    NormedSpace.exp ℝ (jump - 1) = Real.exp (-1) • NormedSpace.exp ℝ jump := by
  have hscalar : NormedSpace.exp ℝ (-(1 : Operator)) = Real.exp (-1) • (1 : Operator) := by
    have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Operator) (-1)
    simpa only [map_neg, map_one, ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using h.symm
  rw [sub_eq_add_neg, NormedSpace.exp_add_of_commute (𝕂 := ℝ) (Commute.one_right jump).neg_right,
    hscalar, mul_smul_comm, mul_one]

/-- The limiting expectation is the normalized Poisson series of fair-jump expectations. -/
theorem limiting_poisson_series (f : Observable) (x : ℝ) :
    (NormedSpace.exp ℝ (jump - 1)) f x =
      ∑' k : ℕ, (Real.exp (-1) / k.factorial) * ((jump ^ k) f x) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) jump).map
    (observer f x) (observer f x).continuous
  have hs := h.mul_left (Real.exp (-1))
  rw [exponential_generator]
  change Real.exp (-1) * ((NormedSpace.exp ℝ jump) f x) = _
  symm
  calc
    _ = ∑' k : ℕ, Real.exp (-1) * (observer f x)
        ((k.factorial : ℝ)⁻¹ • jump ^ k) := by
      apply tsum_congr
      intro k
      simp only [map_smul, observer_apply, smul_eq_mul, div_eq_mul_inv, mul_assoc]
    _ = _ := hs.tsum_eq

end Descent.Portability.BalancedHWEOperatorLimit
