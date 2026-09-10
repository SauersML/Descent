/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWEVanishingLaw

assert_below Descent.Decision Descent.Program

/-!
The balanced three-atom law with an arbitrary jump amplitude has a bounded
translation generator. Its evaluated finite powers depend continuously on the
amplitude, although translation need not be continuous in operator norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWEJumpOperator

open scoped BigOperators BoundedContinuousFunction Topology
open Filter Foundations HWEInteractionLaw BalancedHWEInteraction
open IndependentShiftOperator BalancedHWEOperatorLimit

noncomputable local instance : NormedRing Operator := ContinuousLinearMap.toNormedRing
local instance : IsTopologicalRing Operator :=
  NonUnitalSeminormedRing.toIsTopologicalRing
local instance : SMul Operator Operator := ⟨(· * ·)⟩
local instance : IsScalarTower ℝ Operator Operator :=
  IsScalarTower.right (R := ℝ) (A := Operator)

/-- One fair jump of the requested amplitude. -/
noncomputable def fairJump (a : ℝ) : Operator :=
  (1 / 2 : ℝ) • (translate a + translate (-a))

/-- The compensated fair-jump generator. -/
noncomputable def generator (a : ℝ) : Operator := fairJump a - 1

theorem fairJump_apply (a : ℝ) (f : Observable) (x : ℝ) :
    fairJump a f x = (f (x + a) + f (x - a)) / 2 := by
  simp [fairJump, sub_eq_add_neg, div_eq_mul_inv, mul_comm]
  ring

theorem generator_apply (a : ℝ) (f : Observable) (x : ℝ) :
    generator a f x = (f (x + a) + f (x - a)) / 2 - f x := by
  simp only [generator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    BoundedContinuousFunction.sub_apply, fairJump_apply]

/-- The actual one-block experiment supplies this lazy fair-jump operator. -/
theorem block_shift_eq (m : ℕ) (hm : 0 < m) (a : ℝ) :
    shift (blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness))
      (fun x ↦ a * blockCode x) = 1 + (1 / 2 : ℝ) ^ m • generator a := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  ext f x
  rw [shift_apply, blockCode_law (fun z ↦ f (x + a * z))]
  simp only [Fintype.card_fin, mul_zero, add_zero, mul_one, mul_neg_one,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, smul_eq_mul, generator_apply, sub_eq_add_neg]
  ring

/-- Every finite generator power is jointly continuous in amplitude and starting point. -/
theorem generator_power_continuous (k : ℕ) (f : Observable) :
    Continuous (fun z : ℝ × ℝ ↦ (generator z.1 ^ k) f z.2) := by
  induction k with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply] using
      f.continuous.comp continuous_snd
  | succ k ih =>
    have hp := ih.comp (continuous_fst.prodMk (continuous_snd.add continuous_fst))
    have hm := ih.comp (continuous_fst.prodMk (continuous_snd.sub continuous_fst))
    have hs := ((hp.add hm).div_const 2).sub ih
    simpa only [Function.comp_def, pow_succ', ContinuousLinearMap.mul_apply,
      generator_apply] using hs

/-- A uniform bound for finite generator powers, independent of jump amplitude. -/
theorem generator_power_bound (k : ℕ) (a : ℝ) (f : Observable) (x : ℝ) :
    |(generator a ^ k) f x| ≤ (2 : ℝ) ^ k * ‖f‖ := by
  induction k generalizing x with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply, one_mul, ← Real.norm_eq_abs]
      using f.norm_coe_le_norm x
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, generator_apply]
    calc
      _ ≤ |((generator a ^ k) f (x + a) + (generator a ^ k) f (x - a)) / 2| +
          |(generator a ^ k) f x| := abs_sub _ _
      _ ≤ ((2 : ℝ) ^ k * ‖f‖ + 2 ^ k * ‖f‖) / 2 + 2 ^ k * ‖f‖ := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add (div_le_div_of_nonneg_right
          ((abs_add_le _ _).trans (add_le_add (ih _) (ih _))) (by norm_num)) (ih _)
      _ = _ := by rw [pow_succ]; ring

/-- Evaluation of the Euler product as a scalar, finitely supported series. -/
theorem evaluated_euler_series (A : Operator) (n : ℕ) (f : Observable) (x : ℝ) :
    ((1 + (n : ℝ)⁻¹ • A) ^ n) f x =
      ∑' k : ℕ, ((n.choose k : ℝ) / (n : ℝ) ^ k) * ((A ^ k) f x) := by
  have hs : Summable (fun k : ℕ ↦ ((n.choose k : ℝ) / (n : ℝ) ^ k) • A ^ k) := by
    apply (hasSum_sum_of_ne_finset_zero (s := Finset.range (n + 1)) ?_).summable
    intro k hk
    have hnk : n < k := by simpa only [Finset.mem_range, not_lt] using hk
    simp only [Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero, zero_div, zero_smul]
  change observer f x ((1 + (n : ℝ)⁻¹ • A) ^ n) = _
  rw [BanachEulerExponential.euler_eq_series A n, (observer f x).map_tsum hs]
  apply tsum_congr
  intro k
  simp only [map_smul, observer_apply, smul_eq_mul]

/-- Exact Euler coefficients for the actual balanced HWE experiment. -/
theorem row_euler_series (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    (a : ℝ) (f : Observable) :
    (rowLaw m N).expectation (fun sample ↦ f (rowScore a sample)) =
      ∑' k : ℕ, ((N.choose k : ℝ) / (N : ℝ) ^ k) *
        (((N : ℝ) * (1 / 2 : ℝ) ^ m) ^ k * ((generator a ^ k) f 0)) := by
  have hrow := shift_pow_sample
    (blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness))
    (fun x ↦ a * blockCode x) f 0 N
  simp only [zero_add] at hrow
  rw [block_shift_eq m hm a] at hrow
  change _ = (rowLaw m N).expectation (fun sample ↦ f (rowScore a sample)) at hrow
  rw [← hrow]
  have hstep : (1 : Operator) + (1 / 2 : ℝ) ^ m • generator a =
      1 + (N : ℝ)⁻¹ • (((N : ℝ) * (1 / 2 : ℝ) ^ m) • generator a) := by
    rw [smul_smul, inv_mul_cancel_left₀ (by positivity : (N : ℝ) ≠ 0)]
  rw [hstep, evaluated_euler_series]
  apply tsum_congr
  intro k
  simp only [smul_pow, ContinuousLinearMap.smul_apply,
    BoundedContinuousFunction.smul_apply, smul_eq_mul]

end Descent.Portability.BalancedHWEJumpOperator
