/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace Descent

/-!
# `‖exp x - 1 - x‖ ≤ e^{‖x‖} - 1 - ‖x‖`, in any Banach algebra

`Descent.Coalescent.PairChainLimit` instantiates K-G (2.14) for a two-state generator and
records why it stops there: comparing a general transition matrix to `exp(N⁻¹Q)` needs a
second-order bound on the exponential, and Mathlib has one only for `ℝ` and `ℂ`
(`Real.abs_exp_sub_one_sub_id_le`).  In a Banach algebra there is none, so the many-state
case had no route.

The bound is not hard and it is not about genealogy; it is the exponential series compared
with itself.  Peeling the first two terms off `exp x = Σ (n!)⁻¹ xⁿ` leaves

  `exp x - 1 - x = Σ_{n} ((n+2)!)⁻¹ x^{n+2}`,

whose norm is at most the same series in `‖x‖`, which is `e^{‖x‖} - 1 - ‖x‖`.  Two
applications of `tsum_eq_zero_add` and the triangle inequality for sums do it.

The corollary `norm_exp_sub_one_sub_self_le_sq` is the form K-G's argument consumes: for
`‖x‖ ≤ 1` the remainder is at most `‖x‖²`, so a one-generation operator agreeing with
`1 + N⁻¹Q` to order `N⁻²` agrees with `exp(N⁻¹Q)` to the same order, and
`SemigroupLimit.tendsto_pow_self_exp` applies.

What this does NOT supply is the many-state transition matrix itself.  The corpus counts the
diagonal -- `WrightFisher.noCoalescenceProb` -- and not the off-diagonal entries, which need
the multinomial merge counts.  The obstacle that remains is therefore a construction, and the
analytic one is gone.

## Main results

- `exp_sub_one_sub_self_eq_tsum`: the remainder as a shifted series.
- `norm_exp_sub_one_sub_self_le`: **`‖exp x - 1 - x‖ ≤ e^{‖x‖} - 1 - ‖x‖`**.
- `norm_exp_sub_one_sub_self_le_sq`: hence `≤ ‖x‖²` when `‖x‖ ≤ 1`.
-/

namespace Coalescent

open NormedSpace Nat

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The exponential's remainder after two terms, as a series starting at `x²/2`. -/
theorem exp_sub_one_sub_self_eq_tsum (x : 𝔸) :
    exp ℝ x - 1 - x = ∑' n : ℕ, ((n + 2)! : ℝ)⁻¹ • x ^ (n + 2) := by
  have hsum : Summable fun n : ℕ ↦ ((n ! : ℝ))⁻¹ • x ^ n :=
    expSeries_summable' (𝕂 := ℝ) x
  have h0 : exp ℝ x = ∑' n : ℕ, ((n ! : ℝ))⁻¹ • x ^ n := by
    rw [exp_eq_tsum]
  have hpeel1 : (∑' n : ℕ, ((n ! : ℝ))⁻¹ • x ^ n)
      = ((0 ! : ℝ))⁻¹ • x ^ 0 + ∑' n : ℕ, (((n + 1)! : ℝ))⁻¹ • x ^ (n + 1) :=
    hsum.tsum_eq_zero_add
  have hsum1 : Summable fun n : ℕ ↦ (((n + 1)! : ℝ))⁻¹ • x ^ (n + 1) := by
    simpa using (summable_nat_add_iff (f := fun n : ℕ ↦ ((n ! : ℝ))⁻¹ • x ^ n) 1).mpr hsum
  have hpeel2 : (∑' n : ℕ, (((n + 1)! : ℝ))⁻¹ • x ^ (n + 1))
      = (((0 + 1)! : ℝ))⁻¹ • x ^ (0 + 1) + ∑' n : ℕ, (((n + 2)! : ℝ))⁻¹ • x ^ (n + 2) := by
    have := hsum1.tsum_eq_zero_add
    simpa using this
  rw [h0, hpeel1, hpeel2]
  simp

/-- **The Banach-algebra second-order bound.**  The remainder is dominated termwise by the
real exponential's, so its norm is at most `e^{‖x‖} - 1 - ‖x‖`. -/
theorem norm_exp_sub_one_sub_self_le (x : 𝔸) :
    ‖exp ℝ x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  have hreal : Real.exp ‖x‖ - 1 - ‖x‖ = ∑' n : ℕ, ((n + 2)! : ℝ)⁻¹ * ‖x‖ ^ (n + 2) := by
    have h := exp_sub_one_sub_self_eq_tsum (𝔸 := ℝ) ‖x‖
    rw [← Real.exp_eq_exp_ℝ] at h
    simpa [smul_eq_mul] using h
  rw [exp_sub_one_sub_self_eq_tsum, hreal]
  have hsummable : Summable fun n : ℕ ↦ ‖((n + 2)! : ℝ)⁻¹ • x ^ (n + 2)‖ := by
    have hs : Summable fun n : ℕ ↦ ‖((n ! : ℝ))⁻¹ • x ^ n‖ :=
      norm_expSeries_summable' (𝕂 := ℝ) x
    simpa using (summable_nat_add_iff
      (f := fun n : ℕ ↦ ‖((n ! : ℝ))⁻¹ • x ^ n‖) 2).mpr hs
  refine le_trans (norm_tsum_le_tsum_norm hsummable) ?_
  refine tsum_le_tsum (fun n ↦ ?_) hsummable ?_
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_pow_le' x (by omega)) (by positivity)
  · have h := exp_sub_one_sub_self_eq_tsum (𝔸 := ℝ) ‖x‖
    have hs : Summable fun n : ℕ ↦ ‖((n ! : ℝ))⁻¹ • (‖x‖ : ℝ) ^ n‖ :=
      norm_expSeries_summable' (𝕂 := ℝ) ‖x‖
    have hs2 : Summable fun n : ℕ ↦ ‖((n + 2)! : ℝ)⁻¹ • (‖x‖ : ℝ) ^ (n + 2)‖ := by
      simpa using (summable_nat_add_iff
        (f := fun n : ℕ ↦ ‖((n ! : ℝ))⁻¹ • (‖x‖ : ℝ) ^ n‖) 2).mpr hs
    refine hs2.congr fun n ↦ ?_
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]

/-- **The form K-G's argument consumes.**  For `‖x‖ ≤ 1` the remainder is at most `‖x‖²`, so
a one-generation operator within `C/N²` of `1 + N⁻¹Q` is within `(C + ‖Q‖²)/N²` of
`exp(N⁻¹Q)`. -/
theorem norm_exp_sub_one_sub_self_le_sq {x : 𝔸} (hx : ‖x‖ ≤ 1) :
    ‖exp ℝ x - 1 - x‖ ≤ ‖x‖ ^ 2 := by
  refine le_trans (norm_exp_sub_one_sub_self_le x) ?_
  have h := Real.abs_exp_sub_one_sub_id_le (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg x)])
  have hrw : |Real.exp ‖x‖ - 1 - ‖x‖| = Real.exp ‖x‖ - 1 - ‖x‖ := by
    refine abs_of_nonneg ?_
    have := Real.add_one_le_exp ‖x‖
    linarith
  rw [hrw] at h
  exact h

end Coalescent

end Descent
