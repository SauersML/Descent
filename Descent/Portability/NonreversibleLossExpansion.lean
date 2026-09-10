/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExponentialRemainder
import Mathlib.Analysis.InnerProductSpace.Adjoint

assert_below Descent.Decision Descent.Program

/-!
The finite-horizon stale-observable operator for a generator `L = -S + A`.
The circulation contribution at second order is `t² A* A`. Its error bound
is derived from the actual operator exponential in the induced Hilbert norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NonreversibleLossExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [Nontrivial E]

noncomputable def lossOperator (generator : E →L[ℝ] E) (time : ℝ) : E →L[ℝ] E :=
  (2 : ℝ) • 1 - NormedSpace.exp ℝ (time • generator) -
    star (NormedSpace.exp ℝ (time • generator))

noncomputable def lossRemainder (generator : E →L[ℝ] E) (time : ℝ) : E →L[ℝ] E :=
  -ExponentialRemainder.remainder (time • generator) 3 -
    star (ExponentialRemainder.remainder (time • generator) 3)

/-- The two exponential tails give the explicit `1/3` finite-horizon certificate. -/
theorem lossRemainder_norm (generator : E →L[ℝ] E) (time : ℝ) (htime : 0 ≤ time) :
    ‖lossRemainder generator time‖ ≤
      time ^ 3 / 3 * ‖generator‖ ^ 3 * Real.exp (time * ‖generator‖) := by
  have hstar (operator : E →L[ℝ] E) : ‖star operator‖ = ‖operator‖ :=
    ContinuousLinearMap.adjoint.norm_map operator
  have hbound := ExponentialRemainder.remainder_norm (time • generator) 3
  have hnorm : ‖time • generator‖ = time * ‖generator‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htime]
  simp only [hnorm] at hbound
  norm_num only [Nat.factorial] at hbound
  calc
    ‖lossRemainder generator time‖ ≤
        ‖ExponentialRemainder.remainder (time • generator) 3‖ +
          ‖ExponentialRemainder.remainder (time • generator) 3‖ := by
      unfold lossRemainder
      simpa only [norm_neg, hstar] using norm_sub_le
        (-ExponentialRemainder.remainder (time • generator) 3)
        (star (ExponentialRemainder.remainder (time • generator) 3))
    _ ≤ 2 * ((time * ‖generator‖) ^ 3 / 6 * Real.exp (time * ‖generator‖)) := by
      linarith
    _ = _ := by ring

omit [Nontrivial E] in
/-- This algebraic identity requires neither commutation of `S,A` nor reversibility. -/
theorem lossOperator_expansion (symmetric circulation : E →L[ℝ] E)
    (hsymmetric : star symmetric = symmetric) (hcirculation : star circulation = -circulation)
    (time : ℝ) :
    lossOperator (-symmetric + circulation) time =
      (2 * time) • symmetric - time ^ 2 • symmetric ^ 2 +
        time ^ 2 • (star circulation * circulation) +
        lossRemainder (-symmetric + circulation) time := by
  unfold lossOperator lossRemainder ExponentialRemainder.remainder
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
    Nat.cast_one, inv_one, one_smul, pow_zero, zero_add, pow_one,
    star_sub, star_add, star_smul, star_neg, star_one, star_pow,
    star_trivial, hsymmetric, hcirculation]
  ext vector
  simp only [pow_two, ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, map_add, map_neg, map_smul, smul_add, smul_neg]
  module

end Descent.Portability.NonreversibleLossExpansion
