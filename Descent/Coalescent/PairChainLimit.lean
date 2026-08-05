/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SemigroupLimit
import Descent.Coalescent.Convergence
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace Descent

/-!
# The pair chain's operator limit, instantiated

`Descent.Coalescent.SemigroupLimit` proves K-G (2.14) in the abstract and records what it
lacks: an instantiation, because this corpus carries the chain as a KERNEL and not as a
matrix, so there was no `P_N` to feed the theorem.  This file supplies one for the case the
whole group is built on -- two lineages -- and does it without ever computing a matrix
exponential.

The two-state generator satisfies one identity, and everything follows from it:

  `Q² = -Q`.

That is what a `Q`-matrix on two states is: rows summing to zero
(`Generator.generator_row_sum_zero`) with a single absorbing state.  From it,
`one_add_smul_pow` computes every power of `1 + aQ` in closed form,

  `(1 + aQ)^N = 1 + (1 - (1-a)^N) Q`,

so the comparison family `B_N = 1 + (1 - e^{-1/N})Q` has `B_N^N = 1 + (1 - e^{-1})Q`
independently of `N`.  That is a semigroup obtained by algebra rather than by exponentiation,
which is why `SemigroupLimit.tendsto_pow_of_close` was stated with the comparison family left
open.

The one-generation operator is K-G (2.11) exactly, `P_N = 1 + N⁻¹Q`, and the distance to
`B_N` is `|N⁻¹ - (1 - e^{-1/N})| ‖Q‖ ≤ ‖Q‖/N²` -- the scalar Taylor bound, nothing about
matrices.  So

  `(1 + N⁻¹Q)^N → 1 + (1 - e^{-1})Q`,

and the coefficient `1 - e^{-1}` is the probability that two lineages have coalesced by one
unit of coalescent time.  `Convergence.tendsto_pairDistinct_pow` says the same thing about
the surviving probability `e^{-1}`, counted off the parent law; this says it about the
operator.

## What is assumed

That `P_N` and `B_N` are contractions.  For stochastic matrices under the row-sum norm they
are, and K-G says so in the same breath as (2.13); in an abstract normed algebra it is not
automatic, so it is a hypothesis here rather than a lemma.  Everything else -- the closed
form for the powers, the distance bound, the limit -- is proved.

## Main results

- `one_add_smul_mul`: `(1 + aQ)(1 + bQ) = 1 + (a + b - ab)Q` when `Q² = -Q`.
- `one_add_smul_pow`: **`(1 + aQ)^N = 1 + (1 - (1-a)^N)Q`**.
- `dist_le_of_exp`: `|N⁻¹ - (1 - e^{-1/N})| ≤ N⁻²`, the scalar Taylor bound.
- `tendsto_pairChain_pow`: **K-G (2.14) for the pair chain**, instantiated.
-/

namespace Coalescent

open Filter Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸]

/-- **The two-state composition law.**  With `Q² = -Q`, the family `1 + aQ` is closed under
multiplication and composes by `a ⊕ b = a + b - ab` -- the law for "not both survive". -/
theorem one_add_smul_mul {Q : 𝔸} (hQ : Q * Q = -Q) (a b : ℝ) :
    (1 + a • Q) * (1 + b • Q) = 1 + (a + b - a * b) • Q := by
  have hprod : (a • Q) * (b • Q) = -((a * b) • Q) := by
    calc (a • Q) * (b • Q) = (a * b) • (Q * Q) := by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = (a * b) • (-Q) := by rw [hQ]
      _ = -((a * b) • Q) := by rw [smul_neg]
  rw [add_mul, one_mul, mul_add, mul_one, hprod, sub_smul, add_smul]
  abel

/-- **Every power in closed form.**  `(1 + aQ)^N = 1 + (1 - (1-a)^N)Q`: the coefficient is the
complement of a survival probability, compounded. -/
theorem one_add_smul_pow {Q : 𝔸} (hQ : Q * Q = -Q) (a : ℝ) (N : ℕ) :
    (1 + a • Q) ^ N = 1 + (1 - (1 - a) ^ N) • Q := by
  induction N with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, one_add_smul_mul hQ]
      congr 1
      congr 1
      ring

/-- The scalar Taylor bound: the one-generation coefficient `N⁻¹` and the semigroup
coefficient `1 - e^{-1/N}` differ by at most `N⁻²`. -/
theorem dist_le_of_exp {N : ℕ} (hN : 1 ≤ N) :
    |1 / (N : ℝ) - (1 - Real.exp (-(1 / (N : ℝ))))| ≤ (1 / (N : ℝ)) ^ 2 := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hx : |(-(1 / (N : ℝ)))| ≤ 1 := by
    rw [abs_neg, abs_of_pos (by positivity)]
    rw [div_le_one hpos]
    exact hNR
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have hsq : (-(1 / (N : ℝ))) ^ 2 = (1 / (N : ℝ)) ^ 2 := by ring
  rw [hsq] at h
  have hrw : Real.exp (-(1 / (N : ℝ))) - 1 - -(1 / (N : ℝ))
      = 1 / (N : ℝ) - (1 - Real.exp (-(1 / (N : ℝ)))) := by ring
  rwa [hrw] at h

/-- **K-G (2.14) for the pair chain.**  The one-generation operator `1 + N⁻¹Q` raised to the
`N`-th power converges to `1 + (1 - e^{-1})Q`: one unit of coalescent time, with the
coefficient the chance that two lineages have met.

The contraction hypotheses are K-G's own -- stochastic matrices are contractions -- and are
hypotheses here because an abstract normed algebra does not supply them. -/
theorem tendsto_pairChain_pow {Q : 𝔸} (hQ : Q * Q = -Q)
    (hP : ∀ N : ℕ, ‖(1 : 𝔸) + (1 / (N : ℝ)) • Q‖ ≤ 1)
    (hB : ∀ N : ℕ, ‖(1 : 𝔸) + (1 - Real.exp (-(1 / (N : ℝ)))) • Q‖ ≤ 1) :
    Tendsto (fun N : ℕ ↦ ((1 : 𝔸) + (1 / (N : ℝ)) • Q) ^ N) atTop
      (nhds (1 + (1 - Real.exp (-1)) • Q)) := by
  refine tendsto_pow_of_close (1 + (1 - Real.exp (-1)) • Q) ‖Q‖
    (fun N ↦ (1 : 𝔸) + (1 / (N : ℝ)) • Q)
    (fun N ↦ (1 : 𝔸) + (1 - Real.exp (-(1 / (N : ℝ)))) • Q) hP hB ?_ ?_
  · intro N hN
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [one_add_smul_pow hQ]
    congr 2
    have hsub : 1 - (1 - Real.exp (-(1 / (N : ℝ)))) = Real.exp (-(1 / (N : ℝ))) := by ring
    rw [hsub, ← Real.exp_nat_mul]
    congr 1
    field_simp
  · intro N
    have hdiff : ((1 : 𝔸) + (1 / (N : ℝ)) • Q)
        - ((1 : 𝔸) + (1 - Real.exp (-(1 / (N : ℝ)))) • Q)
        = (1 / (N : ℝ) - (1 - Real.exp (-(1 / (N : ℝ))))) • Q := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]
    rw [hdiff, norm_smul]
    rcases Nat.eq_zero_or_pos N with hz | hpos
    · subst hz
      simp
    · have hb := dist_le_of_exp hpos
      have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hpos
      have hsq : (1 / (N : ℝ)) ^ 2 = 1 / (N : ℝ) ^ 2 := by
        rw [div_pow, one_pow]
      calc ‖1 / (N : ℝ) - (1 - Real.exp (-(1 / (N : ℝ))))‖ * ‖Q‖
          ≤ (1 / (N : ℝ) ^ 2) * ‖Q‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [Real.norm_eq_abs, ← hsq]
            exact hb
        _ = ‖Q‖ / (N : ℝ) ^ 2 := by ring

end Coalescent

end Descent
