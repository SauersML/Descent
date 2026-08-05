/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace Descent

/-!
# The jump chain of the `n`-coalescent

Kingman (1982), *The coalescent* (**K-C**), Theorem 1, factorises the `n`-coalescent into a
pure death process and a discrete-time jump chain `{ℛ_k}`, proves the two independent, and
gives the jump chain's transition and absolute probabilities:

  `P{ℛ_{k-1} = η | ℛ_k = ξ} = 2/(k(k-1))` for `ξ ≺ η`, and `0` otherwise,        K-C (2.2)
  `P{ℛ_k = ξ} = ((n-k)! k! (k-1)! / (n! (n-1)!)) λ₁! λ₂! ⋯ λ_k!`,                K-C (2.3)

with `λ₁, …, λ_k` the class sizes of `ξ`.  This file proves what can be proved without
building the process: (2.2) as a consequence of the cover count, the normalisation that
makes it a probability, and the backward-induction identity that is the whole content of
K-C's proof of (2.3).

The split is deliberate and is stated rather than hidden:

* DERIVED here.  `jumpProb_eq` and `card_covers_mul_jumpProb`: the jump chain is UNIFORM on
  the `C(k,2)` covers of its current state, each getting `2/(k(k-1))`, and those weights
  sum to one.  The uniformity is not an extra assumption -- it is `q_{ξη}/q_ξ` with
  `q_{ξη} = 1` (K-C (1.3)) and `q_ξ` counted by `Descent.Coalescent.StateSpace.card_covers`.
* DERIVED here, and it is the load-bearing step of K-C's Theorem 1: `absoluteProb_recursion`,
  the backward induction from `k` to `k-1`.  Kingman's displayed calculation has two moving
  parts -- the factorial prefactor `jumpCoeff_recursion`, and the fact that splitting a class
  of size `λ` in every way contributes `(λ-1)` copies of `½ λ!` (`inner_split_sum`, via
  `Nat.choose_mul_factorial_mul_factorial`).  Both are here, and they combine exactly as
  K-C's `Σ_l (λ_l - 1) = n - (k-1)`.
* NOT derived here, and NOT claimed: that the weight `½ C(λ_l, ν)` counts the states
  `ξ ≺ η` obtained by splitting `η`'s `l`-th class into parts `ν` and `λ_l - ν`.  The
  identity below carries it as written.  Note what the `½` is and is not:
  `Descent.Coalescent.Split.splitBy_compl` shows a cut is named twice by Kingman's sum, once
  as `ν` and once as `λ_l - ν`, so the `½` corrects THE SUM.  It is not the count attached
  to a single `ν` -- for `2ν ≠ λ_l` there are `C(λ_l, ν)` such states, not half that, and
  only the balanced case `2ν = λ_l` has `C(λ_l, ν)/2`.  Both readings total
  `2^{λ_l - 1} - 1`, which is `Descent.Coalescent.Program`.  The gap between this file and a
  complete proof of (2.3) is the bijection between cuts of a class and the states refining
  `η` there.

## Main results

- `jumpProb_eq`: `1/d_k = 2/(k(k-1))`, K-C (2.2).
- `card_covers_mul_jumpProb`: the uniform weights on covers sum to one.
- `jumpCoeff_recursion`: the factorial prefactor of (2.3) satisfies K-C's recursion.
- `inner_split_sum`: splitting one class contributes `(λ-1)` copies of `½ λ!`.
- `absoluteProb_recursion`: the two combine into K-C's backward induction step.
- `absoluteProb_top`: (2.3) is correct at `k = n`, the base of the induction.
-/

namespace Coalescent

open Finset Nat

/-! ### The jump chain is uniform on covers

K-C's proof of (2.2) is one line of general Markov-chain theory: jump probabilities are
`q_{ξη}/q_ξ`.  With `q_{ξη} = 1` on covers (K-C (1.3)) and `q_ξ` the number of covers, the
jump chain picks a uniformly random pair of blocks to merge.  Since
`Descent.Coalescent.StateSpace.card_covers` counts the covers, the normalisation is a
theorem rather than a postulate. -/

/-- The probability the jump chain assigns to each individual cover of a `k`-block state:
`q_{ξη}/q_ξ = 1/d_k`.  K-C (2.2). -/
noncomputable def jumpProb (k : ℕ) : ℝ := 1 / deathRate k

/-- **K-C (2.2).**  Each of the `C(k,2)` available mergers is taken with probability
`2/(k(k-1))`. -/
theorem jumpProb_eq {k : ℕ} (hk : 2 ≤ k) :
    jumpProb k = 2 / ((k : ℝ) * ((k : ℝ) - 1)) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : ((k : ℝ) - 1) ≠ 0 := by linarith
  have h0 : (k : ℝ) ≠ 0 := by linarith
  unfold jumpProb deathRate
  field_simp

/-- **The uniform weights are a probability distribution.**  The number of covers times the
weight on each is one -- so nothing is assumed about where the jump chain goes beyond
K-C (1.3)'s unit rates, and the count in `card_covers` does the normalising. -/
theorem card_covers_mul_jumpProb {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ) :
    (Nat.card {η : ER n // Covers ξ η} : ℝ) * jumpProb (blocks ξ) = 1 := by
  rw [card_covers_eq_deathRate]
  unfold jumpProb
  field_simp [deathRate_ne_zero hk]

/-! ### The absolute distribution, and the induction that proves it

K-C (2.3) is proved by backward induction from `k = n`.  The two ingredients are separated
here so that each can be checked on its own. -/

/-- The factorial prefactor of K-C (2.3). -/
noncomputable def jumpCoeff (n k : ℕ) : ℝ :=
  (((n - k)! * k ! * (k - 1)! : ℕ) : ℝ) / ((n ! * (n - 1)! : ℕ) : ℝ)

/-- **K-C (2.3) itself**, as a function of the class sizes: the absolute probability that
the jump chain, having reached `k` blocks, is at a state whose classes have the given sizes.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is Kingman's formula, written down; what is
proved below is that it satisfies the recursion its proof requires. -/
noncomputable def absoluteProb (n k : ℕ) (lam : Multiset ℕ) : ℝ :=
  jumpCoeff n k * (((lam.map Nat.factorial).prod : ℕ) : ℝ)

/-- **The base of K-C's backward induction.**  At `k = n` the chain is at `Δ`, whose classes
are `n` singletons, and (2.3) gives probability one -- as it must, since `ℛ_n = Δ` with
certainty. -/
theorem absoluteProb_top (n : ℕ) (hn : 1 ≤ n) :
    absoluteProb n n (Multiset.replicate n 1) = 1 := by
  have hfac : ((Multiset.replicate n 1).map Nat.factorial).prod = 1 := by
    simp [Multiset.map_replicate, Multiset.prod_replicate]
  have hn1 : ((n ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn2 : (((n - 1)! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold absoluteProb jumpCoeff
  rw [hfac, Nat.sub_self]
  simp only [Nat.factorial_zero, one_mul]
  push_cast
  field_simp

/-- **The prefactor recursion.**  Dividing K-C (2.3)'s coefficient at `k` by `d_k` and
multiplying by the `n - k + 1` available splittings gives the coefficient at `k - 1`.  This
is the arithmetic half of Kingman's displayed calculation. -/
theorem jumpCoeff_recursion {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    jumpCoeff n k * ((n - k + 1 : ℕ) : ℝ) / deathRate k = jumpCoeff n (k - 1) := by
  have hfacpos : ((n ! * (n - 1)! : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < n ! * (n - 1)! := Nat.mul_pos (Nat.factorial_pos n) (Nat.factorial_pos _)
    positivity
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hsub : n - (j + 2) + 1 = n - (j + 1) := by omega
  have hstep : (n - (j + 1))! = (n - (j + 1)) * (n - (j + 2))! := by
    have : n - (j + 1) = (n - (j + 2)) + 1 := by omega
    rw [this, Nat.factorial_succ]
    congr 1
    omega
  have hk2 : (j + 2 - 1) = j + 1 := by omega
  have hfj : (j + 2)! = (j + 2) * (j + 1)! := Nat.factorial_succ (j + 1)
  have hfj' : (j + 1)! = (j + 1) * j ! := Nat.factorial_succ j
  unfold jumpCoeff deathRate
  rw [hk2, hsub, hstep, hfj, hfj']
  push_cast
  field_simp
  ring

/-- Splitting a class of size `λ` into parts `ν` and `λ - ν` replaces `λ!` by
`ν! (λ-ν)!`, and the binomial coefficient puts it back. -/
theorem split_factorials {lam nu : ℕ} (h : nu ≤ lam) :
    ((lam.choose nu * nu ! * (lam - nu)! : ℕ) : ℝ) = (lam ! : ℕ) := by
  rw [Nat.choose_mul_factorial_mul_factorial h]

/-- **The combinatorial half of Kingman's calculation.**  Summing over every way to split one
class of size `λ` -- that is, over `ν = 1, …, λ-1` -- contributes exactly `(λ - 1)` copies of
`½ λ!`, because each term is `½ λ!` on the nose.  This is what makes K-C's final step
`Σ_l (λ_l - 1) = n - (k-1)` rather than a sum of unequal terms. -/
theorem inner_split_sum (lam : ℕ) (hlam : 1 ≤ lam) :
    ∑ nu ∈ Finset.Ico 1 lam, ((lam.choose nu * nu ! * (lam - nu)! : ℕ) : ℝ) / 2
      = ((lam : ℝ) - 1) * (lam ! : ℕ) / 2 := by
  have hterm : ∀ nu ∈ Finset.Ico 1 lam,
      ((lam.choose nu * nu ! * (lam - nu)! : ℕ) : ℝ) / 2 = (lam ! : ℕ) / 2 := by
    intro nu hnu
    rw [mem_Ico] at hnu
    rw [split_factorials (le_of_lt hnu.2)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico]
  have hcast : ((lam - 1 : ℕ) : ℝ) = (lam : ℝ) - 1 := by
    push_cast [Nat.cast_sub hlam]
    ring
  rw [nsmul_eq_mul, hcast]
  ring

/-- A constant factor comes out of a sum over classes. -/
theorem sum_map_mul_const (s : Multiset ℕ) (f : ℕ → ℝ) (c : ℝ) :
    (s.map (fun l => f l * c)).sum = (s.map f).sum * c := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons, Multiset.sum_cons]
      ring

/-- `Σ_l (λ_l - 1) = Σ_l λ_l - (number of classes)`: the identity K-C's induction closes
with, once the class sizes are known to be positive. -/
theorem sum_map_sub_one (s : Multiset ℕ) :
    (s.map (fun l => (l : ℝ) - 1)).sum = ((s.sum : ℕ) : ℝ) - (Multiset.card s : ℝ) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]
      push_cast
      ring

/-- **K-C's backward induction step, assembled.**

Take a state `η` with `k - 1` classes of sizes `lam`, summing to `n`.  Every state `ξ` with
`ξ ≺ η` arises by splitting one class of `η`; summing K-C (2.3) at `k` over all those
splittings, weighted by the jump probability `1/d_k` and by the number `½ C(λ_l, ν)` of
partitions realising each split, returns K-C (2.3) at `k - 1`.

The `½ C(λ_l, ν)` is carried as written -- see the module docstring: identifying it as the
number of set partitions realising a split is the step this file does not formalise.  What
IS formalised is that, granting it, the two sides agree exactly, which is the whole of
Kingman's displayed algebra. -/
theorem absoluteProb_recursion {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (lam : Multiset ℕ)
    (hcard : Multiset.card lam = k - 1) (hsum : lam.sum = n) :
    jumpProb k * jumpCoeff n k *
        (lam.map (fun l =>
          ((l : ℝ) - 1) * ((((lam.map Nat.factorial).prod : ℕ) : ℝ) / 2))).sum
      = absoluteProb n (k - 1) lam := by
  have hone : (1 : ℕ) ≤ k := le_trans one_le_two hk
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    push_cast [Nat.cast_sub hone]
    ring
  have hcastnk : ((n - k + 1 : ℕ) : ℝ) = (n : ℝ) - ((k : ℝ) - 1) := by
    have h1 : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
      push_cast [Nat.cast_sub hkn]
      ring
    push_cast [h1]
    ring
  -- Kingman's `Σ_l (λ_l - 1) = n - (k-1)`, with the class-size product factored out
  rw [sum_map_mul_const lam (fun l => (l : ℝ) - 1), sum_map_sub_one lam, hcard, hsum, hk1]
  have hrec := jumpCoeff_recursion hk hkn
  have hd : deathRate k ≠ 0 := deathRate_ne_zero hk
  unfold absoluteProb jumpProb
  rw [← hrec, hcastnk]
  field_simp
  ring

/-! ### The joint law

K-C (2.4) gives the `l`-step transition probability of the jump chain,

  `P{ℛ_l = η | ℛ_k = ξ} = ((k-l)! l! (l-1)! / (k! (k-1)!)) λ₁! ⋯ λ_l!`,

with `λ` now the sizes of the classes that `η` induces ON THE CLASSES of `ξ`.  It is K-C
(2.3) with `n` replaced by `k`: the jump chain restricted to the blocks of `ξ` is again a
jump chain, on `k` labels rather than `n`.  That is exactly what the definition below
records. -/

/-- K-C (2.4): the `l`-step jump-chain transition coefficient is the absolute-probability
coefficient with the sample size replaced by the current block count. -/
theorem jumpCoeff_transition (k l : ℕ) :
    jumpCoeff k l = (((k - l)! * l ! * (l - 1)! : ℕ) : ℝ) / ((k ! * (k - 1)! : ℕ) : ℝ) := by
  unfold jumpCoeff
  ring

end Coalescent

end Descent
