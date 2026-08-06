/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Descent.Coalescent.Mutation
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The Ohta-Kimura recursion is the coalescent's backward equation

K-G section 3 derives, for the generalized Ohta-Kimura model, a recursion for the joint
characteristic function `ψ_n` of `n` sampled individuals (3.6):

  `{½n(n-1) + Σ_j φ(u_j)} ψ_n(u_1, …, u_n) = Σ_{1 ≤ j < k ≤ n} ψ_{n-1}(…, u_j + u_k, …)`.

Kingman then says this "is exactly what one would expect from the theory of the
`n`-coalescent": the left side's `½n(n-1)` is the total rate out of the starting state, the
right side has one term per pair of lineages that could merge, and the `φ` terms are the
mutation.  This file records the arithmetic of that remark, which is a statement about the
state space and not about characteristic functions:

  the number of terms on the right IS the coefficient on the left,

because both are `Descent.Coalescent.Rates.deathRate n`.  The right side counts the covers
of `Δ` -- each merger of two of the `n` singletons -- and
`StateSpace.card_covers_eq_deathRate` says there are `d_n` of them.  Balancing a backward
equation is exactly this: the rate leaving a state equals the total rate into its
successors.

## Main results

- `card_covers_delta`: the covers of `Δ` number `C(n,2)`.
- `ohtaKimura_rate_balance`: **the (3.6) balance** -- the number of merger terms on the
  right equals the coefficient `½n(n-1)` on the left.
- `ewensDenominator_succ`: the `(θ+1)⋯(θ+n-1)` of (3.8) grows by one factor per sample,
  which is the same recursion read off the mutation side.
-/

namespace Coalescent

/-- The covers of `Δ` are the mergers of two of the `n` sampled lineages, and there are
`C(n,2)` of them. -/
theorem card_covers_delta (n : ℕ) :
    Nat.card {η : ER n // Covers (Delta n) η} = n.choose 2 := by
  rw [card_covers, blocks_bot]

/-- **The (3.6) balance.**  The right-hand side of the Ohta-Kimura recursion has one term for
each pair of lineages that can merge, and the left-hand side's coefficient is `½n(n-1)`.
They agree, because both count the covers of `Δ`.

That is Kingman's "exactly what one would expect from the theory of the `n`-coalescent",
made arithmetic: (3.6) is a backward equation, and a backward equation balances the rate out
of a state against the rates into its successors. -/
theorem ohtaKimura_rate_balance (n : ℕ) :
    (Nat.card {η : ER n // Covers (Delta n) η} : ℝ) = deathRate n := by
  have h := card_covers_eq_deathRate (Delta n)
  rwa [blocks_bot] at h

/-- The mutation side's recursion: each additional sampled individual contributes one factor
to the Ewens denominator of (3.8), matching the one extra lineage the genealogy side gains.
`Mutation.ewensDenominator` is `(θ+1)⋯(θ+n-1)`. -/
theorem ewensDenominator_succ (θ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ewensDenominator θ (n + 1) = ewensDenominator θ n * (θ + (n : ℝ)) := by
  unfold ewensDenominator
  rw [show n + 1 - 1 = (n - 1) + 1 from by omega, Finset.prod_range_succ]
  congr 2
  have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    push_cast [Nat.cast_sub hn]
    ring
  rw [this]
  ring

/-- At the smallest informative sample the balance is `d_2 = 1`: a single pair, a single
merger, unit rate.  K-C (1.3)'s normalisation, seen from the mutation side. -/
theorem ohtaKimura_rate_balance_two :
    (Nat.card {η : ER 2 // Covers (Delta 2) η} : ℝ) = 1 := by
  rw [ohtaKimura_rate_balance, deathRate_two]

end Coalescent

end Descent
