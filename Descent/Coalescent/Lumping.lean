/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Why the block count is a Markov chain in its own right

K-G section 5 asks when a function of a Markov chain is again Markov, and cites Rosenblatt's
criterion: `f(R_t)` is a Markov chain if, for `ξ ∈ 𝓔ₙ` and `v ≠ f(ξ)`,

  `Σ_{f(η) = v} q_{ξη}`                                                          K-G (5.1)

depends on `ξ` only through `f(ξ)`.  He then applies it to `f(R) = |R|`, the block count,
and concludes (5.3)-(5.4) that `|R_t|` is a pure death process with rates `d_r = ½r(r-1)`.

The criterion is easy to verify here because the corpus has already counted the covers.
`Σ_{f(η)=v} q_{ξη}` is the number of covers of `ξ` with `v` blocks; K-C (1.4) makes that
zero unless `v = |ξ| - 1` (`no_cover_of_blocks_ne`), and in that case it is all of them,
which `StateSpace.card_covers` says is `C(|ξ|, 2)` -- a function of `|ξ|` alone
(`lumping_criterion`).  So the criterion holds, and the rate it produces is exactly
`deathRate`.

This is the formal content of the sentence in K-G (5.3)-(5.4) that the corpus had been
taking for granted every time it wrote `d_k`: the block count is Markov BECAUSE the number
of available mergers depends on nothing but the block count.

## Main results

- `blocks_of_covers`: a cover has one block fewer.  K-C (1.4).
- `no_cover_of_blocks_ne`: so K-G (5.1) vanishes unless `v = |ξ| - 1`.
- `lumping_criterion`: **K-G (5.1) for the block count** -- states with equally many blocks
  have equally many covers.
- `lumping_rate_eq_deathRate`: and the rate is `d_k`.
-/

namespace Coalescent

/-- A cover has exactly one block fewer.  K-C (1.4). -/
theorem blocks_of_covers {n : ℕ} {ξ η : ER n} (h : Covers ξ η) : blocks η + 1 = blocks ξ := h.2

/-- **K-G (5.1) vanishes off the diagonal below.**  There is no transition from a state with `k`
blocks to one with anything but `k - 1`, so the lumped sum is zero unless `v = k - 1`.
This is Kingman's "the sum (5.1) is 0 unless `u = f(ξ) = v + 1`". -/
theorem no_cover_of_blocks_ne {n : ℕ} {ξ η : ER n} (h : Covers ξ η) {v : ℕ}
    (hv : v + 1 ≠ blocks ξ) : blocks η ≠ v := by
  intro hb
  exact hv (hb ▸ blocks_of_covers h)

/-- **The lumping criterion, K-G (5.1), for `f(R) = |R|`.**  Two states with the same number
of blocks have the same number of covers, so the lumped transition rate depends on the state
only through its block count -- which is Rosenblatt's condition, and hence the reason
`|R_t|` is a Markov chain at all.

The proof is `StateSpace.card_covers`: the count is `C(k,2)`, and `k` is all it sees. -/
theorem lumping_criterion {n : ℕ} (ξ ξ' : ER n) (h : blocks ξ = blocks ξ') :
    Nat.card {η : ER n // Covers ξ η} = Nat.card {η : ER n // Covers ξ' η} := by
  rw [card_covers, card_covers, h]

/-- **And the lumped rate is `d_k`.**  K-G (5.4): the death process's transition rate from
`r` to `r - 1` is `½r(r-1)`.  The corpus has written `deathRate` throughout on the strength
of this; here it is, as the total rate out of any state with that many blocks. -/
theorem lumping_rate_eq_deathRate {n : ℕ} (ξ : ER n) :
    (Nat.card {η : ER n // Covers ξ η} : ℝ) = deathRate (blocks ξ) :=
  card_covers_eq_deathRate ξ

/-- The absorbing case: a state with one block has no covers, so the lumped chain stops at
`1`.  K-G: "the state 1 is absorbing for `{D_t}`". -/
theorem no_covers_of_blocks_le_one {n : ℕ} [NeZero n] {ξ η : ER n} (h : blocks ξ ≤ 1) :
    ¬ Covers ξ η := by
  intro hcov
  have hb := blocks_of_covers hcov
  have : 0 < blocks η := blocks_pos η
  omega

end Coalescent

end Descent
