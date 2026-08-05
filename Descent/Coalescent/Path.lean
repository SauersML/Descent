/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Descent.Coalescent.Rates
import Mathlib.Tactic

namespace Descent

/-!
# The coalescent path, pathwise

Kingman (1982), *On the genealogy of large populations* (**K-G**), section 6, builds an
`n`-coalescent by combining a pure death process with an independent jump chain:
`R_t^{(n)} = ℛ^{(n)}_{D(n,t)}` (6.5), with `|R_t^{(n)}| = D(n,t)` (6.6).  K-C Theorem 1 is
the converse -- that any `n`-coalescent factorises this way, with the two factors
independent.

`Descent.Coalescent.Program` lists both as open, and gives the reason: the corpus has no
continuous-time process.  This file supplies the half of that which is not probability at
all.  Given a descending sequence of states and a sequence of holding times -- one
trajectory, not a law -- the path `t ↦ R_t` is a definition, and everything Kingman asserts
about a single trajectory is a theorem about it:

* the block count `D(n,t)` is a step function of `t`, nonincreasing (`blockCountAt_antitone`);
* it starts at `n` (`blockCountAt_zero`) and reaches `1` at the transit time
  (`blockCountAt_of_transit_le`), which is K-C (1.11);
* `|R_t| = D(n,t)`, K-G (6.6) (`blocks_pathState`);
* `R_t` is nondecreasing in the coarsening order (`pathState_mono`) -- lineages merge and
  never unmerge, K-G (2.6).

What this does NOT give, and what keeps items 4 and 5 open, is the LAW.  Kingman's
construction takes the jump chain and the holding times independent and derives the
`n`-coalescent's finite-dimensional distributions; here they are arguments.  Supplying them
as a product measure would make independence true by construction -- which is Theorem 3's
direction -- and Theorem 1's direction, that an arbitrary `n`-coalescent factorises, would
still need the general theory of jump chains.  Both are about measures on this path space,
and the path space is what was missing.

## Main results

- `descentTime`: when the path first has `k` blocks, K-G (6.1).
- `blockCountAt`: the pure death process `D(n,t)` as a step function.
- `blockCountAt_zero`, `blockCountAt_antitone`, `blockCountAt_of_transit_le`.
- `pathState`: `R_t = ℛ_{D(n,t)}`, K-G (6.5).
- `blocks_pathState`: K-G (6.6).
- `pathState_mono`: the path only coarsens.
-/

namespace Coalescent

open Finset

/-- **K-G (6.1): when the path first has `k` blocks.**  The holding time `hold j` is the time
spent with `j` blocks, so reaching `k` takes the sum of the holds above `k`. -/
noncomputable def descentTime (n : ℕ) (hold : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico (k + 1) (n + 1), hold j

@[simp] theorem descentTime_self (n : ℕ) (hold : ℕ → ℝ) : descentTime n hold n = 0 := by
  simp [descentTime]

/-- The transit time `T_n` of K-C (1.11): when the path reaches its absorbing state. -/
noncomputable def transitTime (n : ℕ) (hold : ℕ → ℝ) : ℝ := descentTime n hold 1

/-- Reaching fewer blocks takes longer. -/
theorem descentTime_antitone (n : ℕ) {hold : ℕ → ℝ} (hpos : ∀ j, 0 ≤ hold j) {k k' : ℕ}
    (h : k ≤ k') : descentTime n hold k' ≤ descentTime n hold k := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hpos j
  intro j hj
  rw [mem_Ico] at hj ⊢
  exact ⟨le_trans (by omega) hj.1, hj.2⟩

theorem descentTime_nonneg (n : ℕ) {hold : ℕ → ℝ} (hpos : ∀ j, 0 ≤ hold j) (k : ℕ) :
    0 ≤ descentTime n hold k :=
  Finset.sum_nonneg fun j _ => hpos j

/-- **The pure death process `D(n,t)` of K-G (6.2), as a step function of one trajectory.**
The count is one more than the number of levels not yet reached. -/
noncomputable def blockCountAt (n : ℕ) (hold : ℕ → ℝ) (t : ℝ) : ℕ :=
  ((Finset.Icc 1 n).filter fun k => t < descentTime n hold k).card + 1

/-- **The death process only descends.**  K-G: `D(n,t)` is nonincreasing in `t`. -/
theorem blockCountAt_antitone (n : ℕ) (hold : ℕ → ℝ) {t t' : ℝ} (h : t ≤ t') :
    blockCountAt n hold t' ≤ blockCountAt n hold t := by
  unfold blockCountAt
  have hsub : ((Finset.Icc 1 n).filter fun k => t' < descentTime n hold k)
      ⊆ ((Finset.Icc 1 n).filter fun k => t < descentTime n hold k) := by
    intro k hk
    rw [mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_le_of_lt h hk.2⟩
  exact Nat.add_le_add_right (Finset.card_le_card hsub) 1

/-- At a nonnegative time the count never exceeds the sample size: the level `n` is reached
at time zero, so it is never among the levels still to come. -/
theorem blockCountAt_le (n : ℕ) {hold : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hn : 1 ≤ n) :
    blockCountAt n hold t ≤ n := by
  classical
  unfold blockCountAt
  have hsub : ((Finset.Icc 1 n).filter fun k => t < descentTime n hold k)
      ⊆ Finset.Icc 1 (n - 1) := by
    intro k hk
    rw [mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, hkn⟩, hlt⟩ := hk
    rw [mem_Icc]
    refine ⟨hk1, ?_⟩
    by_contra hcon
    have hkeq : k = n := by omega
    rw [hkeq, descentTime_self] at hlt
    linarith
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  omega

theorem one_le_blockCountAt (n : ℕ) (hold : ℕ → ℝ) (t : ℝ) : 1 ≤ blockCountAt n hold t := by
  unfold blockCountAt
  omega

/-- **The path starts with every lineage separate.**  K-C (1.1): `R_0 = Δ`, in block-count
form `D(n,0) = n`.  Strictly positive holds are what make this true -- with a zero hold the
path passes through a level instantly, which is exactly the degeneracy K-G's exponential
holding times exclude almost surely. -/
theorem blockCountAt_zero (n : ℕ) {hold : ℕ → ℝ} (hn : 1 ≤ n)
    (hpos : ∀ j, 2 ≤ j → j ≤ n → 0 < hold j) :
    blockCountAt n hold 0 = n := by
  classical
  have hset : ((Finset.Icc 1 n).filter fun k => (0 : ℝ) < descentTime n hold k)
      = Finset.Icc 1 (n - 1) := by
    ext k
    rw [mem_filter, mem_Icc, mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hkn⟩, hlt⟩
      refine ⟨hk1, ?_⟩
      by_contra hcon
      have hkeq : k = n := by omega
      rw [hkeq, descentTime_self] at hlt
      linarith
    · rintro ⟨hk1, hkn⟩
      refine ⟨⟨hk1, by omega⟩, ?_⟩
      have hmem : k + 1 ∈ Finset.Ico (k + 1) (n + 1) := by
        rw [mem_Ico]
        omega
      refine lt_of_lt_of_le (hpos (k + 1) (by omega) (by omega)) ?_
      refine Finset.single_le_sum (f := hold) (fun j hj => ?_) hmem
      rw [mem_Ico] at hj
      exact le_of_lt (hpos j (by omega) (by omega))
  unfold blockCountAt
  rw [hset, Nat.card_Icc]
  omega

/-- **The path is absorbed at the transit time.**  K-C (1.11): after `T_n` the state is `Θ`,
which in block-count form is `D(n,t) = 1`. -/
theorem blockCountAt_of_transit_le (n : ℕ) {hold : ℕ → ℝ} (hpos : ∀ j, 0 ≤ hold j) {t : ℝ}
    (ht : transitTime n hold ≤ t) : blockCountAt n hold t = 1 := by
  classical
  have hempty : ((Finset.Icc 1 n).filter fun k => t < descentTime n hold k) = ∅ := by
    refine Finset.filter_false_of_mem fun k hk => ?_
    rw [mem_Icc] at hk
    have hle : descentTime n hold k ≤ transitTime n hold :=
      descentTime_antitone n hpos hk.1
    linarith
  unfold blockCountAt
  rw [hempty, Finset.card_empty]

/-- **Once a level is reached, the count is at most that level.**  Half of the pathwise
content of K-C (2.6): `D(n,t) ≤ k` exactly when the time to descend to `k` has elapsed. -/
theorem blockCountAt_le_of_descentTime_le (n : ℕ) {hold : ℕ → ℝ} (hpos : ∀ j, 0 ≤ hold j)
    {t : ℝ} {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (ht : descentTime n hold k ≤ t) :
    blockCountAt n hold t ≤ k := by
  classical
  unfold blockCountAt
  have hsub : ((Finset.Icc 1 n).filter fun j => t < descentTime n hold j)
      ⊆ Finset.Icc 1 (k - 1) := by
    intro j hj
    rw [mem_filter, mem_Icc] at hj
    obtain ⟨⟨hj1, hjn⟩, hlt⟩ := hj
    rw [mem_Icc]
    refine ⟨hj1, ?_⟩
    by_contra hcon
    have hkj : k ≤ j := by omega
    have := descentTime_antitone n hpos hkj
    linarith
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  omega

/-- **Before a level is reached, the count is above it.**  The other half: `D(n,t) > k` while
the descent to `k` is still in progress. -/
theorem lt_blockCountAt_of_lt_descentTime (n : ℕ) {hold : ℕ → ℝ} (hpos : ∀ j, 0 ≤ hold j)
    {t : ℝ} {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (ht : t < descentTime n hold k) :
    k < blockCountAt n hold t := by
  classical
  unfold blockCountAt
  have hsub : Finset.Icc 1 k ⊆ ((Finset.Icc 1 n).filter fun j => t < descentTime n hold j) := by
    intro j hj
    rw [mem_Icc] at hj
    rw [mem_filter, mem_Icc]
    refine ⟨⟨hj.1, le_trans hj.2 hkn⟩, ?_⟩
    exact lt_of_lt_of_le ht (descentTime_antitone n hpos hj.2)
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  omega

/-- **The death process, pinned down.**  `D(n,t) = k` exactly when the descent to `k` has
happened and the descent to `k - 1` has not -- which is K-C (2.6) read pathwise, before any
distribution is attached to the holding times. -/
theorem blockCountAt_eq (n : ℕ) {hold : ℕ → ℝ} (hpos : ∀ j, 0 ≤ hold j) {t : ℝ} {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n) (hle : descentTime n hold k ≤ t)
    (hlt : ∀ j, 1 ≤ j → j < k → t < descentTime n hold j) :
    blockCountAt n hold t = k := by
  refine le_antisymm (blockCountAt_le_of_descentTime_le n hpos hk1 hkn hle) ?_
  rcases Nat.eq_or_lt_of_le hk1 with hk | hk
  · rw [← hk]
    exact one_le_blockCountAt n hold t
  · have hprev : k - 1 < blockCountAt n hold t :=
      lt_blockCountAt_of_lt_descentTime n hpos (by omega) (by omega)
        (hlt (k - 1) (by omega) (by omega))
    omega

/-! ### The path itself

With the block count in hand, the path is Kingman's `R_t = ℛ_{D(n,t)}` (K-G (6.5)) -- the
jump chain read at the level the death process has reached. -/

/-- Finitely many holding times, read as a sequence.  `Descent.Coalescent.Law` puts a measure
on `Fin m → ℝ` -- finitely many coordinates, which is all an `n`-coalescent needs -- while the
path construction indexes holds by block count; this is the bridge, and it is what lets the
two compose. -/
noncomputable def extendHold {m : ℕ} (hold : Fin m → ℝ) : ℕ → ℝ :=
  fun j => if hj : j < m then hold ⟨j, hj⟩ else 0

theorem extendHold_nonneg {m : ℕ} {hold : Fin m → ℝ} (h : ∀ i, 0 ≤ hold i) (j : ℕ) :
    0 ≤ extendHold hold j := by
  unfold extendHold
  by_cases hj : j < m
  · rw [dif_pos hj]
    exact h _
  · rw [dif_neg hj]

theorem extendHold_apply {m : ℕ} (hold : Fin m → ℝ) (i : Fin m) :
    extendHold hold (i : ℕ) = hold i := by
  unfold extendHold
  rw [dif_pos i.isLt]

/-- **K-G (6.5): the coalescent path of one trajectory.**  `chain k` is the state with `k`
blocks; the path reads it off at the current block count.

Empirical status: NOT AN EMPIRICAL CLAIM.  This is Kingman's construction, with the jump
chain and the holding times supplied rather than drawn -- the law is exactly what this file
does not provide. -/
noncomputable def pathState (n : ℕ) (chain : ℕ → ER n) (hold : ℕ → ℝ) (t : ℝ) : ER n :=
  chain (blockCountAt n hold t)

/-- A descending chain of states coarsens as the block count falls. -/
theorem chain_antitone {n : ℕ} {chain : ℕ → ER n}
    (hchain : ∀ k, 1 ≤ k → k < n → Blindness.Covers (chain (k + 1)) (chain k)) {k k' : ℕ}
    (h1 : 1 ≤ k) (hk : k ≤ k') (hk' : k' ≤ n) : chain k' ≤ chain k := by
  induction k' with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · have hm : k ≤ m := by omega
        have hmn : m < n := by omega
        have h1m : 1 ≤ m := by omega
        exact le_trans (hchain m h1m hmn).1 (ih hm (by omega))
      · have : k = m + 1 := by omega
        rw [this]

/-- **K-G (6.6): `|R_t| = D(n,t)`.**  The path's block count is the death process, which is
the compatibility that makes the factorisation a factorisation. -/
theorem blocks_pathState (n : ℕ) {chain : ℕ → ER n} {hold : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hn : 1 ≤ n) (hblocks : ∀ k, 1 ≤ k → k ≤ n → blocks (chain k) = k) :
    blocks (pathState n chain hold t) = blockCountAt n hold t :=
  hblocks _ (one_le_blockCountAt n hold t) (blockCountAt_le n ht hn)

/-- **The path only coarsens.**  K-G (2.6): `R_s ⊆ R_t` for `s ≤ t` -- lineages merge and
never unmerge.  It follows from the chain descending and the count falling. -/
theorem pathState_mono (n : ℕ) {chain : ℕ → ER n} {hold : ℕ → ℝ} (hn : 1 ≤ n)
    (hchain : ∀ k, 1 ≤ k → k < n → Blindness.Covers (chain (k + 1)) (chain k)) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    pathState n chain hold s ≤ pathState n chain hold t := by
  unfold pathState
  exact chain_antitone hchain (one_le_blockCountAt n hold t)
    (blockCountAt_antitone n hold hst) (blockCountAt_le n hs hn)

/-- At time zero the path is `Δ`, provided the chain starts there. -/
theorem pathState_zero (n : ℕ) {chain : ℕ → ER n} {hold : ℕ → ℝ} (hn : 1 ≤ n)
    (hpos : ∀ j, 2 ≤ j → j ≤ n → 0 < hold j) (hstart : chain n = Delta n) :
    pathState n chain hold 0 = Delta n := by
  unfold pathState
  rw [blockCountAt_zero n hn hpos, hstart]

/-- After the transit time the path is at its absorbing state, provided the chain ends
there.  K-C (1.10)-(1.11). -/
theorem pathState_of_transit_le (n : ℕ) {chain : ℕ → ER n} {hold : ℕ → ℝ}
    (hpos : ∀ j, 0 ≤ hold j) (hend : chain 1 = Theta n) {t : ℝ}
    (ht : transitTime n hold ≤ t) : pathState n chain hold t = Theta n := by
  unfold pathState
  rw [blockCountAt_of_transit_le n hpos ht, hend]

end Coalescent

end Descent
