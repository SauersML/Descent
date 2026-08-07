/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.Deficit

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Building a pangenome graph performs `n - w` coalescences, all of them at time zero

`Descent.Pangenome.GraphCoalescent.Reduction` says the graph coalescent is Kingman's entered
at `w = Linkage.width s` lineages.  That leaves a question it does not ask: the panel had
`n`, so where did the other `n - w` go?

They were coalesced.  `graphKer s` is a coarsening of `⊥`, and
`Descent.Coalescent.Interpolation` says a coarsening IS a number of coalescences -- one that
does not depend on which pairs are chosen or in what order.  So the count is well defined,
and this file computes it.

**A pangenome graph performs exactly `n - w` coalescences, and it performs all of them
before the process starts.**

## Why that is a multiple-merger statement and not a bookkeeping one

Kingman's coalescent moves one pair at a time: every transition drops the block count by
exactly one, which is the whole content of K-C (1.4).  A graph build drops it by `n - w` at
once.  So unless `n - w ≤ 1` the construction is not a Kingman transition at all
(`covers_bot_graphKer_iff`), and unless the excess sits in a single fiber it is not even a
single multiple merger -- it is a SIMULTANEOUS one, several groups collapsing together,
which is the defining feature of a `Ξ`-coalescent rather than a `Λ`-coalescent
(`two_le_mergerDepth_of_two_fibers`).

The corpus already knows what that costs.  `Descent.Blindness.MultipleMergerBlindness`
records which statistics can distinguish a multiple-merger genealogy from Kingman's and
which are blind to the difference.  The consequence of this file is that **a pangenome graph
applies a simultaneous multiple merger to a sample regardless of what produced the sample**,
so a Kingman population observed through a graph presents the tip signature of a
multiple-merger one, and it is the blindness results that say when that can be detected.

## The depth is the excess of the fiber partition

`mergerDepth_eq_sum_excess` is the arithmetic identity that makes the count readable:

  `n - w = ∑_a (c_a - 1)`

summed over occupied graph states, where `c_a` is how many panel haplotypes occupy state
`a`.  Every fiber contributes its own excess and nothing else does.  A fiber of size one is
free; a fiber of size `c` costs `c - 1` coalescences.  This is the same partition that
`Descent.Pangenome.Linkage.Interface` weighs logarithmically as `identityLoss`, counted
instead of weighed, and `mergerDepth_eq_zero_iff` is the two measures agreeing on when the
graph did nothing.

## Main results

- `mergerDepth`: `n - w`, the number of coalescences the build performs.
- `coalescencePath_bot_graphKer`: **the theorem.**  A path of exactly that many coalescences
  carries `⊥` to `graphKer s`.
- `mergerDepth_unique`: and every such path has that length, so the number is a property of
  the graph and not of a reconstruction of it.
- `covers_bot_graphKer_iff`: the build is a single Kingman step exactly when `w + 1 = n`.
- `mergerDepth_eq_sum_excess`: the depth is the fiber partition's total excess.
- `two_le_mergerDepth_of_two_fibers`: two merged pairs force a simultaneous merger.
- `mergerDepth_eq_zero_iff`: the depth vanishes exactly when `identityLoss` does.
-/

namespace Descent.Pangenome.GraphCoalescent

open Finset

/-! ### The count -/

/-- **The number of coalescences a pangenome graph performs when it is built.**  The panel
brings `n` lineages and the graph starts with `w`; the difference was coalesced by the
builder rather than by the population.

Empirical status: DERIVED.  It is `Fintype.card` minus `Descent.Pangenome.Linkage.width`,
and `coalescencePath_bot_graphKer` is the theorem that the difference counts coalescences
rather than merely measuring a gap. -/
def mergerDepth {n : ℕ} (s : Fin n → Fin n) : ℕ := n - Linkage.width s

/-- **The theorem: a graph build is `n - w` coalescences.**  There is a path of exactly that
many covers from the coalescent's starting state to the state the graph reports before any
time has passed.

`Descent.Coalescent.Interpolation.exists_coalescencePath` supplies the path and
`Observation.blocks_graphKer` supplies the endpoint count; the content is that the two fit,
which is the sense in which a construction step and a population process are commensurable
at all. -/
theorem coalescencePath_bot_graphKer {n : ℕ} (s : Fin n → Fin n) :
    Coalescent.CoalescencePath (mergerDepth s) ⊥ (graphKer s) := by
  have hpath := Coalescent.exists_coalescencePath_sub (bot_le : (⊥ : Coalescent.ER n) ≤ graphKer s)
  rwa [Coalescent.blocks_bot, blocks_graphKer] at hpath

/-- **And the count does not depend on how the build is reconstructed.**  Any way of
realising the graph's merge as a sequence of coalescences uses exactly `mergerDepth s` of
them, whichever pairs it merges and in whatever order -- so the number is a property of the
graph rather than of a story told about it. -/
theorem mergerDepth_unique {n : ℕ} {s : Fin n → Fin n} {k : ℕ}
    (h : Coalescent.CoalescencePath k ⊥ (graphKer s)) : k = mergerDepth s :=
  Coalescent.coalescencePath_length_unique h (coalescencePath_bot_graphKer s)

/-- **The build is a single Kingman coalescence only in the degenerate case.**  K-C (1.4)
transitions drop one block; a graph build drops `n - w`.  The two agree exactly when the
interface merged one pair and nothing else. -/
theorem covers_bot_graphKer_iff {n : ℕ} (s : Fin n → Fin n) :
    Coalescent.Covers ⊥ (graphKer s) ↔ Linkage.width s + 1 = n := by
  constructor
  · intro h
    have hb := h.2
    rwa [Coalescent.blocks_bot, blocks_graphKer] at hb
  · intro h
    refine ⟨bot_le, ?_⟩
    rw [Coalescent.blocks_bot, blocks_graphKer]
    exact h

/-! ### The depth is the fiber partition's total excess

A fiber of size one costs nothing; a fiber of size `c` costs `c - 1`.  Summing over occupied
states gives `n - w`, and that is the whole of the arithmetic: nothing but the fiber sizes
enters. -/

/-- Every occupied graph state has at least one haplotype in it, which is what makes the
excess `c_a - 1` a subtraction that does not truncate. -/
theorem one_le_card_stateFiber {n : ℕ} {s : Fin n → Fin n} {a : Fin n}
    (ha : a ∈ Finset.univ.image s) : 1 ≤ (Linkage.stateFiber s a).card :=
  Linkage.card_stateFiber_pos ha

/-- **The merger depth is the total excess of the fiber partition**: `n - w = ∑_a (c_a - 1)`.

This is the identity that makes the count readable as a property of the merge rather than of
the two totals.  It is also the counted form of what `identityLoss` weighs: the same fiber
sizes, added instead of having their logarithms averaged. -/
theorem mergerDepth_eq_sum_excess {n : ℕ} (s : Fin n → Fin n) :
    mergerDepth s = ∑ a ∈ Finset.univ.image s, ((Linkage.stateFiber s a).card - 1) := by
  have hsplit : ∑ a ∈ Finset.univ.image s, (((Linkage.stateFiber s a).card - 1) + 1)
      = ∑ a ∈ Finset.univ.image s, (Linkage.stateFiber s a).card := by
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have := one_le_card_stateFiber ha
    omega
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    Linkage.sum_card_stateFiber] at hsplit
  have hw : (Finset.univ.image s).card = Linkage.width s := rfl
  have hn : Fintype.card (Fin n) = n := Fintype.card_fin n
  rw [hw, hn] at hsplit
  unfold mergerDepth
  omega

/-- **Two merged pairs force a simultaneous merger.**  If two distinct graph states each hold
at least two haplotypes, the build drops at least two blocks, so it is not a Kingman
transition -- and the two collapses are not nested, so it is not a single multiple merger
either.  That is a `Ξ`-event, and it is what a pangenome graph does whenever it merges in
more than one place. -/
theorem two_le_mergerDepth_of_two_fibers {n : ℕ} {s : Fin n → Fin n} {a b : Fin n}
    (ha : a ∈ Finset.univ.image s) (hb : b ∈ Finset.univ.image s) (hab : a ≠ b)
    (hca : 2 ≤ (Linkage.stateFiber s a).card) (hcb : 2 ≤ (Linkage.stateFiber s b).card) :
    2 ≤ mergerDepth s := by
  have hsub : ({a, b} : Finset (Fin n)) ⊆ Finset.univ.image s := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc'
    · exact ha
    · rw [Finset.mem_singleton.mp hc']
      exact hb
  have hle : ∑ c ∈ ({a, b} : Finset (Fin n)), ((Linkage.stateFiber s c).card - 1)
      ≤ ∑ c ∈ Finset.univ.image s, ((Linkage.stateFiber s c).card - 1) :=
    Finset.sum_le_sum_of_subset hsub
  have hpair : ∑ c ∈ ({a, b} : Finset (Fin n)), ((Linkage.stateFiber s c).card - 1)
      = ((Linkage.stateFiber s a).card - 1) + ((Linkage.stateFiber s b).card - 1) :=
    Finset.sum_pair hab
  rw [mergerDepth_eq_sum_excess]
  omega

/-! ### The depth and the identity loss vanish together

`Descent.Pangenome.GraphCoalescent.Deficit` proved that the transit-time deficit vanishes
exactly with `identityLoss`.  The merger depth is a third measure of the same thing, and it
agrees with both -- a count where one is an entropy and the other a time. -/

/-- **The graph performed no coalescences exactly when it forgot nothing.**

Assumes: `0 < n`, so that the panel is nonempty and `identityLoss` is not about junk. -/
theorem mergerDepth_eq_zero_iff {n : ℕ} {s : Fin n → Fin n} (hn : 0 < n) :
    mergerDepth s = 0 ↔ Linkage.identityLoss s = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hle : Linkage.width s ≤ n := by simpa using Linkage.width_le_card s
  constructor
  · intro h
    have hwn : Linkage.width s = n := by
      unfold mergerDepth at h
      omega
    exact identityLoss_eq_zero_of_width_eq hwn
  · intro h
    have hwn := width_eq_of_identityLoss_eq_zero hn h
    unfold mergerDepth
    omega

/-- The three measures in one statement: no coalescences performed, no time lost, no identity
forgotten.  Each is stated in a different currency -- a count, a duration, a number of nats --
and a pangenome graph satisfies one exactly when it satisfies all three.

Assumes: `0 < n`. -/
theorem mergerDepth_eq_zero_iff_transitDeficit {n : ℕ} {s : Fin n → Fin n} (hn : 0 < n) :
    mergerDepth s = 0 ↔ transitDeficit s = 0 :=
  (mergerDepth_eq_zero_iff hn).trans (transitDeficit_eq_zero_iff hn).symm

end Descent.Pangenome.GraphCoalescent
