/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.MultiMerge
import Mathlib.Tactic

namespace Descent

/-!
# Simultaneous multiple mergers: every coalescent move is an idempotent map on blocks

Schweinsberg, *Coalescents with simultaneous multiple collisions* (Electron. J. Probab. 5,
2000), extends Pitman's family once more: several groups of blocks may merge at the same
instant, each group into one block.  `Descent.Coalescent.MultiMerge` supplies one group;
this file supplies all of them at once, and in doing so finds the general shape of a
coalescent move.

A simultaneous multiple merger is exactly an **idempotent map on blocks**.  Choosing, for
each block, the block it ends up in -- with the requirement that a block chosen as a
destination stays put -- is the same data as a partition of the block set into merging
groups with a representative each.  So:

  `mergeIdem ξ f = Setoid.ker (f ∘ ⟦·⟧)`,

and `blocks_mergeIdem` says the resulting block count is `|range f|`: one block per group,
which is the whole content of "several groups merge simultaneously".

Everything earlier is an instance.  `MultiMerge.mergeSet` is `mergeIdem` at the fold that
sends `S` to `a` (`mergeSet_eq_mergeIdem`), and `StateSpace.merge` is `mergeIdem` at the
fold that sends `b` to `a`.  The block-count theorems of both files follow from
`blocks_mergeIdem` and a range computation, which is why this file is short: the general
statement is easier than either special case, because the range is the answer rather than
something to be computed around.

What is not here: the `Ξ` measure on the infinite simplex and the rates it assigns to these
moves.  This is the state space's half.

## Main results

- `mergeIdem`: a simultaneous multiple merger, as an idempotent map on blocks.
- `blocks_mergeIdem`: **the block count afterwards is the number of groups.**
- `mergeSet_eq_mergeIdem`, `merge_eq_mergeIdem`: the earlier merges are instances.
- `blocks_mergeIdem_le`: a merger never increases the block count.
-/

namespace Coalescent

open scoped Classical

/-- **A simultaneous multiple merger.**  `f` sends each block to the block it ends up in;
the merger relates two sample points when their blocks share a destination.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is the general form of an edge in the
coalescent's transition graph -- Kingman's binary merge, Pitman's `k`-merge and
Schweinsberg's simultaneous merge are the cases where `f` has one non-trivial fibre of size
two, one of size `k`, and several respectively. -/
noncomputable def mergeIdem {n : ℕ} (ξ : ER n) (f : Quotient ξ → Quotient ξ) : ER n :=
  Setoid.ker fun x ↦ f (Quotient.mk ξ x)

/-- Merging coarsens, whatever the merger. -/
theorem le_mergeIdem {n : ℕ} (ξ : ER n) (f : Quotient ξ → Quotient ξ) :
    ξ ≤ mergeIdem ξ f := by
  intro x y hxy
  show f (Quotient.mk ξ x) = f (Quotient.mk ξ y)
  exact congrArg f (Quotient.sound hxy)

/-- **The block count afterwards is the number of groups.**

This is the one theorem the whole file exists for, and it is three lines: the quotient by a
kernel is the range of the map, and `⟦·⟧` is surjective, so the range of `f ∘ ⟦·⟧` is the
range of `f`.  Every block-count theorem in this group -- `StateSpace.blocks_merge`,
`MultiMerge.blocks_mergeSet` -- is this plus an arithmetic computation of `|range f|`. -/
theorem blocks_mergeIdem {n : ℕ} (ξ : ER n) (f : Quotient ξ → Quotient ξ) :
    blocks (mergeIdem ξ f) = Nat.card (Set.range f) := by
  unfold blocks mergeIdem
  rw [Nat.card_congr (Setoid.quotientKerEquivRange _)]
  refine Nat.card_congr (Equiv.setCongr ?_)
  ext c
  simp only [Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Quotient.mk ξ x, rfl⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨x, hx⟩ := quotient_mk_surjective ξ d
    exact ⟨x, by rw [hx]⟩

/-- A merger never increases the block count: the range of a map on a finite type is no
bigger than the type. -/
theorem blocks_mergeIdem_le {n : ℕ} (ξ : ER n) (f : Quotient ξ → Quotient ξ) :
    blocks (mergeIdem ξ f) ≤ blocks ξ := by
  classical
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  rw [blocks_mergeIdem]
  unfold blocks
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_range_le f

/-- `MultiMerge.mergeSet` is the case where `f` folds `S` onto `a`. -/
theorem mergeSet_eq_mergeIdem {n : ℕ} (ξ : ER n) (S : Finset (Quotient ξ)) (a : Quotient ξ) :
    mergeSet ξ S a = mergeIdem ξ (mergeSetMap ξ S a) := rfl

/-- `StateSpace.merge` is the case where `f` folds `b` onto `a`. -/
theorem merge_eq_mergeIdem {n : ℕ} (ξ : ER n) (a b : Quotient ξ) :
    merge ξ a b = mergeIdem ξ (mergeMap ξ a b) := rfl

/-- **The block count drops by the number of blocks that lost their identity.**  Written as a
subtraction-free identity: the blocks that survive are the range, and the rest were absorbed
into it. -/
theorem blocks_mergeIdem_add_card_absorbed {n : ℕ} (ξ : ER n) (f : Quotient ξ → Quotient ξ) :
    blocks (mergeIdem ξ f) + (blocks ξ - blocks (mergeIdem ξ f)) = blocks ξ := by
  have h := blocks_mergeIdem_le ξ f
  omega

/-- A merger that moves nothing changes nothing: the identity map fixes the state, which is
the `Ξ`-coalescent's "no collision" and the reason the family contains a trivial move. -/
theorem mergeIdem_id {n : ℕ} (ξ : ER n) : mergeIdem ξ id = ξ := by
  refine Setoid.ext fun x y ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact Quotient.exact (show Quotient.mk ξ x = Quotient.mk ξ y from h)
  · show id (Quotient.mk ξ x) = id (Quotient.mk ξ y)
    exact congrArg _ (Quotient.sound h)

end Coalescent

end Descent
