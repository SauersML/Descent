/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Descent.Coalescent.Lambda

namespace Descent

/-!
# The shape of a simultaneous merger, and how `Λ` sits inside `Ξ`

`Descent.Coalescent.Xi` gives the state space the moves a `Ξ`-coalescent makes -- every
merger is an idempotent map on blocks -- and `Descent.Coalescent.Lambda` gives the rates a
`Λ`-coalescent attaches to the moves that merge one group.  Between them sits the language
those rates are indexed by, and this file supplies it.

A simultaneous merger is described up to relabelling by its **shape**: the multiset of sizes
of the groups that merge, each at least two, with the untouched blocks left implicit.
Schweinsberg (Electron. J. Probab. 5, 2000) indexes the `Ξ`-coalescent's rates by exactly
this data.  Two facts make the language work, and both are proved here:

* `shapeDrop`, the block count lost, is `Σ (kᵢ - 1)` -- one block survives each group.  For a
  single group this is `Xi.blocks_mergeIdem`'s drop and `MultiMerge.blocks_mergeSet`'s
  `|S| - 1`.
* `Λ`-coalescents are the single-group shapes (`IsLambdaShape`), and Kingman's are the
  single-group shapes of size two (`IsKingmanShape`).  So the three families are nested by a
  condition on shapes, not by three separate definitions.

What is still NOT here, and is what `Descent.Coalescent.Program` lists: the measure `Ξ` on
the infinite simplex and the integral formula assigning a rate to each shape.  That formula
needs the simplex, which needs an infinite-dimensional measure the corpus does not have.
What this file provides is the index set it would be a function on.

## Main results

- `MergerShape`, `IsShape`: the multiset of merging group sizes.
- `shapeDrop`: **the block count lost is `Σ(kᵢ - 1)`.**
- `IsLambdaShape`, `IsKingmanShape`: the nesting of the three families.
- `shapeDrop_lambda`, `shapeDrop_kingman`: their drops are `k - 1` and `1`.
-/

namespace Coalescent

/-- A merger shape: the sizes of the groups that merge simultaneously.  Blocks not in any
group are untouched and are left implicit. -/
abbrev MergerShape := Multiset ℕ

/-- A shape is legitimate when every group has at least two blocks: a "group" of one is not
a merger. -/
def IsShape (s : MergerShape) : Prop := ∀ k ∈ s, 2 ≤ k

/-- **The block count a shape costs.**  Each group of size `kᵢ` leaves one block behind, so
`kᵢ - 1` are lost; summing over groups gives the drop. -/
def shapeDrop (s : MergerShape) : ℕ := (s.map fun k ↦ k - 1).sum

@[simp] theorem shapeDrop_zero : shapeDrop 0 = 0 := rfl

theorem shapeDrop_cons (k : ℕ) (s : MergerShape) :
    shapeDrop (k ::ₘ s) = (k - 1) + shapeDrop s := by
  unfold shapeDrop
  rw [Multiset.map_cons, Multiset.sum_cons]

/-- **A `Λ`-coalescent's shapes are the single-group ones.**  Pitman's family merges one
group at a time; Schweinsberg's merges several.  The distinction is a condition on shapes,
not a different definition. -/
def IsLambdaShape (s : MergerShape) : Prop := ∃ k, 2 ≤ k ∧ s = {k}

/-- **Kingman's shapes are the single-group shapes of size two.**  Which is K-C (1.3) said in
this language, and makes the nesting Kingman ⊂ `Λ` ⊂ `Ξ` a chain of conditions on one index
set. -/
def IsKingmanShape (s : MergerShape) : Prop := s = {2}

theorem IsKingmanShape.isLambdaShape {s : MergerShape} (h : IsKingmanShape s) :
    IsLambdaShape s := ⟨2, le_refl 2, h⟩

theorem IsLambdaShape.isShape {s : MergerShape} (h : IsLambdaShape s) : IsShape s := by
  obtain ⟨k, hk, rfl⟩ := h
  intro j hj
  rw [Multiset.mem_singleton] at hj
  rw [hj]
  exact hk

/-- **A `Λ`-merger of `k` blocks costs `k - 1`**, matching
`MultiMerge.blocks_mergeSet` exactly: `|S|` blocks become one. -/
theorem shapeDrop_lambda {s : MergerShape} {k : ℕ} (h : s = {k}) : shapeDrop s = k - 1 := by
  rw [h]
  unfold shapeDrop
  simp

/-- **A Kingman merger costs one block**, which is K-C (1.4). -/
theorem shapeDrop_kingman {s : MergerShape} (h : IsKingmanShape s) : shapeDrop s = 1 := by
  rw [shapeDrop_lambda h]

/-- The drop is additive over groups, which is what makes simultaneous mergers
simultaneous: `r` groups merging at once cost what they would cost one at a time. -/
theorem shapeDrop_add (s t : MergerShape) : shapeDrop (s + t) = shapeDrop s + shapeDrop t := by
  unfold shapeDrop
  rw [Multiset.map_add, Multiset.sum_add]

/-- A shape with no groups costs nothing: the `Ξ`-coalescent's trivial move, which is
`Xi.mergeIdem_id`. -/
theorem shapeDrop_eq_zero_of_empty {s : MergerShape} (h : s = 0) : shapeDrop s = 0 := by
  rw [h, shapeDrop_zero]

/-- Every legitimate shape with at least one group costs at least one block: a merger that
loses nothing is not a merger. -/
theorem shapeDrop_pos {s : MergerShape} (hs : IsShape s) (hne : s ≠ 0) : 0 < shapeDrop s := by
  obtain ⟨k, hk⟩ := Multiset.exists_mem_of_ne_zero hne
  have hk2 : 2 ≤ k := hs k hk
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hk
  rw [shapeDrop_cons]
  omega

end Coalescent

end Descent
