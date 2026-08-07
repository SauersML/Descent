/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Xi
import Descent.Coalescent.MultiMerge
import Descent.Coalescent.StateSpace
import Descent.Core.Ratios
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

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

/-- **The pairwise merger is a Kingman shape.**  The witness the nesting needs: without one
concrete shape in the class, `IsKingmanShape` is a hypothesis no object is known to satisfy
and everything proved under it is vacuous.  This is K-C (1.3)'s own move -- two blocks
coalesce and no others -- so the class is inhabited by the merger it was written to name. -/
theorem isKingmanShape_pair : IsKingmanShape ({2} : MergerShape) := rfl

/-- **Every single group of two or more is a `Λ`-shape**, so that family is inhabited at each
group size rather than only at the Kingman end. -/
theorem isLambdaShape_singleton {k : ℕ} (hk : 2 ≤ k) : IsLambdaShape ({k} : MergerShape) :=
  ⟨k, hk, rfl⟩

/-- **A `Λ`-merger of `k` blocks costs `k - 1`**, matching
`MultiMerge.blocks_mergeSet` exactly: `|S|` blocks become one. -/
theorem shapeDrop_lambda {s : MergerShape} {k : ℕ} (h : s = {k}) : shapeDrop s = k - 1 := by
  rw [h]
  unfold shapeDrop
  simp

/-- **A Kingman merger costs one block**, which is K-C (1.4). -/
theorem shapeDrop_kingman {s : MergerShape} (h : IsKingmanShape s) : shapeDrop s = 1 := by
  rw [shapeDrop_lambda h]

/-- **A pairwise merger costs exactly one block**, the nesting's two ends met on a witness:
`shapeDrop_kingman` applied to `isKingmanShape_pair` rather than to an assumption. -/
theorem shapeDrop_pair : shapeDrop ({2} : MergerShape) = 1 :=
  shapeDrop_kingman isKingmanShape_pair

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

/-! ### The shape language against the state space it indexes -/

/-- **A shape's cost is the block count the merger it names actually loses.**

The header says `shapeDrop` "for a single group is `MultiMerge.blocks_mergeSet`'s `|S| - 1`",
and until this theorem that was a claim about two expressions that had never been put in one
statement. `MergerShape` is an index set, so nothing about it is forced by the state space
unless something says so; a `shapeDrop` off by one, or reading `|S|` where it means `|S| - 1`,
would leave every theorem in this file true and every rate attached to a shape wrong. Here
the two meet: merging `S` into `a` leaves `blocks ξ - shapeDrop {|S|}` blocks, as naturals,
with no subtraction to truncate on either side. -/
theorem blocks_mergeSet_add_shapeDrop {n : ℕ} (ξ : ER n) {S : Finset (Quotient ξ)}
    {a : Quotient ξ} (ha : a ∈ S) :
    blocks (mergeSet ξ S a) + shapeDrop ({S.card} : MergerShape) = blocks ξ := by
  have hd : shapeDrop ({S.card} : MergerShape) = S.card - 1 := shapeDrop_lambda rfl
  rw [hd]
  exact blocks_mergeSet ξ ha

/-- **A legitimate single-group shape costs at least one block of the state it acts on**, so
the index set contains no shape naming a move that changes nothing.  `shapeDrop_pos` says the
cost is positive; this says the cost is positive AND is the cost of a merger. -/
theorem blocks_mergeSet_lt_of_isLambdaShape {n : ℕ} (ξ : ER n) {S : Finset (Quotient ξ)}
    {a : Quotient ξ} (ha : a ∈ S) (hS : IsLambdaShape ({S.card} : MergerShape)) :
    blocks (mergeSet ξ S a) < blocks ξ := by
  have hdrop : 0 < shapeDrop ({S.card} : MergerShape) :=
    shapeDrop_pos hS.isShape (by simp)
  have hadd := blocks_mergeSet_add_shapeDrop ξ ha
  omega

end Coalescent

end Descent
