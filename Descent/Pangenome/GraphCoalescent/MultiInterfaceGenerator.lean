/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiInterfaceLoads

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The lumped generator of several interfaces, with nothing assumed

`MultiInterfaceClosure.card_blockMergers_eq` counts the ordered pairs of true ancestral blocks
whose merger leads to a lumped target as `lumpedMergerCount` of the cell loads, for an outcome map
on the cells of the common refinement that it takes as given. `MultiInterfaceLoads` proves that
the lumped state after a merger depends only on the lumped state before it and the two cells. This
module builds the outcome map from the mergers themselves and so removes the hypothesis.

`blockCell_mk` reads the cell of a true block off any of its individuals, and
`cellLoad_blockCell_mk` identifies the cell loads counted in `MultiInterfaceClosure` with the loads
`cellLoadAt` carried by the lumped state. `mergerOutcome s ξ κ κ'` is the lumped state after merging
two distinct true blocks lying in the cells `κ` and `κ'`, and the current lumped state when the two
cells hold no such pair, in which case it enters no count.
`multiState_merge_eq_mergerOutcome` shows that every merger of two distinct true blocks lands on the
outcome of its two cells, which is where `MultiInterfaceLoads.multiState_merge_eq_of_cells`
enters. `card_blockMergers_eq_lumpedMergerCount` is the closure as a statement about the lumped
generator: the ordered pairs of distinct true blocks whose merger leads to `target` number
`lumpedMergerCount` of the cell loads for that outcome map.

## Empirical status

None. The bodies here are counts of equivalence classes on a finite set: every statement is an
identity between cardinalities of sets of blocks, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.MultiInterfaceGenerator

open Coalescent Finset MultiInterfaceClosure MultiInterfaceLoads
open scoped Classical

noncomputable section

variable {n m : ℕ}

/-- The cell of a true block is the class of any of its individuals. -/
theorem blockCell_mk (s : Fin m → Fin n → Fin n) (ξ : ER n) (x : Fin n) :
    blockCell s ξ (Quotient.mk ξ x) = Quotient.mk (commonRefinement s ξ) x :=
  rfl

/-- **The counted cell loads are the loads of the lumped state.** The number of true blocks whose
cell is the class of `i` is the load `cellLoadAt s ξ i`. -/
theorem cellLoad_blockCell_mk (s : Fin m → Fin n → Fin n) (ξ : ER n) (i : Fin n) :
    cellLoad (blockCell s ξ) (Quotient.mk (commonRefinement s ξ) i) = cellLoadAt s ξ i := by
  rw [cellLoad, cellLoadAt]
  congr 1
  ext β
  obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ β
  rw [mem_filter, mk_mem_blocksInside_iff (le_commonRefinement s ξ)]
  simp only [mem_univ, true_and]
  exact Quotient.eq

/-- **The outcome of a merger between two cells**: the lumped state after merging two distinct
true blocks lying in the cells `κ` and `κ'` of the common refinement. When the two cells hold no
such pair the value is the current lumped state, and it enters no count. -/
def mergerOutcome (s : Fin m → Fin n → Fin n) (ξ : ER n)
    (κ κ' : Quotient (commonRefinement s ξ)) : (Fin m → ER n) × (Fin n → ℕ) :=
  if h : ∃ pair : Quotient ξ × Quotient ξ,
      pair.1 ≠ pair.2 ∧ blockCell s ξ pair.1 = κ ∧ blockCell s ξ pair.2 = κ' then
    multiState s (merge ξ h.choose.1 h.choose.2)
  else multiState s ξ

/-- **A merger lands on the outcome of its two cells.** Merging two distinct true blocks leads to
the lumped state that `mergerOutcome` assigns to their cells. -/
theorem multiState_merge_eq_mergerOutcome (s : Fin m → Fin n → Fin n) (ξ : ER n)
    {a b : Quotient ξ} (hab : a ≠ b) :
    multiState s (merge ξ a b) = mergerOutcome s ξ (blockCell s ξ a) (blockCell s ξ b) := by
  have hpair : ∃ pair : Quotient ξ × Quotient ξ,
      pair.1 ≠ pair.2 ∧ blockCell s ξ pair.1 = blockCell s ξ a ∧
        blockCell s ξ pair.2 = blockCell s ξ b := ⟨(a, b), hab, rfl, rfl⟩
  rw [mergerOutcome, dif_pos hpair]
  obtain ⟨hne, hfirst, hsecond⟩ := hpair.choose_spec
  obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ a
  obtain ⟨z, rfl⟩ := quotient_mk_surjective ξ b
  obtain ⟨x', hx'⟩ := quotient_mk_surjective ξ hpair.choose.1
  obtain ⟨z', hz'⟩ := quotient_mk_surjective ξ hpair.choose.2
  rw [← hx', ← hz'] at hne ⊢
  rw [← hx'] at hfirst
  rw [← hz'] at hsecond
  have hx : (commonRefinement s ξ).r x x' :=
    Quotient.exact (show Quotient.mk (commonRefinement s ξ) x = Quotient.mk _ x' from hfirst.symm)
  have hz : (commonRefinement s ξ).r z z' :=
    Quotient.exact (show Quotient.mk (commonRefinement s ξ) z = Quotient.mk _ z' from hsecond.symm)
  exact multiState_merge_eq_of_cells s rfl hx hz hab hne

/-- **Several interfaces sharing one coalescent: the lumped generator, with nothing assumed.** The
ordered pairs of distinct true ancestral blocks whose merger leads to the lumped state `target`
number `lumpedMergerCount` of the cell loads, for the outcome map of the mergers themselves. This
is `MultiInterfaceClosure.card_blockMergers_eq` with its outcome-map hypothesis discharged. -/
theorem card_blockMergers_eq_lumpedMergerCount (s : Fin m → Fin n → Fin n) (ξ : ER n)
    (target : (Fin m → ER n) × (Fin n → ℕ)) :
    (univ.filter fun pair : Quotient ξ × Quotient ξ ↦
      pair.1 ≠ pair.2 ∧ multiState s (merge ξ pair.1 pair.2) = target).card =
      lumpedMergerCount (cellLoad (blockCell s ξ)) (mergerOutcome s ξ) target := by
  have hfilter : (univ.filter fun pair : Quotient ξ × Quotient ξ ↦
      pair.1 ≠ pair.2 ∧ multiState s (merge ξ pair.1 pair.2) = target) =
      univ.filter fun pair : Quotient ξ × Quotient ξ ↦
        pair.1 ≠ pair.2 ∧
          mergerOutcome s ξ (blockCell s ξ pair.1) (blockCell s ξ pair.2) = target := by
    refine filter_congr fun pair _ ↦ ?_
    constructor
    · rintro ⟨hne, houtcome⟩
      exact ⟨hne, (multiState_merge_eq_mergerOutcome s ξ hne).symm.trans houtcome⟩
    · rintro ⟨hne, houtcome⟩
      exact ⟨hne, (multiState_merge_eq_mergerOutcome s ξ hne).trans houtcome⟩
  rw [hfilter]
  convert card_blockMergers_eq s ξ (mergerOutcome s ξ) target

end

end Descent.Pangenome.GraphCoalescent.MultiInterfaceGenerator
