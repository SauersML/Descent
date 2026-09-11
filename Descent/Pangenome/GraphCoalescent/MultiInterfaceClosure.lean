/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.Observation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Several interfaces sharing one coalescent: the lumped generator

Section 10 of the hidden-lineage clock extends Theorem A to several interfaces `s₁, …, s_m`
applied to one Kingman genealogy: the sufficient state is every report together with the number
of true ancestral blocks inside every nonempty cell of the common refinement of the reports. This
module proves that closure as a statement about the lumped generator.

`commonRefinement s ξ` is the meet of the reports `observed (s j) ξ`. `le_commonRefinement` says
every true ancestral block lies inside exactly one cell of it, `commonRefinement_le_observed`
that each report is coarser than it, and `observed_commonRefinement` that the common refinement
determines every report: observing it at any interface returns that interface's report. So the
reports together with the cells carry every report.

The generator of the Kingman chain merges every pair of true blocks at rate one. `cellLoad` counts
the blocks inside a cell, and `cellPairCount` the ordered pairs of distinct blocks with prescribed
cells: `L_κ L_κ'` across two cells, `L_κ (L_κ - 1)` inside one (`card_blockPairs_with_cells`).
`lumpedMergerCount load outcome target` is the lumped generator counted over ordered pairs: for an
outcome map sending the cells of the two merging blocks to the next lumped state, it sums the pair
counts of the cell pairs whose outcome is `target`. `card_mergers_eq_lumpedMergerCount` shows the
ordered block pairs whose merger leads to `target` number exactly that, and
`card_mergers_eq_of_cellLoad_eq` concludes Rosenblatt's criterion: two labeled configurations with
the same hidden load in every cell offer equally many mergers into every lumped target. With the
blocks and cells of the corpus setoids this is `card_blockMergers_eq`.

The module defines its own load vocabulary because the load chain of Theorem A is not on main.

Not formalized here: that the outcome of a merger really depends only on the two cells. In each
report the merger joins the components containing those cells, and the new common refinement
aggregates old cells, with loads adding and dropping by one for the merged pair. Here it is the
hypothesis on the outcome map. Also not formalized: the Λ-coalescent extension of section 10.

## Empirical status

None. The bodies here are combinatorics: blocks, cells and outcome maps are supplied finite data,
and every statement is a count of pairs or a lattice identity between equivalence relations, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.MultiInterfaceClosure

noncomputable section

/-! ### The common refinement of several reports -/

/-- **The common refinement of several reports.** For interfaces `s j` applied to one coalescent
state `ξ`, the meet of their reports. -/
def commonRefinement {n m : ℕ} (s : Fin m → Fin n → Fin n) (ξ : Coalescent.ER n) :
    Coalescent.ER n :=
  ⨅ j, observed (s j) ξ

/-- Every true ancestral block lies inside one cell of the common refinement. -/
theorem le_commonRefinement {n m : ℕ} (s : Fin m → Fin n → Fin n) (ξ : Coalescent.ER n) :
    ξ ≤ commonRefinement s ξ :=
  le_iInf fun j ↦ le_observed (s j) ξ

/-- Each report is coarser than the common refinement. -/
theorem commonRefinement_le_observed {n m : ℕ} (s : Fin m → Fin n → Fin n)
    (ξ : Coalescent.ER n) (j : Fin m) : commonRefinement s ξ ≤ observed (s j) ξ :=
  iInf_le _ j

/-- **The common refinement determines every report.** Observing the common refinement at any
interface returns that interface's report of the coalescent state. -/
theorem observed_commonRefinement {n m : ℕ} (s : Fin m → Fin n → Fin n) (ξ : Coalescent.ER n)
    (j : Fin m) : observed (s j) (commonRefinement s ξ) = observed (s j) ξ :=
  le_antisymm
    (observed_le (commonRefinement_le_observed s ξ j) (graphKer_le_observed (s j) ξ))
    (observed_mono (s j) (le_commonRefinement s ξ))

/-! ### The lumped generator -/

section Counting

variable {Block Cell State : Type*} [Fintype Block] [DecidableEq Block] [Fintype Cell]
  [DecidableEq Cell] [DecidableEq State]

/-- The hidden load of a cell: the number of true ancestral blocks inside it. -/
def cellLoad (cellOf : Block → Cell) (cell : Cell) : ℕ :=
  (Finset.univ.filter fun block ↦ cellOf block = cell).card

omit [Fintype Block] [DecidableEq Block] [Fintype Cell] in
/-- The number of ordered pairs of distinct blocks with prescribed cells, from the cell loads:
the product of the loads across two cells, and the load times one less inside one cell. -/
def cellPairCount (load : Cell → ℕ) (first second : Cell) : ℕ :=
  if first = second then load first * (load first - 1) else load first * load second

omit [DecidableEq State] in
/-- **Counting the mergers by cells.** The ordered pairs of distinct blocks whose cells are `first`
and `second` number `cellPairCount` of the cell loads. -/
theorem card_blockPairs_with_cells (cellOf : Block → Cell) (first second : Cell) :
    (Finset.univ.filter fun pair : Block × Block ↦
      pair.1 ≠ pair.2 ∧ (cellOf pair.1, cellOf pair.2) = (first, second)).card =
      cellPairCount (cellLoad cellOf) first second := by
  by_cases hsame : first = second
  · subst hsame
    have hset : (Finset.univ.filter fun pair : Block × Block ↦
        pair.1 ≠ pair.2 ∧ (cellOf pair.1, cellOf pair.2) = (first, first)) =
        (Finset.univ.filter fun block ↦ cellOf block = first).offDiag := by
      ext pair
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag,
        Prod.mk.injEq]
      tauto
    rw [hset, Finset.offDiag_card, cellPairCount, if_pos rfl, cellLoad, Nat.mul_sub_one]
  · have hset : (Finset.univ.filter fun pair : Block × Block ↦
        pair.1 ≠ pair.2 ∧ (cellOf pair.1, cellOf pair.2) = (first, second)) =
        (Finset.univ.filter fun block ↦ cellOf block = first) ×ˢ
          (Finset.univ.filter fun block ↦ cellOf block = second) := by
      ext pair
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Prod.mk.injEq]
      constructor
      · rintro ⟨_, hfirst, hsecond⟩
        exact ⟨hfirst, hsecond⟩
      · rintro ⟨hfirst, hsecond⟩
        refine ⟨fun hequal ↦ hsame ?_, hfirst, hsecond⟩
        rw [← hfirst, ← hsecond, hequal]
    rw [hset, Finset.card_product, cellPairCount, if_neg hsame]
    rfl

omit [Fintype Block] [DecidableEq Block] in
/-- **The lumped generator of several interfaces**, counted over ordered pairs of blocks: the sum,
over the cell pairs whose merger outcome is `target`, of the number of ordered block pairs with
those cells. It depends on the configuration only through the cell loads. -/
def lumpedMergerCount (load : Cell → ℕ) (outcome : Cell → Cell → State) (target : State) : ℕ :=
  ∑ cells : Cell × Cell,
    if outcome cells.1 cells.2 = target then cellPairCount load cells.1 cells.2 else 0

/-- **The closure of several interfaces, the lumped generator.** When the outcome of merging two
blocks depends only on their cells, the ordered pairs of distinct blocks whose merger leads to
`target` number exactly `lumpedMergerCount` of the cell loads. Assumes: the outcome map describes
the next lumped state as a function of the two cells, which is the content of section 10. -/
theorem card_mergers_eq_lumpedMergerCount (cellOf : Block → Cell)
    (outcome : Cell → Cell → State) (target : State) :
    (Finset.univ.filter fun pair : Block × Block ↦
      pair.1 ≠ pair.2 ∧ outcome (cellOf pair.1) (cellOf pair.2) = target).card =
      lumpedMergerCount (cellLoad cellOf) outcome target := by
  have hfiber : ∀ cells : Cell × Cell,
      ((Finset.univ.filter fun pair : Block × Block ↦
          pair.1 ≠ pair.2 ∧ outcome (cellOf pair.1) (cellOf pair.2) = target).filter
        fun pair ↦ (cellOf pair.1, cellOf pair.2) = cells).card =
        if outcome cells.1 cells.2 = target then
          cellPairCount (cellLoad cellOf) cells.1 cells.2 else 0 := by
    rintro ⟨first, second⟩
    rw [Finset.filter_filter]
    by_cases htarget : outcome first second = target
    · rw [if_pos htarget, ← card_blockPairs_with_cells cellOf first second]
      congr 1
      ext pair
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hne, _⟩, hcells⟩
        exact ⟨hne, hcells⟩
      · rintro ⟨hne, hfirst, hsecond⟩
        refine ⟨⟨hne, ?_⟩, hfirst, hsecond⟩
        rw [hfirst, hsecond]
        exact htarget
    · rw [if_neg htarget, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro pair - ⟨⟨_, houtcome⟩, hcells⟩
      simp only [Prod.mk.injEq] at hcells
      rw [hcells.1, hcells.2] at houtcome
      exact htarget houtcome
  calc (Finset.univ.filter fun pair : Block × Block ↦
        pair.1 ≠ pair.2 ∧ outcome (cellOf pair.1) (cellOf pair.2) = target).card
      = ∑ cells : Cell × Cell, ((Finset.univ.filter fun pair : Block × Block ↦
          pair.1 ≠ pair.2 ∧ outcome (cellOf pair.1) (cellOf pair.2) = target).filter
        fun pair ↦ (cellOf pair.1, cellOf pair.2) = cells).card :=
        Finset.card_eq_sum_card_fiberwise fun _ _ ↦ Finset.mem_univ _
    _ = lumpedMergerCount (cellLoad cellOf) outcome target :=
        Finset.sum_congr rfl fun cells _ ↦ hfiber cells

/-- **Rosenblatt's criterion for several interfaces.** Two labeled configurations with the same
hidden load in every cell offer, for every outcome map that depends only on cells, equally many
mergers into every lumped target: the reports together with the cell loads form a strong lumping.
Assumes: the outcome map describes the next lumped state as a function of the two cells. -/
theorem card_mergers_eq_of_cellLoad_eq {Block' : Type*} [Fintype Block'] [DecidableEq Block']
    (cellOf : Block → Cell) (cellOf' : Block' → Cell) (hload : cellLoad cellOf = cellLoad cellOf')
    (outcome : Cell → Cell → State) (target : State) :
    (Finset.univ.filter fun pair : Block × Block ↦
      pair.1 ≠ pair.2 ∧ outcome (cellOf pair.1) (cellOf pair.2) = target).card =
      (Finset.univ.filter fun pair : Block' × Block' ↦
        pair.1 ≠ pair.2 ∧ outcome (cellOf' pair.1) (cellOf' pair.2) = target).card := by
  rw [card_mergers_eq_lumpedMergerCount, card_mergers_eq_lumpedMergerCount, hload]

end Counting

/-! ### The lumped generator on the corpus setoids -/

/-- The cell of the common refinement containing a true ancestral block. -/
def blockCell {n m : ℕ} (s : Fin m → Fin n → Fin n) (ξ : Coalescent.ER n) :
    Quotient ξ → Quotient (commonRefinement s ξ) :=
  Quotient.map' id fun _ _ hrelated ↦ le_commonRefinement s ξ hrelated

open Classical in
/-- **Several interfaces sharing one coalescent.** For every outcome map on the cells of the common
refinement, the ordered pairs of distinct true ancestral blocks whose merger leads to `target`
number `lumpedMergerCount` of the hidden cell loads. Assumes: the outcome map describes the next
lumped state as a function of the two cells. -/
theorem card_blockMergers_eq {n m : ℕ} (s : Fin m → Fin n → Fin n) (ξ : Coalescent.ER n)
    {State : Type*} (outcome : Quotient (commonRefinement s ξ) →
      Quotient (commonRefinement s ξ) → State) (target : State) :
    (Finset.univ.filter fun pair : Quotient ξ × Quotient ξ ↦
      pair.1 ≠ pair.2 ∧ outcome (blockCell s ξ pair.1) (blockCell s ξ pair.2) = target).card =
      lumpedMergerCount (cellLoad (blockCell s ξ)) outcome target :=
  card_mergers_eq_lumpedMergerCount (blockCell s ξ) outcome target

end

end Descent.Pangenome.GraphCoalescent.MultiInterfaceClosure
