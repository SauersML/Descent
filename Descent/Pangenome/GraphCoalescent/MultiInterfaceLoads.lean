/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiInterfaceOutcome
import Descent.Pangenome.GraphCoalescent.HiddenLoads

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Loads under several interfaces, and the closure with nothing assumed

Section 10 of the hidden-lineage clock claims that for several interfaces sharing one Kingman
genealogy the sufficient state is every report together with the number of true ancestral blocks
inside every cell of the common refinement of the reports. `MultiInterfaceOutcome` shows that a
merger changes the reports and the common refinement only through the cells of the two merging
blocks. This module does the same for the loads, and then proves the closure as Rosenblatt's
criterion for the lumped state, with no hypothesis on how a merger acts.

`blocksInside ξ ζ i` is the set of true blocks of `ξ` met by the individuals `ζ`-related to `i`,
which for `ξ ≤ ζ` are the blocks inside the `ζ`-class of `i` (`mk_mem_blocksInside_iff`).
`cellLoadAt s ξ i` is the load of the cell of `i`, and `multiState s ξ` is the lumped state: every
report and every cell load. `cellLoadAt_merge` is the load after a merger: the number of old
blocks inside the new cell of `i`, less one exactly when both merged individuals lie in that new
cell. The old blocks inside a new cell are counted through the cells they fill:
`exists_cellEquiv` builds, from equal cell loads, a bijection between the true blocks of two states
that keeps every block in its cell, and `card_blocksInside_eq` concludes that states with the
same common refinement and loads meet equally many blocks inside every coarser class. So the
loads after a merger depend only on the lumped state and the two cells
(`cellLoadAt_merge_eq_of_cells`), and so does the whole lumped state
(`multiState_merge_eq_of_cells`).

`card_blockMergers_eq_of_multiState_eq` is the closure. Two coalescent states with the same
lumped state have equally many ordered pairs of distinct true blocks whose merger leads to every
lumped state. With Kingman's unit rate per pair, this is strong lumpability of the reports
together with the cell loads.

The module builds on `HiddenLoads` (Theorem A for one interface) for the count of the blocks of a
merged state.

## Empirical status

None. The bodies here are counts of equivalence classes on a finite set: every statement is an
identity between cardinalities of sets of blocks, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.MultiInterfaceLoads

open Coalescent Finset MultiInterfaceClosure MultiInterfaceOutcome
open scoped Classical

noncomputable section

variable {n m : ℕ}

/-- The true blocks of `ξ` met by the individuals `ζ`-related to `i`. When `ξ ≤ ζ` these are the
blocks of `ξ` inside the `ζ`-class of `i`. -/
def blocksInside (ξ ζ : ER n) (i : Fin n) : Finset (Quotient ξ) :=
  (univ.filter fun u ↦ ζ.r u i).image (Quotient.mk ξ)

/-- For `ξ ≤ ζ`, a true block lies inside the `ζ`-class of `i` exactly when its individuals are
`ζ`-related to `i`. -/
theorem mk_mem_blocksInside_iff {ξ ζ : ER n} (h : ξ ≤ ζ) (x i : Fin n) :
    Quotient.mk ξ x ∈ blocksInside ξ ζ i ↔ ζ.r x i := by
  simp only [blocksInside, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, hux⟩
    exact ζ.iseqv.trans (ζ.iseqv.symm (h (Quotient.exact hux))) hu
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **The hidden load of a cell under several interfaces**: the number of true ancestral blocks
inside the cell of `i` of the common refinement of the reports. -/
def cellLoadAt (s : Fin m → Fin n → Fin n) (ξ : ER n) (i : Fin n) : ℕ :=
  (blocksInside ξ (commonRefinement s ξ) i).card

/-- **The lumped state of several interfaces**: every report, and for every individual the load
of its cell of the common refinement. -/
def multiState (s : Fin m → Fin n → Fin n) (ξ : ER n) : (Fin m → ER n) × (Fin n → ℕ) :=
  (fun j ↦ observed (s j) ξ, cellLoadAt s ξ)

/-- **The loads after a merger.** Merging two distinct true blocks leaves in the new cell of `i`
the old blocks inside it, less one exactly when both merged individuals lie in that new cell. -/
theorem cellLoadAt_merge (s : Fin m → Fin n → Fin n) (ξ : ER n) {x z : Fin n}
    (hab : Quotient.mk ξ x ≠ Quotient.mk ξ z) (i : Fin n) :
    cellLoadAt s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)) i =
      if (commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z))).r x i ∧
          (commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z))).r z i then
        (blocksInside ξ (commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)))
          i).card - 1
      else
        (blocksInside ξ (commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)))
          i).card := by
  have hle : ξ ≤ commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)) :=
    le_trans (le_merge ξ _ _) (le_commonRefinement s _)
  rw [cellLoadAt, blocksInside, card_image_mk_merge, card_image_mergeMap ξ hab, ← blocksInside]
  exact if_congr (and_congr (mk_mem_blocksInside_iff hle x i) (mk_mem_blocksInside_iff hle z i))
    rfl rfl

/-- **Equal cell loads give a cell-preserving bijection of blocks.** Two coalescent states with the
same common refinement and the same cell loads have a bijection between their true blocks that
keeps every block in its cell. -/
theorem exists_cellEquiv (s : Fin m → Fin n → Fin n) {ξ ξ' : ER n}
    (hrefinement : commonRefinement s ξ = commonRefinement s ξ')
    (hload : cellLoadAt s ξ = cellLoadAt s ξ') :
    ∃ e : Quotient ξ ≃ Quotient ξ', ∀ u u' : Fin n,
      e (Quotient.mk ξ u) = Quotient.mk ξ' u' → (commonRefinement s ξ).r u u' := by
  have h : ξ ≤ commonRefinement s ξ := le_commonRefinement s ξ
  have h' : ξ' ≤ commonRefinement s ξ := hrefinement ▸ le_commonRefinement s ξ'
  have hfiber : ∀ (ζ : ER n) (hζ : ζ ≤ commonRefinement s ξ) (i : Fin n),
      (univ.filter fun β : Quotient ζ ↦
        blockMap hζ β = Quotient.mk (commonRefinement s ξ) i) =
        blocksInside ζ (commonRefinement s ξ) i := by
    intro ζ hζ i
    ext β
    obtain ⟨u, rfl⟩ := quotient_mk_surjective ζ β
    rw [mem_filter, mk_mem_blocksInside_iff hζ]
    simp only [mem_univ, true_and]
    exact Quotient.eq
  have hcell : ∀ κ : Quotient (commonRefinement s ξ),
      Fintype.card {β : Quotient ξ // blockMap h β = κ} =
        Fintype.card {β : Quotient ξ' // blockMap h' β = κ} := by
    intro κ
    obtain ⟨i, rfl⟩ := quotient_mk_surjective _ κ
    have hloads : (blocksInside ξ (commonRefinement s ξ) i).card =
        (blocksInside ξ' (commonRefinement s ξ) i).card := by
      have hpoint := congrFun hload i
      rw [cellLoadAt, cellLoadAt, ← hrefinement] at hpoint
      exact hpoint
    rw [Fintype.card_subtype, Fintype.card_subtype, hfiber ξ h i, hfiber ξ' h' i]
    exact hloads
  obtain ⟨e, he⟩ : ∃ e : Quotient ξ ≃ Quotient ξ', ∀ β, blockMap h' (e β) = blockMap h β :=
    ⟨_, Equiv.ofFiberEquiv_map fun κ ↦ Fintype.equivOfCardEq (hcell κ)⟩
  refine ⟨e, fun u u' hu' ↦ ?_⟩
  have hcells := he (Quotient.mk ξ u)
  rw [hu'] at hcells
  exact (commonRefinement s ξ).iseqv.symm (Quotient.exact hcells)

/-- **Equal loads count equally inside every coarser class.** Two coalescent states with the same
common refinement and cell loads meet equally many true blocks inside the class of any individual
for any relation above the common refinement. -/
theorem card_blocksInside_eq (s : Fin m → Fin n → Fin n) {ξ ξ' : ER n}
    (hrefinement : commonRefinement s ξ = commonRefinement s ξ')
    (hload : cellLoadAt s ξ = cellLoadAt s ξ') {ζ : ER n} (hζ : commonRefinement s ξ ≤ ζ)
    (i : Fin n) : (blocksInside ξ ζ i).card = (blocksInside ξ' ζ i).card := by
  obtain ⟨e, he⟩ := exists_cellEquiv s hrefinement hload
  have h : ξ ≤ ζ := le_trans (le_commonRefinement s ξ) hζ
  have h' : ξ' ≤ ζ := le_trans (hrefinement ▸ le_commonRefinement s ξ') hζ
  refine card_equiv e fun β ↦ ?_
  obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ β
  obtain ⟨u', hu'⟩ := quotient_mk_surjective ξ' (e (Quotient.mk ξ u))
  have hrelated : ζ.r u u' := hζ (he u u' hu'.symm)
  rw [← hu', mk_mem_blocksInside_iff h, mk_mem_blocksInside_iff h']
  exact ⟨fun hu ↦ ζ.iseqv.trans (ζ.iseqv.symm hrelated) hu, fun hu ↦ ζ.iseqv.trans hrelated hu⟩

/-- **The loads after a merger depend only on the two cells.** Two coalescent states with the same
lumped state, merging distinct blocks whose individuals lie in the same cells of the common
refinement, have the same cell loads afterwards. -/
theorem cellLoadAt_merge_eq_of_cells (s : Fin m → Fin n → Fin n) {ξ ξ' : ER n}
    (hstate : multiState s ξ = multiState s ξ') {x z x' z' : Fin n}
    (hx : (commonRefinement s ξ).r x x') (hz : (commonRefinement s ξ).r z z')
    (hab : Quotient.mk ξ x ≠ Quotient.mk ξ z) (hab' : Quotient.mk ξ' x' ≠ Quotient.mk ξ' z') :
    cellLoadAt s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)) =
      cellLoadAt s (merge ξ' (Quotient.mk ξ' x') (Quotient.mk ξ' z')) := by
  have hreports : ∀ j, observed (s j) ξ = observed (s j) ξ' :=
    fun j ↦ congrFun (congrArg Prod.fst hstate) j
  have hload : cellLoadAt s ξ = cellLoadAt s ξ' := congrArg Prod.snd hstate
  have hrefinement := commonRefinement_eq_of_reports s hreports
  have hmerged := commonRefinement_merge_eq_of_cells s hreports hx hz
  have habove : commonRefinement s ξ ≤
      commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)) :=
    commonRefinement_mono s (le_merge ξ _ _)
  have hxN := habove hx
  have hzN := habove hz
  funext i
  rw [cellLoadAt_merge s ξ hab i, cellLoadAt_merge s ξ' hab' i, ← hmerged,
    card_blocksInside_eq s hrefinement hload habove i]
  by_cases hcondition :
      (commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z))).r x i ∧
        (commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z))).r z i
  · have hprimed :
        (commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z))).r x' i ∧
          (commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z))).r z' i :=
      ⟨(commonRefinement s _).iseqv.trans ((commonRefinement s _).iseqv.symm hxN) hcondition.1,
        (commonRefinement s _).iseqv.trans ((commonRefinement s _).iseqv.symm hzN) hcondition.2⟩
    rw [if_pos hcondition, if_pos hprimed]
  · have hprimed :
        ¬ ((commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z))).r x' i ∧
          (commonRefinement s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z))).r z' i) :=
      fun hboth ↦ hcondition
        ⟨(commonRefinement s _).iseqv.trans hxN hboth.1,
          (commonRefinement s _).iseqv.trans hzN hboth.2⟩
    rw [if_neg hcondition, if_neg hprimed]

/-- **The outcome of a merger depends only on the two cells.** Under the hypotheses of
`cellLoadAt_merge_eq_of_cells`, the two merged states have the same lumped state: the same report
at every interface and the same cell loads. -/
theorem multiState_merge_eq_of_cells (s : Fin m → Fin n → Fin n) {ξ ξ' : ER n}
    (hstate : multiState s ξ = multiState s ξ') {x z x' z' : Fin n}
    (hx : (commonRefinement s ξ).r x x') (hz : (commonRefinement s ξ).r z z')
    (hab : Quotient.mk ξ x ≠ Quotient.mk ξ z) (hab' : Quotient.mk ξ' x' ≠ Quotient.mk ξ' z') :
    multiState s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)) =
      multiState s (merge ξ' (Quotient.mk ξ' x') (Quotient.mk ξ' z')) :=
  Prod.ext
    (funext fun j ↦ observed_merge_eq_of_cells s
      (fun j ↦ congrFun (congrArg Prod.fst hstate) j) hx hz j)
    (cellLoadAt_merge_eq_of_cells s hstate hx hz hab hab')

/-- **Several interfaces sharing one coalescent: the closure, with nothing assumed.** Two
coalescent states with the same lumped state, every report and every cell load, have equally
many ordered pairs of distinct true blocks whose merger leads to every lumped state. With
Kingman's unit rate per pair this is Rosenblatt's criterion: the reports together with the cell
loads form a strong lumping of the coalescent. -/
theorem card_blockMergers_eq_of_multiState_eq (s : Fin m → Fin n → Fin n) {ξ ξ' : ER n}
    (hstate : multiState s ξ = multiState s ξ') (target : (Fin m → ER n) × (Fin n → ℕ)) :
    (univ.filter fun pair : Quotient ξ × Quotient ξ ↦
      pair.1 ≠ pair.2 ∧ multiState s (merge ξ pair.1 pair.2) = target).card =
      (univ.filter fun pair : Quotient ξ' × Quotient ξ' ↦
        pair.1 ≠ pair.2 ∧ multiState s (merge ξ' pair.1 pair.2) = target).card := by
  have hreports : ∀ j, observed (s j) ξ = observed (s j) ξ' :=
    fun j ↦ congrFun (congrArg Prod.fst hstate) j
  have hload : cellLoadAt s ξ = cellLoadAt s ξ' := congrArg Prod.snd hstate
  obtain ⟨e, he⟩ := exists_cellEquiv s (commonRefinement_eq_of_reports s hreports) hload
  refine card_equiv (e.prodCongr e) fun pair ↦ ?_
  obtain ⟨a, b⟩ := pair
  obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ a
  obtain ⟨z, rfl⟩ := quotient_mk_surjective ξ b
  obtain ⟨x', hx'⟩ := quotient_mk_surjective ξ' (e (Quotient.mk ξ x))
  obtain ⟨z', hz'⟩ := quotient_mk_surjective ξ' (e (Quotient.mk ξ z))
  simp only [mem_filter, mem_univ, true_and, Equiv.prodCongr_apply, Prod.map_apply]
  rw [← hx', ← hz']
  have hne : Quotient.mk ξ x ≠ Quotient.mk ξ z ↔ Quotient.mk ξ' x' ≠ Quotient.mk ξ' z' := by
    rw [hx', hz']
    exact e.injective.ne_iff.symm
  constructor
  · rintro ⟨hab, houtcome⟩
    have hab' := hne.mp hab
    exact ⟨hab', (multiState_merge_eq_of_cells s hstate (he x x' hx'.symm) (he z z' hz'.symm)
      hab hab').symm.trans houtcome⟩
  · rintro ⟨hab', houtcome⟩
    have hab := hne.mpr hab'
    exact ⟨hab, (multiState_merge_eq_of_cells s hstate (he x x' hx'.symm) (he z z' hz'.symm)
      hab hab').trans houtcome⟩

end

end Descent.Pangenome.GraphCoalescent.MultiInterfaceLoads
