/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LambdaLoadClosure
import Descent.Pangenome.GraphCoalescent.MultiInterfaceLoads

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# What a Λ-merger does to the lumped state, with nothing assumed

`LambdaLoadClosure` counts the merging sets of a Λ-coalescent by their profile, the number of
merging blocks in each component, and proves that the total rate into a lumped target is
`lumpedLambdaRate` of the loads. It does so for an outcome map on profiles that it takes as given.
This module builds that map from the mergers themselves and removes the hypothesis, on the corpus
setoids and for several interfaces at once. The profile is taken over the cells of the common
refinement of the reports, so one interface is the case of `LambdaLoadClosure`'s single report.

`mergeSet ξ S` is the coalescent state after the true blocks in `S` merge into one: the kernel of
the fold `foldSet ξ S`, which sends every block of `S` to one point (`mergeSet_rel_iff`).
Reporting the merged state at an interface joins the report with the merged state
(`observed_mergeSet_eq`). That join does not change when the merging set is replaced by one
touching the same cells (`sup_mergeSet_eq_of_cells`). The loads after the merger are the old
blocks inside each new cell, less `|S| - 1` in the cell holding the merged block
(`cellLoadAt_mergeSet`): `card_image_mk_mergeSet` passes to the fold of the blocks, and
`card_image_foldSet` counts the fold on a set of blocks containing all of `S` or none of it.

`multiState_mergeSet_eq_of_profile` is the first claim: two merging sets of one state with the
same number of blocks in every cell leave the same lumped state, every report and every cell
load. Equal profiles touch the same cells (`exists_mem_of_subsetProfile_eq`) and have the same
size. `lambdaOutcome s ξ` is the lumped state reached by merging any set with a given profile,
and every merger lands on the outcome of its profile (`multiState_mergeSet_eq_lambdaOutcome`).
`sum_blockMergerRates_eq_lumpedLambdaRate` is the second claim: the total rate of the labeled
Λ-coalescent into a lumped target, over every set of at least two true blocks whose merger leads
there, is `lumpedLambdaRate` of the cell loads for that outcome map, with no hypothesis. At unit
rate this counts the mergers (`card_blockMergers_eq_lumpedLambdaRate`).

## Empirical status

None. The bodies here are counts of equivalence classes on a finite set and sums of supplied
rates over sets of blocks, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.LambdaLoadOutcome

open Coalescent Finset MultiInterfaceClosure MultiInterfaceOutcome MultiInterfaceLoads
  LambdaLoadClosure
open scoped Classical

noncomputable section

variable {n m : ℕ}

/-! ### Merging a set of blocks -/

/-- The fold of a set of blocks: every block of `S` goes to one point and every other block stays
apart. -/
def foldSet (ξ : ER n) (S : Finset (Quotient ξ)) (a : Quotient ξ) : Option (Quotient ξ) :=
  if a ∈ S then none else some a

/-- **The Λ-merger of a set of blocks.** The coalescent state after the true blocks in `S` merge
into one, as the kernel of the fold. -/
def mergeSet (ξ : ER n) (S : Finset (Quotient ξ)) : ER n :=
  Setoid.ker (foldSet ξ S ∘ Quotient.mk ξ)

/-- Two individuals are together after the merger when they were together before, or when both lie
in merging blocks. -/
theorem mergeSet_rel_iff (ξ : ER n) (S : Finset (Quotient ξ)) (x y : Fin n) :
    (mergeSet ξ S).r x y ↔ ξ.r x y ∨ (Quotient.mk ξ x ∈ S ∧ Quotient.mk ξ y ∈ S) := by
  change foldSet ξ S (Quotient.mk ξ x) = foldSet ξ S (Quotient.mk ξ y) ↔ _
  by_cases hx : Quotient.mk ξ x ∈ S
  · by_cases hy : Quotient.mk ξ y ∈ S
    · rw [foldSet, foldSet, if_pos hx, if_pos hy]
      exact ⟨fun _ ↦ Or.inr ⟨hx, hy⟩, fun _ ↦ rfl⟩
    · rw [foldSet, foldSet, if_pos hx, if_neg hy]
      refine ⟨fun h ↦ Option.noConfusion h, fun h ↦ ?_⟩
      rcases h with h | h
      · have hq : Quotient.mk ξ x = Quotient.mk ξ y := Quotient.sound h
        rw [hq] at hx
        exact absurd hx hy
      · exact absurd h.2 hy
  · by_cases hy : Quotient.mk ξ y ∈ S
    · rw [foldSet, foldSet, if_neg hx, if_pos hy]
      refine ⟨fun h ↦ Option.noConfusion h, fun h ↦ ?_⟩
      rcases h with h | h
      · have hq : Quotient.mk ξ x = Quotient.mk ξ y := Quotient.sound h
        rw [hq] at hx
        exact absurd hy hx
      · exact absurd h.1 hx
    · rw [foldSet, foldSet, if_neg hx, if_neg hy]
      refine ⟨fun h ↦ Or.inl (Quotient.exact (Option.some_injective _ h)), fun h ↦ ?_⟩
      rcases h with h | h
      · exact congrArg some (Quotient.sound h)
      · exact absurd h.1 hx

/-- The merger only coarsens. -/
theorem le_mergeSet (ξ : ER n) (S : Finset (Quotient ξ)) : ξ ≤ mergeSet ξ S :=
  fun x y h ↦ (mergeSet_rel_iff ξ S x y).mpr (Or.inl h)

/-- **Reporting a Λ-merger.** The report of the merged state at an interface is the report joined
with the merged state. -/
theorem observed_mergeSet_eq (s : Fin n → Fin n) (ξ : ER n) (S : Finset (Quotient ξ)) :
    observed s (mergeSet ξ S) = observed s ξ ⊔ mergeSet ξ S := by
  rw [observed, observed, sup_right_comm, sup_eq_right.mpr (le_mergeSet ξ S)]

/-- **The join depends on the merging set only through its cells.** If every merging block of `S`
shares a class of `ζ ≥ ξ` with a merging block of `S'`, and conversely, then joining `ζ` with
either merged state gives the same relation. -/
theorem sup_mergeSet_eq_of_cells {ξ ζ : ER n} (hξζ : ξ ≤ ζ) {S S' : Finset (Quotient ξ)}
    (hSS' : ∀ x, Quotient.mk ξ x ∈ S → ∃ x', Quotient.mk ξ x' ∈ S' ∧ ζ.r x x')
    (hS'S : ∀ x', Quotient.mk ξ x' ∈ S' → ∃ x, Quotient.mk ξ x ∈ S ∧ ζ.r x' x) :
    ζ ⊔ mergeSet ξ S = ζ ⊔ mergeSet ξ S' := by
  have hbelow : ∀ {T T' : Finset (Quotient ξ)},
      (∀ x, Quotient.mk ξ x ∈ T → ∃ x', Quotient.mk ξ x' ∈ T' ∧ ζ.r x x') →
      mergeSet ξ T ≤ ζ ⊔ mergeSet ξ T' := by
    intro T T' hTT' x y hxy
    have hleft : ζ ≤ ζ ⊔ mergeSet ξ T' := le_sup_left
    have hright : mergeSet ξ T' ≤ ζ ⊔ mergeSet ξ T' := le_sup_right
    rcases (mergeSet_rel_iff ξ T x y).mp hxy with h | ⟨hx, hy⟩
    · exact hleft (hξζ h)
    · obtain ⟨x', hx', hxx'⟩ := hTT' x hx
      obtain ⟨y', hy', hyy'⟩ := hTT' y hy
      have hmid : (ζ ⊔ mergeSet ξ T').r x' y' :=
        hright ((mergeSet_rel_iff ξ T' x' y').mpr (Or.inr ⟨hx', hy'⟩))
      exact (ζ ⊔ mergeSet ξ T').iseqv.trans (hleft hxx')
        ((ζ ⊔ mergeSet ξ T').iseqv.trans hmid (hleft (ζ.iseqv.symm hyy')))
  exact le_antisymm (sup_le le_sup_left (hbelow hSS')) (sup_le le_sup_left (hbelow hS'S))

/-! ### Counting the blocks of a merged state -/

/-- The blocks of a merged state met by a set of individuals are the images, under the fold, of the
blocks they meet before the merger. -/
theorem card_image_mk_mergeSet (ξ : ER n) (S : Finset (Quotient ξ)) (T : Finset (Fin n)) :
    (T.image (Quotient.mk (mergeSet ξ S))).card =
      ((T.image (Quotient.mk ξ)).image (foldSet ξ S)).card := by
  rw [image_image]
  have hlift : T.image (foldSet ξ S ∘ Quotient.mk ξ) =
      (T.image (Quotient.mk (mergeSet ξ S))).image
        (Quotient.lift (fun x ↦ foldSet ξ S (Quotient.mk ξ x))
          fun u v (h : (mergeSet ξ S).r u v) ↦
            (h : foldSet ξ S (Quotient.mk ξ u) = foldSet ξ S (Quotient.mk ξ v))) := by
    rw [image_image]
    rfl
  rw [hlift, card_image_of_injective _ (Setoid.ker_lift_injective _)]

/-- **Folding a set of blocks.** On a set of blocks that contains all of `S` or none of it, the fold
loses `|S| - 1` blocks exactly when `S` is a nonempty part of the set. -/
theorem card_image_foldSet (ξ : ER n) {S B : Finset (Quotient ξ)} (hSB : S ⊆ B ∨ Disjoint S B) :
    (B.image (foldSet ξ S)).card =
      if S.Nonempty ∧ S ⊆ B then B.card - S.card + 1 else B.card := by
  split_ifs with hS
  · have himage : B.image (foldSet ξ S) = insert none ((B \ S).image some) := by
      ext o
      simp only [mem_image, mem_insert, mem_sdiff]
      constructor
      · rintro ⟨a, ha, rfl⟩
        by_cases haS : a ∈ S
        · left
          rw [foldSet, if_pos haS]
        · right
          exact ⟨a, ⟨ha, haS⟩, (if_neg haS).symm⟩
      · rintro (rfl | ⟨a, ⟨ha, haS⟩, rfl⟩)
        · obtain ⟨a, haS⟩ := hS.1
          exact ⟨a, hS.2 haS, if_pos haS⟩
        · exact ⟨a, ha, if_neg haS⟩
    have hnone : none ∉ (B \ S).image some := by simp
    rw [himage, card_insert_of_notMem hnone, card_image_of_injective _ (Option.some_injective _),
      card_sdiff_of_subset hS.2]
  · have hnot : ∀ a ∈ B, a ∉ S := fun a ha haS ↦ by
      rcases hSB with hsub | hdisj
      · exact hS ⟨⟨a, haS⟩, hsub⟩
      · exact disjoint_left.mp hdisj haS ha
    refine card_image_of_injOn fun a ha b hb hab ↦ ?_
    have ha' := hnot a (mem_coe.mp ha)
    have hb' := hnot b (mem_coe.mp hb)
    rw [foldSet, foldSet, if_neg ha', if_neg hb'] at hab
    exact Option.some_injective _ hab

/-- **The loads after a Λ-merger.** The blocks of the merged state inside the new cell of `i` are
the old blocks inside it, less `|S| - 1` when the merging blocks lie there. -/
theorem cellLoadAt_mergeSet (s : Fin m → Fin n → Fin n) (ξ : ER n) (S : Finset (Quotient ξ))
    (i : Fin n) :
    cellLoadAt s (mergeSet ξ S) i =
      if S.Nonempty ∧ S ⊆ blocksInside ξ (commonRefinement s (mergeSet ξ S)) i then
        (blocksInside ξ (commonRefinement s (mergeSet ξ S)) i).card - S.card + 1
      else (blocksInside ξ (commonRefinement s (mergeSet ξ S)) i).card := by
  have hle : ξ ≤ commonRefinement s (mergeSet ξ S) :=
    le_trans (le_mergeSet ξ S) (le_commonRefinement s _)
  have hsaturated : S ⊆ blocksInside ξ (commonRefinement s (mergeSet ξ S)) i ∨
      Disjoint S (blocksInside ξ (commonRefinement s (mergeSet ξ S)) i) := by
    by_cases hmeet : ∃ a ∈ S, a ∈ blocksInside ξ (commonRefinement s (mergeSet ξ S)) i
    · left
      obtain ⟨a, haS, hai⟩ := hmeet
      obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ a
      intro b hbS
      obtain ⟨y, rfl⟩ := quotient_mk_surjective ξ b
      rw [mk_mem_blocksInside_iff hle] at hai ⊢
      have hyx : (commonRefinement s (mergeSet ξ S)).r y x :=
        le_commonRefinement s _ ((mergeSet_rel_iff ξ S y x).mpr (Or.inr ⟨hbS, haS⟩))
      exact (commonRefinement s (mergeSet ξ S)).iseqv.trans hyx hai
    · right
      exact disjoint_left.mpr fun a haS hai ↦ hmeet ⟨a, haS, hai⟩
  rw [cellLoadAt, blocksInside, card_image_mk_mergeSet, ← blocksInside,
    card_image_foldSet ξ hsaturated]

/-! ### The outcome of a Λ-merger -/

/-- **Equal profiles touch the same cells.** If two merging sets have the same profile, every
merging block of the first shares its cell with a merging block of the second. -/
theorem exists_mem_of_subsetProfile_eq (s : Fin m → Fin n → Fin n) (ξ : ER n)
    {S S' : Finset (Quotient ξ)}
    (hprofile : subsetProfile (blockCell s ξ) S = subsetProfile (blockCell s ξ) S') (x : Fin n)
    (hx : Quotient.mk ξ x ∈ S) :
    ∃ x', Quotient.mk ξ x' ∈ S' ∧ (commonRefinement s ξ).r x x' := by
  have hpos : 0 < subsetProfile (blockCell s ξ) S' (blockCell s ξ (Quotient.mk ξ x)) := by
    rw [← hprofile]
    exact card_pos.mpr ⟨Quotient.mk ξ x, mem_filter.mpr ⟨hx, rfl⟩⟩
  obtain ⟨b, hb⟩ := card_pos.mp hpos
  obtain ⟨hbS', hcell⟩ := mem_filter.mp hb
  obtain ⟨x', rfl⟩ := quotient_mk_surjective ξ b
  have hcell' : Quotient.mk (commonRefinement s ξ) x' = Quotient.mk (commonRefinement s ξ) x :=
    hcell
  exact ⟨x', hbS', (commonRefinement s ξ).iseqv.symm (Quotient.exact hcell')⟩

/-- **The outcome of a Λ-merger depends only on its profile.** Two sets of true blocks of the same
state with the same number of blocks in every cell of the common refinement leave the same lumped
state when they merge: the same report at every interface and the same cell loads. -/
theorem multiState_mergeSet_eq_of_profile (s : Fin m → Fin n → Fin n) (ξ : ER n)
    {S S' : Finset (Quotient ξ)}
    (hprofile : subsetProfile (blockCell s ξ) S = subsetProfile (blockCell s ξ) S') :
    multiState s (mergeSet ξ S) = multiState s (mergeSet ξ S') := by
  have hcells := exists_mem_of_subsetProfile_eq s ξ hprofile
  have hcells' := exists_mem_of_subsetProfile_eq s ξ hprofile.symm
  have hreports : ∀ j, observed (s j) (mergeSet ξ S) = observed (s j) (mergeSet ξ S') := by
    intro j
    rw [observed_mergeSet_eq, observed_mergeSet_eq]
    refine sup_mergeSet_eq_of_cells (le_observed (s j) ξ) (fun x hx ↦ ?_) (fun x' hx' ↦ ?_)
    · obtain ⟨x', hx', hrel⟩ := hcells x hx
      exact ⟨x', hx', commonRefinement_le_observed s ξ j hrel⟩
    · obtain ⟨x, hx, hrel⟩ := hcells' x' hx'
      exact ⟨x, hx, commonRefinement_le_observed s ξ j hrel⟩
  have hrefinement : commonRefinement s (mergeSet ξ S) = commonRefinement s (mergeSet ξ S') :=
    commonRefinement_eq_of_reports s hreports
  have hcard : S.card = S'.card := by
    rw [← sum_subsetProfile (blockCell s ξ) S, ← sum_subsetProfile (blockCell s ξ) S', hprofile]
  refine Prod.ext (funext hreports) (funext fun i ↦ ?_)
  show cellLoadAt s (mergeSet ξ S) i = cellLoadAt s (mergeSet ξ S') i
  rw [cellLoadAt_mergeSet, cellLoadAt_mergeSet, ← hrefinement, hcard]
  have hle : commonRefinement s ξ ≤ commonRefinement s (mergeSet ξ S) :=
    commonRefinement_mono s (le_mergeSet ξ S)
  have hξ : ξ ≤ commonRefinement s (mergeSet ξ S) := le_trans (le_commonRefinement s ξ) hle
  have hsub : ∀ {T T' : Finset (Quotient ξ)},
      (∀ x, Quotient.mk ξ x ∈ T' → ∃ x', Quotient.mk ξ x' ∈ T ∧ (commonRefinement s ξ).r x x') →
      T ⊆ blocksInside ξ (commonRefinement s (mergeSet ξ S)) i →
      T' ⊆ blocksInside ξ (commonRefinement s (mergeSet ξ S)) i := by
    intro T T' hTT' hT b hb
    obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ b
    obtain ⟨x', hx', hrel⟩ := hTT' x hb
    have hin := hT hx'
    rw [mk_mem_blocksInside_iff hξ] at hin ⊢
    exact (commonRefinement s (mergeSet ξ S)).iseqv.trans (hle hrel) hin
  have hnonempty : S.Nonempty ↔ S'.Nonempty := by
    rw [← card_pos, ← card_pos, hcard]
  have hcondition : (S.Nonempty ∧ S ⊆ blocksInside ξ (commonRefinement s (mergeSet ξ S)) i) ↔
      (S'.Nonempty ∧ S' ⊆ blocksInside ξ (commonRefinement s (mergeSet ξ S)) i) :=
    and_congr hnonempty ⟨hsub hcells', hsub hcells⟩
  exact if_congr hcondition rfl rfl

/-- **The outcome of a Λ-merger with a given profile**: the lumped state after merging a set of
true blocks with that profile. When no set has the profile the value is the current lumped state,
and it enters no rate. -/
def lambdaOutcome (s : Fin m → Fin n → Fin n) (ξ : ER n)
    (profile : Quotient (commonRefinement s ξ) → ℕ) : (Fin m → ER n) × (Fin n → ℕ) :=
  if h : ∃ S : Finset (Quotient ξ), subsetProfile (blockCell s ξ) S = profile then
    multiState s (mergeSet ξ h.choose)
  else multiState s ξ

/-- **Every Λ-merger lands on the outcome of its profile.** -/
theorem multiState_mergeSet_eq_lambdaOutcome (s : Fin m → Fin n → Fin n) (ξ : ER n)
    (S : Finset (Quotient ξ)) :
    multiState s (mergeSet ξ S) = lambdaOutcome s ξ (subsetProfile (blockCell s ξ) S) := by
  have h : ∃ S' : Finset (Quotient ξ),
      subsetProfile (blockCell s ξ) S' = subsetProfile (blockCell s ξ) S := ⟨S, rfl⟩
  rw [lambdaOutcome, dif_pos h]
  exact multiState_mergeSet_eq_of_profile s ξ h.choose_spec.symm

/-- **The Λ-coalescent closure, with nothing assumed.** The total rate at which the labeled
Λ-coalescent moves into a lumped target, over every set of at least two true blocks whose merger
leads there, is `lumpedLambdaRate` of the cell loads for the outcome map of the mergers
themselves. This is `LambdaLoadClosure.sum_mergerRates_eq_lumpedLambdaRate` with its outcome-map
hypothesis discharged. -/
theorem sum_blockMergerRates_eq_lumpedLambdaRate (s : Fin m → Fin n → Fin n) (ξ : ER n)
    (rate : ℕ → ℕ → ℝ) (target : (Fin m → ER n) × (Fin n → ℕ)) :
    ∑ S ∈ univ.filter (fun S : Finset (Quotient ξ) ↦
        2 ≤ S.card ∧ multiState s (mergeSet ξ S) = target), rate (blocks ξ) S.card =
      lumpedLambdaRate (cellLoad (blockCell s ξ)) rate (lambdaOutcome s ξ) target := by
  have hfilter : (univ.filter fun S : Finset (Quotient ξ) ↦
      2 ≤ S.card ∧ multiState s (mergeSet ξ S) = target) =
      univ.filter fun S : Finset (Quotient ξ) ↦
        2 ≤ S.card ∧ lambdaOutcome s ξ (subsetProfile (blockCell s ξ) S) = target := by
    refine filter_congr fun S _ ↦ ?_
    rw [multiState_mergeSet_eq_lambdaOutcome]
  rw [hfilter, blocks, Nat.card_eq_fintype_card]
  convert sum_mergerRates_eq_lumpedLambdaRate (blockCell s ξ) rate (lambdaOutcome s ξ) target

/-- **Counting the Λ-mergers into a lumped target.** The sets of at least two true blocks whose
merger leads to `target` number `lumpedLambdaRate` of the cell loads at unit rate. -/
theorem card_blockMergers_eq_lumpedLambdaRate (s : Fin m → Fin n → Fin n) (ξ : ER n)
    (target : (Fin m → ER n) × (Fin n → ℕ)) :
    ((univ.filter fun S : Finset (Quotient ξ) ↦
        2 ≤ S.card ∧ multiState s (mergeSet ξ S) = target).card : ℝ) =
      lumpedLambdaRate (cellLoad (blockCell s ξ)) (fun _ _ ↦ 1) (lambdaOutcome s ξ) target := by
  rw [← sum_blockMergerRates_eq_lumpedLambdaRate s ξ (fun _ _ ↦ 1) target, sum_const, nsmul_one]

end

end Descent.Pangenome.GraphCoalescent.LambdaLoadOutcome
