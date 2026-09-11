/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MergerDepth

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Hidden loads: what a pangenome graph deleted, restored as a count

`Descent.Pangenome.GraphCoalescent.Visibility` shows that a graph's report
`observed s ξ = ξ ⊔ graphKer s` of the panel's coalescent is not a Markov chain: the next step
depends on how many un-coalesced ancestral lineages hide behind each reported component, and
the report forgot that number. This file restores exactly that number and counts every
transition in terms of it. The spec is `PANGENOME_HIDDEN_CLOCK.md` §3, Theorem A.

The load `hiddenLoad s ξ C` of a report component `C` is the number of true ancestral blocks of
`ξ` inside `C`, the spec's `L_C`. The loads add up to the true block count (`sum_hiddenLoad`),
are positive (`hiddenLoad_pos`), and before any coalescence are the fiber sizes of the
interface (`hiddenLoad_bot`).

Every cover `ξ ⋖ η` of the coalescent is of one of two kinds, and the report either stays or
takes one covering step itself (`observed_eq_or_covers`). An invisible merger joins two true
blocks inside one component: the report is unchanged (`observed_merge_of_rel`), that
component's load drops by one (`hiddenLoad_merge_of_rel_self`), and every other load is
unchanged (`hiddenLoad_merge_of_rel_of_not_rel`). A visible merger joins two components: the
report becomes their merge (`observed_merge_of_not_rel`), the joined component carries
`a + b - 1` (`hiddenLoad_merge_of_not_rel_self`), and every other load is unchanged
(`hiddenLoad_merge_of_not_rel_of_not_rel`). There are `C(L_C, 2)` invisible covers inside `C`
(`card_invisibleCovers`, spec (A1)) and `L_C L_D` visible covers joining `C` and `D`
(`card_visibleCovers`, spec (A2)); with Kingman's unit rate on every cover these are the
transition rates. Together they account for all `C(K, 2)` covers
(`sum_choose_two_hiddenLoad_add_sum_pairs`, spec (A3)). At the bottom the visible count is the
product `c_A c_B` of fiber sizes (`card_visibleCovers_bot`), which the group header had recorded
as not formalized.

Scope. What is proved is the combinatorial content of Theorem A: the classification of covers,
the load updates and the cover counts, with the unit rate per cover of
`Descent.Coalescent.StateSpace`. The continuous-time Markov chain and the probabilistic reading
of strong lumpability are not constructed here.

## Empirical status

None. The bodies here are counts of equivalence classes on a finite set: the interface `s` and
the coalescent state `ξ` are supplied, and no measurement can bear on a cardinality.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset
open scoped Classical

noncomputable section

/-! ### Loads -/

/-- The report component containing a true ancestral block. The report coarsens `ξ`, so every
block of `ξ` lies inside exactly one reported component. -/
def reportComponent {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    Quotient ξ → Quotient (observed s ξ) :=
  blockMap (le_observed s ξ)

/-- The component of an individual's block is that individual's report class. -/
theorem reportComponent_mk {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (x : Fin n) :
    reportComponent s ξ (Quotient.mk ξ x) = Quotient.mk (observed s ξ) x :=
  rfl

/-- The true ancestral blocks inside a report component. -/
def hiddenBlocks {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (C : Quotient (observed s ξ)) :
    Finset (Quotient ξ) :=
  univ.filter fun block ↦ reportComponent s ξ block = C

/-- **The load `L_C(ξ)`**: the number of true ancestral lineages hidden inside the report
component `C`. -/
def hiddenLoad {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (C : Quotient (observed s ξ)) : ℕ :=
  (hiddenBlocks s ξ C).card

/-- A true block lies in a report component exactly when its individuals are reported in that
class. -/
theorem mk_mem_hiddenBlocks_iff {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (x z : Fin n) :
    Quotient.mk ξ x ∈ hiddenBlocks s ξ (Quotient.mk (observed s ξ) z) ↔
      (observed s ξ).r x z := by
  simp only [hiddenBlocks, mem_filter, mem_univ, true_and, reportComponent_mk]
  exact Quotient.eq

/-- **The loads add up to the true block count**: `∑_C L_C(ξ) = |ξ|`. -/
theorem sum_hiddenLoad {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∑ C, hiddenLoad s ξ C = blocks ξ := by
  have h := card_eq_sum_card_fiberwise (f := reportComponent s ξ)
    (s := (univ : Finset (Quotient ξ))) (t := (univ : Finset (Quotient (observed s ξ))))
    fun _ _ ↦ mem_univ _
  rw [card_univ, ← Nat.card_eq_fintype_card] at h
  convert h.symm using 1

/-- Every report component hides at least one true lineage. -/
theorem hiddenLoad_pos {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (C : Quotient (observed s ξ)) :
    0 < hiddenLoad s ξ C := by
  obtain ⟨block, hblock⟩ := blockMap_surjective (le_observed s ξ) C
  exact card_pos.mpr ⟨block, mem_filter.mpr ⟨mem_univ _, hblock⟩⟩

/-- **Before any coalescence the loads are the fiber sizes**: the report component of `x` hides
exactly the haplotypes the interface merged into `x`'s graph state. -/
theorem hiddenLoad_bot {n : ℕ} (s : Fin n → Fin n) (x : Fin n) :
    hiddenLoad s ⊥ (Quotient.mk (observed s ⊥) x) = Linkage.fiberCard s x := by
  have himage : hiddenBlocks s ⊥ (Quotient.mk (observed s ⊥) x) =
      (Linkage.fiber s x).image (Quotient.mk (⊥ : ER n)) := by
    ext block
    obtain ⟨y, rfl⟩ := quotient_mk_surjective (⊥ : ER n) block
    rw [mk_mem_hiddenBlocks_iff, observed_bot, graphKer_rel_iff, mem_image]
    constructor
    · intro hy
      exact ⟨y, Linkage.mem_fiber.mpr hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Quotient.exact hzy
      subst hzy'
      exact Linkage.mem_fiber.mp hz
  rw [hiddenLoad, himage, card_image_of_injective _ fun a b h ↦ Quotient.exact h]
  rfl

/-! ### Two kinds of cover -/

/-- **An invisible merger.** Merging two true blocks the graph already reports together leaves
the report unchanged. -/
theorem observed_merge_of_rel {n : ℕ} {s : Fin n → Fin n} {ξ : ER n} {x y : Fin n}
    (hab : Quotient.mk ξ x ≠ Quotient.mk ξ y) (hxy : (observed s ξ).r x y) :
    observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y)) = observed s ξ :=
  le_antisymm
    (observed_le (merge_le_of_le_of_rel (le_observed s ξ) hab rfl rfl hxy)
      (graphKer_le_observed s ξ))
    (observed_mono s (le_merge ξ _ _))

/-- **A visible merger.** Merging two true blocks the graph reports apart merges their two
report components. -/
theorem observed_merge_of_not_rel {n : ℕ} {s : Fin n → Fin n} {ξ : ER n} {x y : Fin n}
    (hab : Quotient.mk ξ x ≠ Quotient.mk ξ y) (hxy : ¬ (observed s ξ).r x y) :
    observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y)) =
      merge (observed s ξ) (Quotient.mk (observed s ξ) x) (Quotient.mk (observed s ξ) y) := by
  have hCD : Quotient.mk (observed s ξ) x ≠ Quotient.mk (observed s ξ) y :=
    fun h ↦ hxy (Quotient.exact h)
  refine le_antisymm (observed_le ?_ (le_trans (graphKer_le_observed s ξ) (le_merge _ _ _))) ?_
  · exact merge_le_of_le_of_rel (le_trans (le_observed s ξ) (le_merge _ _ _)) hab rfl rfl
      (merge_rel (observed s ξ) (Quotient.mk (observed s ξ) x) (Quotient.mk (observed s ξ) y)
        rfl rfl)
  · exact merge_le_of_le_of_rel (observed_mono s (le_merge ξ _ _)) hCD rfl rfl
      (le_observed s _ (merge_rel ξ (Quotient.mk ξ x) (Quotient.mk ξ y) rfl rfl))

/-- **Every cover is an invisible or a visible merger**: the report either stays where it was
or takes one covering step itself. -/
theorem observed_eq_or_covers {n : ℕ} (s : Fin n → Fin n) {ξ η : ER n} (h : Covers ξ η) :
    observed s η = observed s ξ ∨ Covers (observed s ξ) (observed s η) := by
  obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge ξ η).mp h
  obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ A
  obtain ⟨y, rfl⟩ := quotient_mk_surjective ξ B
  by_cases hxy : (observed s ξ).r x y
  · exact Or.inl (observed_merge_of_rel hAB hxy)
  · right
    rw [observed_merge_of_not_rel hAB hxy]
    exact merge_covers _ fun hq ↦ hxy (Quotient.exact hq)

/-! ### How the loads move -/

/-- The true blocks inside the component of `z` are the blocks of the individuals reported with
`z`. -/
theorem hiddenBlocks_mk {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (z : Fin n) :
    hiddenBlocks s ξ (Quotient.mk (observed s ξ) z) =
      (univ.filter fun y ↦ (observed s ξ).r y z).image (Quotient.mk ξ) := by
  ext block
  obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ block
  rw [mk_mem_hiddenBlocks_iff, mem_image]
  constructor
  · intro hx
    exact ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact (observed s ξ).iseqv.trans (le_observed s ξ (Quotient.exact hyx.symm))
      (mem_filter.mp hy).2

/-- The blocks of a merged state met by a set of individuals are the images, under the fold, of
the blocks they meet before the merger. -/
theorem card_image_mk_merge {n : ℕ} (ξ : ER n) (a b : Quotient ξ) (S : Finset (Fin n)) :
    (S.image (Quotient.mk (merge ξ a b))).card =
      ((S.image (Quotient.mk ξ)).image (mergeMap ξ a b)).card := by
  rw [image_image]
  have hlift : S.image (mergeMap ξ a b ∘ Quotient.mk ξ) =
      (S.image (Quotient.mk (merge ξ a b))).image
        (Quotient.lift (fun x ↦ mergeMap ξ a b (Quotient.mk ξ x))
          fun u v (h : (merge ξ a b).r u v) ↦
            (h : mergeMap ξ a b (Quotient.mk ξ u) = mergeMap ξ a b (Quotient.mk ξ v))) := by
    rw [image_image]
    rfl
  rw [hlift, card_image_of_injective _ (Setoid.ker_lift_injective _)]

/-- Folding one block onto another loses one element of a set of blocks exactly when both named
blocks are in the set. -/
theorem card_image_mergeMap {n : ℕ} (ξ : ER n) {a b : Quotient ξ} (hab : a ≠ b)
    (T : Finset (Quotient ξ)) :
    (T.image (mergeMap ξ a b)).card = if a ∈ T ∧ b ∈ T then T.card - 1 else T.card := by
  split_ifs with hT
  · have himage : T.image (mergeMap ξ a b) = T.erase b := by
      ext c
      simp only [mem_image, mem_erase]
      constructor
      · rintro ⟨d, hd, rfl⟩
        by_cases hdb : d = b
        · subst hdb
          rw [mergeMap_apply_self]
          exact ⟨hab, hT.1⟩
        · rw [mergeMap_apply_of_ne ξ a b d hdb]
          exact ⟨hdb, hd⟩
      · rintro ⟨hcb, hc⟩
        exact ⟨c, hc, mergeMap_apply_of_ne ξ a b c hcb⟩
    rw [himage, card_erase_of_mem hT.2]
  · refine card_image_of_injOn fun d hd e he hde ↦ ?_
    rcases (mergeMap_eq_iff ξ hab d e).mp hde with h | ⟨hd', he'⟩ | ⟨hd', he'⟩
    · exact h
    · exact absurd ⟨hd' ▸ mem_coe.mp hd, he' ▸ mem_coe.mp he⟩ hT
    · exact absurd ⟨he' ▸ mem_coe.mp he, hd' ▸ mem_coe.mp hd⟩ hT

/-- The relation of a merged report, pair by pair. -/
theorem merge_rel_iff_of_not_rel {n : ℕ} (Y : ER n) {x y : Fin n} (hxy : ¬ Y.r x y)
    (u v : Fin n) :
    (merge Y (Quotient.mk Y x) (Quotient.mk Y y)).r u v ↔
      Y.r u v ∨ (Y.r u x ∧ Y.r v y) ∨ (Y.r u y ∧ Y.r v x) := by
  have hCD : Quotient.mk Y x ≠ Quotient.mk Y y := fun h ↦ hxy (Quotient.exact h)
  constructor
  · intro h
    have h' : mergeMap Y (Quotient.mk Y x) (Quotient.mk Y y) (Quotient.mk Y u) =
        mergeMap Y (Quotient.mk Y x) (Quotient.mk Y y) (Quotient.mk Y v) := h
    rcases (mergeMap_eq_iff Y hCD _ _).mp h' with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Quotient.exact h1)
    · exact Or.inr (Or.inl ⟨Quotient.exact h1, Quotient.exact h2⟩)
    · exact Or.inr (Or.inr ⟨Quotient.exact h1, Quotient.exact h2⟩)
  · intro h
    show mergeMap Y (Quotient.mk Y x) (Quotient.mk Y y) (Quotient.mk Y u) =
      mergeMap Y (Quotient.mk Y x) (Quotient.mk Y y) (Quotient.mk Y v)
    refine (mergeMap_eq_iff Y hCD _ _).mpr ?_
    rcases h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Quotient.sound h1)
    · exact Or.inr (Or.inl ⟨Quotient.sound h1, Quotient.sound h2⟩)
    · exact Or.inr (Or.inr ⟨Quotient.sound h1, Quotient.sound h2⟩)

/-- **An invisible merger removes one hidden lineage from its component.** -/
theorem hiddenLoad_merge_of_rel_self {n : ℕ} {s : Fin n → Fin n} {ξ : ER n} {x y : Fin n}
    (hab : Quotient.mk ξ x ≠ Quotient.mk ξ y) (hxy : (observed s ξ).r x y) :
    hiddenLoad s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))
        (Quotient.mk (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))) x) =
      hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1 := by
  rw [hiddenLoad, hiddenBlocks_mk, observed_merge_of_rel hab hxy, card_image_mk_merge,
    ← hiddenBlocks_mk, card_image_mergeMap ξ hab, if_pos, hiddenLoad]
  exact ⟨(mk_mem_hiddenBlocks_iff s ξ x x).mpr ((observed s ξ).iseqv.refl x),
    (mk_mem_hiddenBlocks_iff s ξ y x).mpr ((observed s ξ).iseqv.symm hxy)⟩

/-- An invisible merger leaves the loads of the other components unchanged. -/
theorem hiddenLoad_merge_of_rel_of_not_rel {n : ℕ} {s : Fin n → Fin n} {ξ : ER n}
    {x y z : Fin n} (hab : Quotient.mk ξ x ≠ Quotient.mk ξ y) (hxy : (observed s ξ).r x y)
    (hxz : ¬ (observed s ξ).r x z) :
    hiddenLoad s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))
        (Quotient.mk (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))) z) =
      hiddenLoad s ξ (Quotient.mk (observed s ξ) z) := by
  rw [hiddenLoad, hiddenBlocks_mk, observed_merge_of_rel hab hxy, card_image_mk_merge,
    ← hiddenBlocks_mk, card_image_mergeMap ξ hab, if_neg, hiddenLoad]
  rintro ⟨hx, -⟩
  exact hxz ((mk_mem_hiddenBlocks_iff s ξ x z).mp hx)

/-- **A visible merger pools the two loads**: the joined component carries `a + b - 1`. -/
theorem hiddenLoad_merge_of_not_rel_self {n : ℕ} {s : Fin n → Fin n} {ξ : ER n} {x y : Fin n}
    (hab : Quotient.mk ξ x ≠ Quotient.mk ξ y) (hxy : ¬ (observed s ξ).r x y) :
    hiddenLoad s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))
        (Quotient.mk (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))) x) =
      hiddenLoad s ξ (Quotient.mk (observed s ξ) x) +
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) - 1 := by
  have hfilter : (univ.filter fun u ↦
      (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))).r u x) =
        (univ.filter fun u ↦ (observed s ξ).r u x) ∪
          (univ.filter fun u ↦ (observed s ξ).r u y) := by
    rw [observed_merge_of_not_rel hab hxy]
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_union, merge_rel_iff_of_not_rel _ hxy]
    constructor
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨h, (observed s ξ).iseqv.refl x⟩)
  have hdisjoint : Disjoint (hiddenBlocks s ξ (Quotient.mk (observed s ξ) x))
      (hiddenBlocks s ξ (Quotient.mk (observed s ξ) y)) := by
    refine disjoint_left.mpr fun block hx hy ↦ ?_
    obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ block
    exact hxy ((observed s ξ).iseqv.trans
      ((observed s ξ).iseqv.symm ((mk_mem_hiddenBlocks_iff s ξ u x).mp hx))
      ((mk_mem_hiddenBlocks_iff s ξ u y).mp hy))
  rw [hiddenLoad, hiddenBlocks_mk, hfilter, card_image_mk_merge, image_union, ← hiddenBlocks_mk,
    ← hiddenBlocks_mk, card_image_mergeMap ξ hab, if_pos, card_union_of_disjoint hdisjoint,
    hiddenLoad, hiddenLoad]
  exact ⟨mem_union_left _ ((mk_mem_hiddenBlocks_iff s ξ x x).mpr ((observed s ξ).iseqv.refl x)),
    mem_union_right _ ((mk_mem_hiddenBlocks_iff s ξ y y).mpr ((observed s ξ).iseqv.refl y))⟩

/-- A visible merger leaves the loads of the components it does not join unchanged. -/
theorem hiddenLoad_merge_of_not_rel_of_not_rel {n : ℕ} {s : Fin n → Fin n} {ξ : ER n}
    {x y z : Fin n} (hab : Quotient.mk ξ x ≠ Quotient.mk ξ y) (hxy : ¬ (observed s ξ).r x y)
    (hxz : ¬ (observed s ξ).r x z) (hyz : ¬ (observed s ξ).r y z) :
    hiddenLoad s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))
        (Quotient.mk (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))) z) =
      hiddenLoad s ξ (Quotient.mk (observed s ξ) z) := by
  have hfilter : (univ.filter fun u ↦
      (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))).r u z) =
        univ.filter fun u ↦ (observed s ξ).r u z := by
    rw [observed_merge_of_not_rel hab hxy]
    ext u
    simp only [mem_filter, mem_univ, true_and, merge_rel_iff_of_not_rel _ hxy]
    constructor
    · rintro (h | ⟨-, h⟩ | ⟨-, h⟩)
      · exact h
      · exact absurd ((observed s ξ).iseqv.symm h) hyz
      · exact absurd ((observed s ξ).iseqv.symm h) hxz
    · exact fun h ↦ Or.inl h
  rw [hiddenLoad, hiddenBlocks_mk, hfilter, card_image_mk_merge, ← hiddenBlocks_mk,
    card_image_mergeMap ξ hab, if_neg, hiddenLoad]
  rintro ⟨hx, -⟩
  exact hxz ((mk_mem_hiddenBlocks_iff s ξ x z).mp hx)

/-! ### Counting the covers of each kind -/

/-- The mergers of two blocks taken from a set `T` of blocks number `C(|T|, 2)`. -/
theorem card_merges_of_subset {n : ℕ} (ξ : ER n) (T : Finset (Quotient ξ)) :
    Nat.card {η : ER n // ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ η = merge ξ a b} = T.card.choose 2 := by
  have hmem : ∀ p ∈ T.powersetCard 2, ∀ hp : p.card = 2, pairFst hp ∈ T ∧ pairSnd hp ∈ T := by
    intro p hp hcard
    have hsub := (mem_powersetCard.mp hp).1
    have hspec := (pair_spec hcard).2
    exact ⟨hsub ((Finset.ext_iff.mp hspec _).mpr (mem_insert_self _ _)),
      hsub ((Finset.ext_iff.mp hspec _).mpr (mem_insert.mpr (Or.inr (mem_singleton_self _))))⟩
  let f : T.powersetCard 2 → {η : ER n // ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ η = merge ξ a b} :=
    fun p ↦ ⟨merge ξ (pairFst (mem_powersetCard.mp p.2).2) (pairSnd (mem_powersetCard.mp p.2).2),
      pairFst (mem_powersetCard.mp p.2).2, (hmem p.1 p.2 (mem_powersetCard.mp p.2).2).1,
      pairSnd (mem_powersetCard.mp p.2).2, (hmem p.1 p.2 (mem_powersetCard.mp p.2).2).2,
      (pair_spec (mem_powersetCard.mp p.2).2).1, rfl⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
      have hpair := (merge_eq_merge_iff ξ (pair_spec (mem_powersetCard.mp hp).2).1
        (pair_spec (mem_powersetCard.mp hq).2).1).mp (congrArg Subtype.val hpq)
      exact Subtype.ext ((pair_spec (mem_powersetCard.mp hp).2).2.trans
        (hpair.trans (pair_spec (mem_powersetCard.mp hq).2).2.symm))
    · rintro ⟨η, a, ha, b, hb, hab, rfl⟩
      have hp : ({a, b} : Finset (Quotient ξ)) ∈ T.powersetCard 2 :=
        mem_powersetCard.mpr ⟨insert_subset ha (singleton_subset_iff.mpr hb), card_pair hab⟩
      refine ⟨⟨{a, b}, hp⟩, Subtype.ext ?_⟩
      exact (merge_eq_merge_iff ξ (pair_spec (mem_powersetCard.mp hp).2).1 hab).mpr
        (pair_spec (mem_powersetCard.mp hp).2).2.symm
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_coe,
    card_powersetCard]

/-- The mergers of a block of `T` with a block of a disjoint set `U` number `|T| |U|`. -/
theorem card_merges_across {n : ℕ} (ξ : ER n) {T U : Finset (Quotient ξ)} (hTU : Disjoint T U) :
    Nat.card {η : ER n // ∃ a ∈ T, ∃ b ∈ U, η = merge ξ a b} = T.card * U.card := by
  have hne : ∀ {a b : Quotient ξ}, a ∈ T → b ∈ U → a ≠ b :=
    fun ha hb hab ↦ disjoint_left.mp hTU ha (hab ▸ hb)
  let f : T ×ˢ U → {η : ER n // ∃ a ∈ T, ∃ b ∈ U, η = merge ξ a b} := fun p ↦
    ⟨merge ξ p.1.1 p.1.2, p.1.1, (mem_product.mp p.2).1, p.1.2, (mem_product.mp p.2).2, rfl⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨a', b'⟩, hq⟩ hpq
      obtain ⟨ha, hb⟩ := mem_product.mp hp
      obtain ⟨ha', hb'⟩ := mem_product.mp hq
      have hpair := (merge_eq_merge_iff ξ (hne ha hb) (hne ha' hb')).mp (congrArg Subtype.val hpq)
      have haa : a ∈ ({a', b'} : Finset (Quotient ξ)) := hpair ▸ mem_insert_self a {b}
      have hbb : b ∈ ({a', b'} : Finset (Quotient ξ)) :=
        hpair ▸ mem_insert_of_mem (mem_singleton_self b)
      simp only [mem_insert, mem_singleton] at haa hbb
      rcases haa with rfl | rfl
      · rcases hbb with rfl | rfl
        · exact absurd rfl (hne ha hb)
        · rfl
      · exact absurd hb' (disjoint_left.mp hTU ha)
    · rintro ⟨η, a, ha, b, hb, rfl⟩
      exact ⟨⟨(a, b), mem_product.mpr ⟨ha, hb⟩⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_coe,
    card_product]

/-- The invisible covers inside a report component: mergers of two of its true blocks. -/
def invisibleCovers {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (C : Quotient (observed s ξ)) :
    Set (ER n) :=
  {η | ∃ a ∈ hiddenBlocks s ξ C, ∃ b ∈ hiddenBlocks s ξ C, a ≠ b ∧ η = merge ξ a b}

/-- The visible covers joining two report components: mergers of a true block of one with a true
block of the other. -/
def visibleCovers {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (C D : Quotient (observed s ξ)) :
    Set (ER n) :=
  {η | ∃ a ∈ hiddenBlocks s ξ C, ∃ b ∈ hiddenBlocks s ξ D, η = merge ξ a b}

/-- An invisible cover is a cover of the coalescent that the graph does not report. -/
theorem covers_observed_eq_of_mem_invisibleCovers {n : ℕ} {s : Fin n → Fin n} {ξ η : ER n}
    {C : Quotient (observed s ξ)} (h : η ∈ invisibleCovers s ξ C) :
    Covers ξ η ∧ observed s η = observed s ξ := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := h
  obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ a
  obtain ⟨y, rfl⟩ := quotient_mk_surjective ξ b
  exact ⟨merge_covers ξ hab, observed_merge_of_rel hab
    (Quotient.exact ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm))⟩

/-- A visible cover joining two distinct components is a cover the graph reports as a cover. -/
theorem covers_covers_of_mem_visibleCovers {n : ℕ} {s : Fin n → Fin n} {ξ η : ER n}
    {C D : Quotient (observed s ξ)} (hCD : C ≠ D) (h : η ∈ visibleCovers s ξ C D) :
    Covers ξ η ∧ Covers (observed s ξ) (observed s η) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ a
  obtain ⟨y, rfl⟩ := quotient_mk_surjective ξ b
  have hxy : ¬ (observed s ξ).r x y := fun hxy ↦
    hCD ((mem_filter.mp ha).2.symm.trans ((Quotient.sound hxy).trans (mem_filter.mp hb).2))
  have hab : Quotient.mk ξ x ≠ Quotient.mk ξ y := fun hq ↦ hxy (le_observed s ξ (Quotient.exact hq))
  refine ⟨merge_covers ξ hab, ?_⟩
  rw [observed_merge_of_not_rel hab hxy]
  exact merge_covers _ fun hq ↦ hxy (Quotient.exact hq)

/-- **Spec (A1): an invisible transition at rate `C(L_C, 2)`.** A report component hiding `L_C`
true lineages has exactly `C(L_C, 2)` invisible covers. -/
theorem card_invisibleCovers {n : ℕ} (s : Fin n → Fin n) (ξ : ER n)
    (C : Quotient (observed s ξ)) :
    Nat.card (invisibleCovers s ξ C) = (hiddenLoad s ξ C).choose 2 :=
  card_merges_of_subset ξ (hiddenBlocks s ξ C)

/-- **Spec (A2): a visible transition at rate `L_C L_D`.** Two distinct report components have
exactly `L_C L_D` visible covers joining them. -/
theorem card_visibleCovers {n : ℕ} (s : Fin n → Fin n) (ξ : ER n)
    {C D : Quotient (observed s ξ)} (hCD : C ≠ D) :
    Nat.card (visibleCovers s ξ C D) = hiddenLoad s ξ C * hiddenLoad s ξ D :=
  card_merges_across ξ (disjoint_left.mpr fun _ hC hD ↦
    hCD ((mem_filter.mp hC).2.symm.trans (mem_filter.mp hD).2))

/-- **The exact visible count from the bottom**: two graph states with fiber sizes `c_A` and
`c_B` are joined by `c_A c_B` covers of the panel's coalescent, the count
`Descent.Pangenome.GraphCoalescent.Visibility` only bounds below by two. -/
theorem card_visibleCovers_bot {n : ℕ} (s : Fin n → Fin n) {x y : Fin n} (hxy : s x ≠ s y) :
    Nat.card (visibleCovers s ⊥ (Quotient.mk (observed s ⊥) x) (Quotient.mk (observed s ⊥) y)) =
      Linkage.fiberCard s x * Linkage.fiberCard s y := by
  have hCD : Quotient.mk (observed s ⊥) x ≠ Quotient.mk (observed s ⊥) y := by
    intro hq
    have hrel : (observed s ⊥).r x y := Quotient.exact hq
    rw [observed_bot, graphKer_rel_iff] at hrel
    exact hxy hrel
  rw [card_visibleCovers s ⊥ hCD, hiddenLoad_bot, hiddenLoad_bot]

/-- **Pairs split by where they fall**, spec (A3) as arithmetic: for any finite family of loads,
the pairs inside one member and the pairs across two members together are all the pairs. -/
theorem sum_choose_two_add_sum_pairs {ι : Type*} [DecidableEq ι] (S : Finset ι) (L : ι → ℕ) :
    ∑ C ∈ S, (L C).choose 2 + ∑ p ∈ S.powersetCard 2, ∏ C ∈ p, L C =
      (∑ C ∈ S, L C).choose 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    have hsplit : (insert x T).powersetCard 2 =
        T.powersetCard 2 ∪ (T.powersetCard 1).image (insert x) :=
      powersetCard_succ_insert hx 1
    have hdisjoint : Disjoint (T.powersetCard 2) ((T.powersetCard 1).image (insert x)) := by
      refine disjoint_left.mpr fun p hp hp' ↦ ?_
      obtain ⟨q, -, rfl⟩ := mem_image.mp hp'
      exact hx ((mem_powersetCard.mp hp).1 (mem_insert_self x q))
    have hinj : Set.InjOn (insert x) (T.powersetCard 1 : Set (Finset ι)) := by
      intro p hp q hq hpq
      have hxp : x ∉ p := fun h ↦ hx ((mem_powersetCard.mp (mem_coe.mp hp)).1 h)
      have hxq : x ∉ q := fun h ↦ hx ((mem_powersetCard.mp (mem_coe.mp hq)).1 h)
      rw [← erase_insert hxp, ← erase_insert hxq, hpq]
    have hsingle : ∑ p ∈ T.powersetCard 1, ∏ C ∈ insert x p, L C = L x * ∑ C ∈ T, L C := by
      rw [powersetCard_one, sum_map, mul_sum]
      refine sum_congr rfl fun C hC ↦ ?_
      have hxC : x ∉ ({C} : Finset ι) := by
        rw [mem_singleton]
        exact fun h ↦ hx (h ▸ hC)
      simp [prod_insert hxC]
    have hchoose : ((L x + ∑ C ∈ T, L C).choose 2 : ℚ) =
        ((L x).choose 2 : ℚ) + L x * ∑ C ∈ T, (L C : ℚ) + ((∑ C ∈ T, L C).choose 2 : ℚ) := by
      simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_sum]
      ring
    have hchoose' : (L x + ∑ C ∈ T, L C).choose 2 =
        (L x).choose 2 + L x * ∑ C ∈ T, L C + (∑ C ∈ T, L C).choose 2 := by
      exact_mod_cast hchoose
    rw [sum_insert hx, sum_insert hx, hsplit, sum_union hdisjoint, sum_image hinj, hsingle,
      hchoose', ← ih]
    ring

/-- **Spec (A3).** The invisible and visible covers account for every cover exactly once:
`∑_C C(L_C, 2) + ∑_{C<D} L_C L_D = C(K, 2)` with `K = |ξ|`. -/
theorem sum_choose_two_hiddenLoad_add_sum_pairs {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∑ C, (hiddenLoad s ξ C).choose 2 + ∑ p ∈ univ.powersetCard 2, ∏ C ∈ p, hiddenLoad s ξ C =
      (blocks ξ).choose 2 := by
  rw [sum_choose_two_add_sum_pairs, sum_hiddenLoad]

end

end Descent.Pangenome.GraphCoalescent
