/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralBranchExposure

assert_below Descent.Decision Descent.Program

/-!
Clades coarsen backwards along the actual marked ancestral process. Retained
older material was present earlier; every younger clade that intersects an
older clade is contained in it. Both properties compose, including when locally
completed material is removed. No assumed tree ordering is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralCladePartition

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw
open AncestralBranchExposure

variable {D L n : ℕ}

@[simp] theorem mem_locusDescendants (material : Material L n) (locus : Fin L)
    (sample : Fin n) : sample ∈ locusDescendants material locus ↔
      (locus, sample) ∈ material := by
  classical
  simp [locusDescendants]

theorem locusDescendants_mono {first second : Material L n} (h : first ⊆ second)
    (locus : Fin L) : locusDescendants first locus ⊆ locusDescendants second locus := by
  intro sample hsample
  exact (mem_locusDescendants _ _ _).mpr (h ((mem_locusDescendants _ _ _).mp hsample))

theorem locusDescendants_disjoint {first second : Material L n} (h : Disjoint first second)
    (locus : Fin L) : Disjoint (locusDescendants first locus) (locusDescendants second locus) := by
  rw [Finset.disjoint_left]
  intro sample hf hs
  exact Finset.disjoint_left.mp h ((mem_locusDescendants _ _ _).mp hf)
    ((mem_locusDescendants _ _ _).mp hs)

private theorem same_state_relation (s : State D L n) (a b : Lineage D L n)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (locus : Fin L) :
    Disjoint (locusDescendants a.2 locus) (locusDescendants b.2 locus) ∨
      locusDescendants b.2 locus ⊆ locusDescendants a.2 locus := by
  by_cases hab : a = b
  · subst b
    exact Or.inr Finset.Subset.rfl
  · exact Or.inl (locusDescendants_disjoint (s.property.2 ha hb hab) locus)

/-- Coarsening together with the support needed to compose coarsenings after
locally completed loci disappear from the active state. -/
def Extends (younger older : State D L n) : Prop :=
  (∀ a ∈ older.val, ∀ token ∈ a.2, ∃ b ∈ younger.val, token ∈ b.2) ∧
  (∀ a ∈ older.val, ∀ b ∈ younger.val, ∀ locus : Fin L,
    Disjoint (locusDescendants a.2 locus) (locusDescendants b.2 locus) ∨
      locusDescendants b.2 locus ⊆ locusDescendants a.2 locus)

theorem Extends.refl (s : State D L n) : Extends s s :=
  ⟨fun a ha _token ht ↦ ⟨a, ha, ht⟩,
    fun a ha b hb locus ↦ same_state_relation s a b ha hb locus⟩

theorem Extends.trans {first middle last : State D L n}
    (hfirst : Extends first middle) (hlast : Extends middle last) : Extends first last := by
  classical
  constructor
  · intro a ha token ht
    obtain ⟨b, hb, hbt⟩ := hlast.1 a ha token ht
    exact hfirst.1 b hb token hbt
  · intro a ha b hb locus
    by_cases hd : Disjoint (locusDescendants a.2 locus) (locusDescendants b.2 locus)
    · exact Or.inl hd
    · obtain ⟨sample, hsa, hsb⟩ := Finset.not_disjoint_iff.mp hd
      obtain ⟨c, hc, hsc⟩ := hlast.1 a ha (locus, sample)
        ((mem_locusDescendants _ _ _).mp hsa)
      have hsc' : sample ∈ locusDescendants c.2 locus :=
        (mem_locusDescendants _ _ _).mpr hsc
      have hca : locusDescendants c.2 locus ⊆ locusDescendants a.2 locus := by
        rcases hlast.2 a ha c hc locus with hdis | hsub
        · exact (Finset.disjoint_left.mp hdis hsa hsc').elim
        · exact hsub
      have hbc : locusDescendants b.2 locus ⊆ locusDescendants c.2 locus := by
        rcases hfirst.2 c hc b hb locus with hdis | hsub
        · exact (Finset.disjoint_left.mp hdis hsc' hsb).elim
        · exact hsub
      exact Or.inr (hbc.trans hca)

theorem extends_migrate (s : State D L n) (a : Lineage D L n)
    (ha : a ∈ s.val) (destination : Fin D) : Extends s (migrate s a ha destination) := by
  classical
  constructor
  · intro c hc token ht
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨a, ha, ht⟩
    · exact ⟨c, (Finset.mem_erase.mp hc).2, ht⟩
  · intro c hc b hb locus
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact same_state_relation s a b ha hb locus
    · exact same_state_relation s c b (Finset.mem_erase.mp hc).2 hb locus

theorem extends_relabel (s : State D L n) (destination : Fin D → Fin D) :
    Extends s (relabelDemes s destination) := by
  constructor
  · intro c hc token ht
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨old, hold, ht⟩
  · intro c hc b hb locus
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hc
    exact same_state_relation s old b hold hb locus


@[simp] theorem locusDescendants_union (first second : Material L n) (locus : Fin L) :
    locusDescendants (first ∪ second) locus =
      locusDescendants first locus ∪ locusDescendants second locus := by
  classical
  ext sample
  simp

@[simp] theorem locusDescendants_left (material : Material L n) (cut : Fin (L + 1))
    (locus : Fin L) : locusDescendants (leftMaterial material cut) locus =
      if locus.val < cut.val then locusDescendants material locus else ∅ := by
  classical
  ext sample
  by_cases h : locus.val < cut.val <;> simp [leftMaterial, h]

@[simp] theorem locusDescendants_right (material : Material L n) (cut : Fin (L + 1))
    (locus : Fin L) : locusDescendants (rightMaterial material cut) locus =
      if locus.val < cut.val then ∅ else locusDescendants material locus := by
  classical
  ext sample
  by_cases h : locus.val < cut.val
  · simp [rightMaterial, h]
  · simp [rightMaterial, h, Nat.le_of_not_gt h]

theorem locusDescendants_unresolved_of_complete (material : Material L n) (locus : Fin L)
    (h : completedLocus material locus) : locusDescendants (unresolved material) locus = ∅ := by
  classical
  ext sample
  simp [unresolved, h]

theorem locusDescendants_unresolved_of_incomplete (material : Material L n) (locus : Fin L)
    (h : ¬ completedLocus material locus) :
    locusDescendants (unresolved material) locus = locusDescendants material locus := by
  classical
  ext sample
  simp [unresolved, h]

theorem extends_recombine (s : State D L n) (a : Lineage D L n)
    (ha : a ∈ s.val) (cut : Fin (L + 1))
    (hl : (leftMaterial a.2 cut).Nonempty) (hr : (rightMaterial a.2 cut).Nonempty) :
    Extends s (recombine s a ha cut hl hr) := by
  classical
  constructor
  · intro c hc token ht
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨a, ha, (Finset.mem_filter.mp ht).1⟩
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · exact ⟨a, ha, (Finset.mem_filter.mp ht).1⟩
      · exact ⟨c, (Finset.mem_erase.mp hc).2, ht⟩
  · intro c hc b hb locus
    rcases Finset.mem_insert.mp hc with rfl | hc
    · by_cases hcut : locus.val < cut.val
      · simp [locusDescendants_right, hcut]
      · simpa only [locusDescendants_right, hcut, ↓reduceIte] using
          same_state_relation s a b ha hb locus
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · by_cases hcut : locus.val < cut.val
        · simpa only [locusDescendants_left, hcut, ↓reduceIte] using
            same_state_relation s a b ha hb locus
        · simp [locusDescendants_left, hcut]
      · exact same_state_relation s c b (Finset.mem_erase.mp hc).2 hb locus

private theorem member_coalesce (s : State D L n) (a b : Lineage D L n)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (hab : a ≠ b) (hd : a.1 = b.1)
    (c : Lineage D L n) :
    c ∈ (coalesce s a b ha hb hab hd).val ↔
      (c ∈ s.val ∧ c ≠ a ∧ c ≠ b) ∨
      ((unresolved (a.2 ∪ b.2)).Nonempty ∧ c = (a.1, unresolved (a.2 ∪ b.2))) := by
  classical
  unfold coalesce
  dsimp only
  split <;> simp_all only [Finset.mem_insert, Finset.mem_erase] <;> tauto

private theorem merged_clade_relation (s : State D L n) (a b c : Lineage D L n)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (hc : c ∈ s.val) (locus : Fin L) :
    Disjoint (locusDescendants (a.2 ∪ b.2) locus) (locusDescendants c.2 locus) ∨
      locusDescendants c.2 locus ⊆ locusDescendants (a.2 ∪ b.2) locus := by
  classical
  rw [locusDescendants_union]
  by_cases hca : c = a
  · subst c
    exact Or.inr Finset.subset_union_left
  · by_cases hcb : c = b
    · subst c
      exact Or.inr Finset.subset_union_right
    · exact Or.inl (Finset.disjoint_union_left.mpr
        ⟨locusDescendants_disjoint (s.property.2 ha hc (fun h ↦ hca h.symm)) locus,
          locusDescendants_disjoint (s.property.2 hb hc (fun h ↦ hcb h.symm)) locus⟩)

theorem extends_coalesce (s : State D L n) (a b : Lineage D L n)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (hab : a ≠ b) (hd : a.1 = b.1) :
    Extends s (coalesce s a b ha hb hab hd) := by
  classical
  constructor
  · intro c hc token ht
    rcases (member_coalesce s a b ha hb hab hd c).mp hc with ⟨hc, _, _⟩ | ⟨_, rfl⟩
    · exact ⟨c, hc, ht⟩
    · rcases Finset.mem_union.mp (unresolved_subset _ ht) with hta | htb
      · exact ⟨a, ha, hta⟩
      · exact ⟨b, hb, htb⟩
  · intro c hc d hdmem locus
    rcases (member_coalesce s a b ha hb hab hd c).mp hc with ⟨hc, _, _⟩ | ⟨_, rfl⟩
    · exact same_state_relation s c d hc hdmem locus
    · by_cases hcomplete : completedLocus (a.2 ∪ b.2) locus
      · simp [locusDescendants_unresolved_of_complete _ _ hcomplete]
      · simpa only [locusDescendants_unresolved_of_incomplete _ _ hcomplete] using
          merged_clade_relation s a b d ha hb hdmem locus

/-- Every actual proposal preserves the backwards coarsening relation. -/
theorem extends_proposal (s : State D L n) (event : Option (Channel s)) :
    Extends s (proposalNext s event) := by
  rcases event with _ | (event | (event | event))
  · exact Extends.refl s
  · exact extends_migrate s _ event.property.1 _
  · exact extends_coalesce s _ _ event.property.1 event.property.2.1
      event.property.2.2.1 event.property.2.2.2
  · exact extends_recombine s _ event.property.1 _ event.property.2.1 event.property.2.2

/-- The complete marked history coarsens every retained locus, even across
recombination, migration, and removal of locally completed ancestry. -/
theorem extends_terminal {count : ℕ} {s : State D L n} (trace : Trace count s) :
    Extends s (terminal trace) := by
  induction count generalizing s with
  | zero => exact Extends.refl s
  | succ count ih => exact (extends_proposal s trace.1).trans (ih trace.2)

end Descent.Portability.AncestralCladePartition
