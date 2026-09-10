/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Tactic

assert_below Descent.Portability Descent.Decision Descent.Program

/-!
Finite-genome ancestral configurations. A material token identifies a sampled
haploid chromosome at a locus. Distinct active lineages carry disjoint tokens.
Common ancestry unions tokens, recombination partitions them at a breakpoint,
and migration changes only the population. Completed loci are removed from
active material when all their sampled descendants have merged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Coalescent.FiniteGenomeAncestry

variable {D L n : ℕ}

abbrev Material (L n : ℕ) := Finset (Fin L × Fin n)
abbrev Lineage (D L n : ℕ) := Fin D × Material L n

def Valid (lineages : Finset (Lineage D L n)) : Prop :=
  (∀ a ∈ lineages, a.2.Nonempty) ∧
    (↑lineages : Set (Lineage D L n)).Pairwise (fun a b ↦ Disjoint a.2 b.2)

abbrev State (D L n : ℕ) := {lineages : Finset (Lineage D L n) // Valid lineages}

noncomputable instance stateFintype : Fintype (State D L n) := by
  classical
  exact inferInstanceAs (Fintype {s : Finset (Lineage D L n) // Valid s})

theorem valid_empty : Valid (∅ : Finset (Lineage D L n)) := by
  simp [Valid]

theorem Valid.subset {s t : Finset (Lineage D L n)} (hs : Valid s) (ht : t ⊆ s) :
    Valid t := by
  exact ⟨fun a ha ↦ hs.1 a (ht ha), fun a ha b hb hab ↦ hs.2 (ht ha) (ht hb) hab⟩

theorem Valid.insert {s : Finset (Lineage D L n)} (hs : Valid s)
    (a : Lineage D L n) (ha : a.2.Nonempty)
    (hd : ∀ b ∈ s, Disjoint a.2 b.2) : Valid (insert a s) := by
  constructor
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ha
    · exact hs.1 b hb
  · intro b hb c hc hbc
    rcases Finset.mem_insert.mp hb with hba | hbs
    · subst b
      rcases Finset.mem_insert.mp hc with hca | hcs
      · exact (hbc hca.symm).elim
      · exact hd c hcs
    · rcases Finset.mem_insert.mp hc with hca | hcs
      · subst c
        exact (hd b hbs).symm
      · exact hs.2 hbs hcs hbc

/-- The number of active lineages is bounded even when recombination is allowed. -/
theorem lineage_count_bound (s : State D L n) : s.val.card ≤ L * n := by
  calc
    s.val.card = ∑ _a ∈ s.val, 1 := by simp
    _ ≤ ∑ a ∈ s.val, a.2.card := by
      apply Finset.sum_le_sum
      intro a ha
      exact (s.property.1 a ha).card_pos
    _ = (s.val.biUnion Prod.snd).card := by
      exact (Finset.card_biUnion s.property.2).symm
    _ ≤ (Finset.univ : Finset (Fin L × Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = L * n := by simp

/-- Present-day haploid samples begin with one lineage per sampled chromosome.
The caller supplies each chromosome's deme; diploid cohorts repeat that deme
for the two chromosomes of each individual. -/
noncomputable def initialState (sampleDeme : Fin n → Fin D) (hL : 0 < L)
    (_hn : 2 ≤ n) : State D L n := by
  let lineage := fun sample : Fin n ↦
    (sampleDeme sample, (Finset.univ : Finset (Fin L)).product {sample})
  refine ⟨Finset.univ.image lineage, ?_, ?_⟩
  · intro a ha
    obtain ⟨sample, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨(⟨0, hL⟩, sample), by simp [lineage]⟩
  · intro a ha b hb hab
    obtain ⟨first, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨second, _, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.disjoint_left]
    intro token ht hu
    have hf : token.2 = first := Finset.mem_singleton.mp (Finset.mem_product.mp ht).2
    have hs : token.2 = second := Finset.mem_singleton.mp (Finset.mem_product.mp hu).2
    exact hab (congrArg lineage (hf.symm.trans hs))

/-- Migration changes the location of a lineage and preserves its material. -/
noncomputable def migrate (s : State D L n) (a : Lineage D L n)
    (ha : a ∈ s.val) (destination : Fin D) : State D L n := by
  refine ⟨insert (destination, a.2) (s.val.erase a), ?_⟩
  apply (s.property.subset (Finset.erase_subset a s.val)).insert
  · exact s.property.1 a ha
  · intro b hb
    exact s.property.2 ha (Finset.mem_erase.mp hb).2 (Finset.mem_erase.mp hb).1.symm

/-- Deterministic backward population movement, including a population split
or a mass-migration event of proportion one. Distinct lineages remain distinct
because their nonempty descendant material is disjoint. -/
noncomputable def relabelDemes (s : State D L n) (destination : Fin D → Fin D) :
    State D L n := by
  let relabel := fun a : Lineage D L n ↦ (destination a.1, a.2)
  refine ⟨s.val.image relabel, ?_, ?_⟩
  · intro a ha
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp ha
    exact s.property.1 old hold
  · intro a ha b hb hab
    obtain ⟨first, hf, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨second, hs, rfl⟩ := Finset.mem_image.mp hb
    have hdis := s.property.2 hf hs (fun h ↦ hab (congrArg relabel h))
    exact hdis

def completedLocus (material : Material L n) (locus : Fin L) : Prop :=
  ∀ sample : Fin n, (locus, sample) ∈ material

/-- Material above a local MRCA is removed from the active ancestry process. -/
noncomputable def unresolved (material : Material L n) : Material L n := by
  classical
  exact material.filter fun token ↦ ¬ completedLocus material token.1

theorem unresolved_subset (material : Material L n) : unresolved material ⊆ material := by
  classical
  exact Finset.filter_subset _ _

theorem unresolved_complete {material : Material L n} {locus : Fin L}
    (h : completedLocus material locus) (sample : Fin n) :
    (locus, sample) ∉ unresolved material := by
  simp [unresolved, h]

/-- The event record can retain `a`, `b`, and the event time; the next active
state retains only the still-unresolved descendant material. -/
noncomputable def coalesce (s : State D L n) (a b : Lineage D L n)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (_hab : a ≠ b)
    (_sameDeme : a.1 = b.1) : State D L n := by
  let remaining := (s.val.erase a).erase b
  have hremaining : Valid remaining :=
    s.property.subset ((Finset.erase_subset b _).trans (Finset.erase_subset a _))
  let material := unresolved (a.2 ∪ b.2)
  by_cases hm : material.Nonempty
  · refine ⟨insert (a.1, material) remaining, hremaining.insert _ hm ?_⟩
    intro c hc
    have hc' := Finset.mem_erase.mp hc
    have hc'' := Finset.mem_erase.mp hc'.2
    exact (Finset.disjoint_union_left.mpr
      ⟨s.property.2 ha hc''.2 hc''.1.symm,
        s.property.2 hb hc''.2 hc'.1.symm⟩).mono_left (unresolved_subset _)
  · exact ⟨remaining, hremaining⟩

def leftMaterial (material : Material L n) (cut : Fin (L + 1)) : Material L n :=
  material.filter fun token ↦ token.1.val < cut.val

def rightMaterial (material : Material L n) (cut : Fin (L + 1)) : Material L n :=
  material.filter fun token ↦ ¬ token.1.val < cut.val

theorem split_material_union (material : Material L n) (cut : Fin (L + 1)) :
    leftMaterial material cut ∪ rightMaterial material cut = material := by
  ext token
  simp only [leftMaterial, rightMaterial, Finset.mem_union, Finset.mem_filter]
  tauto

theorem split_material_disjoint (material : Material L n) (cut : Fin (L + 1)) :
    Disjoint (leftMaterial material cut) (rightMaterial material cut) := by
  rw [Finset.disjoint_left]
  intro token hl hr
  exact (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hl).2

/-- Only breakpoints with material on both sides are ancestral recombination
channels; a cut in a gap between occupied sites still qualifies. -/
noncomputable def recombine (s : State D L n) (a : Lineage D L n)
    (ha : a ∈ s.val) (cut : Fin (L + 1))
    (hl : (leftMaterial a.2 cut).Nonempty)
    (hr : (rightMaterial a.2 cut).Nonempty) : State D L n := by
  let remaining := s.val.erase a
  have hremaining : Valid remaining := s.property.subset (Finset.erase_subset a _)
  have hleft : Valid (insert (a.1, leftMaterial a.2 cut) remaining) := by
    apply hremaining.insert _ hl
    intro b hb
    exact (s.property.2 ha (Finset.mem_erase.mp hb).2
      (Finset.mem_erase.mp hb).1.symm).mono_left (Finset.filter_subset _ _)
  refine ⟨insert (a.1, rightMaterial a.2 cut)
    (insert (a.1, leftMaterial a.2 cut) remaining), hleft.insert _ hr ?_⟩
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact (split_material_disjoint a.2 cut).symm
  · exact (s.property.2 ha (Finset.mem_erase.mp hb).2
      (Finset.mem_erase.mp hb).1.symm).mono_left (Finset.filter_subset _ _)

end Descent.Coalescent.FiniteGenomeAncestry
