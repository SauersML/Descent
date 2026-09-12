/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulant

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The degree of the connectivity cumulant

NOTE Theorem D states that the connectivity cumulant `C_c(z)` of an interface with `w` fibers
on `n` individuals has degree `n - w + 1`. By (D3), `ConnectivityCumulant`'s
`connectivityCumulant_eq_sum_connected`, its coefficient of `z^j` counts the genealogy
partitions `π` with `j` blocks and `q ⊔ π = ⊤`. The bound therefore says a connecting partition
has at most `n - w + 1` blocks. This module proves that, and the vanishing of the higher
coefficients, from the semimodular rank inequality of the partition lattice:
`card_parts_add_card_parts_le`, `|q| + |π| ≤ n + |q ⊔ π|`.

The rank inequality is proved by inserting one individual at a time with the insertion bijection
of `LahWeights`. Let the new individual `a` join the parts `t_q` of the interface and `t_π` of
the genealogy, or start a new singleton part (`∅`). A common coarsening of the smaller pair is
extended to a common coarsening of the larger pair in one of three ways.
- `a` gets a new part when both `t`'s are empty: the counts `|q|` and `|π|` each grow by one
  and the coarsening gains a part.
- `a` joins the part containing the nonempty `t`'s when they share one: at least one count
  stays and the coarsening keeps its count.
- `a` joins the union of the two containing parts, merged by `mergeParts`: both counts stay and
  the coarsening loses at most one part.

Each extension lies above the finest common coarsening (`insertAt_le`), so the part counts
compare through `Finpartition.card_mono`.

`card_parts_add_card_parts_le_of_connected` is the connected case `|q| + |π| ≤ n + 1`.
`coeff_connectivityCumulant_eq_zero` and `natDegree_connectivityCumulant_le` give the degree
bound `n - w + 1`. That the top coefficient is positive is Theorem E, which is not proved here.

## Empirical status

None. The bodies here are finite combinatorics on the partition lattice of a finite set, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Polynomial
open scoped Classical

noncomputable section

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The partition obtained by merging two distinct parts `w₁` and `w₂` into `w₁ ∪ w₂`. -/
def mergeParts (P : Finpartition s) {w₁ w₂ : Finset α} (h₁ : w₁ ∈ P.parts) (h₂ : w₂ ∈ P.parts)
    (hne : w₁ ≠ w₂) : Finpartition s :=
  Finpartition.ofExistsUnique (insert (w₁ ∪ w₂) ((P.parts.erase w₁).erase w₂))
    (by
      intro p hp
      rcases mem_insert.mp hp with hpw | hp
      · rw [hpw]
        exact union_subset (P.subset h₁) (P.subset h₂)
      · exact P.subset (mem_of_mem_erase (mem_of_mem_erase hp)))
    (by
      intro x hx
      obtain ⟨u, ⟨hu, hxu⟩, huniq⟩ := P.existsUnique_mem hx
      by_cases hu12 : u = w₁ ∨ u = w₂
      · refine ⟨w₁ ∪ w₂, ⟨mem_insert_self _ _, ?_⟩, ?_⟩
        · rcases hu12 with h | h
          · exact mem_union_left _ (h ▸ hxu)
          · exact mem_union_right _ (h ▸ hxu)
        · rintro p ⟨hp, hxp⟩
          rcases mem_insert.mp hp with hpw | hp
          · exact hpw
          · have hpu : p = u := huniq p ⟨mem_of_mem_erase (mem_of_mem_erase hp), hxp⟩
            rcases hu12 with h | h
            · exact absurd (hpu.trans h) (ne_of_mem_erase (mem_of_mem_erase hp))
            · exact absurd (hpu.trans h) (ne_of_mem_erase hp)
      · push_neg at hu12
        refine ⟨u, ⟨mem_insert_of_mem (mem_erase.mpr ⟨hu12.2, mem_erase.mpr ⟨hu12.1, hu⟩⟩),
          hxu⟩, ?_⟩
        rintro p ⟨hp, hxp⟩
        rcases mem_insert.mp hp with hpw | hp
        · rw [hpw] at hxp
          rcases mem_union.mp hxp with hx1 | hx2
          · exact absurd (huniq w₁ ⟨h₁, hx1⟩).symm hu12.1
          · exact absurd (huniq w₂ ⟨h₂, hx2⟩).symm hu12.2
        · exact huniq p ⟨mem_of_mem_erase (mem_of_mem_erase hp), hxp⟩)
    (by
      intro hempty
      rcases mem_insert.mp hempty with h | h
      · obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts h₁
        have hmem : x ∈ w₁ ∪ w₂ := mem_union_left _ hx
        rw [← h] at hmem
        exact notMem_empty x hmem
      · exact P.empty_notMem_parts (mem_of_mem_erase (mem_of_mem_erase h)))

/-- Merging two parts loses exactly one part. -/
theorem card_parts_mergeParts (P : Finpartition s) {w₁ w₂ : Finset α} (h₁ : w₁ ∈ P.parts)
    (h₂ : w₂ ∈ P.parts) (hne : w₁ ≠ w₂) : #(mergeParts P h₁ h₂ hne).parts + 1 = #P.parts := by
  show #(insert (w₁ ∪ w₂) ((P.parts.erase w₁).erase w₂)) + 1 = #P.parts
  have hnot : w₁ ∪ w₂ ∉ (P.parts.erase w₁).erase w₂ := by
    intro hmem
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts h₁
    have heq : w₁ ∪ w₂ = w₁ :=
      P.eq_of_mem_parts (mem_of_mem_erase (mem_of_mem_erase hmem)) h₁ (mem_union_left _ hx) hx
    exact ne_of_mem_erase (mem_of_mem_erase hmem) heq
  have htwo : 1 < #P.parts := one_lt_card.mpr ⟨w₁, h₁, w₂, h₂, hne⟩
  rw [card_insert_of_notMem hnot, card_erase_of_mem (mem_erase.mpr ⟨hne.symm, h₂⟩),
    card_erase_of_mem h₁]
  omega

/-- Merging two parts coarsens the partition. -/
theorem le_mergeParts (P : Finpartition s) {w₁ w₂ : Finset α} (h₁ : w₁ ∈ P.parts)
    (h₂ : w₂ ∈ P.parts) (hne : w₁ ≠ w₂) : P ≤ mergeParts P h₁ h₂ hne := by
  intro u hu
  by_cases hu12 : u = w₁ ∨ u = w₂
  · refine ⟨w₁ ∪ w₂, mem_insert_self _ _, ?_⟩
    rcases hu12 with h | h
    · rw [h]
      exact subset_union_left
    · rw [h]
      exact subset_union_right
  · push_neg at hu12
    exact ⟨u, mem_insert_of_mem (mem_erase.mpr ⟨hu12.2, mem_erase.mpr ⟨hu12.1, hu⟩⟩), le_rfl⟩

section Insert

variable {a : α}

/-- The part of the removed individual, with the individual deleted, is a new-part marker or a
part of the smaller partition. -/
theorem erase_part_mem_insert_parts (ha : a ∉ s) (Q : Finpartition (insert a s)) :
    (Q.part a).erase a ∈ insert ∅ (removeElement ha Q).parts := by
  rcases eq_or_ne ((Q.part a).erase a) ∅ with hempty | hne
  · rw [hempty]
    exact mem_insert_self _ _
  · refine mem_insert_of_mem ((mem_removeElement_parts ha Q _).mpr
      ⟨Q.part a, Q.part_mem.mpr (mem_insert_self a s), fun hsub ↦ hne ?_, ?_⟩)
    · rw [← sdiff_singleton_eq_erase]
      exact sdiff_eq_empty_iff_subset.mpr hsub
    · exact sdiff_singleton_eq_erase a (Q.part a)

/-- After inserting `a` at `w`, the part of `a` is `insert a w`. -/
theorem part_insertAt (P : Finpartition s) (ha : a ∉ s) {w : Finset α}
    (hw : w ∈ insert ∅ P.parts) : (insertAt P ha w).part a = insert a w := by
  have hapart : a ∈ (insertAt P ha w).part a :=
    (insertAt P ha w).mem_part_self.mpr (mem_insert_self a s)
  rw [← part_insertAt_erase P ha hw, insert_erase hapart]

/-- Inserting as a new singleton part adds one part. -/
theorem card_parts_insertAt_empty (P : Finpartition s) (ha : a ∉ s) :
    #(insertAt P ha ∅).parts = #P.parts + 1 := by
  rw [insertAt, dif_neg P.empty_notMem_parts, (blockWeight_insertNewPart P ha).2]

/-- Inserting into an existing part keeps the number of parts. -/
theorem card_parts_insertAt_of_mem (P : Finpartition s) (ha : a ∉ s) {t : Finset α}
    (ht : t ∈ P.parts) : #(insertAt P ha t).parts = #P.parts := by
  rw [insertAt, dif_pos ht, (blockWeight_insertIntoPart P ha ht).2]

/-- An insertion lies below a partition of `insert a s` when the smaller partition lies below its
restriction and the part receiving `a` lies inside the part of `a`. -/
theorem insertAt_le (ha : a ∉ s) (P : Finpartition s) (σ : Finpartition (insert a s))
    (hP : P ≤ removeElement ha σ) (t : Finset α) (hsub : insert a t ⊆ σ.part a) :
    insertAt P ha t ≤ σ := by
  have hapart : σ.part a ∈ σ.parts := σ.part_mem.mpr (mem_insert_self a s)
  have hold : ∀ p ∈ P.parts, ∃ d ∈ σ.parts, p ≤ d := by
    intro p hp
    obtain ⟨c, hc, hpc⟩ := hP hp
    obtain ⟨d, hd, -, rfl⟩ := (mem_removeElement_parts ha σ c).mp hc
    exact ⟨d, hd, (hpc : p ⊆ d \ {a}).trans sdiff_subset⟩
  intro u hu
  unfold insertAt at hu
  split_ifs at hu with ht
  · rw [insertIntoPart_parts] at hu
    rcases mem_insert.mp hu with hut | hu
    · exact ⟨σ.part a, hapart, hut ▸ hsub⟩
    · exact hold u (mem_of_mem_erase hu)
  · rw [insertNewPart_parts] at hu
    rcases mem_insert.mp hu with hua | hu
    · exact ⟨σ.part a, hapart,
        hua ▸ singleton_subset_iff.mpr (hsub (mem_insert_self a t))⟩
    · exact hold u hu

end Insert

/-- **Semimodularity of the partition lattice.** For two partitions of `s`,
`|q| + |π| ≤ |s| + |q ⊔ π|`, with `q ⊔ π` the finest common coarsening. -/
theorem card_parts_add_card_parts_le (s : Finset α) :
    ∀ q π : Finpartition s, #q.parts + #π.parts ≤ #s + #(commonCoarsening q π).parts := by
  induction s using Finset.induction_on with
  | empty =>
    intro q π
    rw [finpartition_empty_eq_bot q, finpartition_empty_eq_bot π]
    simp
  | insert a s ha ih =>
    intro q π
    have hq : insertAt (removeElement ha q) ha ((q.part a).erase a) = q :=
      insertAt_removeElement ha q
    have hπ : insertAt (removeElement ha π) ha ((π.part a).erase a) = π :=
      insertAt_removeElement ha π
    have hmq := erase_part_mem_insert_parts ha q
    have hmπ := erase_part_mem_insert_parts ha π
    have hIH := ih (removeElement ha q) (removeElement ha π)
    have hle := (le_commonCoarsening_iff (removeElement ha q) (removeElement ha π)
      (commonCoarsening (removeElement ha q) (removeElement ha π))).mp le_rfl
    generalize removeElement ha q = q' at hq hmq hIH hle
    generalize removeElement ha π = π' at hπ hmπ hIH hle
    generalize (q.part a).erase a = tq at hq hmq
    generalize (π.part a).erase a = tπ at hπ hmπ
    generalize commonCoarsening q' π' = τ' at hIH hle
    subst hq hπ
    have hsubset : ∀ (W : Finpartition s) (w : Finset α), w ∈ insert ∅ W.parts →
        q' ≤ W → π' ≤ W → tq ⊆ w → tπ ⊆ w →
        #(insertAt W ha w).parts
          ≤ #(commonCoarsening (insertAt q' ha tq) (insertAt π' ha tπ)).parts := by
      intro W w hw hqW hπW htqw htπw
      refine Finpartition.card_mono ((le_commonCoarsening_iff _ _ _).mpr ⟨?_, ?_⟩)
      · refine insertAt_le ha q' _ (by rw [removeElement_insertAt]; exact hqW) tq ?_
        rw [part_insertAt W ha hw]
        exact insert_subset_insert a htqw
      · refine insertAt_le ha π' _ (by rw [removeElement_insertAt]; exact hπW) tπ ?_
        rw [part_insertAt W ha hw]
        exact insert_subset_insert a htπw
    rw [card_insert_of_notMem ha]
    rcases mem_insert.mp hmq with hq0 | hqmem <;> rcases mem_insert.mp hmπ with hπ0 | hπmem
    · have h := hsubset τ' ∅ (mem_insert_self _ _) hle.1 hle.2 (subset_empty.mpr hq0)
        (subset_empty.mpr hπ0)
      rw [card_parts_insertAt_empty] at h
      rw [hq0, hπ0, card_parts_insertAt_empty, card_parts_insertAt_empty]
      omega
    · obtain ⟨w, hw, htπw⟩ := hle.2 hπmem
      have h := hsubset τ' w (mem_insert_of_mem hw) hle.1 hle.2
        (by rw [hq0]; exact empty_subset w) htπw
      rw [card_parts_insertAt_of_mem τ' ha hw] at h
      rw [hq0, card_parts_insertAt_empty, card_parts_insertAt_of_mem π' ha hπmem]
      omega
    · obtain ⟨w, hw, htqw⟩ := hle.1 hqmem
      have h := hsubset τ' w (mem_insert_of_mem hw) hle.1 hle.2 htqw
        (by rw [hπ0]; exact empty_subset w)
      rw [card_parts_insertAt_of_mem τ' ha hw] at h
      rw [hπ0, card_parts_insertAt_empty, card_parts_insertAt_of_mem q' ha hqmem]
      omega
    · obtain ⟨w₁, hw₁, htqw₁⟩ := hle.1 hqmem
      obtain ⟨w₂, hw₂, htπw₂⟩ := hle.2 hπmem
      rw [card_parts_insertAt_of_mem q' ha hqmem, card_parts_insertAt_of_mem π' ha hπmem]
      by_cases hw : w₁ = w₂
      · have htπw₁ : tπ ⊆ w₁ := hw ▸ htπw₂
        have h := hsubset τ' w₁ (mem_insert_of_mem hw₁) hle.1 hle.2 htqw₁ htπw₁
        rw [card_parts_insertAt_of_mem τ' ha hw₁] at h
        omega
      · have hmerge := card_parts_mergeParts τ' hw₁ hw₂ hw
        have hunion : w₁ ∪ w₂ ∈ (mergeParts τ' hw₁ hw₂ hw).parts := mem_insert_self _ _
        have h := hsubset (mergeParts τ' hw₁ hw₂ hw) (w₁ ∪ w₂) (mem_insert_of_mem hunion)
          (hle.1.trans (le_mergeParts τ' hw₁ hw₂ hw)) (hle.2.trans (le_mergeParts τ' hw₁ hw₂ hw))
          (htqw₁.trans subset_union_left) (htπw₂.trans subset_union_right)
        rw [card_parts_insertAt_of_mem _ ha hunion] at h
        omega

/-- **A connecting partition has at most `n - w + 1` blocks.** If `q ⊔ π = ⊤` on a nonempty set
`s`, then `|q| + |π| ≤ |s| + 1`. -/
theorem card_parts_add_card_parts_le_of_connected (q π : Finpartition s) (hs : s.Nonempty)
    (h : ReportConnected q π) : #q.parts + #π.parts ≤ #s + 1 := by
  have hbound := card_parts_add_card_parts_le s q π
  rw [(reportConnected_iff q π).mp h, (card_parts_eq_one_iff (⊤ : Finpartition s) hs).mpr rfl]
    at hbound
  exact hbound

/-- **NOTE Theorem D: the degree.** For an interface `q` with `w` fibers on `n` individuals, every
coefficient of `C_q(z)` above `z^{n - w + 1}` vanishes. -/
theorem coeff_connectivityCumulant_eq_zero (q : Finpartition s) (hs : s.Nonempty) {j : ℕ}
    (hj : #s + 1 < #q.parts + j) : (connectivityCumulant q).coeff j = 0 := by
  rw [connectivityCumulant_eq_sum_connected q hs, Polynomial.finset_sum_coeff]
  refine sum_eq_zero fun π hπ ↦ ?_
  have hbound := card_parts_add_card_parts_le_of_connected q π hs (mem_filter.mp hπ).2
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

/-- **NOTE Theorem D: the degree.** `deg C_q ≤ n - w + 1`. -/
theorem natDegree_connectivityCumulant_le (q : Finpartition s) (hs : s.Nonempty) :
    (connectivityCumulant q).natDegree ≤ #s + 1 - #q.parts := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have hqs := q.card_parts_le_card
  exact coeff_connectivityCumulant_eq_zero q hs (by omega)

end

end Descent.Pangenome.GraphCoalescent
