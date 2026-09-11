/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.Polynomial.Coeff

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Lah weights: weighted set partitions and the polynomials `A_m`

The pangenome hidden-clock note (§6, equation (D1)) weights a partition `π` of `m` individuals
by `∏_{B ∈ π} |B|!` and collects the weights by the number of blocks:
`A_m(z) = Σ_j (m! / j!) C(m - 1, j - 1) z^j`. The coefficients are the Lah numbers. This module
proves both sides of that display.

`lahNumber` is defined by the recurrence `L(m + 1, j + 1) = L(m, j) + (m + j + 1) L(m, j + 1)`.
`lahNumber_mul_factorial` is the closed form of (D1), `L(m, j) j! = m! C(m - 1, j - 1)`, and
`lahPolynomial R m` is `A_m` over any commutative semiring.

The counting half is proved on Mathlib's `Finpartition`, where parts are finite sets and the
weight `blockWeight P = ∏_{t ∈ P.parts} |t|!` is literal. The engine is an insertion bijection:
the partitions of `insert a s` are exactly the partitions of `s` with `a` added as a new
singleton part (`insertNewPart`) or added to one existing part (`insertIntoPart`).
`removeElement` inverts both, and `sum_finpartition_insert` is the resulting sum identity. A new
singleton leaves the weight unchanged and adds a block; joining a part of size `k` multiplies
the weight by `k + 1`, and those factors sum to `|s| + (number of parts)`. That is the Lah
recurrence, so `sum_blockWeight_card_eq_lahNumber` gives
`Σ_{|P| = j} blockWeight P = L(|s|, j)`. `sum_blockWeight_X_pow_eq_lahPolynomial` is the
polynomial form of (D1).

`card_parts_ofSetoid` ties the vocabulary to the corpus: a coalescent state
`Coalescent.ER n`, read as a finite partition, has as many parts as it has
`Coalescent.blocks`.

## Empirical status

None. The bodies here are finite combinatorics: products of factorials over the parts of a
finite partition, and a recurrence of natural numbers, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset

/-! ## Lah numbers -/

/-- The Lah numbers `L(m, j)`: the ways to split `m` labeled individuals into `j` nonempty
blocks, each carrying a linear order. A new individual either starts its own block or is placed
in one of the `m + j + 1` gaps of the existing ordered blocks, which is the recurrence. -/
def lahNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | m + 1, j + 1 => lahNumber m j + (m + j + 1) * lahNumber m (j + 1)

/-- The Lah recurrence, as an equation. -/
theorem lahNumber_succ_succ (m j : ℕ) :
    lahNumber (m + 1) (j + 1) = lahNumber m j + (m + j + 1) * lahNumber m (j + 1) := rfl

/-- A nonempty set has no partition into zero blocks. -/
theorem lahNumber_succ_zero (m : ℕ) : lahNumber (m + 1) 0 = 0 := rfl

/-- There are no partitions into more blocks than individuals. -/
theorem lahNumber_eq_zero_of_lt : ∀ {m j : ℕ}, m < j → lahNumber m j = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | m + 1, j + 1, h => by
    rw [lahNumber_succ_succ, lahNumber_eq_zero_of_lt (by omega : m < j),
      lahNumber_eq_zero_of_lt (by omega : m < j + 1), mul_zero, add_zero]

/-- **NOTE (D1), the closed form of the coefficients.** `L(k + 1, i + 1) (i + 1)! =
(k + 1)! C(k, i)`, that is `L(m, j) = (m! / j!) C(m - 1, j - 1)` for `m, j ≥ 1`. -/
theorem lahNumber_succ_mul_factorial (k i : ℕ) :
    lahNumber (k + 1) (i + 1) * (i + 1).factorial = (k + 1).factorial * k.choose i := by
  induction k generalizing i with
  | zero =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [lahNumber_succ_succ, Nat.choose_eq_zero_of_lt (by omega : 0 < i + 1)]
      simp [lahNumber]
  | succ k ih =>
    cases i with
    | zero =>
      have h0 := ih 0
      rw [lahNumber_succ_succ, lahNumber_succ_zero, Nat.factorial_succ (k + 1)]
      simp only [Nat.choose_zero_right, zero_add, mul_one, Nat.factorial_one] at h0 ⊢
      rw [mul_comm (k + 1 + 0 + 1), h0]
      ring
    | succ i =>
      by_cases hik : i ≤ k
      · obtain ⟨d, rfl⟩ : ∃ d, k = i + d := ⟨k - i, by omega⟩
        have h1 := ih i
        have h2 := ih (i + 1)
        have hright := Nat.choose_succ_right_eq (i + d) i
        rw [Nat.add_sub_cancel_left] at hright
        rw [lahNumber_succ_succ, Nat.factorial_succ (i + 1), Nat.factorial_succ (i + d + 1),
          Nat.choose_succ_succ]
        rw [Nat.factorial_succ (i + 1)] at h2
        zify at h1 h2 hright ⊢
        linear_combination (↑i + 2) * h1 + (2 * ↑i + ↑d + 3) * h2
          + ((i + d + 1).factorial : ℤ) * hright
      · have hzero : lahNumber (k + 1 + 1) (i + 1 + 1) = 0 :=
          lahNumber_eq_zero_of_lt (by omega)
        rw [hzero, Nat.choose_eq_zero_of_lt (by omega), zero_mul, mul_zero]

/-- **NOTE (D1), closed form.** For `m, j ≥ 1`, `L(m, j) j! = m! C(m - 1, j - 1)`. -/
theorem lahNumber_mul_factorial (m j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) :
    lahNumber m j * j.factorial = m.factorial * (m - 1).choose (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simpa using lahNumber_succ_mul_factorial k i

/-- **NOTE (D1).** The Lah polynomial `A_m(z) = Σ_j L(m, j) z^j`. -/
noncomputable def lahPolynomial (R : Type*) [CommSemiring R] (m : ℕ) : Polynomial R :=
  ∑ j ∈ range (m + 1), Polynomial.C (lahNumber m j : R) * Polynomial.X ^ j

/-- The coefficients of `A_m` are the Lah numbers. -/
theorem coeff_lahPolynomial (R : Type*) [CommSemiring R] (m j : ℕ) :
    (lahPolynomial R m).coeff j = lahNumber m j := by
  rw [lahPolynomial, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with hj
  · rfl
  · rw [lahNumber_eq_zero_of_lt (by simp only [mem_range, not_lt] at hj; omega), Nat.cast_zero]

/-! ## Inserting one individual into a finite partition -/

section Insertion

variable {α : Type*} [DecidableEq α] {s : Finset α} {a : α}

/-- A partition of `insert a s` from a partition of `s`: `a` becomes a new singleton part. -/
def insertNewPart (P : Finpartition s) (ha : a ∉ s) : Finpartition (insert a s) :=
  P.extend (b := ({a} : Finset α)) (by simp) (disjoint_singleton_right.mpr ha)
    (by rw [sup_eq_union, union_comm, ← insert_eq])

/-- A partition of `insert a s` from a partition of `s`: `a` joins the part `t`. -/
def insertIntoPart (P : Finpartition s) (ha : a ∉ s) {t : Finset α} (ht : t ∈ P.parts) :
    Finpartition (insert a s) :=
  Finpartition.ofExistsUnique (insert (insert a t) (P.parts.erase t))
    (by
      intro p hp
      rcases mem_insert.mp hp with hpt | hp
      · rw [hpt]
        exact insert_subset_insert a (P.le ht)
      · exact (P.le (mem_of_mem_erase hp)).trans (subset_insert a s))
    (by
      intro x hx
      rcases mem_insert.mp hx with hxa | hxs
      · subst hxa
        refine ⟨insert x t, ⟨mem_insert_self _ _, mem_insert_self _ _⟩, ?_⟩
        rintro p ⟨hp, hxp⟩
        rcases mem_insert.mp hp with hpt | hp
        · exact hpt
        · exact absurd (P.le (mem_of_mem_erase hp) hxp) ha
      · obtain ⟨u, ⟨hu, hxu⟩, huniq⟩ := P.existsUnique_mem hxs
        by_cases hut : u = t
        · subst hut
          refine ⟨insert a u, ⟨mem_insert_self _ _, mem_insert_of_mem hxu⟩, ?_⟩
          rintro p ⟨hp, hxp⟩
          rcases mem_insert.mp hp with hpt | hp
          · exact hpt
          · exact absurd (huniq p ⟨mem_of_mem_erase hp, hxp⟩) (ne_of_mem_erase hp)
        · refine ⟨u, ⟨mem_insert_of_mem (mem_erase.mpr ⟨hut, hu⟩), hxu⟩, ?_⟩
          rintro p ⟨hp, hxp⟩
          rcases mem_insert.mp hp with hpt | hp
          · rw [hpt] at hxp
            rcases mem_insert.mp hxp with hxa | hxt
            · exact absurd (hxa ▸ hxs) ha
            · exact absurd (huniq t ⟨ht, hxt⟩).symm hut
          · exact huniq p ⟨mem_of_mem_erase hp, hxp⟩)
    (by
      intro hempty
      rcases mem_insert.mp hempty with h | h
      · exact insert_ne_empty a t h.symm
      · exact P.empty_notMem_parts (mem_of_mem_erase h))

/-- Insert `a` into the part `t` when `t` is a part, and as a new singleton part otherwise. -/
def insertAt (P : Finpartition s) (ha : a ∉ s) (t : Finset α) : Finpartition (insert a s) :=
  if ht : t ∈ P.parts then insertIntoPart P ha ht else insertNewPart P ha

/-- The partition of `s` left after deleting `a` from a partition of `insert a s`. -/
def removeElement (ha : a ∉ s) (Q : Finpartition (insert a s)) : Finpartition s :=
  (Q.avoid {a}).copy (by
    ext x
    by_cases hx : x = a
    · subst hx
      simp [ha]
    · simp [hx])

@[simp] theorem insertNewPart_parts (P : Finpartition s) (ha : a ∉ s) :
    (insertNewPart P ha).parts = insert {a} P.parts := rfl

@[simp] theorem insertIntoPart_parts (P : Finpartition s) (ha : a ∉ s) {t : Finset α}
    (ht : t ∈ P.parts) : (insertIntoPart P ha ht).parts = insert (insert a t) (P.parts.erase t) :=
  rfl

theorem mem_removeElement_parts (ha : a ∉ s) (Q : Finpartition (insert a s)) (u : Finset α) :
    u ∈ (removeElement ha Q).parts ↔ ∃ d ∈ Q.parts, ¬d ⊆ {a} ∧ d \ {a} = u := by
  simp only [removeElement, Finpartition.copy_parts, Finpartition.mem_avoid, le_iff_subset]

/-- Parts of a partition of `s` avoid every `a ∉ s`. -/
theorem notMem_of_mem_parts (P : Finpartition s) (ha : a ∉ s) {t : Finset α}
    (ht : t ∈ P.parts) : a ∉ t :=
  fun hat ↦ ha (P.le ht hat)

omit [DecidableEq α] in
/-- A nonempty set avoiding `a` is not contained in `{a}`. -/
theorem not_subset_singleton_of_notMem {t : Finset α} (hne : t.Nonempty) (hat : a ∉ t) :
    ¬t ⊆ {a} := by
  intro hsub
  obtain ⟨x, hx⟩ := hne
  have hxa : x = a := mem_singleton.mp (hsub hx)
  exact hat (hxa ▸ hx)

/-- Removing `a` after inserting it anywhere returns the original partition. -/
theorem removeElement_insertAt (P : Finpartition s) (ha : a ∉ s) (t : Finset α) :
    removeElement ha (insertAt P ha t) = P := by
  ext u
  rw [mem_removeElement_parts]
  unfold insertAt
  split_ifs with ht
  · rw [insertIntoPart_parts]
    constructor
    · rintro ⟨d, hd, -, rfl⟩
      rcases mem_insert.mp hd with hdt | hdP
      · rw [hdt, insert_sdiff_of_mem _ (mem_singleton_self a), sdiff_singleton_eq_erase,
          erase_eq_of_notMem (notMem_of_mem_parts P ha ht)]
        exact ht
      · rw [sdiff_singleton_eq_erase,
          erase_eq_of_notMem (notMem_of_mem_parts P ha (mem_of_mem_erase hdP))]
        exact mem_of_mem_erase hdP
    · intro hu
      by_cases hut : u = t
      · subst hut
        refine ⟨insert a u, mem_insert_self _ _, ?_, ?_⟩
        · exact fun hsub ↦ not_subset_singleton_of_notMem (P.nonempty_of_mem_parts ht)
            (notMem_of_mem_parts P ha ht) ((subset_insert a u).trans hsub)
        · rw [insert_sdiff_of_mem _ (mem_singleton_self a), sdiff_singleton_eq_erase,
            erase_eq_of_notMem (notMem_of_mem_parts P ha ht)]
      · refine ⟨u, mem_insert_of_mem (mem_erase.mpr ⟨hut, hu⟩), ?_, ?_⟩
        · exact not_subset_singleton_of_notMem (P.nonempty_of_mem_parts hu)
            (notMem_of_mem_parts P ha hu)
        · rw [sdiff_singleton_eq_erase, erase_eq_of_notMem (notMem_of_mem_parts P ha hu)]
  · rw [insertNewPart_parts]
    constructor
    · rintro ⟨d, hd, hnot, rfl⟩
      rcases mem_insert.mp hd with hda | hdP
      · exact absurd (fun x hx ↦ by rw [hda] at hx; exact hx) hnot
      · rw [sdiff_singleton_eq_erase, erase_eq_of_notMem (notMem_of_mem_parts P ha hdP)]
        exact hdP
    · intro hu
      refine ⟨u, mem_insert_of_mem hu, not_subset_singleton_of_notMem
        (P.nonempty_of_mem_parts hu) (notMem_of_mem_parts P ha hu), ?_⟩
      rw [sdiff_singleton_eq_erase, erase_eq_of_notMem (notMem_of_mem_parts P ha hu)]

/-- After inserting `a` at `t ∈ insert ∅ P.parts`, the part of `a` with `a` removed is `t`. -/
theorem part_insertAt_erase (P : Finpartition s) (ha : a ∉ s) {t : Finset α}
    (ht : t ∈ insert ∅ P.parts) : ((insertAt P ha t).part a).erase a = t := by
  unfold insertAt
  split_ifs with htP
  · have hpart : (insertIntoPart P ha htP).part a = insert a t :=
      Finpartition.part_eq_of_mem _ (by rw [insertIntoPart_parts]; exact mem_insert_self _ _)
        (mem_insert_self _ _)
    rw [hpart, erase_insert (notMem_of_mem_parts P ha htP)]
  · have hte : t = ∅ := by
      rcases mem_insert.mp ht with h | h
      · exact h
      · exact absurd h htP
    have hpart : (insertNewPart P ha).part a = {a} :=
      Finpartition.part_eq_of_mem _ (by rw [insertNewPart_parts]; exact mem_insert_self _ _)
        (mem_singleton_self a)
    rw [hpart, hte, erase_singleton]

/-- Inserting `a` back where it was removed returns the original partition of `insert a s`. -/
theorem insertAt_removeElement (ha : a ∉ s) (Q : Finpartition (insert a s)) :
    insertAt (removeElement ha Q) ha ((Q.part a).erase a) = Q := by
  have hpart : Q.part a ∈ Q.parts := Q.part_mem.mpr (mem_insert_self a s)
  have hapart : a ∈ Q.part a := Q.mem_part_self.mpr (mem_insert_self a s)
  have hothers : ∀ d ∈ Q.parts, d ≠ Q.part a → a ∉ d := fun d hd hne had ↦
    hne (Q.eq_of_mem_parts hd hpart had hapart)
  have hrest : ∀ d ∈ Q.parts, d ≠ Q.part a → d \ {a} = d := fun d hd hne ↦ by
    rw [sdiff_singleton_eq_erase, erase_eq_of_notMem (hothers d hd hne)]
  have hrestNot : ∀ d ∈ Q.parts, d ≠ Q.part a → ¬d ⊆ {a} := fun d hd hne ↦
    not_subset_singleton_of_notMem (Q.nonempty_of_mem_parts hd) (hothers d hd hne)
  unfold insertAt
  split_ifs with ht
  · ext u
    rw [insertIntoPart_parts]
    constructor
    · intro hu
      rcases mem_insert.mp hu with hut | hu
      · rw [hut, insert_erase hapart]
        exact hpart
      · obtain ⟨hne, hu⟩ := mem_erase.mp hu
        obtain ⟨d, hd, -, rfl⟩ := (mem_removeElement_parts ha Q u).mp hu
        by_cases hdpart : d = Q.part a
        · subst hdpart
          rw [sdiff_singleton_eq_erase] at hne
          exact absurd rfl hne
        · rw [hrest d hd hdpart]
          exact hd
    · intro hu
      by_cases hupart : u = Q.part a
      · subst hupart
        rw [insert_erase hapart]
        exact mem_insert_self _ _
      · refine mem_insert_of_mem (mem_erase.mpr ⟨?_, ?_⟩)
        · intro heq
          obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hu
          have hxpart : x ∈ Q.part a := by
            rw [heq] at hx
            exact mem_of_mem_erase hx
          exact hupart (Q.eq_of_mem_parts hu hpart hx hxpart)
        · exact (mem_removeElement_parts ha Q u).mpr ⟨u, hu, hrestNot u hu hupart,
            hrest u hu hupart⟩
  · have hempty : (Q.part a).erase a = ∅ := by
      by_contra hne
      exact ht ((mem_removeElement_parts ha Q _).mpr ⟨Q.part a, hpart, fun hsub ↦ hne (by
        rw [← sdiff_singleton_eq_erase]
        exact sdiff_eq_empty_iff_subset.mpr hsub), by rw [sdiff_singleton_eq_erase]⟩)
    have hsingle : Q.part a = {a} := by
      rw [← insert_erase hapart, hempty]
      rfl
    ext u
    rw [insertNewPart_parts]
    constructor
    · intro hu
      rcases mem_insert.mp hu with hua | hu
      · rw [hua, ← hsingle]
        exact hpart
      · obtain ⟨d, hd, hnot, rfl⟩ := (mem_removeElement_parts ha Q u).mp hu
        by_cases hdpart : d = Q.part a
        · rw [hdpart, hsingle] at hnot
          exact absurd (subset_refl _) hnot
        · rw [hrest d hd hdpart]
          exact hd
    · intro hu
      by_cases hupart : u = Q.part a
      · rw [hupart, hsingle]
        exact mem_insert_self _ _
      · exact mem_insert_of_mem ((mem_removeElement_parts ha Q u).mpr
          ⟨u, hu, hrestNot u hu hupart, hrest u hu hupart⟩)

/-- **The insertion bijection as a sum identity.** Summing over the partitions of `insert a s`
is summing over the partitions of `s` and over where `a` goes: a new singleton part (`∅`) or
one of the existing parts. -/
theorem sum_finpartition_insert {M : Type*} [AddCommMonoid M] (ha : a ∉ s)
    (F : Finpartition (insert a s) → M) :
    ∑ Q, F Q = ∑ P : Finpartition s, ∑ t ∈ insert ∅ P.parts, F (insertAt P ha t) := by
  rw [sum_sigma' univ (fun P : Finpartition s ↦ insert ∅ P.parts)
    (fun P t ↦ F (insertAt P ha t))]
  refine sum_nbij' (fun Q ↦ (⟨removeElement ha Q, (Q.part a).erase a⟩ :
      Σ _ : Finpartition s, Finset α)) (fun x ↦ insertAt x.1 ha x.2) ?_ ?_ ?_ ?_ ?_
  · intro Q _
    refine mem_sigma.mpr ⟨mem_univ _, ?_⟩
    show (Q.part a).erase a ∈ insert ∅ (removeElement ha Q).parts
    by_cases hempty : (Q.part a).erase a = ∅
    · rw [hempty]
      exact mem_insert_self _ _
    · refine mem_insert_of_mem ((mem_removeElement_parts ha Q _).mpr ⟨Q.part a,
        Q.part_mem.mpr (mem_insert_self a s), fun hsub ↦ hempty ?_, ?_⟩)
      · rw [← sdiff_singleton_eq_erase]
        exact sdiff_eq_empty_iff_subset.mpr hsub
      · rw [sdiff_singleton_eq_erase]
  · intro x _
    exact mem_univ _
  · intro Q _
    exact insertAt_removeElement ha Q
  · rintro ⟨P, t⟩ hx
    have ht : t ∈ insert ∅ P.parts := (mem_sigma.mp hx).2
    simp only [removeElement_insertAt, part_insertAt_erase P ha ht]
  · intro Q _
    rw [insertAt_removeElement ha Q]

end Insertion

/-! ## Weighted counts -/

section Weights

variable {α : Type*} [DecidableEq α] {s : Finset α} {a : α}

/-- The weight `∏_{B ∈ π} |B|!` of NOTE (D1): the number of ways to order every block. -/
def blockWeight (P : Finpartition s) : ℕ := ∏ t ∈ P.parts, (#t).factorial

/-- A new singleton part adds a block and leaves the weight unchanged. -/
theorem blockWeight_insertNewPart (P : Finpartition s) (ha : a ∉ s) :
    blockWeight (insertNewPart P ha) = blockWeight P ∧
      #(insertNewPart P ha).parts = #P.parts + 1 := by
  have hnot : ({a} : Finset α) ∉ P.parts := fun hmem ↦
    notMem_of_mem_parts P ha hmem (mem_singleton_self a)
  refine ⟨?_, ?_⟩
  · rw [blockWeight, insertNewPart_parts, prod_insert hnot, card_singleton, Nat.factorial_one,
      one_mul, blockWeight]
  · rw [insertNewPart_parts, card_insert_of_notMem hnot]

/-- Joining a part of size `k` multiplies the weight by `k + 1` and keeps the block count. -/
theorem blockWeight_insertIntoPart (P : Finpartition s) (ha : a ∉ s) {t : Finset α}
    (ht : t ∈ P.parts) :
    blockWeight (insertIntoPart P ha ht) = (#t + 1) * blockWeight P ∧
      #(insertIntoPart P ha ht).parts = #P.parts := by
  have hnot : insert a t ∉ P.parts.erase t := fun hmem ↦
    notMem_of_mem_parts P ha (mem_of_mem_erase hmem) (mem_insert_self a t)
  have hat : a ∉ t := notMem_of_mem_parts P ha ht
  refine ⟨?_, ?_⟩
  · rw [blockWeight, insertIntoPart_parts, prod_insert hnot, card_insert_of_notMem hat,
      Nat.factorial_succ, mul_assoc, mul_prod_erase P.parts (fun u ↦ (#u).factorial) ht,
      blockWeight]
  · rw [insertIntoPart_parts, card_insert_of_notMem hnot, card_erase_of_mem ht,
      Nat.sub_add_cancel (card_pos.mpr ⟨t, ht⟩)]

/-- The factors a new individual can contribute sum to `|s|` plus the number of parts. -/
theorem sum_card_add_one_parts (P : Finpartition s) :
    ∑ t ∈ P.parts, (#t + 1) = #s + #P.parts := by
  rw [sum_add_distrib, P.sum_card_parts, card_eq_sum_ones P.parts]

/-- The empty set has exactly one partition, with no parts. -/
theorem finpartition_empty_eq_bot (P : Finpartition (∅ : Finset α)) : P = ⊥ := by
  ext u
  have hP : P.parts = ∅ := Finpartition.parts_eq_empty_iff.mpr rfl
  simp [hP]

/-- **NOTE (D1), counting form.** The partitions of `s` into `j` parts, each weighted by
`∏_{B} |B|!`, total the Lah number `L(|s|, j)`. -/
theorem sum_blockWeight_card_eq_lahNumber (s : Finset α) (j : ℕ) :
    ∑ P : Finpartition s, (if #P.parts = j then blockWeight P else 0) = lahNumber #s j := by
  induction s using Finset.induction_on generalizing j with
  | empty =>
    rw [sum_eq_single (⊥ : Finpartition (∅ : Finset α))
      (fun P _ hne ↦ absurd (finpartition_empty_eq_bot P) hne) (fun h ↦ absurd (mem_univ _) h)]
    cases j with
    | zero => simp [blockWeight, lahNumber]
    | succ j => simp [lahNumber]
  | insert a s ha ih =>
    rw [sum_finpartition_insert ha, card_insert_of_notMem ha]
    have hstep : ∀ P : Finpartition s,
        ∑ t ∈ insert ∅ P.parts,
            (if #(insertAt P ha t).parts = j then blockWeight (insertAt P ha t) else 0)
          = (if #P.parts + 1 = j then blockWeight P else 0)
            + (#s + j) * (if #P.parts = j then blockWeight P else 0) := by
      intro P
      rw [sum_insert P.empty_notMem_parts]
      congr 1
      · rw [insertAt, dif_neg P.empty_notMem_parts, (blockWeight_insertNewPart P ha).1,
          (blockWeight_insertNewPart P ha).2]
      · calc ∑ t ∈ P.parts,
              (if #(insertAt P ha t).parts = j then blockWeight (insertAt P ha t) else 0)
            = ∑ t ∈ P.parts, (if #P.parts = j then (#t + 1) * blockWeight P else 0) :=
              sum_congr rfl fun t ht ↦ by
                rw [insertAt, dif_pos ht, (blockWeight_insertIntoPart P ha ht).1,
                  (blockWeight_insertIntoPart P ha ht).2]
          _ = (#s + j) * (if #P.parts = j then blockWeight P else 0) := by
              split_ifs with hj
              · rw [← sum_mul, sum_card_add_one_parts, hj]
              · simp
    rw [sum_congr rfl fun P _ ↦ hstep P, sum_add_distrib, ← mul_sum, ih j]
    cases j with
    | zero =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, sum_const_zero, zero_add]
      cases hcard : #s with
      | zero => simp [lahNumber]
      | succ m => rw [lahNumber_succ_zero, lahNumber_succ_zero, mul_zero]
    | succ j =>
      simp only [Nat.add_right_cancel_iff]
      rw [ih j, lahNumber_succ_succ]
      ring

/-- **NOTE (D1), polynomial form.** Over any commutative semiring, the weighted sum of `z` to the
number of parts over all partitions of `s` is the Lah polynomial `A_{|s|}(z)`. -/
theorem sum_blockWeight_X_pow_eq_lahPolynomial (R : Type*) [CommSemiring R] (s : Finset α) :
    ∑ P : Finpartition s, Polynomial.C (blockWeight P : R) * Polynomial.X ^ #P.parts
      = lahPolynomial R #s := by
  ext j
  rw [Polynomial.finset_sum_coeff, coeff_lahPolynomial, ← sum_blockWeight_card_eq_lahNumber s j]
  push_cast
  refine sum_congr rfl fun P _ ↦ ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hj : #P.parts = j
  · simp [hj]
  · simp [hj, Ne.symm hj]

end Weights

/-! ## The corpus coalescent states as finite partitions -/

/-- A coalescent state `Coalescent.ER n`, read as a finite partition of the sample, has as many
parts as it has blocks. -/
theorem card_parts_ofSetoid {n : ℕ} (ξ : Coalescent.ER n) [DecidableRel ξ.r] :
    #(Finpartition.ofSetoid ξ).parts = Coalescent.blocks ξ := by
  have hclass : ∀ x y : Fin n, ξ.r x y →
      ({z ∈ (univ : Finset (Fin n)) | ξ.r x z} : Finset (Fin n))
        = {z ∈ (univ : Finset (Fin n)) | ξ.r y z} := by
    intro x y hxy
    ext z
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h ↦ ξ.trans (ξ.symm hxy) h, fun h ↦ ξ.trans hxy h⟩
  have hmem : ∀ x : Fin n, ({z ∈ (univ : Finset (Fin n)) | ξ.r x z} : Finset (Fin n))
      ∈ (Finpartition.ofSetoid ξ).parts := by
    intro x
    rw [Finpartition.ofSetoid_parts]
    exact mem_image_of_mem _ (mem_univ x)
  let toPart : Quotient ξ → (Finpartition.ofSetoid ξ).parts :=
    Quotient.lift (fun x ↦ ⟨{z ∈ (univ : Finset (Fin n)) | ξ.r x z}, hmem x⟩)
      (fun x y hxy ↦ Subtype.ext (hclass x y hxy))
  have hinj : Function.Injective toPart := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | h x =>
      induction q using Quotient.inductionOn with
      | h y =>
        have hsets : ({z ∈ (univ : Finset (Fin n)) | ξ.r x z} : Finset (Fin n))
            = {z ∈ (univ : Finset (Fin n)) | ξ.r y z} := congrArg Subtype.val hpq
        have hy : y ∈ ({z ∈ (univ : Finset (Fin n)) | ξ.r x z} : Finset (Fin n)) := by
          rw [hsets]
          simp only [mem_filter, mem_univ, true_and]
          exact ξ.refl y
        exact Quotient.sound (by simpa using hy)
  have hsurj : Function.Surjective toPart := by
    rintro ⟨p, hp⟩
    rw [Finpartition.ofSetoid_parts] at hp
    obtain ⟨x, -, rfl⟩ := mem_image.mp hp
    exact ⟨Quotient.mk ξ x, rfl⟩
  unfold Coalescent.blocks
  rw [Nat.card_congr (Equiv.ofBijective toPart ⟨hinj, hsurj⟩), Nat.card_eq_finsetCard]

end Descent.Pangenome.GraphCoalescent
