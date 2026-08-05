/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Descent

/-!
# The state space of the `n`-coalescent: `𝓔ₙ`, its covers, and where `k(k-1)/2` comes from

Kingman (1982), *The coalescent* (**K-C**), section 1, takes as state space the finite set
`𝓔ₙ` of equivalence relations on `{1, …, n}`, starts at the identity relation `Δ` (1.1),
and gives every transition rate as

  `q_{ξη} = 1` if `ξ ≺ η`, and `0` otherwise,                                    K-C (1.3)

where `ξ ≺ η` means `η` is obtained from `ξ` by combining two of its equivalence classes.
The total rate out of `ξ` is then (1.6)

  `q_ξ = ½ |ξ| (|ξ| - 1)`,

and that is the theorem this file exists to prove.  Everywhere else in the corpus --
`Descent.Coalescent.Rates`, `Descent.Blindness.SpectrumIdentifiability` -- the ladder
`d_k = k(k-1)/2` is taken as given and its consequences worked out.  Here it is counted:
`card_covers` shows a state with `k` blocks has exactly `C(k, 2)` states above it in the
covering order, one for each unordered pair of blocks, and K-C (1.3) puts unit rate on each.

The state space is `Setoid (Fin n)`, which is `𝓔ₙ` on the nose.  `Δ` is `⊥`, `Θ` (K-C
(1.10)) is `⊤`, and the order is Mathlib's `ξ ≤ η ↔ ξ ⊆ η`.  So K-C (1.4) -- `ξ ≺ η ⇔ ξ ⊂ η`
with `|ξ| = |η| + 1` -- is taken as the DEFINITION of `Covers`, and the content is that
covers are exactly merges (`covers_iff_exists_merge`) and that there are `C(k,2)` of them.

## Main results

- `blocks_bot`, `blocks_top`: `|Δ| = n` and `|Θ| = 1`.
- `merge`: combining two classes, built as the kernel of a fold, so that it is an
  equivalence relation by construction rather than by three more lemmas.
- `blocks_merge`: merging drops the block count by exactly one.  K-C (1.4).
- `eq_of_le_of_blocks_eq`: a coarsening that loses no block is the identity.
- `covers_iff_exists_merge`: every cover is a merge -- the direction that needs an argument.
- `merge_eq_merge_iff`: the merged relation remembers exactly which pair was merged.
- `card_covers`: **K-C (1.6)**, a `k`-block state has `C(k,2)` covers.
- `card_covers_eq_deathRate`: that count IS `Descent.Coalescent.Rates.deathRate`.
-/

namespace Coalescent

open scoped Classical

/-- `𝓔ₙ`, Kingman's state space: the equivalence relations on an `n`-element set. -/
abbrev ER (n : ℕ) := Setoid (Fin n)

/-- `|ξ|`, the number of equivalence classes.  K-C section 1. -/
noncomputable def blocks {n : ℕ} (ξ : ER n) : ℕ := Nat.card (Quotient ξ)

/-- `Δ`, the identity relation, at which the `n`-coalescent starts.  K-C (1.1). -/
abbrev Delta (n : ℕ) : ER n := ⊥

/-- `Θ`, the all-relating relation, the unique absorbing state.  K-C (1.10). -/
abbrev Theta (n : ℕ) : ER n := ⊤

theorem quotient_mk_surjective {n : ℕ} (ξ : ER n) :
    Function.Surjective (Quotient.mk ξ) :=
  fun q => Quotient.inductionOn q fun a => ⟨a, rfl⟩

/-- A sample of `n` starts with `n` blocks: nobody has yet been shown to share an
ancestor. -/
theorem blocks_bot (n : ℕ) : blocks (Delta n) = n := by
  have e : Quotient (⊥ : ER n) ≃ Fin n :=
    { toFun := fun q => Quotient.liftOn q id fun _ _ h => h
      invFun := fun a => Quotient.mk _ a
      left_inv := fun q => Quotient.inductionOn q fun _ => rfl
      right_inv := fun _ => rfl }
  unfold blocks Delta
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The absorbing state has one block: the sample has a single common ancestor. -/
theorem blocks_top (n : ℕ) [NeZero n] : blocks (Theta n) = 1 := by
  unfold blocks Theta
  have hsub : Subsingleton (Quotient (⊤ : ER n)) :=
    ⟨fun p q => Quotient.inductionOn₂ p q fun _ _ => Quotient.sound trivial⟩
  have hne : Nonempty (Quotient (⊤ : ER n)) :=
    ⟨Quotient.mk _ ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, hne⟩

/-- **One block means absorbed.**  A relation on the sample with a single class is `Θ`: the
whole sample has a common ancestor.  K-C (1.10) names `Θ` as the absorbing state, and this
is why the block count `1` is the only thing the death process needs to detect it. -/
theorem blocks_eq_one_iff {n : ℕ} [NeZero n] (ξ : ER n) : blocks ξ = 1 ↔ ξ = Theta n := by
  constructor
  · intro h
    have hsub : Subsingleton (Quotient ξ) := by
      have := (Nat.card_eq_one_iff_unique.mp h).1
      exact this
    refine Setoid.ext fun x y => ⟨fun _ => trivial, fun _ => ?_⟩
    exact Quotient.exact (Subsingleton.elim (Quotient.mk ξ x) (Quotient.mk ξ y))
  · intro h
    rw [h]
    exact blocks_top n

theorem blocks_pos {n : ℕ} [NeZero n] (ξ : ER n) : 0 < blocks ξ := by
  have hne : Nonempty (Quotient ξ) := ⟨Quotient.mk ξ ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  exact Nat.card_pos

/-- The map on blocks induced by a coarsening. -/
noncomputable def blockMap {n : ℕ} {ξ η : ER n} (h : ξ ≤ η) : Quotient ξ → Quotient η :=
  Quotient.lift (fun x => Quotient.mk η x) fun _ _ hab => Quotient.sound (h hab)

theorem blockMap_surjective {n : ℕ} {ξ η : ER n} (h : ξ ≤ η) :
    Function.Surjective (blockMap h) := by
  intro q
  obtain ⟨x, hx⟩ := quotient_mk_surjective η q
  exact ⟨Quotient.mk ξ x, hx⟩

/-! ### Merging two classes

K-C's `ξ ≺ η` is "`η` is obtained from `ξ` by combining two of its equivalence classes".
Building the combined relation directly means proving reflexivity, symmetry and
transitivity of a disjunction.  Building it as the KERNEL of a map that folds the class `b`
onto the class `a` means proving none of them: a kernel is an equivalence relation because
equality is.  Every structural fact below is then a fact about that fold. -/

/-- Fold the class `b` onto the class `a`, fixing every other class. -/
noncomputable def mergeMap {n : ℕ} (ξ : ER n) (a b : Quotient ξ) : Quotient ξ → Quotient ξ :=
  fun c => if c = b then a else c

/-- **Combining two equivalence classes.**  `merge ξ a b` relates `x` and `y` exactly when
they land in the same class after `b` has been folded onto `a`.  K-C section 1.

Empirical status: NOT AN EMPIRICAL CLAIM.  This is Kingman's `≺`: a definition of which
states the process can move to, not an assertion about any population. -/
noncomputable def merge {n : ℕ} (ξ : ER n) (a b : Quotient ξ) : ER n :=
  Setoid.ker fun x => mergeMap ξ a b (Quotient.mk ξ x)

theorem mergeMap_apply_of_ne {n : ℕ} (ξ : ER n) (a b c : Quotient ξ) (h : c ≠ b) :
    mergeMap ξ a b c = c := by
  simp [mergeMap, h]

@[simp] theorem mergeMap_apply_self {n : ℕ} (ξ : ER n) (a b : Quotient ξ) :
    mergeMap ξ a b b = a := by
  simp [mergeMap]

/-- **What the fold identifies, and nothing more.**  Two distinct classes are merged exactly
when they are the two classes named -- so the pair is recoverable from the merged relation,
which is what makes `card_covers` a count of pairs. -/
theorem mergeMap_eq_iff {n : ℕ} (ξ : ER n) {a b : Quotient ξ} (hab : a ≠ b)
    (x y : Quotient ξ) :
    mergeMap ξ a b x = mergeMap ξ a b y ↔ x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  by_cases hx : x = b <;> by_cases hy : y = b
  · rw [hx, hy]
    simp
  · rw [hx, mergeMap_apply_self, mergeMap_apply_of_ne ξ a b y hy]
    constructor
    · intro h
      exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
    · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h.symm hy
      · exact absurd h.symm hab
      · exact h.symm
  · rw [hy, mergeMap_apply_self, mergeMap_apply_of_ne ξ a b x hx]
    constructor
    · intro h
      exact Or.inr (Or.inl ⟨h, rfl⟩)
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact absurd h hx
      · exact h
      · exact absurd h hx
  · rw [mergeMap_apply_of_ne ξ a b x hx, mergeMap_apply_of_ne ξ a b y hy]
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd h hy
      · exact absurd h hx

/-- Merging coarsens: every pair related by `ξ` stays related. -/
theorem le_merge {n : ℕ} (ξ : ER n) (a b : Quotient ξ) : ξ ≤ merge ξ a b := by
  intro x y hxy
  show mergeMap ξ a b (Quotient.mk ξ x) = mergeMap ξ a b (Quotient.mk ξ y)
  exact congrArg _ (Quotient.sound hxy)

/-- The two named classes are merged. -/
theorem merge_rel {n : ℕ} (ξ : ER n) (a b : Quotient ξ) {x y : Fin n}
    (hx : Quotient.mk ξ x = a) (hy : Quotient.mk ξ y = b) : (merge ξ a b).r x y := by
  show mergeMap ξ a b (Quotient.mk ξ x) = mergeMap ξ a b (Quotient.mk ξ y)
  rw [hx, hy, mergeMap_apply_self]
  by_cases hab : a = b
  · rw [hab, mergeMap_apply_self]
  · rw [mergeMap_apply_of_ne ξ a b a hab]

/-- The image of the fold is everything but the class that was folded away. -/
theorem range_mergeMap {n : ℕ} (ξ : ER n) {a b : Quotient ξ} (hab : a ≠ b) :
    Set.range (fun x : Fin n => mergeMap ξ a b (Quotient.mk ξ x)) = {c | c ≠ b} := by
  ext c
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : Quotient.mk ξ x = b
    · show mergeMap ξ a b (Quotient.mk ξ x) ≠ b
      rw [hx, mergeMap_apply_self]
      exact hab
    · show mergeMap ξ a b (Quotient.mk ξ x) ≠ b
      rw [mergeMap_apply_of_ne ξ a b _ hx]
      exact hx
  · intro hc
    obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
    refine ⟨x, ?_⟩
    show mergeMap ξ a b (Quotient.mk ξ x) = c
    rw [hx, mergeMap_apply_of_ne ξ a b c hc]

/-- **K-C (1.4): merging two distinct classes drops the block count by exactly one.** -/
theorem blocks_merge {n : ℕ} (ξ : ER n) {a b : Quotient ξ} (hab : a ≠ b) :
    blocks (merge ξ a b) + 1 = blocks ξ := by
  classical
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  have hrange : blocks (merge ξ a b) = Nat.card {c : Quotient ξ // c ≠ b} := by
    unfold blocks merge
    rw [Nat.card_congr (Setoid.quotientKerEquivRange _)]
    exact Nat.card_congr (Equiv.setCongr (range_mergeMap ξ hab))
  have hsub : Nat.card {c : Quotient ξ // c ≠ b} = Fintype.card (Quotient ξ) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfilter : (Finset.univ.filter fun c : Quotient ξ => c ≠ b)
        = Finset.univ.erase b := by
      ext c
      simp [Finset.mem_erase]
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
  have hcard : blocks ξ = Fintype.card (Quotient ξ) := Nat.card_eq_fintype_card
  have hpos : 0 < Fintype.card (Quotient ξ) := Fintype.card_pos_iff.mpr ⟨b⟩
  rw [hrange, hsub, hcard]
  omega

/-! ### Covers

K-C (1.4) writes `ξ ≺ η ⇔ ξ ⊂ η, |ξ| = |η| + 1`.  That is taken here as the definition, so
what has to be proved is that covers and merges coincide. -/

/-- `ξ ≺ η`: `η` sits directly above `ξ` in the coalescent's transition graph.  K-C (1.4). -/
def Covers {n : ℕ} (ξ η : ER n) : Prop := ξ ≤ η ∧ blocks η + 1 = blocks ξ

theorem merge_covers {n : ℕ} (ξ : ER n) {a b : Quotient ξ} (hab : a ≠ b) :
    Covers ξ (merge ξ a b) := ⟨le_merge ξ a b, blocks_merge ξ hab⟩

/-- **A coarsening that loses no block is not a coarsening.**  Two relations on a finite set
with `ξ ≤ η` and equal block counts are equal.  This is what lets `covers_iff_exists_merge`
avoid a fibre-counting argument: rather than analysing how blocks map, it is enough to
exhibit a merge below `η` with the same count. -/
theorem eq_of_le_of_blocks_eq {n : ℕ} {ξ η : ER n} (h : ξ ≤ η) (hb : blocks ξ = blocks η) :
    ξ = η := by
  classical
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  letI : Fintype (Quotient η) := Fintype.ofFinite _
  have hcard : Fintype.card (Quotient ξ) = Fintype.card (Quotient η) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hb
  have hbij : Function.Bijective (blockMap h) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr ⟨blockMap_surjective h, hcard⟩
  refine Setoid.ext fun x y => ⟨fun hxy => h hxy, fun hxy => ?_⟩
  have hmk : blockMap h (Quotient.mk ξ x) = blockMap h (Quotient.mk ξ y) :=
    Quotient.sound hxy
  exact Quotient.exact (hbij.1 hmk)

/-- **Every cover is a merge.**  K-C's `ξ ≺ η` -- "`η` is obtained from `ξ` by combining two
of its equivalence classes" -- is not an extra hypothesis on top of the block-count drop:
it follows from it. -/
theorem covers_iff_exists_merge {n : ℕ} (ξ η : ER n) :
    Covers ξ η ↔ ∃ a b : Quotient ξ, a ≠ b ∧ η = merge ξ a b := by
  constructor
  · rintro ⟨hle, hb⟩
    classical
    letI : Fintype (Quotient ξ) := Fintype.ofFinite _
    letI : Fintype (Quotient η) := Fintype.ofFinite _
    have hninj : ¬ Function.Injective (blockMap hle) := by
      intro hinj
      have hbij : Function.Bijective (blockMap hle) := ⟨hinj, blockMap_surjective hle⟩
      have hcard : Nat.card (Quotient ξ) = Nat.card (Quotient η) :=
        Nat.card_eq_of_bijective _ hbij
      unfold blocks at hb
      omega
    obtain ⟨a, b, hFab, hab⟩ : ∃ a b : Quotient ξ, blockMap hle a = blockMap hle b ∧ a ≠ b := by
      by_contra hcon
      push_neg at hcon
      exact hninj fun a b hEq => by
        by_contra hne
        exact hne (hcon a b hEq)
    refine ⟨a, b, hab, ?_⟩
    have hmle : merge ξ a b ≤ η := by
      intro x y hxy
      have hxy' : mergeMap ξ a b (Quotient.mk ξ x) = mergeMap ξ a b (Quotient.mk ξ y) := hxy
      rcases (mergeMap_eq_iff ξ hab _ _).mp hxy' with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hle (Quotient.exact h)
      · have hb' : blockMap hle (Quotient.mk ξ x) = blockMap hle (Quotient.mk ξ y) := by
          rw [hx, hy]
          exact hFab
        exact Quotient.exact hb'
      · have hb' : blockMap hle (Quotient.mk ξ x) = blockMap hle (Quotient.mk ξ y) := by
          rw [hx, hy]
          exact hFab.symm
        exact Quotient.exact hb'
    have hbm : blocks (merge ξ a b) = blocks η := by
      have hm := blocks_merge ξ hab
      omega
    exact (eq_of_le_of_blocks_eq hmle hbm).symm
  · rintro ⟨a, b, hab, rfl⟩
    exact merge_covers ξ hab

/-! ### The count

Covers of a `k`-block state biject with two-element subsets of its block set, so there are
`C(k,2) = k(k-1)/2` of them.  With K-C (1.3)'s unit rate on each, that is K-C (1.6). -/

/-- Merging is symmetric: the two folds differ, but their kernels -- the relations -- agree.
This is where the factor of two in `k(k-1)/2` comes from: covers are indexed by UNORDERED
pairs of blocks. -/
theorem merge_comm {n : ℕ} (ξ : ER n) {a b : Quotient ξ} (hab : a ≠ b) :
    merge ξ a b = merge ξ b a := by
  refine Setoid.ext fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩
  · have h := (mergeMap_eq_iff ξ hab _ _).mp hxy
    refine (mergeMap_eq_iff ξ (Ne.symm hab) _ _).mpr ?_
    rcases h with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hx, hy⟩)
    · exact Or.inr (Or.inl ⟨hx, hy⟩)
  · have h := (mergeMap_eq_iff ξ (Ne.symm hab) _ _).mp hxy
    refine (mergeMap_eq_iff ξ hab _ _).mpr ?_
    rcases h with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hx, hy⟩)
    · exact Or.inr (Or.inl ⟨hx, hy⟩)

/-- **The merged relation remembers exactly which pair was merged.**  Distinct unordered
pairs give distinct states, so covers are not overcounted. -/
theorem merge_eq_merge_iff {n : ℕ} (ξ : ER n) {a b c d : Quotient ξ}
    (hab : a ≠ b) (hcd : c ≠ d) :
    merge ξ a b = merge ξ c d ↔ ({a, b} : Finset (Quotient ξ)) = {c, d} := by
  classical
  constructor
  · intro h
    have hkey : ∀ x y : Quotient ξ,
        (mergeMap ξ a b x = mergeMap ξ a b y ↔ mergeMap ξ c d x = mergeMap ξ c d y) := by
      intro x y
      obtain ⟨x', hx'⟩ := quotient_mk_surjective ξ x
      obtain ⟨y', hy'⟩ := quotient_mk_surjective ξ y
      subst hx'
      subst hy'
      constructor
      · intro hxy
        have hr : (merge ξ a b).r x' y' := hxy
        rw [h] at hr
        exact hr
      · intro hxy
        have hr : (merge ξ c d).r x' y' := hxy
        rw [← h] at hr
        exact hr
    have hab' : mergeMap ξ c d a = mergeMap ξ c d b := (hkey a b).mp (by simp [mergeMap])
    have hcd' : mergeMap ξ a b c = mergeMap ξ a b d := (hkey c d).mpr (by simp [mergeMap])
    rcases (mergeMap_eq_iff ξ hcd a b).mp hab' with h1 | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact absurd h1 hab
    · rw [ha, hb]
    · rw [ha, hb]
      exact Finset.pair_comm d c
  · intro h
    have hmem : a ∈ ({c, d} : Finset (Quotient ξ)) := by
      rw [← h]
      simp
    have hmem' : b ∈ ({c, d} : Finset (Quotient ξ)) := by
      rw [← h]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hmem'
    rcases hmem with ha | ha
    · rcases hmem' with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha, hb]
    · rcases hmem' with hb | hb
      · rw [ha, hb, merge_comm ξ (Ne.symm hcd)]
      · exact absurd (ha.trans hb.symm) hab

/-- The first named block of a two-element set of blocks.

Empirical status: NOT AN EMPIRICAL CLAIM.  A choice function on a two-element `Finset`.

The name is `pair` + `Fst` for FIRST, and has nothing to do with `F_ST`; it is screened as
a population-genetic claim because the screen matches the letters, which is the screen
being right to be blunt rather than the name being wrong.  Kept explicit because the same
letters make `validation/conventions.json` ask for a ledger entry saying which `F_ST` this
is, and the answer is that it is not one. -/
noncomputable def pairFst {n : ℕ} {ξ : ER n} {s : Finset (Quotient ξ)} (h : s.card = 2) :
    Quotient ξ := (Finset.card_eq_two.mp h).choose

/-- The second named block of a two-element set of blocks. -/
noncomputable def pairSnd {n : ℕ} {ξ : ER n} {s : Finset (Quotient ξ)} (h : s.card = 2) :
    Quotient ξ := (Finset.card_eq_two.mp h).choose_spec.choose

theorem pair_spec {n : ℕ} {ξ : ER n} {s : Finset (Quotient ξ)} (h : s.card = 2) :
    pairFst h ≠ pairSnd h ∧ s = {pairFst h, pairSnd h} :=
  (Finset.card_eq_two.mp h).choose_spec.choose_spec

/-- The cover a two-element set of blocks names. -/
noncomputable def coverOfPair {n : ℕ} (ξ : ER n) (s : {s : Finset (Quotient ξ) // s.card = 2}) :
    {η : ER n // Covers ξ η} :=
  ⟨merge ξ (pairFst s.2) (pairSnd s.2), merge_covers ξ (pair_spec s.2).1⟩

theorem coverOfPair_bijective {n : ℕ} (ξ : ER n) : Function.Bijective (coverOfPair ξ) := by
  classical
  constructor
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    have hmerge : merge ξ (pairFst hs) (pairSnd hs) = merge ξ (pairFst ht) (pairSnd ht) :=
      congrArg Subtype.val hst
    have hpair : ({pairFst hs, pairSnd hs} : Finset (Quotient ξ))
        = {pairFst ht, pairSnd ht} :=
      (merge_eq_merge_iff ξ (pair_spec hs).1 (pair_spec ht).1).mp hmerge
    have hs' := (pair_spec hs).2
    have ht' := (pair_spec ht).2
    have hst' : s = t := by
      rw [hs', ht', hpair]
    exact Subtype.ext hst'
  · rintro ⟨η, hη⟩
    obtain ⟨a, b, hab, rfl⟩ := (covers_iff_exists_merge ξ η).mp hη
    have hcard : ({a, b} : Finset (Quotient ξ)).card = 2 := Finset.card_pair hab
    refine ⟨⟨{a, b}, hcard⟩, ?_⟩
    have hpair : ({pairFst hcard, pairSnd hcard} : Finset (Quotient ξ)) = {a, b} :=
      ((pair_spec hcard).2).symm
    exact Subtype.ext
      ((merge_eq_merge_iff ξ (pair_spec hcard).1 hab).mpr hpair)

/-- **K-C (1.6): a state with `k` blocks has exactly `C(k,2)` covers.**

Every cover is the merge of a unique unordered pair of blocks, so the covers biject with the two-element subsets of the block set.  K-C (1.3) puts rate `1` on each, so the total
rate out of the state is `C(k,2) = k(k-1)/2`.  That is the ladder `d_k` -- counted, not
assumed. -/
theorem card_covers {n : ℕ} (ξ : ER n) :
    Nat.card {η : ER n // Covers ξ η} = (blocks ξ).choose 2 := by
  classical
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  rw [← Nat.card_eq_of_bijective _ (coverOfPair_bijective ξ), Nat.card_eq_fintype_card,
    Fintype.card_finset_len]
  congr 1
  exact (Nat.card_eq_fintype_card (α := Quotient ξ)).symm ▸ rfl

/-- `2 C(k,2) = k(k-1)`, the integer form of the halving. -/
theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  induction k with | zero => simp
  | succ m ih =>
      have hsplit : (m + 1).choose 2 = m + m.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      rw [hsplit, Nat.add_sub_cancel, Nat.mul_add]
      rw [ih]
      cases m with | zero => simp
      | succ p =>
          simp only [Nat.add_sub_cancel]
          ring

/-- **The cover count is the death rate.**  `Descent.Coalescent.Rates.deathRate` was
introduced there as a formula; here it is identified with a cardinality of the state space.
The ladder that file telescopes is the number of pairs of blocks. -/
theorem card_covers_eq_deathRate {n : ℕ} (ξ : ER n) :
    (Nat.card {η : ER n // Covers ξ η} : ℝ) = deathRate (blocks ξ) := by
  rw [card_covers]
  have hint : 2 * (blocks ξ).choose 2 = blocks ξ * (blocks ξ - 1) := two_mul_choose_two _
  rcases Nat.eq_zero_or_pos (blocks ξ) with hb | hb
  · rw [hb]
    norm_num [deathRate,
      Descent.Core.pairCount]
  · have hcast : ((blocks ξ * (blocks ξ - 1) : ℕ) : ℝ)
        = (blocks ξ : ℝ) * ((blocks ξ : ℝ) - 1) := by
      push_cast [Nat.cast_sub hb]
      ring
    have h2 : 2 * (((blocks ξ).choose 2 : ℕ) : ℝ)
        = (blocks ξ : ℝ) * ((blocks ξ : ℝ) - 1) := by
      rw [← hcast, ← hint]
      push_cast
      ring
    unfold deathRate Descent.Core.pairCount
    linear_combination h2 / 2

end Coalescent

end Descent
