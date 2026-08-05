/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.CutSets
import Descent.Coalescent.Ewens
import Mathlib.Tactic

namespace Descent

/-!
# Counting the states below `η`

`Descent.Coalescent.CutSets` names each state below `η` exactly once, by a cut set: a
nonempty subset of one class omitting that class's representative.  This file counts them,
which closes `Descent.Coalescent.Program`'s open item 1.

The count is now a count of subsets and nothing more.  A cut set of the class `c` is exactly
a nonempty subset of that class with the representative deleted -- `isCutSetOf_iff` -- and
there are `2^{λ_c - 1} - 1` of those.  Summing over classes gives

  `#{ξ ; ξ ≺ η} = Σ_c (2^{λ_c - 1} - 1)`,

which is Kingman's `Σ_ν ½C(λ,ν)` with the halving replaced by the basepoint convention.
`Program.sum_choose_interior_eq_two_mul_cutCount` is the check that the two agree.

## Main results

- `isCutSetOf_iff`: a cut set of `c` is a nonempty subset of `c` minus its representative.
- `card_cutSetsOf`: there are `2^{λ_c - 1} - 1` of them.
- `card_covers_eq_card_cutSets`: cut sets and states below `η` biject.
- `card_covers_below`: **the count**, `Σ_c (2^{λ_c - 1} - 1)`.
-/

namespace Coalescent

open scoped Classical

/-- The class of `c`, with its representative deleted: the `λ_c - 1` elements a cut set of
`c` is a nonempty subset of. -/
noncomputable def cutBase {n : ℕ} (η : ER n) (c : Quotient η) : Finset (Fin n) :=
  (classFinset η c.out).erase c.out

theorem mem_classFinset_out {n : ℕ} (η : ER n) (c : Quotient η) (y : Fin n) :
    y ∈ classFinset η c.out ↔ Quotient.mk η y = c := by
  rw [mem_classFinset]
  constructor
  · intro h
    rw [Quotient.sound h, Quotient.out_eq]
  · intro h
    exact Quotient.exact (h.trans (Quotient.out_eq c).symm)

theorem card_classFinset_out {n : ℕ} (η : ER n) (c : Quotient η) :
    (classFinset η c.out).card = classSize η c := by
  unfold classSize
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_classFinset_out η c y

theorem card_cutBase {n : ℕ} (η : ER n) (c : Quotient η) :
    (cutBase η c).card = classSize η c - 1 := by
  unfold cutBase
  rw [Finset.card_erase_of_mem, card_classFinset_out]
  exact (mem_classFinset_out η c c.out).mpr (Quotient.out_eq c)

/-- **A cut set of the class `c` is a nonempty subset of `c` minus its representative.**
Both conditions of `IsCutSet` -- lying in one class, and omitting the representative --
become the single containment. -/
theorem isCutSetOf_iff {n : ℕ} (η : ER n) (c : Quotient η) (S : Finset (Fin n)) :
    (IsCutSet η S ∧ ∀ x ∈ S, Quotient.mk η x = c) ↔ (S.Nonempty ∧ S ⊆ cutBase η c) := by
  constructor
  · rintro ⟨⟨hne, hcl, hrep⟩, hall⟩
    refine ⟨hne, fun y hy => ?_⟩
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hcontra
      have := hrep y hy
      rw [hall y hy] at this
      exact this (hcontra ▸ hy)
    · exact (mem_classFinset_out η c y).mpr (hall y hy)
  · rintro ⟨hne, hsub⟩
    have hall : ∀ x ∈ S, Quotient.mk η x = c := fun x hx =>
      (mem_classFinset_out η c x).mp (Finset.mem_of_mem_erase (hsub hx))
    refine ⟨⟨hne, fun x hx y hy => ?_, fun x hx hmem => ?_⟩, hall⟩
    · exact Quotient.exact ((hall x hx).trans (hall y hy).symm)
    · rw [hall x hx] at hmem
      exact (Finset.mem_erase.mp (hsub hmem)).1 rfl

/-- **There are `2^{λ_c - 1} - 1` cut sets of a class of size `λ_c`.**  A count of subsets:
every nonempty subset of the `λ_c - 1` non-representative elements, and no others. -/
theorem card_cutSetsOf {n : ℕ} (η : ER n) (c : Quotient η) :
    (Finset.univ.filter fun S : Finset (Fin n) =>
        IsCutSet η S ∧ ∀ x ∈ S, Quotient.mk η x = c).card
      = 2 ^ (classSize η c - 1) - 1 := by
  classical
  have hset : (Finset.univ.filter fun S : Finset (Fin n) =>
      IsCutSet η S ∧ ∀ x ∈ S, Quotient.mk η x = c)
      = (cutBase η c).powerset.erase ∅ := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Finset.mem_powerset]
    rw [isCutSetOf_iff η c S]
    exact ⟨fun h => ⟨Finset.nonempty_iff_ne_empty.mp h.1, h.2⟩,
      fun h => ⟨Finset.nonempty_iff_ne_empty.mpr h.1, h.2⟩⟩
  rw [hset, Finset.card_erase_of_mem (Finset.empty_mem_powerset _),
    Finset.card_powerset, card_cutBase]

/-- Every cut set determines the class it cuts. -/
noncomputable def cutClass {n : ℕ} [NeZero n] (η : ER n) (S : Finset (Fin n)) : Quotient η :=
  if h : S.Nonempty then Quotient.mk η h.choose
  else Quotient.mk η ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩

theorem cutClass_eq {n : ℕ} [NeZero n] {η : ER n} {S : Finset (Fin n)} (hS : IsCutSet η S)
    {x : Fin n} (hx : x ∈ S) : cutClass η S = Quotient.mk η x := by
  have hne : S.Nonempty := ⟨x, hx⟩
  rw [cutClass, dif_pos hne]
  exact Quotient.sound (hS.2.1 _ hne.choose_spec x hx)

/-- **The cut sets of `η` number `Σ_c (2^{λ_c - 1} - 1)`.**  Fibred over the class each one
cuts, and counted class by class. -/
theorem card_cutSets {n : ℕ} [NeZero n] (η : ER n) :
    (Finset.univ.filter fun S : Finset (Fin n) => IsCutSet η S).card
      = ∑ c : Quotient η, (2 ^ (classSize η c - 1) - 1) := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := cutClass η) (s := Finset.univ.filter fun S : Finset (Fin n) => IsCutSet η S)
    (t := (Finset.univ : Finset (Quotient η))) (fun S _ => Finset.mem_univ _)
  rw [hfib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← card_cutSetsOf η c]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hS, hc⟩
    refine ⟨hS, fun x hx => ?_⟩
    rw [← cutClass_eq hS hx, hc]
  · rintro ⟨hS, hall⟩
    obtain ⟨x, hx⟩ := hS.1
    exact ⟨hS, by rw [cutClass_eq hS hx, hall x hx]⟩

/-- **Cut sets and states below `η` biject.**  `CutSets` proved both halves; this packages
them as an equality of cardinalities. -/
theorem card_covers_eq_card_cutSets {n : ℕ} (η : ER n) :
    Nat.card {ξ : ER n // Blindness.Covers ξ η}
      = Nat.card {S : Finset (Fin n) // IsCutSet η S} := by
  classical
  refine (Nat.card_eq_of_bijective
    (fun S : {S : Finset (Fin n) // IsCutSet η S} =>
      (⟨splitBy η S.1, ?_⟩ : {ξ : ER n // Blindness.Covers ξ η})) ?_).symm
  · obtain ⟨x, hx⟩ := S.2.1
    refine splitBy_covers η S.1 (a := x) (fun y hy => S.2.2.1 y hy x hx) ⟨x, hx⟩ ?_
    refine ⟨(Quotient.mk η x).out, ?_, out_not_mem_cutSet S.2 x⟩
    exact Quotient.exact (Quotient.out_eq (Quotient.mk η x))
  · constructor
    · rintro ⟨S, hS⟩ ⟨T, hT⟩ h
      exact Subtype.ext (splitBy_injective_on_cutSets η hS hT (congrArg Subtype.val h))
    · rintro ⟨ξ, hξ⟩
      obtain ⟨T, hT, hTeq⟩ := exists_cutSet_of_covers hξ
      exact ⟨⟨T, hT⟩, Subtype.ext hTeq.symm⟩

/-- **The count, `#{ξ ; ξ ≺ η} = Σ_c (2^{λ_c - 1} - 1)`.**

Kingman's backward induction for K-C (2.3) sums over the states below `η`, weighting each
split of a class of size `λ` into pieces `ν` and `λ - ν` by `½ C(λ, ν)`.  This is the total
those weights carry, arrived at without the halving:
`Program.sum_choose_interior_eq_two_mul_cutCount` checks that the two agree. -/
theorem card_covers_below {n : ℕ} [NeZero n] (η : ER n) :
    Nat.card {ξ : ER n // Blindness.Covers ξ η} = ∑ c : Quotient η, (2 ^ (classSize η c - 1) - 1) := by
  classical
  rw [card_covers_eq_card_cutSets, ← card_cutSets η, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

end Coalescent

end Descent
