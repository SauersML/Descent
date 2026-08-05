/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Mathlib.Tactic

namespace Descent

/-!
# Splitting a block: the covering order seen from above

`Descent.Coalescent.StateSpace` describes a cover `ξ ≺ η` from below: `η` is `ξ` with two
classes merged.  Kingman's proof of K-C (2.3) needs it from above.  His backward induction
fixes `η` with classes `λ₁, …, λ_{k-1}` and sums over the states `ξ` beneath it -- "those of
`ξ` are `λ₁, …, λ_{l-1}, ν, λ_l - ν, λ_{l+1}, …`" -- that is, over ways of splitting one
class of `η` into two nonempty pieces.

`Descent.Coalescent.JumpChain` proves the arithmetic of that induction but carries the
factor `½ C(λ_l, ν)` -- the number of states realising a given split -- as written, because
the corpus had no way to talk about splitting.  This file supplies it.  `splitBy` cuts every
class of `η` along a set `S`; when `S` is a nonempty proper subset of one class, only that
class is cut, and the result is a cover.  `covers_iff_exists_splitBy` shows every cover
arises this way, so the states below `η` are exactly the cuts of its classes.

What remains open after this file, and is stated rather than glossed: the cardinality
`#{ξ ; ξ ≺ η} = Σ_c (2^{|c|-1} - 1)`, and its refinement by piece size, which is the
`½ C(λ, ν)` itself.  Both are now expressible -- `splitBy` and `splitBy_eq_iff` are the
statement and the injectivity it needs -- and neither is proved here.

## Main results

- `splitBy`: cut the classes of `η` along `S`, as a kernel.
- `splitBy_rel_iff`: what it relates -- same class, same side of the cut.
- `blocks_splitBy`: cutting one class in two adds exactly one block.
- `splitBy_covers`: so it is a cover, from above.
- `covers_iff_exists_splitBy`: and every cover is one.
- `splitBy_eq_iff`: a cut is determined by its set up to swapping the two pieces -- the
  source of the `½` in `½ C(λ, ν)`.
-/

namespace Coalescent

open scoped Classical

/-- **Cut along `S`.**  `splitBy η S` relates `x` and `y` when `η` does and they lie on the
same side of `S`.  Written as a kernel, so it is an equivalence relation by construction.

Empirical status: NOT AN EMPIRICAL CLAIM.  This is the inverse operation to `merge`, i.e.
a description of the coalescent's transition graph, not of a population. -/
noncomputable def splitBy {n : ℕ} (η : ER n) (S : Finset (Fin n)) : ER n :=
  Setoid.ker fun x => (Quotient.mk η x, decide (x ∈ S))

theorem splitBy_rel_iff {n : ℕ} (η : ER n) (S : Finset (Fin n)) (x y : Fin n) :
    (splitBy η S).r x y ↔ (η.r x y ∧ (x ∈ S ↔ y ∈ S)) := by
  constructor
  · intro h
    have hpair : (Quotient.mk η x, decide (x ∈ S)) = (Quotient.mk η y, decide (y ∈ S)) := h
    have h1 : Quotient.mk η x = Quotient.mk η y := congrArg Prod.fst hpair
    have h2 : decide (x ∈ S) = decide (y ∈ S) := congrArg Prod.snd hpair
    exact ⟨Quotient.exact h1, by simpa using decide_eq_decide.mp h2⟩
  · rintro ⟨h1, h2⟩
    show (Quotient.mk η x, decide (x ∈ S)) = (Quotient.mk η y, decide (y ∈ S))
    rw [Quotient.sound h1, decide_eq_decide.mpr h2]

/-- A cut only refines: it never relates what `η` did not. -/
theorem splitBy_le {n : ℕ} (η : ER n) (S : Finset (Fin n)) : splitBy η S ≤ η := by
  intro x y hxy
  exact ((splitBy_rel_iff η S x y).mp hxy).1

/-- The image of the cutting map, when `S` is a nonempty proper subset of a single class:
every class contributes its `false` side, and the cut class contributes a `true` side too. -/
theorem range_splitMap {n : ℕ} (η : ER n) (S : Finset (Fin n)) {a : Fin n}
    (hSa : ∀ x ∈ S, η.r x a) (hSne : ∃ x, x ∈ S) (hSproper : ∃ x, η.r x a ∧ x ∉ S) :
    Set.range (fun x : Fin n => (Quotient.mk η x, decide (x ∈ S)))
      = {p | p.2 = false} ∪ {(Quotient.mk η a, true)} := by
  classical
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : x ∈ S
    · refine Or.inr ?_
      simp only [Set.mem_singleton_iff, Prod.mk.injEq]
      exact ⟨Quotient.sound (hSa x hx), by simpa using hx⟩
    · exact Or.inl (by simpa using hx)
  · rintro (hp | hp)
    · obtain ⟨c, b⟩ := p
      simp only [Set.mem_setOf_eq] at hp
      subst hp
      obtain ⟨x, hx⟩ := quotient_mk_surjective η c
      by_cases hxS : x ∈ S
      · obtain ⟨w, hw, hwS⟩ := hSproper
        refine ⟨w, ?_⟩
        have hwc : Quotient.mk η w = c := by
          rw [← hx]
          exact Quotient.sound (η.iseqv.trans hw (η.iseqv.symm (hSa x hxS)))
        simp [hwc, hwS]
      · exact ⟨x, by simp [hx, hxS]⟩
    · simp only [Set.mem_singleton_iff] at hp
      subst hp
      obtain ⟨x, hx⟩ := hSne
      exact ⟨x, by simp [Quotient.sound (hSa x hx), hx]⟩

/-- **Cutting one class in two adds exactly one block.**  The dual of
`Descent.Coalescent.StateSpace.blocks_merge`, and the reason a cut is a cover. -/
theorem blocks_splitBy {n : ℕ} (η : ER n) (S : Finset (Fin n)) {a : Fin n}
    (hSa : ∀ x ∈ S, η.r x a) (hSne : ∃ x, x ∈ S) (hSproper : ∃ x, η.r x a ∧ x ∉ S) :
    blocks (splitBy η S) = blocks η + 1 := by
  classical
  letI : Fintype (Quotient η) := Fintype.ofFinite _
  have hrange := range_splitMap η S hSa hSne hSproper
  have hequiv : Nat.card (Set.range (fun x : Fin n => (Quotient.mk η x, decide (x ∈ S))))
      = Nat.card ({p : Quotient η × Bool | p.2 = false} ∪ {(Quotient.mk η a, true)} : Set _) :=
    Nat.card_congr (Equiv.setCongr hrange)
  have hfalse : Nat.card ({p : Quotient η × Bool | p.2 = false} : Set _)
      = Nat.card (Quotient η) := by
    refine Nat.card_congr ⟨fun p => p.1.1, fun c => ⟨(c, false), rfl⟩, ?_, ?_⟩
    · rintro ⟨⟨c, b⟩, hb⟩
      simp only [Set.mem_setOf_eq] at hb
      subst hb
      rfl
    · intro c
      rfl
  have hnotmem : ((Quotient.mk η a, true) : Quotient η × Bool)
      ∉ {p : Quotient η × Bool | p.2 = false} := by
    simp
  have hunion : Nat.card ({p : Quotient η × Bool | p.2 = false} ∪
      {(Quotient.mk η a, true)} : Set _)
      = Nat.card ({p : Quotient η × Bool | p.2 = false} : Set _) + 1 := by
    classical
    rw [Set.union_singleton, Nat.card_insert_of_not_mem hnotmem]
  unfold blocks splitBy
  rw [Nat.card_congr (Setoid.quotientKerEquivRange _), hequiv, hunion, hfalse]

/-- **A cut of one class is a cover, from above.** -/
theorem splitBy_covers {n : ℕ} (η : ER n) (S : Finset (Fin n)) {a : Fin n}
    (hSa : ∀ x ∈ S, η.r x a) (hSne : ∃ x, x ∈ S) (hSproper : ∃ x, η.r x a ∧ x ∉ S) :
    Covers (splitBy η S) η :=
  ⟨splitBy_le η S, by rw [blocks_splitBy η S hSa hSne hSproper]⟩

/-- **Every cover is a cut.**  Given `ξ ≺ η`, the set `S` is one of the two `ξ`-classes that
`η` merges; `covers_iff_exists_merge` supplies the pair, and this turns it into a set.  With
this, the states below `η` in Kingman's induction are exactly the cuts of its classes. -/
theorem covers_iff_exists_splitBy {n : ℕ} (ξ η : ER n) :
    Covers ξ η ↔ ∃ S : Finset (Fin n), ξ = splitBy η S ∧ Covers (splitBy η S) η := by
  classical
  constructor
  · intro hcov
    obtain ⟨a, b, hab, rfl⟩ := (covers_iff_exists_merge ξ η).mp hcov
    have hS : ξ = splitBy (merge ξ a b) (Finset.univ.filter fun x => Quotient.mk ξ x = a) := by
      refine Setoid.ext fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩
      · refine (splitBy_rel_iff _ _ x y).mpr ⟨le_merge ξ a b hxy, ?_⟩
        have hcl : Quotient.mk ξ x = Quotient.mk ξ y := Quotient.sound hxy
        simp [hcl]
      · obtain ⟨hmerge, hside⟩ := (splitBy_rel_iff _ _ x y).mp hxy
        have hmm : mergeMap ξ a b (Quotient.mk ξ x) = mergeMap ξ a b (Quotient.mk ξ y) := hmerge
        rcases (mergeMap_eq_iff ξ hab _ _).mp hmm with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Quotient.exact h
        · exfalso
          have hxs : x ∈ Finset.univ.filter fun z => Quotient.mk ξ z = a :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
          have hys : y ∉ Finset.univ.filter fun z => Quotient.mk ξ z = a := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hy]
            exact fun h => hab h.symm
          exact hys (hside.mp hxs)
        · exfalso
          have hys : y ∈ Finset.univ.filter fun z => Quotient.mk ξ z = a :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩
          have hxs : x ∉ Finset.univ.filter fun z => Quotient.mk ξ z = a := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hx]
            exact fun h => hab h.symm
          exact hxs (hside.mpr hys)
    exact ⟨_, hS, hS ▸ hcov⟩
  · rintro ⟨S, rfl, hcov⟩
    exact hcov

/-- **Cutting along `S` and along the rest of `S`'s class give the same state.**

This is the double-naming that Kingman's factor `½` corrects.  His sum runs over piece sizes
`ν = 1, …, λ-1`, and the cut into pieces `{ν, λ-ν}` is reached twice -- once as `ν` and once
as `λ - ν`.  The `½` is therefore a convention about that SUM, not the number of states
attached to any single `ν`: for `2ν ≠ λ` there are `C(λ, ν)` cuts of type `{ν, λ-ν}`, and
only in the balanced case `2ν = λ` is the count `C(λ, ν)/2`.  Both readings give the same
total, `Σ_ν ½C(λ,ν) = 2^{λ-1} - 1`, which is `Coalescent.Program`. -/
theorem splitBy_compl {n : ℕ} (η : ER n) (S : Finset (Fin n)) (a : Fin n)
    (hSa : ∀ x ∈ S, η.r x a) :
    splitBy η S = splitBy η ((Finset.univ.filter fun z => η.r z a) \ S) := by
  classical
  refine (splitBy_eq_iff η S _).mpr ?_
  intro x y hxy
  by_cases hx : η.r x a
  · have hy : η.r y a := η.iseqv.trans (η.iseqv.symm hxy) hx
    have hmx : (x ∈ (Finset.univ.filter fun z => η.r z a) \ S) ↔ x ∉ S := by
      simp [Finset.mem_sdiff, hx]
    have hmy : (y ∈ (Finset.univ.filter fun z => η.r z a) \ S) ↔ y ∉ S := by
      simp [Finset.mem_sdiff, hy]
    rw [hmx, hmy]
    tauto
  · have hy : ¬ η.r y a := fun h => hx (η.iseqv.trans hxy h)
    have hxS : x ∉ S := fun h => hx (hSa x h)
    have hyS : y ∉ S := fun h => hy (hSa y h)
    have hmx : x ∉ (Finset.univ.filter fun z => η.r z a) \ S := by
      simp [Finset.mem_sdiff, hx]
    have hmy : y ∉ (Finset.univ.filter fun z => η.r z a) \ S := by
      simp [Finset.mem_sdiff, hy]
    simp [hxS, hyS, hmx, hmy]

/-- **A cut is determined by its set, up to swapping the two pieces.**  Cutting a class
along `S` and along its complement within that class give the same state -- which is exactly
why Kingman's sum over `ν = 1, …, λ-1` carries a factor `½`: it counts each cut twice. -/
theorem splitBy_eq_iff {n : ℕ} (η : ER n) (S T : Finset (Fin n)) :
    splitBy η S = splitBy η T ↔
      ∀ x y : Fin n, η.r x y → ((x ∈ S ↔ y ∈ S) ↔ (x ∈ T ↔ y ∈ T)) := by
  constructor
  · intro h x y hxy
    constructor
    · intro hS
      exact ((splitBy_rel_iff η T x y).mp
        (h ▸ (splitBy_rel_iff η S x y).mpr ⟨hxy, hS⟩)).2
    · intro hT
      exact ((splitBy_rel_iff η S x y).mp
        (h ▸ (splitBy_rel_iff η T x y).mpr ⟨hxy, hT⟩)).2
  · intro h
    refine Setoid.ext fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩
    · obtain ⟨h1, h2⟩ := (splitBy_rel_iff η S x y).mp hxy
      exact (splitBy_rel_iff η T x y).mpr ⟨h1, (h x y h1).mp h2⟩
    · obtain ⟨h1, h2⟩ := (splitBy_rel_iff η T x y).mp hxy
      exact (splitBy_rel_iff η S x y).mpr ⟨h1, (h x y h1).mpr h2⟩

end Coalescent

end Descent
