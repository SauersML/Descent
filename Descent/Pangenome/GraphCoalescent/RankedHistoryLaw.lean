/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Extend
import Descent.Coalescent.Trajectory

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Where the jump chain first reaches `k` blocks: Kingman's absolute law, derived

The hidden-lineage clock of a pangenome report (`ReportedConnectionClock`) needs one fact
about the Kingman `n`-coalescent itself: the law of the partition `Π^(k)` the embedded jump
chain occupies when it first reaches `k` blocks.  That is K-C (2.3), equation (D4) of the
pangenome note,

  `Pr(Π^(k) = π) = a_{n,k} ∏_{B ∈ π} |B|!`,   `a_{n,k} = (n-k)! k! (k-1)! / (n! (n-1)!)`.

`Descent.Coalescent.JumpChain` writes the formula down (`absoluteProb`) and proves its
backward-induction algebra, carrying as written the one combinatorial step it names as not
formalised: that the states refining a partition `η` by one block are the splits of one of
its classes, weighted by the binomial coefficient.  `Descent.Coalescent.Trajectory` has the
law itself (`blockLaw`).  This file supplies the missing count and joins the two:
`blockLaw_toReal_eq_absoluteProb` says the law of the jump chain after `n - k` jumps is
Kingman's formula, on the nose.

## The count

Kingman's weight is counted one sample at a time.  `rankWeight ξ` multiplies, over the
samples `x`, the number of members of `x`'s class that are at most `x`; inside a class of
size `m` those ranks run through `1, …, m`, so the product is `∏_B |B|!`
(`rankWeight_eq_blockWeight`).  A cover `ξ ≺ η` splits one class `C` of `η` along a proper
part `S`, and in rank form the weight changes only inside `C`:
`w(ξ) · |C|! = w(η) · |S|! · |C \ S|!` (`rankWeight_splitRel_mul`).

Every cover is the split of its class along the part holding the class minimum, and along no
other such part (`exists_canonical_split`, `splitRel_injective`).  Summing the split weights
over those parts gives `(|C| - 1) · w(η) / 2` per class (`two_mul_sum_splitIndex`), and
summing over classes gives the identity the backward induction needs:

  `2 · ∑_{ξ ≺ η} w(ξ) = (n - |η|) · w(η)`.            (`two_mul_sum_rankWeight_covers`)

With the jump probability `1/C(k,2)` and `JumpChain.jumpCoeff_recursion`, induction on the
number of jumps proves (D4) (`blockLaw_toReal`, `rankedHistoryLaw`).

## Scope

The theorem is about `Trajectory.blockLaw n (n - k)`, the head of the jump chain's trajectory
law after `n - k` jumps from `Δ`.  Each jump from a state with at least two blocks drops the
count by one (`Trajectory.blocks_of_mem_support_blockLaw`), so that state is where the chain
FIRST reaches `k` blocks.  The note proves (D4) by counting ranked merger sequences.  Here
it is proved by Kingman's backward recursion, whose count of covers weighted by `∏|B|!` does
the same work.  The number of ranked histories ending at `π` is not enumerated.

## Main results

- `rankWeight`, `blockWeight`, `rankWeight_eq_blockWeight`: `∏_B |B|!`, two ways.
- `covers_splitRel`, `exists_canonical_split`, `splitRel_injective`: covers are splits.
- `two_mul_sum_rankWeight_covers`: the weighted cover count below a partition.
- `blockLaw_succ`, `chainLaw_map_getD`: the head law is a Markov chain, and every entry of
  the trajectory has the head law of the matching jump count.
- `rankedHistoryLaw`: **(D4)**.
- `blockLaw_toReal_eq_absoluteProb`: **K-C (2.3) for the corpus's jump-chain law.**
- `jumpCoeff_mul_sum_blockWeight`: the normalisation, `a_{n,k} ∑_{|π| = k} ∏|B|! = 1`.

## Empirical status

None.  Every declaration is a statement about finite equivalence relations and about the
jump-chain law `Descent.Coalescent.Trajectory` builds from K-C (1.3)'s unit rates.  Whether a
real genealogy is Kingman's is the modelling premise of that module, not of this one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Coalescent
open scoped Classical Nat

/-! ### Kingman's weight, one sample at a time -/

/-- The class of `x` under `ξ`, as a finset of sample indices. -/
noncomputable def sampleClass {n : ℕ} (ξ : ER n) (x : Fin n) : Finset (Fin n) :=
  univ.filter fun y ↦ ξ.r x y

theorem mem_sampleClass {n : ℕ} {ξ : ER n} {x y : Fin n} :
    y ∈ sampleClass ξ x ↔ ξ.r x y := by
  simp [sampleClass]

theorem mem_sampleClass_self {n : ℕ} (ξ : ER n) (x : Fin n) : x ∈ sampleClass ξ x :=
  mem_sampleClass.mpr (ξ.iseqv.refl x)

/-- Related samples have the same class. -/
theorem sampleClass_eq_of_rel {n : ℕ} {ξ : ER n} {x y : Fin n} (h : ξ.r x y) :
    sampleClass ξ y = sampleClass ξ x := by
  ext z
  rw [mem_sampleClass, mem_sampleClass]
  exact ⟨fun hyz ↦ ξ.iseqv.trans h hyz, fun hxz ↦ ξ.iseqv.trans (ξ.iseqv.symm h) hxz⟩

/-- The rank of `x` inside its own class: how many members of the class are at most `x`. -/
noncomputable def classRank {n : ℕ} (ξ : ER n) (x : Fin n) : ℕ :=
  ((sampleClass ξ x).filter fun y ↦ y ≤ x).card

/-- **Kingman's weight `∏_B |B|!`, read one sample at a time.**  Each sample contributes its
rank inside its class, and the ranks inside a class of size `m` are `1, …, m`. -/
noncomputable def rankWeight {n : ℕ} (ξ : ER n) : ℕ := ∏ x : Fin n, classRank ξ x

/-- `∏_B |B|!`, the class-size factorials of K-C (2.3). -/
noncomputable def blockWeight {n : ℕ} (ξ : ER n) : ℕ := ∏ c : Quotient ξ, (classSize ξ c)!

/-- Inside any finite set of samples, the ranks multiply to the factorial of its size. -/
theorem prod_card_filter_le {n : ℕ} (T : Finset (Fin n)) :
    ∏ x ∈ T, (T.filter fun y ↦ y ≤ x).card = T.card ! := by
  refine Finset.induction_on_max T (by simp) fun a s hlt ih ↦ ?_
  have ha : a ∉ s := fun h ↦ lt_irrefl a (hlt a h)
  have htop : ((insert a s).filter fun y ↦ y ≤ a) = insert a s := by
    refine filter_true_of_mem fun y hy ↦ ?_
    rcases mem_insert.mp hy with rfl | hy
    · exact le_rfl
    · exact (hlt y hy).le
  have hrest : ∀ x ∈ s,
      ((insert a s).filter fun y ↦ y ≤ x).card = (s.filter fun y ↦ y ≤ x).card := by
    intro x hx
    rw [filter_insert, if_neg (not_le.mpr (hlt x hx))]
  rw [prod_insert ha, htop, prod_congr rfl hrest, ih, card_insert_of_notMem ha,
    Nat.factorial_succ]

/-- **The two readings of Kingman's weight agree.** -/
theorem rankWeight_eq_blockWeight {n : ℕ} (ξ : ER n) : rankWeight ξ = blockWeight ξ := by
  have hfib := prod_fiberwise_eq_prod_filter (univ : Finset (Fin n))
    (univ : Finset (Quotient ξ)) (Quotient.mk ξ) (classRank ξ)
  simp only [mem_univ, filter_true] at hfib
  rw [rankWeight, ← hfib, blockWeight]
  refine prod_congr rfl fun c _ ↦ ?_
  have hclass : ∀ x ∈ univ.filter (fun x : Fin n ↦ Quotient.mk ξ x = c),
      classRank ξ x
        = ((univ.filter fun x : Fin n ↦ Quotient.mk ξ x = c).filter fun y ↦ y ≤ x).card := by
    intro x hx
    have hxc : Quotient.mk ξ x = c := (mem_filter.mp hx).2
    unfold classRank
    congr 2
    ext y
    rw [mem_sampleClass, mem_filter]
    constructor
    · intro hxy
      exact ⟨mem_univ y, (Quotient.sound hxy).symm.trans hxc⟩
    · rintro ⟨-, hyc⟩
      exact Quotient.exact (hxc.trans hyc.symm)
  rw [prod_congr rfl hclass, prod_card_filter_le]
  rfl

/-! ### Splitting a class along a proper part -/

/-- **Split `η` along `S`**: two samples stay related when `η` relates them and `S` does not
separate them.  Built as a kernel, so it is an equivalence relation with no argument. -/
noncomputable def splitRel {n : ℕ} (η : ER n) (S : Finset (Fin n)) : ER n :=
  Setoid.ker fun x ↦ (Quotient.mk η x, decide (x ∈ S))

theorem splitRel_rel_iff {n : ℕ} {η : ER n} {S : Finset (Fin n)} {x y : Fin n} :
    (splitRel η S).r x y ↔ η.r x y ∧ (x ∈ S ↔ y ∈ S) := by
  show (Quotient.mk η x, decide (x ∈ S)) = (Quotient.mk η y, decide (y ∈ S)) ↔ _
  rw [Prod.mk.injEq, decide_eq_decide]
  exact and_congr ⟨Quotient.exact, Quotient.sound⟩ Iff.rfl

/-- A part of a class that is not the whole class leaves a member outside it. -/
theorem exists_mem_notMem_of_ne {n : ℕ} {S C : Finset (Fin n)} (hS : S ⊆ C) (hne : S ≠ C) :
    ∃ t ∈ C, t ∉ S := by
  by_contra h
  push_neg at h
  exact hne (Subset.antisymm hS h)

theorem sampleClass_splitRel_of_mem {n : ℕ} {η : ER n} {x y : Fin n} {S : Finset (Fin n)}
    (hS : S ⊆ sampleClass η x) (hy : y ∈ S) : sampleClass (splitRel η S) y = S := by
  ext z
  rw [mem_sampleClass, splitRel_rel_iff]
  constructor
  · rintro ⟨-, hz⟩
    exact hz.mp hy
  · intro hz
    have hxy : η.r x y := mem_sampleClass.mp (hS hy)
    have hxz : η.r x z := mem_sampleClass.mp (hS hz)
    exact ⟨η.iseqv.trans (η.iseqv.symm hxy) hxz, ⟨fun _ ↦ hz, fun _ ↦ hy⟩⟩

theorem sampleClass_splitRel_of_mem_sdiff {n : ℕ} {η : ER n} {x y : Fin n}
    {S : Finset (Fin n)} (hy : y ∈ sampleClass η x \ S) :
    sampleClass (splitRel η S) y = sampleClass η x \ S := by
  obtain ⟨hyC, hyS⟩ := mem_sdiff.mp hy
  have hxy : η.r x y := mem_sampleClass.mp hyC
  ext z
  rw [mem_sampleClass, splitRel_rel_iff, mem_sdiff, mem_sampleClass]
  constructor
  · rintro ⟨hyz, hz⟩
    exact ⟨η.iseqv.trans hxy hyz, fun hzS ↦ hyS (hz.mpr hzS)⟩
  · rintro ⟨hxz, hzS⟩
    exact ⟨η.iseqv.trans (η.iseqv.symm hxy) hxz,
      ⟨fun h ↦ absurd h hyS, fun h ↦ absurd h hzS⟩⟩

theorem sampleClass_splitRel_of_notMem {n : ℕ} {η : ER n} {x y : Fin n} {S : Finset (Fin n)}
    (hS : S ⊆ sampleClass η x) (hy : y ∉ sampleClass η x) :
    sampleClass (splitRel η S) y = sampleClass η y := by
  have hyS : y ∉ S := fun h ↦ hy (hS h)
  ext z
  rw [mem_sampleClass, splitRel_rel_iff, mem_sampleClass]
  constructor
  · exact fun h ↦ h.1
  · intro hyz
    have hzS : z ∉ S := by
      intro hz
      exact hy (mem_sampleClass.mpr
        (η.iseqv.trans (mem_sampleClass.mp (hS hz)) (η.iseqv.symm hyz)))
    exact ⟨hyz, ⟨fun h ↦ absurd h hyS, fun h ↦ absurd h hzS⟩⟩

/-- **The weight of a split.**  Only the split class changes, and there `|C|!` becomes
`|S|! |C \ S|!`. -/
theorem rankWeight_splitRel_mul {n : ℕ} {η : ER n} {x : Fin n} {S : Finset (Fin n)}
    (hS : S ⊆ sampleClass η x) :
    rankWeight (splitRel η S) * (sampleClass η x).card !
      = rankWeight η * S.card ! * (sampleClass η x \ S).card ! := by
  have hout : ∀ y ∈ univ \ sampleClass η x,
      classRank (splitRel η S) y = classRank η y := by
    intro y hy
    rw [classRank, classRank, sampleClass_splitRel_of_notMem hS (mem_sdiff.mp hy).2]
  have hin : ∀ y ∈ S, classRank (splitRel η S) y = (S.filter fun z ↦ z ≤ y).card := by
    intro y hy
    rw [classRank, sampleClass_splitRel_of_mem hS hy]
  have hrest : ∀ y ∈ sampleClass η x \ S, classRank (splitRel η S) y
      = ((sampleClass η x \ S).filter fun z ↦ z ≤ y).card := by
    intro y hy
    rw [classRank, sampleClass_splitRel_of_mem_sdiff hy]
  have hclass : ∀ y ∈ sampleClass η x,
      classRank η y = ((sampleClass η x).filter fun z ↦ z ≤ y).card := by
    intro y hy
    rw [classRank, sampleClass_eq_of_rel (mem_sampleClass.mp hy)]
  have hsplit : rankWeight (splitRel η S)
      = (∏ y ∈ univ \ sampleClass η x, classRank η y)
        * (S.card ! * (sampleClass η x \ S).card !) := by
    rw [rankWeight, ← prod_sdiff (subset_univ (sampleClass η x)), ← prod_sdiff hS,
      prod_congr rfl hout, prod_congr rfl hin, prod_congr rfl hrest, prod_card_filter_le,
      prod_card_filter_le]
    ring
  have hη : rankWeight η
      = (∏ y ∈ univ \ sampleClass η x, classRank η y) * (sampleClass η x).card ! := by
    rw [rankWeight, ← prod_sdiff (subset_univ (sampleClass η x)), prod_congr rfl hclass,
      prod_card_filter_le]
  rw [hsplit, hη]
  ring

/-- **Splitting a class along a proper part is one Kingman step below the class.** -/
theorem covers_splitRel {n : ℕ} {η : ER n} {x : Fin n} {S : Finset (Fin n)} (hxS : x ∈ S)
    (hS : S ⊆ sampleClass η x) (hne : S ≠ sampleClass η x) : Covers (splitRel η S) η := by
  obtain ⟨t, htC, htS⟩ := exists_mem_notMem_of_ne hS hne
  have hxt : η.r x t := mem_sampleClass.mp htC
  have hmem : ∀ y ∈ S, η.r x y := fun y hy ↦ mem_sampleClass.mp (hS hy)
  have hab : Quotient.mk (splitRel η S) x ≠ Quotient.mk (splitRel η S) t := by
    intro h
    exact htS ((splitRel_rel_iff.mp (Quotient.exact h)).2.mp hxS)
  have hA : ∀ w, Quotient.mk (splitRel η S) w = Quotient.mk (splitRel η S) x ↔ w ∈ S := by
    intro w
    constructor
    · intro h
      exact (splitRel_rel_iff.mp (Quotient.exact h)).2.mpr hxS
    · intro hw
      exact Quotient.sound (splitRel_rel_iff.mpr
        ⟨η.iseqv.symm (hmem w hw), ⟨fun _ ↦ hxS, fun _ ↦ hw⟩⟩)
  have hB : ∀ w, Quotient.mk (splitRel η S) w = Quotient.mk (splitRel η S) t
      ↔ η.r x w ∧ w ∉ S := by
    intro w
    constructor
    · intro h
      obtain ⟨hwt, hiff⟩ := splitRel_rel_iff.mp (Quotient.exact h)
      exact ⟨η.iseqv.trans hxt (η.iseqv.symm hwt), fun hw ↦ htS (hiff.mp hw)⟩
    · rintro ⟨hxw, hw⟩
      exact Quotient.sound (splitRel_rel_iff.mpr
        ⟨η.iseqv.trans (η.iseqv.symm hxw) hxt, ⟨fun h ↦ absurd h hw, fun h ↦ absurd h htS⟩⟩)
  have hE : ∀ w v, Quotient.mk (splitRel η S) w = Quotient.mk (splitRel η S) v
      ↔ η.r w v ∧ (w ∈ S ↔ v ∈ S) :=
    fun w v ↦ ⟨fun h ↦ splitRel_rel_iff.mp (Quotient.exact h),
      fun h ↦ Quotient.sound (splitRel_rel_iff.mpr h)⟩
  refine (covers_iff_exists_merge _ η).mpr ⟨_, _, hab, Setoid.ext fun y z ↦ ?_⟩
  show η.r y z ↔ mergeMap (splitRel η S) _ _ (Quotient.mk _ y)
    = mergeMap (splitRel η S) _ _ (Quotient.mk _ z)
  rw [mergeMap_eq_iff _ hab, hE y z, hA y, hB z, hB y, hA z]
  constructor
  · intro hyz
    by_cases hy : y ∈ S <;> by_cases hz : z ∈ S
    · exact Or.inl ⟨hyz, ⟨fun _ ↦ hz, fun _ ↦ hy⟩⟩
    · exact Or.inr (Or.inl ⟨hy, η.iseqv.trans (hmem y hy) hyz, hz⟩)
    · exact Or.inr (Or.inr ⟨⟨η.iseqv.trans (hmem z hz) (η.iseqv.symm hyz), hy⟩, hz⟩)
    · exact Or.inl ⟨hyz, ⟨fun h ↦ absurd h hy, fun h ↦ absurd h hz⟩⟩
  · rintro (⟨hyz, -⟩ | ⟨hy, hxz, -⟩ | ⟨⟨hxy, -⟩, hz⟩)
    · exact hyz
    · exact η.iseqv.trans (η.iseqv.symm (hmem y hy)) hxz
    · exact η.iseqv.trans (η.iseqv.symm hxy) (hmem z hz)

/-! ### Class minima, and the canonical split of a cover -/

/-- The samples that are the least member of their class: one per block. -/
noncomputable def classMinima {n : ℕ} (η : ER n) : Finset (Fin n) :=
  univ.filter fun x ↦ ∀ y, η.r x y → x ≤ y

theorem mem_classMinima {n : ℕ} {η : ER n} {x : Fin n} :
    x ∈ classMinima η ↔ ∀ y, η.r x y → x ≤ y := by
  simp [classMinima]

/-- The least member of the class of `y`. -/
noncomputable def classMinOf {n : ℕ} (η : ER n) (y : Fin n) : Fin n :=
  (sampleClass η y).min' ⟨y, mem_sampleClass_self η y⟩

theorem classMinOf_rel {n : ℕ} (η : ER n) (y : Fin n) : η.r y (classMinOf η y) :=
  mem_sampleClass.mp (min'_mem _ _)

theorem classMinOf_le {n : ℕ} {η : ER n} {y z : Fin n} (h : η.r y z) : classMinOf η y ≤ z :=
  min'_le _ _ (mem_sampleClass.mpr h)

theorem classMinOf_mem_classMinima {n : ℕ} (η : ER n) (y : Fin n) :
    classMinOf η y ∈ classMinima η :=
  mem_classMinima.mpr fun _ hz ↦ classMinOf_le (η.iseqv.trans (classMinOf_rel η y) hz)

theorem classMinOf_eq_iff {n : ℕ} {η : ER n} {x y : Fin n} (hx : x ∈ classMinima η) :
    classMinOf η y = x ↔ η.r x y := by
  constructor
  · rintro rfl
    exact η.iseqv.symm (classMinOf_rel η y)
  · intro hxy
    exact le_antisymm (classMinOf_le (η.iseqv.symm hxy))
      (mem_classMinima.mp hx _ (η.iseqv.trans hxy (classMinOf_rel η y)))

/-- **One minimum per block.** -/
theorem card_classMinima {n : ℕ} (η : ER n) : (classMinima η).card = blocks η := by
  have hbij : Function.Bijective (fun x : classMinima η ↦ Quotient.mk η x.1) := by
    constructor
    · rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
      have hxx' : η.r x x' := Quotient.exact h
      exact Subtype.ext (le_antisymm (mem_classMinima.mp hx _ hxx')
        (mem_classMinima.mp hx' _ (η.iseqv.symm hxx')))
    · intro q
      obtain ⟨y, rfl⟩ := quotient_mk_surjective η q
      exact ⟨⟨classMinOf η y, classMinOf_mem_classMinima η y⟩,
        Quotient.sound (η.iseqv.symm (classMinOf_rel η y))⟩
  rw [blocks, ← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_finsetCard]

/-- The classes of the minima cover the sample exactly once. -/
theorem sum_card_sampleClass_classMinima {n : ℕ} (η : ER n) :
    ∑ x ∈ classMinima η, (sampleClass η x).card = n := by
  have h := card_eq_sum_card_fiberwise (f := classMinOf η) (s := univ) (t := classMinima η)
    (fun y _ ↦ classMinOf_mem_classMinima η y)
  rw [card_univ, Fintype.card_fin] at h
  refine (sum_congr rfl fun x hx ↦ ?_).trans h.symm
  congr 1
  ext y
  rw [mem_sampleClass, mem_filter]
  exact ⟨fun hxy ↦ ⟨mem_univ y, (classMinOf_eq_iff hx).mpr hxy⟩,
    fun h ↦ (classMinOf_eq_iff hx).mp h.2⟩

/-- A merge, split back along the class holding a given sample, returns the partition it
merged; the part is proper and contains the sample. -/
theorem splitRel_merge {n : ℕ} {ξ : ER n} {c d : Quotient ξ} (hcd : c ≠ d) {x : Fin n}
    (hx : Quotient.mk ξ x = c) :
    splitRel (merge ξ c d) (univ.filter fun y ↦ Quotient.mk ξ y = c) = ξ ∧
      x ∈ univ.filter (fun y ↦ Quotient.mk ξ y = c) ∧
      univ.filter (fun y ↦ Quotient.mk ξ y = c) ⊆ sampleClass (merge ξ c d) x ∧
      univ.filter (fun y ↦ Quotient.mk ξ y = c) ≠ sampleClass (merge ξ c d) x := by
  obtain ⟨t, ht⟩ := quotient_mk_surjective ξ d
  refine ⟨Setoid.ext fun y z ↦ ?_, mem_filter.mpr ⟨mem_univ x, hx⟩, fun y hy ↦ ?_, ?_⟩
  · rw [splitRel_rel_iff, mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    constructor
    · rintro ⟨hyz, hiff⟩
      have h' : mergeMap ξ c d (Quotient.mk ξ y) = mergeMap ξ c d (Quotient.mk ξ z) := hyz
      rcases (mergeMap_eq_iff ξ hcd _ _).mp h' with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Quotient.exact h1
      · exact absurd ((hiff.mp h1).symm.trans h2) hcd
      · exact absurd ((hiff.mpr h2).symm.trans h1) hcd
    · intro hyz
      exact ⟨le_merge ξ c d hyz, by rw [Quotient.sound hyz]⟩
  · have hyc : Quotient.mk ξ y = c := (mem_filter.mp hy).2
    exact mem_sampleClass.mpr (le_merge ξ c d (Quotient.exact (hx.trans hyc.symm)))
  · intro heq
    have htC : t ∈ sampleClass (merge ξ c d) x := mem_sampleClass.mpr (merge_rel ξ c d hx ht)
    rw [← heq, mem_filter] at htC
    exact hcd (htC.2.symm.trans ht)

/-- **Every cover is the split of a class along the part holding the class minimum.** -/
theorem exists_canonical_split {n : ℕ} {ξ η : ER n} (h : Covers ξ η) :
    ∃ x ∈ classMinima η, ∃ S, x ∈ S ∧ S ⊆ sampleClass η x ∧ S ≠ sampleClass η x ∧
      splitRel η S = ξ := by
  obtain ⟨a, b, hab, rfl⟩ := (covers_iff_exists_merge ξ η).mp h
  obtain ⟨x0, hx0⟩ := quotient_mk_surjective ξ a
  obtain ⟨x, hxmin, hrel⟩ : ∃ x, x ∈ classMinima (merge ξ a b) ∧ (merge ξ a b).r x0 x :=
    ⟨classMinOf _ x0, classMinOf_mem_classMinima _ x0, classMinOf_rel _ x0⟩
  have hcases : Quotient.mk ξ x = a ∨ Quotient.mk ξ x = b := by
    have h' : mergeMap ξ a b (Quotient.mk ξ x0) = mergeMap ξ a b (Quotient.mk ξ x) := hrel
    rcases (mergeMap_eq_iff ξ hab _ _).mp h' with h1 | ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inl (h1.symm.trans hx0)
    · exact Or.inr h2
    · exact Or.inl h2
  rcases hcases with hxa | hxb
  · obtain ⟨hsplit, hxS, hS, hne⟩ := splitRel_merge hab hxa
    exact ⟨x, hxmin, _, hxS, hS, hne, hsplit⟩
  · rw [merge_comm ξ hab] at hxmin ⊢
    obtain ⟨hsplit, hxS, hS, hne⟩ := splitRel_merge (Ne.symm hab) hxb
    exact ⟨x, hxmin, _, hxS, hS, hne, hsplit⟩

/-- **And along no other such part.**  Two canonical splits giving the same partition split
the same class along the same part. -/
theorem splitRel_injective {n : ℕ} {η : ER n} {x x' : Fin n} {S S' : Finset (Fin n)}
    (hx : x ∈ classMinima η) (hxS : x ∈ S) (hS : S ⊆ sampleClass η x)
    (hne : S ≠ sampleClass η x) (hx' : x' ∈ classMinima η) (hxS' : x' ∈ S')
    (hS' : S' ⊆ sampleClass η x') (h : splitRel η S = splitRel η S') : x = x' ∧ S = S' := by
  have hxx' : η.r x x' := by
    by_contra hc
    obtain ⟨t, htC, htS⟩ := exists_mem_notMem_of_ne hS hne
    have hxt : η.r x t := mem_sampleClass.mp htC
    have hxS'n : x ∉ S' := fun hm ↦ hc (η.iseqv.symm (mem_sampleClass.mp (hS' hm)))
    have htS'n : t ∉ S' := fun hm ↦
      hc (η.iseqv.trans hxt (η.iseqv.symm (mem_sampleClass.mp (hS' hm))))
    have hrel' : (splitRel η S').r x t :=
      splitRel_rel_iff.mpr ⟨hxt, ⟨fun hm ↦ absurd hm hxS'n, fun hm ↦ absurd hm htS'n⟩⟩
    rw [← h] at hrel'
    exact htS ((splitRel_rel_iff.mp hrel').2.mp hxS)
  have hxeq : x = x' := le_antisymm (mem_classMinima.mp hx _ hxx')
    (mem_classMinima.mp hx' _ (η.iseqv.symm hxx'))
  subst hxeq
  refine ⟨rfl, ?_⟩
  have key : ∀ T : Finset (Fin n), x ∈ T → T ⊆ sampleClass η x →
      ∀ y, y ∈ T ↔ (splitRel η T).r x y := by
    intro T hxT hT y
    rw [splitRel_rel_iff]
    exact ⟨fun hy ↦ ⟨mem_sampleClass.mp (hT hy), ⟨fun _ ↦ hy, fun _ ↦ hxT⟩⟩,
      fun hy ↦ hy.2.mp hxT⟩
  ext y
  rw [key S hxS hS y, key S' hxS' hS' y, h]

/-! ### The weighted count of covers -/

/-- The proper parts of the class of `x` that contain `x`, indexed by what they add to `x`. -/
noncomputable def splitIndex {n : ℕ} (η : ER n) (x : Fin n) : Finset (Finset (Fin n)) :=
  ((sampleClass η x).erase x).powerset.erase ((sampleClass η x).erase x)

/-- `2 ∑_{j=0}^{m-1} (j+1) = m (m+1)`. -/
theorem two_mul_sum_range_succ (m : ℕ) : 2 * ∑ j ∈ range m, (j + 1) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

/-- **The factorial sum over proper parts.**  Adding a marked element to every proper subset
`T` of a `d`-set and weighting by `(|T|+1)! (d-|T|)!` gives `(d+1)! d / 2`. -/
theorem two_mul_sum_split_factorial {α : Type*} [DecidableEq α] (D : Finset α) :
    2 * ∑ T ∈ D.powerset.erase D, (T.card + 1)! * (D.card - T.card)!
      = (D.card + 1)! * D.card := by
  have hcard := sum_powerset_apply_card (fun j ↦ (j + 1)! * (D.card - j)!) (x := D)
  simp only at hcard
  have hall : ∑ T ∈ D.powerset, (T.card + 1)! * (D.card - T.card)!
      = D.card ! * ∑ j ∈ range (D.card + 1), (j + 1) := by
    rw [hcard, mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    have hjd : j ≤ D.card := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [smul_eq_mul, Nat.factorial_succ, ← Nat.choose_mul_factorial_mul_factorial hjd]
    ring
  have htop := add_sum_erase D.powerset (fun T ↦ (T.card + 1)! * (D.card - T.card)!)
    (mem_powerset_self D)
  simp only [Nat.sub_self, Nat.factorial_zero, mul_one] at htop
  have hgauss := two_mul_sum_range_succ (D.card + 1)
  have hkey : 2 * ∑ T ∈ D.powerset.erase D, (T.card + 1)! * (D.card - T.card)!
      + 2 * (D.card + 1)! = (D.card + 1)! * D.card + 2 * (D.card + 1)! := by
    calc 2 * ∑ T ∈ D.powerset.erase D, (T.card + 1)! * (D.card - T.card)!
          + 2 * (D.card + 1)!
        = 2 * ∑ T ∈ D.powerset, (T.card + 1)! * (D.card - T.card)! := by
          rw [← htop]
          ring
      _ = D.card ! * (2 * ∑ j ∈ range (D.card + 1), (j + 1)) := by
          rw [hall]
          ring
      _ = (D.card + 1)! * D.card + 2 * (D.card + 1)! := by
          rw [hgauss, Nat.factorial_succ]
          ring
  omega

/-- **The canonical splits of one class, weighted.**  Splitting the class `C` of `x` along the
proper parts containing `x` gives total weight `(|C| - 1) w(η) / 2`. -/
theorem two_mul_sum_splitIndex {n : ℕ} (η : ER n) (x : Fin n) :
    2 * ∑ T ∈ splitIndex η x, rankWeight (splitRel η (insert x T))
      = rankWeight η * ((sampleClass η x).card - 1) := by
  have hxC : x ∈ sampleClass η x := mem_sampleClass_self η x
  have hCD : (sampleClass η x).card = ((sampleClass η x).erase x).card + 1 :=
    (card_erase_add_one hxC).symm
  have hterm : ∀ T ∈ splitIndex η x,
      rankWeight (splitRel η (insert x T)) * (sampleClass η x).card !
        = rankWeight η * ((T.card + 1)! * (((sampleClass η x).erase x).card - T.card)!) := by
    intro T hT
    have hTD : T ⊆ (sampleClass η x).erase x := mem_powerset.mp (mem_of_mem_erase hT)
    have hxT : x ∉ T := fun h ↦ notMem_erase x (sampleClass η x) (hTD h)
    have hsub : insert x T ⊆ sampleClass η x :=
      insert_subset hxC (hTD.trans (erase_subset x (sampleClass η x)))
    have hsd : (sampleClass η x \ insert x T).card
        = ((sampleClass η x).erase x).card - T.card := by
      rw [card_sdiff_of_subset hsub, card_insert_of_notMem hxT, hCD]
      omega
    rw [rankWeight_splitRel_mul hsub, card_insert_of_notMem hxT, hsd]
    ring
  have hpos : 0 < (sampleClass η x).card ! := Nat.factorial_pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  have h2 := two_mul_sum_split_factorial ((sampleClass η x).erase x)
  calc 2 * ∑ T ∈ splitIndex η x, rankWeight (splitRel η (insert x T))
        * (sampleClass η x).card !
      = 2 * ∑ T ∈ splitIndex η x,
          rankWeight (splitRel η (insert x T)) * (sampleClass η x).card ! := by
        rw [mul_assoc, sum_mul]
    _ = rankWeight η * (2 * ∑ T ∈ ((sampleClass η x).erase x).powerset.erase
          ((sampleClass η x).erase x),
          (T.card + 1)! * (((sampleClass η x).erase x).card - T.card)!) := by
        rw [sum_congr rfl hterm, ← mul_sum, splitIndex]
        ring
    _ = rankWeight η * ((sampleClass η x).card - 1) * (sampleClass η x).card ! := by
        rw [h2, hCD, Nat.add_sub_cancel]
        ring

/-- The covers below `η` are the canonical splits, one each. -/
theorem sum_rankWeight_splitRel {n : ℕ} (η : ER n) :
    ∑ p ∈ (classMinima η).sigma (splitIndex η), rankWeight (splitRel η (insert p.1 p.2))
      = ∑ ξ ∈ univ.filter (fun ξ ↦ Covers ξ η), rankWeight ξ := by
  have hfacts : ∀ x T, T ∈ splitIndex η x →
      x ∉ T ∧ insert x T ⊆ sampleClass η x ∧ insert x T ≠ sampleClass η x := by
    intro x T hT
    obtain ⟨hne, hpow⟩ := mem_erase.mp hT
    have hTD : T ⊆ (sampleClass η x).erase x := mem_powerset.mp hpow
    have hxT : x ∉ T := fun h ↦ notMem_erase x (sampleClass η x) (hTD h)
    refine ⟨hxT, insert_subset (mem_sampleClass_self η x)
      (hTD.trans (erase_subset x (sampleClass η x))), fun heq ↦ hne ?_⟩
    rw [← heq, erase_insert hxT]
  refine sum_bij (fun p _ ↦ splitRel η (insert p.1 p.2)) ?_ ?_ ?_ fun _ _ ↦ rfl
  · rintro ⟨x, T⟩ hp
    obtain ⟨-, hT⟩ := mem_sigma.mp hp
    obtain ⟨-, hsub, hne⟩ := hfacts x T hT
    exact mem_filter.mpr ⟨mem_univ _, covers_splitRel (mem_insert_self x T) hsub hne⟩
  · rintro ⟨x, T⟩ hp ⟨x', T'⟩ hp' h
    obtain ⟨hx, hT⟩ := mem_sigma.mp hp
    obtain ⟨hx', hT'⟩ := mem_sigma.mp hp'
    obtain ⟨hxT, hsub, hne⟩ := hfacts x T hT
    obtain ⟨hxT', hsub', -⟩ := hfacts x' T' hT'
    obtain ⟨rfl, hins⟩ := splitRel_injective hx (mem_insert_self x T) hsub hne hx'
      (mem_insert_self x' T') hsub' h
    have hTT : T = T' := by rw [← erase_insert hxT, hins, erase_insert hxT']
    rw [hTT]
  · intro ξ hξ
    obtain ⟨x, hx, S, hxS, hS, hne, rfl⟩ := exists_canonical_split (mem_filter.mp hξ).2
    refine ⟨⟨x, S.erase x⟩, mem_sigma.mpr ⟨hx, mem_erase.mpr ⟨fun heq ↦ hne ?_,
      mem_powerset.mpr (erase_subset_erase x hS)⟩⟩, ?_⟩
    · rw [← insert_erase hxS, heq, insert_erase (mem_sampleClass_self η x)]
    · show splitRel η (insert x (S.erase x)) = splitRel η S
      rw [insert_erase hxS]

/-- **The weighted cover count below a partition.**  `2 ∑_{ξ ≺ η} ∏_{B∈ξ} |B|! =
(n - |η|) ∏_{B∈η} |B|!`: the combinatorial step of K-C's proof of (2.3). -/
theorem two_mul_sum_rankWeight_covers {n : ℕ} (η : ER n) :
    2 * ∑ ξ ∈ univ.filter (fun ξ ↦ Covers ξ η), rankWeight ξ
      = (n - blocks η) * rankWeight η := by
  have hexcess : ∑ x ∈ classMinima η, ((sampleClass η x).card - 1) = n - blocks η := by
    have hsplit : ∑ x ∈ classMinima η, (((sampleClass η x).card - 1) + 1)
        = ∑ x ∈ classMinima η, (sampleClass η x).card := by
      refine sum_congr rfl fun x _ ↦ ?_
      have : 0 < (sampleClass η x).card := card_pos.mpr ⟨x, mem_sampleClass_self η x⟩
      omega
    rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one, card_classMinima,
      sum_card_sampleClass_classMinima] at hsplit
    omega
  rw [← sum_rankWeight_splitRel, sum_sigma, mul_sum,
    sum_congr rfl fun x _ ↦ two_mul_sum_splitIndex η x, ← mul_sum, hexcess, mul_comm]

/-! ### The law of the jump chain's head -/

/-- The head of the trajectory law is the trajectory's first entry. -/
theorem blockLaw_eq_map (n j : ℕ) :
    blockLaw n j = (chainLaw n j).map fun l ↦ l.getD 0 (Delta n) := by
  unfold blockLaw PMF.map
  congr 1
  funext l
  cases l <;> rfl

/-- **Every entry of a trajectory has the head law of its jump count.**  Entry `i` after `m`
jumps is the state `i` jumps ago, and its law is `blockLaw n (m - i)`. -/
theorem chainLaw_map_getD {n : ℕ} :
    ∀ m i, i ≤ m → (chainLaw n m).map (fun l ↦ l.getD i (Delta n)) = blockLaw n (m - i) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    exact (blockLaw_eq_map n 0).symm
  | succ m ih =>
    intro i hi
    cases i with
    | zero => exact (blockLaw_eq_map n (m + 1)).symm
    | succ i =>
      rw [Nat.add_sub_add_right, ← ih i (by omega), chainLaw, PMF.map_bind]
      show _ = (chainLaw n m).bind (PMF.pure ∘ fun l ↦ l.getD i (Delta n))
      congr 1
      funext l
      cases l with
      | nil =>
        show (PMF.pure []).map (fun l ↦ l.getD (i + 1) (Delta n))
          = PMF.pure (([] : List (ER n)).getD i (Delta n))
        rw [PMF.pure_map]
        rfl
      | cons x rest =>
        show ((jumpLaw x).map fun y ↦ y :: x :: rest).map (fun l ↦ l.getD (i + 1) (Delta n))
          = PMF.pure ((x :: rest).getD i (Delta n))
        rw [PMF.map_comp]
        exact PMF.map_const

/-- **The head of the trajectory is a Markov chain with kernel `jumpLaw`.** -/
theorem blockLaw_succ (n j : ℕ) : blockLaw n (j + 1) = (blockLaw n j).bind jumpLaw := by
  rw [blockLaw_eq_map, blockLaw_eq_map, chainLaw, PMF.map_bind, PMF.bind_map]
  refine PMF.ext fun η ↦ ?_
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun l ↦ ?_
  by_cases hl : l ∈ (chainLaw n j).support
  · obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil (chainLaw_ne_nil j hl)
    congr 1
    show ((jumpLaw x).map fun y ↦ y :: x :: rest).map (fun l ↦ l.getD 0 (Delta n)) η
      = jumpLaw x η
    have hid : ((fun l : List (ER n) ↦ l.getD 0 (Delta n)) ∘ fun y ↦ y :: x :: rest) = id :=
      rfl
    rw [PMF.map_comp, hid, PMF.map_id]
  · simp only [(PMF.apply_eq_zero_iff _ _).mpr hl, zero_mul]

/-- The mass the jump kernel puts on `η`, in real form: `1/d_k` on a cover, `0` elsewhere. -/
theorem jumpLaw_toReal {n : ℕ} {ξ : ER n} (hk : 2 ≤ blocks ξ) (η : ER n) :
    (jumpLaw ξ η).toReal = if Covers ξ η then 1 / deathRate (blocks ξ) else 0 := by
  by_cases h : Covers ξ η
  · rw [if_pos h, jumpLaw_apply_cover hk h, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ← card_covers, card_covers_eq_deathRate, one_div]
  · rw [if_neg h, (PMF.apply_eq_zero_iff _ _).mpr fun hm ↦ h ((mem_support_jumpLaw hk).mp hm),
      ENNReal.toReal_zero]

/-- K-C (2.3)'s prefactor at `k = n` is `1`. -/
theorem jumpCoeff_self (n : ℕ) : jumpCoeff n n = 1 := by
  have hn1 : ((n ! * (n - 1)! : ℕ) : ℝ) ≠ 0 := by positivity
  unfold jumpCoeff
  rw [Nat.sub_self, Nat.factorial_zero, one_mul]
  exact div_self hn1

/-- The singleton partition has weight `1`. -/
theorem rankWeight_bot (n : ℕ) : rankWeight (⊥ : ER n) = 1 := by
  refine prod_eq_one fun x _ ↦ ?_
  have hclass : sampleClass (⊥ : ER n) x = {x} := by
    ext y
    rw [mem_sampleClass, mem_singleton]
    exact ⟨fun h ↦ Eq.symm h, fun h ↦ Eq.symm h⟩
  rw [classRank, hclass, filter_singleton, if_pos le_rfl, card_singleton]

/-- **(D4) at every jump count.**  After `j < n` jumps from `Δ`, the jump chain is at `ξ` with
probability `a_{n,n-j} ∏_B |B|!` when `ξ` has `n - j` blocks, and never otherwise. -/
theorem blockLaw_toReal {n : ℕ} :
    ∀ j, j < n → ∀ ξ : ER n, (blockLaw n j ξ).toReal
      = if blocks ξ = n - j then jumpCoeff n (n - j) * (rankWeight ξ : ℝ) else 0 := by
  intro j
  induction j with
  | zero =>
    intro _ ξ
    have hlaw : blockLaw n 0 = PMF.pure (Delta n) := by
      rw [blockLaw_eq_map, chainLaw, PMF.pure_map]
      rfl
    rw [hlaw, PMF.pure_apply, Nat.sub_zero]
    by_cases hξ : ξ = Delta n
    · subst hξ
      rw [if_pos rfl, if_pos (blocks_bot n), jumpCoeff_self, rankWeight_bot]
      simp
    · have hb : blocks ξ ≠ n := fun hb ↦
        hξ (eq_of_le_of_blocks_eq bot_le (by rw [blocks_bot, hb])).symm
      rw [if_neg hξ, if_neg hb]
      simp
  | succ j ih =>
    intro hj η
    have hjn : j < n := by omega
    have hk2 : 2 ≤ n - j := by omega
    rw [blockLaw_succ, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum
      fun ξ _ ↦ ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    have hterm : ∀ ξ ∈ (univ : Finset (ER n)), (blockLaw n j ξ * jumpLaw ξ η).toReal
        = if Covers ξ η ∧ blocks ξ = n - j then
            jumpCoeff n (n - j) * (rankWeight ξ : ℝ) / deathRate (n - j) else 0 := by
      intro ξ _
      rw [ENNReal.toReal_mul, ih hjn ξ]
      by_cases hb : blocks ξ = n - j
      · rw [if_pos hb, jumpLaw_toReal (by omega : 2 ≤ blocks ξ) η, hb]
        by_cases hc : Covers ξ η
        · rw [if_pos hc, if_pos ⟨hc, rfl⟩]
          ring
        · rw [if_neg hc, if_neg fun h ↦ hc h.1, mul_zero]
      · rw [if_neg hb, if_neg fun h ↦ hb h.2, zero_mul]
    rw [sum_congr rfl hterm, ← sum_filter]
    by_cases hη : blocks η = n - (j + 1)
    · rw [if_pos hη]
      have hfilter : univ.filter (fun ξ ↦ Covers ξ η ∧ blocks ξ = n - j)
          = univ.filter (fun ξ ↦ Covers ξ η) := by
        refine filter_congr fun ξ _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
        have := h.2
        omega
      rw [hfilter, ← sum_div, ← mul_sum]
      have hsplit := two_mul_sum_rankWeight_covers η
      rw [hη, show n - (n - (j + 1)) = j + 1 by omega] at hsplit
      have hsplitR : (∑ ξ ∈ univ.filter (fun ξ ↦ Covers ξ η), (rankWeight ξ : ℝ))
          = ((j : ℝ) + 1) * rankWeight η / 2 := by
        have hcast := congrArg (fun m : ℕ ↦ (m : ℝ)) hsplit
        push_cast at hcast
        linarith
      rw [hsplitR]
      have hrec := jumpCoeff_recursion hk2 (Nat.sub_le n j)
      rw [show n - (n - j) + 1 = j + 1 by omega, show n - j - 1 = n - (j + 1) by omega] at hrec
      push_cast at hrec
      have hd : deathRate (n - j) ≠ 0 := deathRate_ne_zero hk2
      calc jumpCoeff n (n - j) * (((j : ℝ) + 1) * rankWeight η / 2) / deathRate (n - j)
          = (jumpCoeff n (n - j) * ((j : ℝ) + 1)) * rankWeight η
              / (2 * deathRate (n - j)) := by ring
        _ = (2 * deathRate (n - j) * jumpCoeff n (n - (j + 1))) * rankWeight η
              / (2 * deathRate (n - j)) := by rw [hrec]
        _ = jumpCoeff n (n - (j + 1)) * rankWeight η := by field_simp
    · rw [if_neg hη]
      have hfilter : univ.filter (fun ξ ↦ Covers ξ η ∧ blocks ξ = n - j) = ∅ := by
        refine filter_eq_empty_iff.mpr fun ξ _ h ↦ hη ?_
        have h1 := h.1.2
        have h2 := h.2
        omega
      rw [hfilter, sum_empty]

/-- **(D4).**  The probability that the embedded Kingman jump chain, on first reaching `k`
blocks, is at the partition `π` is `a_{n,k} ∏_{B ∈ π} |B|!`,
`a_{n,k} = (n-k)! k! (k-1)! / (n! (n-1)!)`. -/
theorem rankedHistoryLaw {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {π : ER n} (hπ : blocks π = k) :
    (blockLaw n (n - k) π).toReal = jumpCoeff n k * (blockWeight π : ℝ) := by
  rw [blockLaw_toReal (n - k) (by omega) π, if_pos (show blocks π = n - (n - k) by omega),
    show n - (n - k) = k by omega, rankWeight_eq_blockWeight]

/-- **K-C (2.3) for the corpus's jump-chain law.**  `Trajectory.blockLaw` after `n - k` jumps
is `JumpChain.absoluteProb` at the multiset of class sizes: the formula and the law agree. -/
theorem blockLaw_toReal_eq_absoluteProb {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {π : ER n}
    (hπ : blocks π = k) :
    (blockLaw n (n - k) π).toReal = absoluteProb n k (univ.val.map (classSize π)) := by
  rw [rankedHistoryLaw hk hkn hπ, absoluteProb, Multiset.map_map, blockWeight,
    prod_eq_multiset_prod]
  rfl

/-- **The normalisation of (D4).**  `a_{n,k} ∑_{|π| = k} ∏_B |B|! = 1`, so the weighted count
of `k`-block partitions is `1/a_{n,k} = n! (n-1)! / ((n-k)! k! (k-1)!)`. -/
theorem jumpCoeff_mul_sum_blockWeight {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    jumpCoeff n k * ∑ π ∈ univ.filter (fun π : ER n ↦ blocks π = k), (blockWeight π : ℝ)
      = 1 := by
  have hmass : ∑ π : ER n, (blockLaw n (n - k) π).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun π _ ↦ PMF.apply_ne_top _ _, ← tsum_fintype, PMF.tsum_coe,
      ENNReal.toReal_one]
  have hform : ∀ π ∈ (univ : Finset (ER n)), (blockLaw n (n - k) π).toReal
      = if blocks π = k then jumpCoeff n k * (blockWeight π : ℝ) else 0 := by
    intro π _
    rw [blockLaw_toReal (n - k) (by omega) π, show n - (n - k) = k by omega,
      rankWeight_eq_blockWeight]
  rw [sum_congr rfl hform, ← sum_filter] at hmass
  rw [mul_sum]
  exact hmass

end Descent.Pangenome.GraphCoalescent
