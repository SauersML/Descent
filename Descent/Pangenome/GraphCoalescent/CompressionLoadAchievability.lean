/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MarkovCompressions
import Descent.Pangenome.GraphCoalescent.RankedHistoryLaw

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Every hidden load within the bound is attained

A report component `C` of an interface `s`, with `|C|` individuals occupying `w_C` graph states,
hides at least one and at most `|C| - w_C + 1` true lineages
(`MarkovCompressions.hiddenLoad_add_componentWidth_le`).  This file proves the converse: for every
report `Y` above the interface kernel and every choice of loads within those bounds, one per
component, some coalescent state reports `Y` and carries exactly those loads.  So the hidden state
over a report ranges over the whole box `∏_C [1, |C| - w_C + 1]`, which is what the counts of the
coarsest Markov refinement are made of.

The construction.  In each component keep the least individual of every graph state it occupies,
the fiber minima, in one block together with every individual not chosen as a singleton, and
choose `L_C - 1` of the `|C| - w_C` other individuals as singletons
(`exists_observed_eq_hiddenLoad_eq`).  The report of this state is `Y`: two individuals of one
component are joined through their fiber minima, which share the big block.  Its load in `C` is
the big block plus the singletons.  The number of fiber minima in a component is its width
(`card_filter_classMinima_eq_componentWidth`), which is why there are exactly `|C| - w_C`
individuals to choose the singletons from.

`exists_observed_eq_hiddenLoad_eq_iff` states the resulting characterization: a load assignment
is realized over `Y` exactly when it is constant on the components of `Y`, positive, and within
the bound.

## Empirical status

None.  The bodies construct finite equivalence relations and count their classes, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.CompressionLoadAchievability

open Coalescent Finset MarkovCompressions
open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ## Class minima -/

/-- Two individuals have the same class minimum exactly when they are related. -/
theorem classMinOf_eq_classMinOf_iff (η : ER n) (x y : Fin n) :
    classMinOf η x = classMinOf η y ↔ η.r x y := by
  constructor
  · intro h
    have hx : η.r x (classMinOf η y) := h ▸ classMinOf_rel η x
    exact η.iseqv.trans hx (η.iseqv.symm (classMinOf_rel η y))
  · intro h
    exact le_antisymm (classMinOf_le (η.iseqv.trans h (classMinOf_rel η y)))
      (classMinOf_le (η.iseqv.trans (η.iseqv.symm h) (classMinOf_rel η x)))

/-- A class minimum is the minimum of its own class. -/
theorem classMinOf_eq_self_of_mem {η : ER n} {m : Fin n} (hm : m ∈ classMinima η) :
    classMinOf η m = m :=
  le_antisymm (classMinOf_le (η.iseqv.refl m)) (mem_classMinima.mp hm _ (classMinOf_rel η m))

/-- **The graph states of a report component are counted by its fiber minima.** -/
theorem card_filter_classMinima_eq_componentWidth {s : Fin n → Fin n} {Y : ER n}
    (hY : graphKer s ≤ Y) (x : Fin n) :
    #((univ.filter fun z ↦ Y.r z x).filter fun z ↦ z ∈ classMinima (graphKer s))
      = componentWidth s Y x := by
  have hobsY : observed s Y = Y := sup_eq_left.mpr hY
  have hinj : Set.InjOn s
      ↑((univ.filter fun z ↦ Y.r z x).filter fun z ↦ z ∈ classMinima (graphKer s)) := by
    intro a ha b hb hab
    have ha' := (mem_filter.mp (mem_coe.mp ha)).2
    have hb' := (mem_filter.mp (mem_coe.mp hb)).2
    have hrel : (graphKer s).r a b := graphKer_rel_iff.mpr hab
    exact le_antisymm (mem_classMinima.mp ha' b hrel)
      (mem_classMinima.mp hb' a ((graphKer s).iseqv.symm hrel))
  rw [← card_image_of_injOn hinj, componentWidth, hobsY]
  congr 1
  ext t
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨z, ⟨hz, -⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨classMinOf (graphKer s) z, ⟨?_, classMinOf_mem_classMinima _ z⟩, ?_⟩
    · exact Y.iseqv.trans (Y.iseqv.symm (hY (classMinOf_rel (graphKer s) z))) hz
    · exact (graphKer_rel_iff.mp (classMinOf_rel (graphKer s) z)).symm

/-! ## The construction -/

/-- **Every load assignment within the bound is attained.**  If `Y` is a report above the
interface kernel and `L` assigns to each component a load between `1` and `|C| - w_C + 1`, some
coalescent state reports `Y` and hides exactly `L` in every component. -/
theorem exists_observed_eq_hiddenLoad_eq {s : Fin n → Fin n} {Y : ER n} (hY : graphKer s ≤ Y)
    (L : Fin n → ℕ) (hconst : ∀ x y, Y.r x y → L x = L y) (hpos : ∀ x, 1 ≤ L x)
    (hbound : ∀ x, L x + componentWidth s Y x ≤ componentSize s Y x + 1) :
    ∃ ξ : ER n, observed s ξ = Y ∧
      ∀ x, hiddenLoad s ξ (Quotient.mk (observed s ξ) x) = L x := by
  have hobsY : observed s Y = Y := sup_eq_left.mpr hY
  have hchoice : ∀ m : Fin n, ∃ t ⊆ (univ.filter fun z ↦ Y.r z m).filter
      (fun z ↦ ¬ z ∈ classMinima (graphKer s)), #t = L m - 1 := by
    intro m
    refine exists_subset_card_eq ?_
    have hsplit := filter_card_add_filter_neg_card_eq_card (s := univ.filter fun z ↦ Y.r z m)
      (fun z ↦ z ∈ classMinima (graphKer s))
    have hwidth := card_filter_classMinima_eq_componentWidth hY m
    have hb := hbound m
    rw [componentSize, hobsY] at hb
    omega
  choose T hTsub hTcard using hchoice
  let S : Finset (Fin n) := (classMinima Y).biUnion T
  let f : Fin n → Fin n ⊕ Fin n := fun z ↦ if z ∈ S then Sum.inl z else Sum.inr (classMinOf Y z)
  have hSR : ∀ z ∈ S, z ∉ classMinima (graphKer s) := by
    intro z hz
    obtain ⟨m, -, hzm⟩ := mem_biUnion.mp hz
    exact (mem_filter.mp (hTsub m hzm)).2
  have hrS : ∀ z, classMinOf (graphKer s) z ∉ S := fun z hz ↦
    hSR _ hz (classMinOf_mem_classMinima _ z)
  have hle : Setoid.ker f ≤ Y := by
    intro a b hab
    have hab' : f a = f b := hab
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
      simp only [f, ha, hb, ↓reduceIte, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hab'
    · rw [hab']
    · exact (classMinOf_eq_classMinOf_iff Y a b).mp hab'
  have hobs : observed s (Setoid.ker f) = Y := by
    refine le_antisymm (sup_le hle hY) fun a b hab ↦ ?_
    have hra := classMinOf_rel (graphKer s) a
    have hrb := classMinOf_rel (graphKer s) b
    have hmid : (Setoid.ker f).r (classMinOf (graphKer s) a) (classMinOf (graphKer s) b) := by
      show f _ = f _
      simp only [f, hrS a, hrS b, ↓reduceIte, Sum.inr.injEq]
      exact (classMinOf_eq_classMinOf_iff Y _ _).mpr
        (Y.iseqv.trans (Y.iseqv.symm (hY hra)) (Y.iseqv.trans hab (hY hrb)))
    have h1 : (observed s (Setoid.ker f)).r a (classMinOf (graphKer s) a) :=
      (le_sup_right : graphKer s ≤ Setoid.ker f ⊔ graphKer s) hra
    have h2 : (observed s (Setoid.ker f)).r (classMinOf (graphKer s) a)
        (classMinOf (graphKer s) b) :=
      (le_sup_left : Setoid.ker f ≤ Setoid.ker f ⊔ graphKer s) hmid
    have h3 : (observed s (Setoid.ker f)).r (classMinOf (graphKer s) b) b :=
      (observed s (Setoid.ker f)).iseqv.symm
        ((le_sup_right : graphKer s ≤ Setoid.ker f ⊔ graphKer s) hrb)
    exact (observed s (Setoid.ker f)).iseqv.trans h1
      ((observed s (Setoid.ker f)).iseqv.trans h2 h3)
  refine ⟨Setoid.ker f, hobs, fun x ↦ ?_⟩
  have hTx : ∀ z, z ∈ S ∧ Y.r z x ↔ z ∈ T (classMinOf Y x) := by
    intro z
    constructor
    · rintro ⟨hzS, hzx⟩
      obtain ⟨m, hm, hzm⟩ := mem_biUnion.mp hzS
      have hzm' : Y.r z m := (mem_filter.mp (mem_filter.mp (hTsub m hzm)).1).2
      have hmx : m = classMinOf Y x := by
        rw [← classMinOf_eq_self_of_mem hm]
        exact (classMinOf_eq_classMinOf_iff Y m x).mpr (Y.iseqv.trans (Y.iseqv.symm hzm') hzx)
      rwa [← hmx]
    · intro hzT
      refine ⟨mem_biUnion.mpr ⟨classMinOf Y x, classMinOf_mem_classMinima Y x, hzT⟩, ?_⟩
      have hz : Y.r z (classMinOf Y x) := (mem_filter.mp (mem_filter.mp (hTsub _ hzT)).1).2
      exact Y.iseqv.trans hz (Y.iseqv.symm (classMinOf_rel Y x))
  have hblocks : hiddenBlocks s (Setoid.ker f) (Quotient.mk (observed s (Setoid.ker f)) x)
      = (insert (classMinOf (graphKer s) x) (T (classMinOf Y x))).image
          (Quotient.mk (Setoid.ker f)) := by
    ext block
    obtain ⟨z, rfl⟩ := quotient_mk_surjective (Setoid.ker f) block
    rw [mk_mem_hiddenBlocks_iff, hobs, mem_image]
    constructor
    · intro hz
      by_cases hzS : z ∈ S
      · exact ⟨z, mem_insert_of_mem ((hTx z).mp ⟨hzS, hz⟩), rfl⟩
      · refine ⟨classMinOf (graphKer s) x, mem_insert_self _ _, Quotient.sound ?_⟩
        show f _ = f _
        simp only [f, hrS x, hzS, ↓reduceIte, Sum.inr.injEq]
        exact (classMinOf_eq_classMinOf_iff Y _ _).mpr
          (Y.iseqv.trans (Y.iseqv.symm (hY (classMinOf_rel _ x))) (Y.iseqv.symm hz))
    · rintro ⟨w, hw, hwz⟩
      have hwz' : Y.r w z := hle (Quotient.exact hwz)
      have hwx : Y.r w x := by
        rcases mem_insert.mp hw with rfl | hwT
        · exact Y.iseqv.symm (hY (classMinOf_rel _ x))
        · exact ((hTx w).mpr hwT).2
      exact Y.iseqv.trans (Y.iseqv.symm hwz') hwx
  have hinj : Set.InjOn (Quotient.mk (Setoid.ker f))
      ↑(insert (classMinOf (graphKer s) x) (T (classMinOf Y x))) := by
    intro a ha b hb hab
    have hab' : f a = f b := Quotient.exact hab
    have hnS : ∀ c ∈ insert (classMinOf (graphKer s) x) (T (classMinOf Y x)), c ∉ S →
        c = classMinOf (graphKer s) x := by
      intro c hc hcS
      rcases mem_insert.mp hc with h | h
      · exact h
      · exact absurd ((hTx c).mpr h).1 hcS
    by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S <;>
      simp only [f, haS, hbS, ↓reduceIte, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hab'
    · exact hab'
    · rw [hnS a (mem_coe.mp ha) haS, hnS b (mem_coe.mp hb) hbS]
  have hnot : classMinOf (graphKer s) x ∉ T (classMinOf Y x) := fun h ↦ hrS x ((hTx _).mpr h).1
  rw [hiddenLoad, hblocks, card_image_of_injOn hinj, card_insert_of_notMem hnot, hTcard,
    hconst _ _ (Y.iseqv.symm (classMinOf_rel Y x))]
  have := hpos x
  omega

/-- **The attainable loads are exactly the load range.**  Over a report `Y` above the interface
kernel, a load assignment is realized by some coalescent state exactly when it is constant on the
components of `Y`, positive, and within `|C| - w_C + 1`. -/
theorem exists_observed_eq_hiddenLoad_eq_iff {s : Fin n → Fin n} {Y : ER n}
    (hY : graphKer s ≤ Y) (L : Fin n → ℕ) :
    (∃ ξ : ER n, observed s ξ = Y ∧ ∀ x, hiddenLoad s ξ (Quotient.mk (observed s ξ) x) = L x) ↔
      (∀ x y, Y.r x y → L x = L y) ∧ (∀ x, 1 ≤ L x) ∧
        ∀ x, L x + componentWidth s Y x ≤ componentSize s Y x + 1 := by
  constructor
  · rintro ⟨ξ, hobs, hload⟩
    have hobsY : observed s Y = Y := sup_eq_left.mpr hY
    refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
    · have hxy' : (observed s ξ).r x y := by
        rw [hobs]
        exact hxy
      rw [← hload x, ← hload y, Quotient.sound hxy']
    · rw [← hload x]
      exact hiddenLoad_pos s ξ _
    · have hb := hiddenLoad_add_componentWidth_le s ξ x
      have hsize : componentSize s ξ x = componentSize s Y x := by
        rw [componentSize, componentSize, hobs, hobsY]
      have hwidth : componentWidth s ξ x = componentWidth s Y x := by
        rw [componentWidth, componentWidth, hobs, hobsY]
      rwa [hload x, hsize, hwidth] at hb
  · rintro ⟨hconst, hpos, hbound⟩
    exact exists_observed_eq_hiddenLoad_eq hY L hconst hpos hbound

end

end Descent.Pangenome.GraphCoalescent.CompressionLoadAchievability
