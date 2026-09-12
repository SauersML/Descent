/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLumpability
import Descent.Pangenome.GraphCoalescent.LeadingCoefficient
import Descent.Pangenome.GraphCoalescent.ShortTimeConnectionLaw

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Theorem E, (E2): lumping the minimal connecting histories

`ShortTimeConnectionLaw` expands the probability that the report is connected at time `t` as
`minimalHistoryCount s t^{w-1}/(w-1)! + O(t^w)`, where `minimalHistoryCount s` counts the chains of
`w - 1` visible covers from the singletons to a connected report. The note's constant is `H_w(c)`,
defined by the merger recursion `H_w(c) = Σ_{i<j} c_i c_j H_{w-1}(c^{(ij)})` over the fiber sizes;
in the corpus it is `historyWeight` of `LeadingCoefficient`. This module builds the lumping that
identifies the two.

## What is proved

* `historyWeight_congr`: the history sum reads the sizes on its fiber set only.
* `visibleTarget_comm`: the hidden state a visible merger reaches is symmetric in the two
  components it joins.
* Representative sets. `IsRepresentativeSet s ξ T` says that `T` holds one individual from each
  report component of `ξ`; `representatives s ξ` is one (`representatives_isRepresentativeSet`),
  and every such set counts the report components (`IsRepresentativeSet.card_eq`). A visible
  merger of the components of `i` and `j` leaves the representative set `T.erase j`
  (`IsRepresentativeSet.erase`), which is the fused fiber of the recursion for `H_w`.
* `connectingCount s k ξ` counts the chains of `k` visible covers from `ξ` to a connected report,
  `minimalHistoryCount s` is its value at the singletons
  (`minimalHistoryCount_eq_connectingCount`), a connected report has one chain of length zero
  (`connectingCount_zero`), and a chain of length `k + 1` is a visible cover followed by a chain
  of length `k` (`connectingCount_succ`).
* Visible covers by representative pairs. Every visible cover sits at the visible target of two
  distinct representatives (`exists_visibleTarget_of_visible`), and that target determines the
  pair up to order (`visibleTarget_eq_iff`).

Not yet here: counting the visible covers into each target by the loads, and the induction that
turns `connectingCount_succ` into the recursion of `historyWeight`.

## Empirical status

None. The bodies here are counts of chains of covers of equivalence relations on a finite set and
the algebra of a finite recursion, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.MinimalHistoryLumping

open Coalescent Finset ShortTimeConnectionLaw
open scoped Classical

noncomputable section

/-! ### The history sum on its fiber set -/

/-- **The history sum reads the sizes on its fiber set only.** Two size functions that agree on
the fibers give the same history sum. -/
theorem historyWeight_congr {ι : Type*} [DecidableEq ι] :
    ∀ (w : ℕ) (T : Finset ι) (c c' : ι → ℕ), (∀ i ∈ T, c i = c' i) →
      historyWeight w T c = historyWeight w T c'
  | 0, T, c, c', _ => by rw [historyWeight_zero, historyWeight_zero]
  | w + 1, T, c, c', h => by
      rw [historyWeight_succ, historyWeight_succ]
      congr 1
      refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
      have hjT : j ∈ T := mem_of_mem_erase hj
      have hupdate : ∀ z ∈ T.erase j, Function.update c i (c i + c j - 1) z =
          Function.update c' i (c' i + c' j - 1) z := by
        intro z hz
        by_cases hzi : z = i
        · rw [hzi, Function.update_self, Function.update_self, h i hi, h j hjT]
        · rw [Function.update_of_ne hzi, Function.update_of_ne hzi, h z (mem_of_mem_erase hz)]
      rw [historyWeight_congr w (T.erase j) _ _ hupdate, h i hi, h j hjT]

/-! ### Visible targets -/

/-- **A visible merger is symmetric in the components it joins.** -/
theorem visibleTarget_comm {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) {x y : Fin n}
    (hxy : ¬(observed s ξ).r x y) :
    visibleTarget (hiddenState s ξ) x y = visibleTarget (hiddenState s ξ) y x := by
  have hCD : Quotient.mk (observed s ξ) x ≠ Quotient.mk (observed s ξ) y :=
    fun hq ↦ hxy (Quotient.exact hq)
  refine Prod.ext (merge_comm _ hCD) (funext fun z ↦ ?_)
  show (if (observed s ξ).r x z ∨ (observed s ξ).r y z then
      hiddenLoad s ξ (Quotient.mk (observed s ξ) x) +
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) - 1
      else hiddenLoad s ξ (Quotient.mk (observed s ξ) z)) =
    if (observed s ξ).r y z ∨ (observed s ξ).r x z then
      hiddenLoad s ξ (Quotient.mk (observed s ξ) y) +
        hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1
      else hiddenLoad s ξ (Quotient.mk (observed s ξ) z)
  by_cases hz : (observed s ξ).r x z ∨ (observed s ξ).r y z
  · rw [if_pos hz, if_pos hz.symm, add_comm]
  · have hz' : ¬((observed s ξ).r y z ∨ (observed s ξ).r x z) := fun hboth ↦ hz hboth.symm
    rw [if_neg hz, if_neg hz']

/-! ### Representative sets of a report -/

/-- **A representative set of the report of `ξ`**: individuals, one from each report component.
Every individual is reported together with some member, and no two members are reported
together. -/
def IsRepresentativeSet {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (T : Finset (Fin n)) : Prop :=
  (∀ z, ∃ i ∈ T, (observed s ξ).r i z) ∧ ∀ i ∈ T, ∀ j ∈ T, (observed s ξ).r i j → i = j

/-- The chosen individual of every report component. -/
def representatives {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) : Finset (Fin n) :=
  univ.image fun C : Quotient (observed s ξ) ↦ C.out

/-- **The chosen individuals form a representative set.** -/
theorem representatives_isRepresentativeSet {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    IsRepresentativeSet s ξ (representatives s ξ) := by
  refine ⟨fun z ↦ ⟨(Quotient.mk (observed s ξ) z).out, mem_image_of_mem _ (mem_univ _),
    Quotient.exact (Quotient.out_eq (Quotient.mk (observed s ξ) z))⟩, fun i hi j hj hij ↦ ?_⟩
  obtain ⟨C, -, rfl⟩ := mem_image.mp hi
  obtain ⟨D, -, rfl⟩ := mem_image.mp hj
  have hCD : C = D := by
    rw [← Quotient.out_eq C, ← Quotient.out_eq D]
    exact Quotient.sound hij
  rw [hCD]

/-- **A representative set counts the report components.** -/
theorem IsRepresentativeSet.card_eq {n : ℕ} {s : Fin n → Fin n} {ξ : ER n} {T : Finset (Fin n)}
    (hT : IsRepresentativeSet s ξ T) : #T = blocks (observed s ξ) := by
  rw [blocks, Nat.card_eq_fintype_card, ← card_univ]
  refine card_bij (fun i _ ↦ Quotient.mk (observed s ξ) i) (fun _ _ ↦ mem_univ _)
    (fun i hi j hj hij ↦ hT.2 i hi j hj (Quotient.exact hij)) fun C _ ↦ ?_
  obtain ⟨z, rfl⟩ := quotient_mk_surjective (observed s ξ) C
  obtain ⟨i, hi, hiz⟩ := hT.1 z
  exact ⟨i, hi, Quotient.sound hiz⟩

/-- **A visible merger removes one representative.** If the report of `η` merges the report
components of two distinct members `i` and `j` of a representative set of `ξ`, then removing `j`
leaves a representative set of `η`. -/
theorem IsRepresentativeSet.erase {n : ℕ} {s : Fin n → Fin n} {ξ η : ER n} {T : Finset (Fin n)}
    (hT : IsRepresentativeSet s ξ T) {i j : Fin n} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j)
    (hreport : observed s η =
      merge (observed s ξ) (Quotient.mk (observed s ξ) i) (Quotient.mk (observed s ξ) j)) :
    IsRepresentativeSet s η (T.erase j) := by
  have hnot : ¬(observed s ξ).r i j := fun hrel ↦ hij (hT.2 i hi j hj hrel)
  have hrel : ∀ u v, (observed s η).r u v ↔ (observed s ξ).r u v ∨
      ((observed s ξ).r u i ∧ (observed s ξ).r v j) ∨
        ((observed s ξ).r u j ∧ (observed s ξ).r v i) := fun u v ↦ by
    rw [hreport]
    exact merge_rel_iff_of_not_rel _ hnot u v
  refine ⟨fun z ↦ ?_, fun t ht t' ht' htt' ↦ ?_⟩
  · obtain ⟨t, ht, htz⟩ := hT.1 z
    by_cases htj : t = j
    · subst htj
      exact ⟨i, mem_erase.mpr ⟨hij, hi⟩,
        (hrel i z).mpr (Or.inr (Or.inl ⟨(observed s ξ).iseqv.refl i,
          (observed s ξ).iseqv.symm htz⟩))⟩
    · exact ⟨t, mem_erase.mpr ⟨htj, ht⟩, (hrel t z).mpr (Or.inl htz)⟩
  · have htT := mem_of_mem_erase ht
    have ht'T := mem_of_mem_erase ht'
    rcases (hrel t t').mp htt' with h | ⟨_, h⟩ | ⟨h, _⟩
    · exact hT.2 t htT t' ht'T h
    · exact absurd (hT.2 t' ht'T j hj h) (ne_of_mem_erase ht')
    · exact absurd (hT.2 t htT j hj h) (ne_of_mem_erase ht)

/-! ### Minimal histories counted from any state -/

/-- **The minimal connecting histories of length `k` from `ξ`**: the chains of `k` visible covers
from `ξ` to a connected report. -/
def connectingCount {n : ℕ} (s : Fin n → Fin n) (k : ℕ) (ξ : ER n) : ℝ :=
  ∑ η ∈ (connectedStates s).filter (fun η ↦ blocks (observed s η) = 1),
    (descentMatrix (kingmanMatrix n) (fun ζ ↦ blocks (observed s ζ)) ^ k) ξ η

/-- The minimal connecting histories of the note are those from the singletons. -/
theorem minimalHistoryCount_eq_connectingCount {n : ℕ} (s : Fin n → Fin n) :
    minimalHistoryCount s = connectingCount s (Linkage.width s - 1) ⊥ :=
  rfl

/-- **A connected report has one history of length zero.** -/
theorem connectingCount_zero {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hξ : blocks (observed s ξ) = 1) : connectingCount s 0 ξ = 1 := by
  have hmem : ξ ∈ (connectedStates s).filter (fun η ↦ blocks (observed s η) = 1) :=
    mem_filter.mpr ⟨(mem_connectedStates s ξ).mpr hξ.le, hξ⟩
  rw [connectingCount, pow_zero]
  simp only [Matrix.one_apply]
  rw [sum_ite_eq, if_pos hmem]

/-- **Minimal histories by their first step.** A history of length `k + 1` from `ξ` is a visible
cover of `ξ` followed by a history of length `k`. -/
theorem connectingCount_succ {n : ℕ} (s : Fin n → Fin n) (k : ℕ) (ξ : ER n) :
    connectingCount s (k + 1) ξ =
      ∑ η ∈ univ.filter (fun η ↦
          Covers ξ η ∧ blocks (observed s η) + 1 = blocks (observed s ξ)),
        connectingCount s k η := by
  rw [sum_filter]
  unfold connectingCount
  rw [pow_succ']
  simp only [Matrix.mul_apply]
  rw [sum_comm]
  refine sum_congr rfl fun η _ ↦ ?_
  rw [← mul_sum, descentMatrix_kingmanMatrix_apply, ite_mul, one_mul, zero_mul]

/-! ### Visible covers by representative pairs -/

/-- **Every visible cover sits at the visible target of two representatives.** -/
theorem exists_visibleTarget_of_visible {n : ℕ} {s : Fin n → Fin n} {ξ η : ER n}
    {T : Finset (Fin n)} (hT : IsRepresentativeSet s ξ T) (hcovers : Covers ξ η)
    (hlevel : blocks (observed s η) + 1 = blocks (observed s ξ)) :
    ∃ i ∈ T, ∃ j ∈ T, i ≠ j ∧ hiddenState s η = visibleTarget (hiddenState s ξ) i j := by
  rcases hiddenState_of_covers s hcovers with ⟨u, hu⟩ | ⟨u, v, huv, hstate⟩
  · exfalso
    have hreport : observed s η = observed s ξ := congrArg Prod.fst hu
    rw [hreport] at hlevel
    omega
  · obtain ⟨i, hi, hiu⟩ := hT.1 u
    obtain ⟨j, hj, hjv⟩ := hT.1 v
    have hij : i ≠ j := fun hij ↦ huv ((observed s ξ).iseqv.trans
      ((observed s ξ).iseqv.symm hiu) (hij ▸ hjv))
    exact ⟨i, hi, j, hj, hij, hstate.trans (visibleTarget_eq_of_rel s ξ hiu hjv).symm⟩

/-- **The visible target determines the pair.** If `η` sits at the visible target of distinct
representatives `i` and `j`, it sits at the visible target of distinct representatives `i'` and
`j'` exactly when `(i', j')` is `(i, j)` or `(j, i)`. -/
theorem visibleTarget_eq_iff {n : ℕ} {s : Fin n → Fin n} {ξ η : ER n} {T : Finset (Fin n)}
    (hT : IsRepresentativeSet s ξ T) {i j i' j' : Fin n} (hi : i ∈ T) (hj : j ∈ T)
    (hi' : i' ∈ T) (hj' : j' ∈ T) (hij : i ≠ j) (hij' : i' ≠ j')
    (hstate : hiddenState s η = visibleTarget (hiddenState s ξ) i j) :
    hiddenState s η = visibleTarget (hiddenState s ξ) i' j' ↔
      (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i) := by
  have hnot : ¬(observed s ξ).r i j := fun hrel ↦ hij (hT.2 i hi j hj hrel)
  constructor
  · intro hstate'
    have hCD : Quotient.mk (observed s ξ) i ≠ Quotient.mk (observed s ξ) j :=
      fun hq ↦ hij (hT.2 i hi j hj (Quotient.exact hq))
    have hCD' : Quotient.mk (observed s ξ) i' ≠ Quotient.mk (observed s ξ) j' :=
      fun hq ↦ hij' (hT.2 i' hi' j' hj' (Quotient.exact hq))
    have hmerge : merge (observed s ξ) (Quotient.mk (observed s ξ) i)
        (Quotient.mk (observed s ξ) j) =
          merge (observed s ξ) (Quotient.mk (observed s ξ) i') (Quotient.mk (observed s ξ) j') :=
      (congrArg Prod.fst hstate).symm.trans (congrArg Prod.fst hstate')
    have hpair := (merge_eq_merge_iff _ hCD hCD').mp hmerge
    have hi'mem : Quotient.mk (observed s ξ) i' ∈
        ({Quotient.mk (observed s ξ) i, Quotient.mk (observed s ξ) j} : Finset _) :=
      hpair ▸ mem_insert_self _ _
    have hj'mem : Quotient.mk (observed s ξ) j' ∈
        ({Quotient.mk (observed s ξ) i, Quotient.mk (observed s ξ) j} : Finset _) :=
      hpair ▸ mem_insert_of_mem (mem_singleton_self _)
    simp only [mem_insert, mem_singleton] at hi'mem hj'mem
    have hrep : ∀ {u v : Fin n}, u ∈ T → v ∈ T →
        Quotient.mk (observed s ξ) u = Quotient.mk (observed s ξ) v → u = v :=
      fun hu hv hq ↦ hT.2 _ hu _ hv (Quotient.exact hq)
    rcases hi'mem with h1 | h1 <;> rcases hj'mem with h2 | h2
    · exact absurd ((hrep hi' hi h1).trans (hrep hj' hi h2).symm) hij'
    · exact Or.inl ⟨hrep hi' hi h1, hrep hj' hj h2⟩
    · exact Or.inr ⟨hrep hi' hj h1, hrep hj' hi h2⟩
    · exact absurd ((hrep hi' hj h1).trans (hrep hj' hj h2).symm) hij'
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hstate
    · exact hstate.trans (visibleTarget_comm s ξ hnot)

end

end Descent.Pangenome.GraphCoalescent.MinimalHistoryLumping
