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
in the corpus it is `historyWeight` of `LeadingCoefficient`. This module lumps the labeled
histories into that recursion and states (E2) with the note's constant.

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
  pair up to order (`visibleTarget_eq_iff`), so each visible cover is counted by exactly two
  ordered pairs (`sum_pairs_ite_visibleTarget`, `two_mul_sum_visible`). The covers into the
  visible target of `i` and `j` number `L_i L_j` (`card_filter_visibleTarget`,
  `sum_filter_visibleTarget`).
* **The lumping.** `connectingCount_eq_historyWeight`: from a state whose report has `k + 1`
  components, the minimal connecting histories number `historyWeight k T L` of any representative
  set `T` with the loads `L`. At the singletons the loads are the fiber sizes:
  `minimalHistoryCount_eq_historyWeight`, and with `historyWeight_eq_prod_historyFactor`,
  `minimalHistoryCount_eq_prod_historyFactor`, `H_w(c) = (∏_i c_i) g_w(n)`
  (`sum_fiberCard_representatives` gives the panel size `n`).
* **(E2) with the note's constant.** `reportConnectedProbability_sub_note_isBigO`:
  `Pr(report connected at t) = (∏_i c_i) (2n - w)! / (2^{w-2} (2n - 2w + 2)!) t^{w-1} + O(t^w)`.

Scope, as in `ShortTimeConnectionLaw`: the probability is the weight of the connected reports in
the matrix exponential of Kingman's generator; the continuous-time chain as a process is not
constructed.

## Empirical status

None. The bodies here are counts of chains of covers of equivalence relations on a finite set and
the algebra of a finite recursion, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.MinimalHistoryLumping

open Coalescent Finset ShortTimeConnectionLaw
open scoped Classical Nat

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

/-- The fibers of the chosen individuals at the singletons cover the panel. -/
theorem sum_fiberCard_representatives {n : ℕ} (s : Fin n → Fin n) :
    ∑ i ∈ representatives s ⊥, Linkage.fiberCard s i = n := by
  have hinj : Set.InjOn (fun C : Quotient (observed s ⊥) ↦ C.out)
      (↑(univ : Finset (Quotient (observed s ⊥))) : Set (Quotient (observed s ⊥))) :=
    fun C _ D _ hCD ↦ by
      rw [← Quotient.out_eq C, ← Quotient.out_eq D]
      exact congrArg _ hCD
  have hload : ∀ C : Quotient (observed s ⊥), Linkage.fiberCard s C.out = hiddenLoad s ⊥ C :=
    fun C ↦ by rw [← hiddenLoad_bot s C.out, Quotient.out_eq]
  rw [representatives, sum_image hinj, sum_congr rfl fun C _ ↦ hload C, sum_hiddenLoad]
  exact blocks_bot n

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

/-! ### Counting the visible covers -/

/-- **The covers into one visible target number the product of the loads.** -/
theorem card_filter_visibleTarget {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) {x y : Fin n}
    (hxy : ¬(observed s ξ).r x y) :
    #(univ.filter fun η ↦ Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) x y) =
      hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) := by
  rw [← card_covers_visibleTarget s ξ hxy]
  exact (Nat.subtype_card (univ.filter fun η ↦
    Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) x y)
      fun η ↦ mem_filter.trans (and_iff_right (mem_univ η))).symm

/-- **A function constant on the covers into a visible target** sums over them to the product of
the loads times its value. -/
theorem sum_filter_visibleTarget {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) {x y : Fin n}
    (hxy : ¬(observed s ξ).r x y) (f : ER n → ℝ) {value : ℝ}
    (hvalue : ∀ η, Covers ξ η → hiddenState s η = visibleTarget (hiddenState s ξ) x y →
      f η = value) :
    ∑ η ∈ univ.filter (fun η ↦
        Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) x y), f η =
      (hiddenLoad s ξ (Quotient.mk (observed s ξ) x) : ℝ) *
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) * value := by
  have hconst : ∀ η ∈ univ.filter (fun η ↦
      Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) x y), f η = value :=
    fun η hη ↦ hvalue η (mem_filter.mp hη).2.1 (mem_filter.mp hη).2.2
  rw [sum_congr rfl hconst, sum_const, card_filter_visibleTarget s ξ hxy, nsmul_eq_mul,
    Nat.cast_mul]

/-- **Each visible cover is counted by two ordered pairs of representatives**, and every other
state by none. -/
theorem sum_pairs_ite_visibleTarget {n : ℕ} {s : Fin n → Fin n} {ξ : ER n} {T : Finset (Fin n)}
    (hT : IsRepresentativeSet s ξ T) (η : ER n) (value : ℝ) :
    ∑ i ∈ T, ∑ j ∈ T.erase i,
        (if Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) i j then value
          else 0) =
      if Covers ξ η ∧ blocks (observed s η) + 1 = blocks (observed s ξ) then 2 * value
        else 0 := by
  by_cases hvisible : Covers ξ η ∧ blocks (observed s η) + 1 = blocks (observed s ξ)
  · rw [if_pos hvisible]
    obtain ⟨i₀, hi₀, j₀, hj₀, hij₀, hstate⟩ :=
      exists_visibleTarget_of_visible hT hvisible.1 hvisible.2
    have hpair : ∀ i ∈ T, ∀ j ∈ T.erase i,
        (Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) i j) ↔
          (i = i₀ ∧ j = j₀) ∨ (i = j₀ ∧ j = i₀) := by
      intro i hi j hj
      rw [and_iff_right hvisible.1]
      exact visibleTarget_eq_iff hT hi₀ hj₀ hi (mem_of_mem_erase hj) hij₀
        (ne_of_mem_erase hj).symm hstate
    have hj₀mem : j₀ ∈ T.erase i₀ := mem_erase.mpr ⟨hij₀.symm, hj₀⟩
    have hi₀mem : i₀ ∈ T.erase j₀ := mem_erase.mpr ⟨hij₀, hi₀⟩
    have hrow₀ : ∀ j ∈ T.erase i₀, j ≠ j₀ →
        (if Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) i₀ j then value
          else 0) = 0 := by
      intro j hj hjj₀
      refine if_neg fun hP ↦ ?_
      rcases (hpair i₀ hi₀ j hj).mp hP with ⟨_, h⟩ | ⟨h, _⟩
      · exact hjj₀ h
      · exact hij₀ h
    have hrow₁ : ∀ j ∈ T.erase j₀, j ≠ i₀ →
        (if Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) j₀ j then value
          else 0) = 0 := by
      intro j hj hji₀
      refine if_neg fun hP ↦ ?_
      rcases (hpair j₀ hj₀ j hj).mp hP with ⟨h, _⟩ | ⟨_, h⟩
      · exact hij₀ h.symm
      · exact hji₀ h
    have houter : ∀ i ∈ T, i ≠ i₀ ∧ i ≠ j₀ → ∑ j ∈ T.erase i,
        (if Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) i j then value
          else 0) = 0 := by
      intro i hi hne
      refine sum_eq_zero fun j hj ↦ if_neg fun hP ↦ ?_
      rcases (hpair i hi j hj).mp hP with ⟨h, _⟩ | ⟨h, _⟩
      · exact hne.1 h
      · exact hne.2 h
    rw [sum_eq_add_of_mem i₀ j₀ hi₀ hj₀ hij₀ houter, sum_eq_single_of_mem j₀ hj₀mem hrow₀,
      sum_eq_single_of_mem i₀ hi₀mem hrow₁,
      if_pos ((hpair i₀ hi₀ j₀ hj₀mem).mpr (Or.inl ⟨rfl, rfl⟩)),
      if_pos ((hpair j₀ hj₀ i₀ hi₀mem).mpr (Or.inr ⟨rfl, rfl⟩))]
    ring
  · rw [if_neg hvisible]
    refine sum_eq_zero fun i hi ↦ sum_eq_zero fun j hj ↦ if_neg fun hP ↦ hvisible ?_
    obtain ⟨hcovers, hstate⟩ := hP
    have hij : i ≠ j := (ne_of_mem_erase hj).symm
    have hnot : ¬(observed s ξ).r i j := fun hrel ↦ hij (hT.2 i hi j (mem_of_mem_erase hj) hrel)
    have hCD : Quotient.mk (observed s ξ) i ≠ Quotient.mk (observed s ξ) j :=
      fun hq ↦ hnot (Quotient.exact hq)
    have hreport : observed s η = merge (observed s ξ) (Quotient.mk (observed s ξ) i)
        (Quotient.mk (observed s ξ) j) := congrArg Prod.fst hstate
    refine ⟨hcovers, ?_⟩
    rw [hreport]
    exact (merge_covers _ hCD).2

/-- **Visible covers by representative pairs.** Twice the sum of a function over the visible covers
of `ξ` is its sum over the covers into the visible targets of the ordered pairs of distinct
representatives. -/
theorem two_mul_sum_visible {n : ℕ} {s : Fin n → Fin n} {ξ : ER n} {T : Finset (Fin n)}
    (hT : IsRepresentativeSet s ξ T) (f : ER n → ℝ) :
    2 * ∑ η ∈ univ.filter (fun η ↦
        Covers ξ η ∧ blocks (observed s η) + 1 = blocks (observed s ξ)), f η =
      ∑ i ∈ T, ∑ j ∈ T.erase i, ∑ η ∈ univ.filter (fun η ↦
        Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) i j), f η := by
  have hswap : ∑ i ∈ T, ∑ j ∈ T.erase i, ∑ η, (if Covers ξ η ∧
      hiddenState s η = visibleTarget (hiddenState s ξ) i j then f η else 0) =
        ∑ η, ∑ i ∈ T, ∑ j ∈ T.erase i, (if Covers ξ η ∧
          hiddenState s η = visibleTarget (hiddenState s ξ) i j then f η else 0) :=
    (sum_congr rfl fun i _ ↦ sum_comm).trans sum_comm
  simp only [sum_filter]
  rw [mul_sum, hswap]
  refine sum_congr rfl fun η _ ↦ ?_
  rw [sum_pairs_ite_visibleTarget hT η (f η), mul_ite, mul_zero]

/-! ### The lumping -/

/-- **Theorem E, the lumping of the minimal histories.** From a state whose report has `k + 1`
components, the chains of `k` visible covers to a connected report number the history sum of the
report components with their loads, read at any representative set. Assumes: `T` is a
representative set of the report of `ξ` with `k + 1` members. -/
theorem connectingCount_eq_historyWeight {n : ℕ} (s : Fin n → Fin n) :
    ∀ (k : ℕ) (ξ : ER n) (T : Finset (Fin n)), IsRepresentativeSet s ξ T → #T = k + 1 →
      connectingCount s k ξ = historyWeight k T (hiddenState s ξ).2
  | 0, ξ, T, hT, hcard => by
      rw [connectingCount_zero s (ξ := ξ) (by rw [← hT.card_eq, hcard]), historyWeight_zero,
        Rat.cast_one]
  | k + 1, ξ, T, hT, hcard => by
      have hstep : ∀ i ∈ T, ∀ j ∈ T.erase i, ∀ η, Covers ξ η →
          hiddenState s η = visibleTarget (hiddenState s ξ) i j →
            connectingCount s k η = historyWeight k (T.erase j)
              (Function.update (hiddenState s ξ).2 i
                ((hiddenState s ξ).2 i + (hiddenState s ξ).2 j - 1)) := by
        intro i hi j hj η _ hstate
        have hjT : j ∈ T := mem_of_mem_erase hj
        have hij : i ≠ j := (ne_of_mem_erase hj).symm
        have hT' := hT.erase hi hjT hij (congrArg Prod.fst hstate)
        have hcard' : #(T.erase j) = k + 1 := by
          rw [card_erase_of_mem hjT]
          omega
        rw [connectingCount_eq_historyWeight s k η (T.erase j) hT' hcard']
        refine congrArg _ (historyWeight_congr k (T.erase j) _ _ fun z hz ↦ ?_)
        rw [hstate]
        by_cases hzi : z = i
        · rw [hzi, Function.update_self]
          show (if (observed s ξ).r i i ∨ (observed s ξ).r j i then
              hiddenLoad s ξ (Quotient.mk (observed s ξ) i) +
                hiddenLoad s ξ (Quotient.mk (observed s ξ) j) - 1
              else hiddenLoad s ξ (Quotient.mk (observed s ξ) i)) = _
          rw [if_pos (Or.inl ((observed s ξ).iseqv.refl i))]
          rfl
        · have hzT : z ∈ T := mem_of_mem_erase hz
          have hzj : z ≠ j := ne_of_mem_erase hz
          have hnz : ¬((observed s ξ).r i z ∨ (observed s ξ).r j z) := by
            rintro (h | h)
            · exact hzi (hT.2 i hi z hzT h).symm
            · exact hzj (hT.2 j hjT z hzT h).symm
          rw [Function.update_of_ne hzi]
          show (if (observed s ξ).r i z ∨ (observed s ξ).r j z then
              hiddenLoad s ξ (Quotient.mk (observed s ξ) i) +
                hiddenLoad s ξ (Quotient.mk (observed s ξ) j) - 1
              else hiddenLoad s ξ (Quotient.mk (observed s ξ) z)) = _
          rw [if_neg hnz]
          rfl
      have hpairs : ∑ i ∈ T, ∑ j ∈ T.erase i, ∑ η ∈ univ.filter (fun η ↦
          Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) i j),
            connectingCount s k η =
          ∑ i ∈ T, ∑ j ∈ T.erase i, ((hiddenState s ξ).2 i : ℝ) * ((hiddenState s ξ).2 j : ℝ) *
            (historyWeight k (T.erase j) (Function.update (hiddenState s ξ).2 i
              ((hiddenState s ξ).2 i + (hiddenState s ξ).2 j - 1)) : ℝ) := by
        refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
        have hnot : ¬(observed s ξ).r i j := fun hrel ↦
          (ne_of_mem_erase hj).symm (hT.2 i hi j (mem_of_mem_erase hj) hrel)
        exact sum_filter_visibleTarget s ξ hnot (connectingCount s k) (hstep i hi j hj)
      have htwo := two_mul_sum_visible hT (connectingCount s k)
      rw [hpairs] at htwo
      rw [connectingCount_succ, historyWeight_succ]
      push_cast
      linarith

/-- **Theorem E, (E2), the constant as a history sum.** The minimal connecting histories from the
singletons number the history sum `H_w(c)` of the fibers with their sizes, read at the chosen
individuals. -/
theorem minimalHistoryCount_eq_historyWeight {n : ℕ} (s : Fin n → Fin n)
    (hwidth : 1 ≤ Linkage.width s) :
    minimalHistoryCount s =
      historyWeight (Linkage.width s - 1) (representatives s ⊥) (Linkage.fiberCard s) := by
  have hT := representatives_isRepresentativeSet s ⊥
  have hcard : #(representatives s ⊥) = Linkage.width s - 1 + 1 := by
    rw [hT.card_eq, observed_bot, blocks_graphKer, Nat.sub_add_cancel hwidth]
  rw [minimalHistoryCount_eq_connectingCount,
    connectingCount_eq_historyWeight s _ ⊥ _ hT hcard]
  exact congrArg _ (historyWeight_congr _ _ _ _ fun i _ ↦ hiddenLoad_bot s i)

/-- **Theorem E, (E2), the constant as a product.** For `w ≥ 2` fibers the minimal connecting
histories number `(∏_i c_i) g_w(n)`. -/
theorem minimalHistoryCount_eq_prod_historyFactor {n : ℕ} (s : Fin n → Fin n)
    (hwidth : 2 ≤ Linkage.width s) :
    minimalHistoryCount s =
      (∏ i ∈ representatives s ⊥, (Linkage.fiberCard s i : ℚ)) *
        historyFactor (Linkage.width s) n := by
  have hT := representatives_isRepresentativeSet s ⊥
  have hcard : #(representatives s ⊥) = Linkage.width s := by
    rw [hT.card_eq, observed_bot, blocks_graphKer]
  rw [minimalHistoryCount_eq_historyWeight s (by omega), ← hcard,
    historyWeight_eq_prod_historyFactor (representatives s ⊥) (Linkage.fiberCard s)
      (by rw [hcard]; exact hwidth) fun i _ ↦ Linkage.fiberCard_pos s i,
    sum_fiberCard_representatives, Rat.cast_mul]

open Asymptotics Topology in
/-- **Theorem E, (E2).** For an interface of width `w ≥ 2` with fiber sizes `c_i` on a panel of
`n` individuals, the probability that the report is connected at time `t`, started at the
singletons, is `(∏_i c_i) (2n - w)! / (2^{w-2} (2n - 2w + 2)!) t^{w-1} + O(t^w)` as `t → 0`. -/
theorem reportConnectedProbability_sub_note_isBigO {n : ℕ} (s : Fin n → Fin n)
    (hwidth : 2 ≤ Linkage.width s) :
    (fun t : ℝ ↦ reportConnectedProbability s t -
        (∏ i ∈ representatives s ⊥, (Linkage.fiberCard s i : ℝ)) *
          (2 * n - Linkage.width s)! /
            (2 ^ (Linkage.width s - 2) * (2 * n - 2 * Linkage.width s + 2)!) *
          t ^ (Linkage.width s - 1)) =O[𝓝 0] fun t : ℝ ↦ t ^ Linkage.width s := by
  have hle : Linkage.width s ≤ n := by simpa using Linkage.width_le_card s
  have hfactorial : ((Linkage.width s - 1)! : ℝ) ≠ 0 := by positivity
  have hfactorial' : ((2 * n - 2 * Linkage.width s + 2)! : ℝ) ≠ 0 := by positivity
  have hcount : minimalHistoryCount s =
      (∏ i ∈ representatives s ⊥, (Linkage.fiberCard s i : ℝ)) *
        ((Linkage.width s - 1)! / 2 ^ (Linkage.width s - 2) *
          ((2 * n - Linkage.width s)! / (2 * n - 2 * Linkage.width s + 2)!)) := by
    rw [minimalHistoryCount_eq_prod_historyFactor s hwidth, historyFactor_eq _ _ hwidth hle]
    push_cast
    try ring
  have hfun : (fun t : ℝ ↦ reportConnectedProbability s t -
        (∏ i ∈ representatives s ⊥, (Linkage.fiberCard s i : ℝ)) *
          (2 * n - Linkage.width s)! /
            (2 ^ (Linkage.width s - 2) * (2 * n - 2 * Linkage.width s + 2)!) *
          t ^ (Linkage.width s - 1)) =
      fun t : ℝ ↦ reportConnectedProbability s t -
        t ^ (Linkage.width s - 1) / (Linkage.width s - 1)! * minimalHistoryCount s := by
    funext t
    rw [hcount]
    field_simp
  rw [hfun]
  exact reportConnectedProbability_sub_isBigO s (by omega)

end

end Descent.Pangenome.GraphCoalescent.MinimalHistoryLumping
