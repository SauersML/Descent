/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.CoarsestRefinement
import Descent.Pangenome.GraphCoalescent.Conservation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# How much a pangenome compression hides: counting the coarsest Markov state

An interface `s` compresses a sample into graph states, and the report `observed s ξ` of the
coalescent is in general not Markov.  `CoarsestRefinement` builds the coarsest statistic that
restores the Markov property, `coarsestState s ξ`: the report with every hidden load while it has
at least three components, the unordered pair of loads while it has two, and nothing more once it
has one.  The number of distinct values of that statistic, against the number of reports, measures
how much hidden state the compression forces an observer to carry.

- `reportStateCount s` is the number of reports of the interface, and `coarsestStateCount s` the
  number of coarsest states, both over all coalescent states of the sample.
- `reportStateCount_le_coarsestStateCount`: the coarsest state determines the report, so a
  compression never needs fewer states than it reports.
- `coarsestStateCount_eq_reportStateCount_of_injective`: **no compression, nothing hidden.**  With
  an injective interface the report is the coalescent state (`observed_of_injective`), every
  hidden load is one (`hiddenLoad_of_injective`), and the coarsest state is a function of the
  report.
- `reportStateCount_lt_coarsestStateCount`: **a compression hides.**  As soon as two individuals
  share a graph state and the interface has at least two occupied states, some report is carried
  by two different coarsest states, so the coarsest refinement has strictly more states than the
  report.  The witness is the singleton state and the state that merges the two individuals: the
  report is the same, while the hidden load of their component drops by one (three or more
  components) or the number of true blocks drops by one (two).

Scope.  The counts are compared, and the extremes are characterized; the exact number of coarsest
states as a function of the fiber sizes, the sum over reports of the load ranges, is not yet
proved here.

## Empirical status

None.  The bodies compare cardinalities of images of finite maps on coalescent states, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.CompressionHiddenStateCount

open Coalescent Finset CoarsestRefinement
open scoped Classical

attribute [local instance] LumpingVisibleRates.fintypeStates

noncomputable section

variable {n : ℕ}

/-- The number of reports an interface can show, over all coalescent states of the sample. -/
def reportStateCount (s : Fin n → Fin n) : ℕ :=
  #(univ.image (observed s))

/-- The number of states of the coarsest predictive Markov refinement of the report. -/
def coarsestStateCount (s : Fin n → Fin n) : ℕ :=
  #(univ.image (coarsestState s))

/-- The reports are the first coordinates of the coarsest states. -/
theorem image_observed_eq_image_fst (s : Fin n → Fin n) :
    univ.image (observed s) = (univ.image (coarsestState s)).image Prod.fst := by
  rw [image_image]
  exact image_congr fun ξ _ ↦ (coarsestState_fst s ξ).symm

/-- **A compression never needs fewer states than it reports.** -/
theorem reportStateCount_le_coarsestStateCount (s : Fin n → Fin n) :
    reportStateCount s ≤ coarsestStateCount s := by
  rw [reportStateCount, coarsestStateCount, image_observed_eq_image_fst]
  exact card_image_le

/-! ## No compression -/

/-- An injective interface merges no two individuals. -/
theorem graphKer_le_of_injective {s : Fin n → Fin n} (hs : Function.Injective s) (ξ : ER n) :
    graphKer s ≤ ξ := by
  intro x y hxy
  rw [hs (graphKer_rel_iff.mp hxy)]

/-- With an injective interface the report is the coalescent state itself. -/
theorem observed_of_injective {s : Fin n → Fin n} (hs : Function.Injective s) (ξ : ER n) :
    observed s ξ = ξ :=
  sup_eq_left.mpr (graphKer_le_of_injective hs ξ)

/-- With an injective interface every report component holds exactly one true block. -/
theorem hiddenLoad_of_injective {s : Fin n → Fin n} (hs : Function.Injective s) (ξ : ER n)
    (C : Quotient (observed s ξ)) : hiddenLoad s ξ C = 1 := by
  have hexcess := sum_hiddenLoad_sub_one s ξ
  have hzero : hiddenExcess s ξ = 0 := by
    rw [hiddenExcess, observed_of_injective hs, Nat.sub_self]
  rw [hzero, sum_eq_zero_iff] at hexcess
  have h := hexcess C (mem_univ C)
  have hpos := hiddenLoad_pos s ξ C
  omega

/-- **No compression, nothing hidden.**  With an injective interface the coarsest refinement has
exactly as many states as the report. -/
theorem coarsestStateCount_eq_reportStateCount_of_injective {s : Fin n → Fin n}
    (hs : Function.Injective s) : coarsestStateCount s = reportStateCount s := by
  refine le_antisymm ?_ (reportStateCount_le_coarsestStateCount s)
  let F : ER n → ER n × (ℕ × ℕ) × (Fin n → ℕ) := fun σ ↦
    if 3 ≤ blocks σ then (σ, (0, 0), fun _ ↦ 1)
    else if blocks σ = 2 then (σ, (blocks σ, 1), 0) else (σ, (0, 0), 0)
  have hF : ∀ ξ : ER n, coarsestState s ξ = F (observed s ξ) := by
    intro ξ
    have hload : ∀ C, hiddenLoad s ξ C = 1 := hiddenLoad_of_injective hs ξ
    have hblocks : blocks ξ = blocks (observed s ξ) := by rw [observed_of_injective hs]
    rw [coarsestState]
    simp only [F, hiddenState, hload, prod_const_one, ← hblocks]
  have himage : univ.image (coarsestState s) = (univ.image (observed s)).image F := by
    rw [image_image]
    exact image_congr fun ξ _ ↦ hF ξ
  rw [coarsestStateCount, reportStateCount, himage]
  exact card_image_le

/-! ## A compression hides -/

/-- With two report components the coarsest state records the number of true blocks. -/
theorem coarsestState_blocks_of_two (s : Fin n → Fin n) (ξ : ER n)
    (hcomponents : blocks (observed s ξ) = 2) : (coarsestState s ξ).2.1.1 = blocks ξ := by
  rw [coarsestState, if_neg (by omega), if_pos hcomponents]

/-- **A compression hides.**  If two individuals share a graph state and the interface occupies at
least two states, the coarsest refinement has strictly more states than the report. -/
theorem reportStateCount_lt_coarsestStateCount {s : Fin n → Fin n} {x y : Fin n} (hxy : x ≠ y)
    (hsxy : s x = s y) (hwidth : 2 ≤ Linkage.width s) :
    reportStateCount s < coarsestStateCount s := by
  have hne : Quotient.mk (⊥ : ER n) x ≠ Quotient.mk (⊥ : ER n) y :=
    fun h ↦ hxy (Quotient.exact h)
  have hrel : (observed s ⊥).r x y := by
    rw [observed_bot]
    exact graphKer_rel_iff.mpr hsxy
  have hobs : observed s (merge ⊥ (Quotient.mk ⊥ x) (Quotient.mk ⊥ y)) = observed s ⊥ :=
    observed_merge_of_rel hne hrel
  have hbot : blocks (observed s (⊥ : ER n)) = Linkage.width s := by
    rw [observed_bot, blocks_graphKer]
  have hdiff : coarsestState s (merge ⊥ (Quotient.mk ⊥ x) (Quotient.mk ⊥ y))
      ≠ coarsestState s ⊥ := by
    intro h
    rcases (by omega : Linkage.width s = 2 ∨ 3 ≤ Linkage.width s) with hw2 | hw3
    · have hb : (coarsestState s (merge ⊥ (Quotient.mk ⊥ x) (Quotient.mk ⊥ y))).2.1.1
          = (coarsestState s ⊥).2.1.1 := by rw [h]
      rw [coarsestState_blocks_of_two s _ (by rw [hobs, hbot, hw2]),
        coarsestState_blocks_of_two s ⊥ (by rw [hbot, hw2])] at hb
      have hmerge := blocks_merge (⊥ : ER n) hne
      omega
    · have hload : (coarsestState s (merge ⊥ (Quotient.mk ⊥ x) (Quotient.mk ⊥ y))).2.2 x
          = (coarsestState s ⊥).2.2 x := by rw [h]
      simp only [coarsestState_of_three s _ (by rw [hobs, hbot]; exact hw3),
        coarsestState_of_three s ⊥ (by rw [hbot]; exact hw3), hiddenState] at hload
      rw [hiddenLoad_merge_of_rel_self hne hrel, hiddenLoad_bot] at hload
      have hpos := Linkage.fiberCard_pos s x
      omega
  rw [reportStateCount, coarsestStateCount, image_observed_eq_image_fst]
  refine lt_of_le_of_ne card_image_le fun hcard ↦ ?_
  have hinj := card_image_iff.mp hcard
  exact hdiff (hinj (mem_image_of_mem _ (mem_univ _)) (mem_image_of_mem _ (mem_univ _))
    (by rw [coarsestState_fst, coarsestState_fst, hobs]))

end

end Descent.Pangenome.GraphCoalescent.CompressionHiddenStateCount
