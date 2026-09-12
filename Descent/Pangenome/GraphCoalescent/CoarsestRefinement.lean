/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LumpingUnorderedPair

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The coarsest predictive Markov refinement of a pangenome report

Theorem B of the hidden-lineage clock: among the deterministic statistics of the labeled
coalescent state that determine the report and are strong lumpings, the coarsest keeps every
labeled load while the report has at least three components, only the unordered pair of loads
while it has two, and nothing beyond the report once it has one. This module defines that
statistic and proves both halves for cover counts, with strong lumpability in Rosenblatt's form
as in `LumpingVisibleRates`.

`coarsestState s ξ` is the report together with the hidden loads while the report has at least
three components. With two components it carries the unordered pair of loads as its sum, the
number of true blocks, and its product, which together determine the pair
(`MinimalRefinement.unorderedPair_of_survivalDerivatives_eq`). With one component it carries only
the report (`coarsestState_of_three`, `coarsestState_of_two`, `coarsestState_of_one`).

Minimality is `coarsestState_eq_of_lumping`: every statistic that determines the report and is a
strong lumping refines the coarsest state. With three components this is
`LumpingVisibleRates.hiddenState_eq_of_lumping`. With two, the statistic determines the number of
true blocks (`LumpingUnorderedPair.blocks_eq_of_lumping`) and the visible rate
(`LumpingVisibleRates.visibleRate_eq_of_lumping`).

Sufficiency is `card_covers_coarsestState_eq`: from two states with the same coarsest state,
equally many covers lead to every other value of it. The coarsest state is a function of the
hidden state (`coarsestState_eq_of_hiddenState_eq`), so with three components this is Theorem A
(`card_covers_eq_of_hiddenState_eq`). With two components every cover lands on one of three hidden
targets (`hiddenState_of_covers_two`), and `card_covers_coarsestState_of_two` counts the covers
into each value as `twoComponentCount`: `C(a, 2)` invisible covers inside the component with load
`a`, `C(b, 2)` inside the other, and `a b` visible covers. Exchanging the two loads exchanges the
first two kinds without changing the values they reach, which is why only the unordered pair
enters. With one component no cover changes the coarsest state
(`coarsestState_of_covers_of_one`). `coarsestState_determines_report_and_lumps` records both
hypotheses for the coarsest state itself.

## Empirical status

None. The bodies here are counts of equivalence classes on a finite set: every statement is an
identity between cardinalities of sets of coalescent states or between their values, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.CoarsestRefinement

open Coalescent Finset LumpingVisibleRates LumpingUnorderedPair
open scoped Classical

attribute [local instance] LumpingVisibleRates.fintypeStates

noncomputable section

variable {n : ℕ}

/-! ### Two report components -/

/-- The visible target does not depend on the order of the two components it joins. -/
theorem visibleTarget_swap (X : ER n × (Fin n → ℕ)) {x y : Fin n} (hxy : ¬ X.1.r x y) :
    visibleTarget X y x = visibleTarget X x y := by
  have hyx : Quotient.mk X.1 y ≠ Quotient.mk X.1 x :=
    fun hq ↦ hxy (X.1.iseqv.symm (Quotient.exact hq))
  refine Prod.ext (merge_comm X.1 hyx) (funext fun z ↦ ?_)
  show (if X.1.r y z ∨ X.1.r x z then X.2 y + X.2 x - 1 else X.2 z) =
    if X.1.r x z ∨ X.1.r y z then X.2 x + X.2 y - 1 else X.2 z
  exact if_congr or_comm (congrArg (fun t ↦ t - 1) (Nat.add_comm (X.2 y) (X.2 x))) rfl

/-- With two report components, the components are those of two individuals reported apart. -/
theorem univ_eq_pair (s : Fin n → Fin n) (ξ : ER n) (hcomponents : blocks (observed s ξ) = 2)
    {x y : Fin n} (hxy : ¬ (observed s ξ).r x y) :
    (univ : Finset (Quotient (observed s ξ))) =
      {Quotient.mk (observed s ξ) x, Quotient.mk (observed s ξ) y} := by
  have hne : Quotient.mk (observed s ξ) x ≠ Quotient.mk (observed s ξ) y :=
    fun hq ↦ hxy (Quotient.exact hq)
  refine (eq_univ_of_card _ ?_).symm
  rw [card_pair hne, ← Nat.card_eq_fintype_card]
  exact hcomponents.symm

/-- With two report components, every individual is reported with `x` or with `y`. -/
theorem rel_or_rel_of_two (s : Fin n → Fin n) (ξ : ER n) (hcomponents : blocks (observed s ξ) = 2)
    {x y : Fin n} (hxy : ¬ (observed s ξ).r x y) (u : Fin n) :
    (observed s ξ).r u x ∨ (observed s ξ).r u y := by
  have hu : Quotient.mk (observed s ξ) u ∈
      ({Quotient.mk (observed s ξ) x, Quotient.mk (observed s ξ) y} : Finset _) := by
    rw [← univ_eq_pair s ξ hcomponents hxy]
    exact mem_univ _
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with hu | hu
  · exact Or.inl (Quotient.exact hu)
  · exact Or.inr (Quotient.exact hu)

/-- With two report components, the product of the loads is the product of the two loads. -/
theorem prod_hiddenLoad_of_two (s : Fin n → Fin n) (ξ : ER n)
    (hcomponents : blocks (observed s ξ) = 2) {x y : Fin n} (hxy : ¬ (observed s ξ).r x y) :
    ∏ C, hiddenLoad s ξ C =
      hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) := by
  have hne : Quotient.mk (observed s ξ) x ≠ Quotient.mk (observed s ξ) y :=
    fun hq ↦ hxy (Quotient.exact hq)
  rw [univ_eq_pair s ξ hcomponents hxy, prod_pair hne]

/-- A report with at least two components reports two individuals apart. -/
theorem exists_not_rel_of_two (s : Fin n → Fin n) (ξ : ER n)
    (hcomponents : 2 ≤ blocks (observed s ξ)) : ∃ x y : Fin n, ¬ (observed s ξ).r x y := by
  have hcard : 1 < (univ : Finset (Quotient (observed s ξ))).card := by
    rw [card_univ, ← Nat.card_eq_fintype_card]
    exact hcomponents
  obtain ⟨C, -, D, -, hCD⟩ := one_lt_card.mp hcard
  obtain ⟨x, rfl⟩ := quotient_mk_surjective (observed s ξ) C
  obtain ⟨y, rfl⟩ := quotient_mk_surjective (observed s ξ) D
  exact ⟨x, y, fun h ↦ hCD (Quotient.sound h)⟩

/-! ### The coarsest state -/

/-- **The coarsest predictive Markov refinement of the report** (spec §4, Theorem B): the report,
with every labeled load while the report has at least three components; with two components only
the unordered pair of loads, carried as its sum, the number of true blocks, and its product; with
one component nothing more. -/
def coarsestState (s : Fin n → Fin n) (ξ : ER n) : ER n × (ℕ × ℕ) × (Fin n → ℕ) :=
  if 3 ≤ blocks (observed s ξ) then (observed s ξ, (0, 0), (hiddenState s ξ).2)
  else if blocks (observed s ξ) = 2 then (observed s ξ, (blocks ξ, ∏ C, hiddenLoad s ξ C), 0)
  else (observed s ξ, (0, 0), 0)

/-- The coarsest state carries the report. -/
theorem coarsestState_fst (s : Fin n → Fin n) (ξ : ER n) :
    (coarsestState s ξ).1 = observed s ξ := by
  unfold coarsestState
  split_ifs <;> rfl

/-- With at least three components the coarsest state carries the hidden loads. -/
theorem coarsestState_of_three (s : Fin n → Fin n) (ξ : ER n)
    (hcomponents : 3 ≤ blocks (observed s ξ)) :
    coarsestState s ξ = (observed s ξ, (0, 0), (hiddenState s ξ).2) := by
  rw [coarsestState, if_pos hcomponents]

/-- With two components the coarsest state carries the number of true blocks and the product of
the two loads. -/
theorem coarsestState_of_two (s : Fin n → Fin n) (ξ : ER n)
    (hcomponents : blocks (observed s ξ) = 2) {x y : Fin n} (hxy : ¬ (observed s ξ).r x y) :
    coarsestState s ξ = (observed s ξ, (blocks ξ, hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
      hiddenLoad s ξ (Quotient.mk (observed s ξ) y)), 0) := by
  have hthree : ¬ 3 ≤ blocks (observed s ξ) := by omega
  rw [coarsestState, if_neg hthree, if_pos hcomponents, prod_hiddenLoad_of_two s ξ hcomponents hxy]

/-- With one component the coarsest state carries only the report. -/
theorem coarsestState_of_one (s : Fin n → Fin n) (ξ : ER n)
    (hcomponents : blocks (observed s ξ) ≤ 1) : coarsestState s ξ = (observed s ξ, (0, 0), 0) := by
  have hthree : ¬ 3 ≤ blocks (observed s ξ) := by omega
  have htwo : ¬ blocks (observed s ξ) = 2 := by omega
  rw [coarsestState, if_neg hthree, if_neg htwo]

/-! ### Minimality -/

/-- **Theorem B, minimality.** Every statistic that determines the report and is a strong lumping
in Rosenblatt's form refines the coarsest state: two states with the same value have the same
coarsest state. Assumes: the statistic determines the report, and it is a strong lumping in
Rosenblatt's form. -/
theorem coarsestState_eq_of_lumping {Stat : Type*} (s : Fin n → Fin n) (f : ER n → Stat)
    (hreport : ∀ ξ ξ' : ER n, f ξ = f ξ' → observed s ξ = observed s ξ')
    (hlumping : ∀ ξ ξ' : ER n, f ξ = f ξ' → ∀ v, v ≠ f ξ →
      Nat.card {η : ER n // Covers ξ η ∧ f η = v} = Nat.card {η : ER n // Covers ξ' η ∧ f η = v})
    {ξ ξ' : ER n} (hsame : f ξ = f ξ') : coarsestState s ξ = coarsestState s ξ' := by
  have hreports : observed s ξ = observed s ξ' := hreport ξ ξ' hsame
  by_cases hthree : 3 ≤ blocks (observed s ξ)
  · have hthree' : 3 ≤ blocks (observed s ξ') := hreports ▸ hthree
    rw [coarsestState_of_three s ξ hthree, coarsestState_of_three s ξ' hthree',
      hiddenState_eq_of_lumping s f hreport hlumping hsame hthree, hreports]
  · by_cases htwo : blocks (observed s ξ) = 2
    · obtain ⟨x, y, hxy⟩ := exists_not_rel_of_two s ξ htwo.ge
      have htwo' : blocks (observed s ξ') = 2 := hreports ▸ htwo
      have hxy' : ¬ (observed s ξ').r x y := hreports ▸ hxy
      rw [coarsestState_of_two s ξ htwo hxy, coarsestState_of_two s ξ' htwo' hxy',
        visibleRate_eq_of_lumping s f hreport hlumping hsame hxy,
        blocks_eq_of_lumping s f hreport hlumping (Fin.pos x) hsame htwo.ge, hreports]
    · have hone : blocks (observed s ξ) ≤ 1 := by omega
      have hone' : blocks (observed s ξ') ≤ 1 := hreports ▸ hone
      rw [coarsestState_of_one s ξ hone, coarsestState_of_one s ξ' hone', hreports]

/-! ### Sufficiency -/

/-- The coarsest state is a function of the hidden state. -/
theorem coarsestState_eq_of_hiddenState_eq (s : Fin n → Fin n) {η η' : ER n}
    (hstate : hiddenState s η = hiddenState s η') : coarsestState s η = coarsestState s η' := by
  have hreports : observed s η = observed s η' := congrArg Prod.fst hstate
  by_cases hthree : 3 ≤ blocks (observed s η)
  · have hthree' : 3 ≤ blocks (observed s η') := hreports ▸ hthree
    rw [coarsestState_of_three s η hthree, coarsestState_of_three s η' hthree', hstate, hreports]
  · by_cases htwo : blocks (observed s η) = 2
    · obtain ⟨x, y, hxy⟩ := exists_not_rel_of_two s η htwo.ge
      have htwo' : blocks (observed s η') = 2 := hreports ▸ htwo
      have hxy' : ¬ (observed s η').r x y := hreports ▸ hxy
      have hx : hiddenLoad s η (Quotient.mk (observed s η) x) =
          hiddenLoad s η' (Quotient.mk (observed s η') x) :=
        congrFun (congrArg Prod.snd hstate) x
      have hy : hiddenLoad s η (Quotient.mk (observed s η) y) =
          hiddenLoad s η' (Quotient.mk (observed s η') y) :=
        congrFun (congrArg Prod.snd hstate) y
      rw [coarsestState_of_two s η htwo hxy, coarsestState_of_two s η' htwo' hxy',
        ← hiddenLoad_add_hiddenLoad s η htwo hxy, ← hiddenLoad_add_hiddenLoad s η' htwo' hxy', hx,
        hy, hreports]
    · have hone : blocks (observed s η) ≤ 1 := by omega
      have hone' : blocks (observed s η') ≤ 1 := hreports ▸ hone
      rw [coarsestState_of_one s η hone, coarsestState_of_one s η' hone', hreports]

/-- **Equal hidden states count alike.** Two states with the same hidden state have equally many
covers into every value of the coarsest state, by Theorem A. -/
theorem card_covers_eq_of_hiddenState_eq (s : Fin n → Fin n) {ξ ξ' : ER n}
    (hstate : hiddenState s ξ = hiddenState s ξ') (v : ER n × (ℕ × ℕ) × (Fin n → ℕ)) :
    Nat.card {η : ER n // Covers ξ η ∧ coarsestState s η = v} =
      Nat.card {η : ER n // Covers ξ' η ∧ coarsestState s η = v} := by
  obtain ⟨g, hg⟩ : ∃ g : ER n × (Fin n → ℕ) → ER n × (ℕ × ℕ) × (Fin n → ℕ),
      ∀ η, g (hiddenState s η) = coarsestState s η := by
    refine ⟨fun w ↦ if h : ∃ ζ, hiddenState s ζ = w then coarsestState s h.choose
      else coarsestState s ⊥, fun η ↦ ?_⟩
    have h : ∃ ζ, hiddenState s ζ = hiddenState s η := ⟨η, rfl⟩
    show (if h : ∃ ζ, hiddenState s ζ = hiddenState s η then coarsestState s h.choose
      else coarsestState s ⊥) = coarsestState s η
    rw [dif_pos h]
    exact coarsestState_eq_of_hiddenState_eq s h.choose_spec
  have hcomp : ∀ ζ : ER n, Nat.card {η : ER n // Covers ζ η ∧ coarsestState s η = v} =
      ((univ.filter (Covers ζ)).filter fun η ↦ g (hiddenState s η) = v).card := by
    intro ζ
    rw [natCard_covers_eq ζ fun η ↦ coarsestState s η = v]
    congr 1
    ext η
    simp only [mem_filter, hg]
  rw [hcomp ξ, hcomp ξ']
  refine card_filter_comp_eq _ _ (hiddenState s) g v fun w _ ↦ ?_
  have hcount := (natCard_covers_eq ξ fun η ↦ hiddenState s η = w).symm.trans
    ((card_covers_hiddenState_eq s hstate w).trans
      (natCard_covers_eq ξ' fun η ↦ hiddenState s η = w))
  convert hcount

/-- **The covers of a two-component state.** Every cover lands on the invisible target of the
component of `x`, on that of `y`, or on the visible target joining the two. -/
theorem hiddenState_of_covers_two (s : Fin n → Fin n) {ξ η : ER n}
    (hcomponents : blocks (observed s ξ) = 2) {x y : Fin n} (hxy : ¬ (observed s ξ).r x y)
    (hcov : Covers ξ η) :
    hiddenState s η = invisibleTarget (hiddenState s ξ) x ∨
      hiddenState s η = invisibleTarget (hiddenState s ξ) y ∨
        hiddenState s η = visibleTarget (hiddenState s ξ) x y := by
  rcases hiddenState_of_covers s hcov with ⟨u, hu⟩ | ⟨u, w, huw, hw⟩
  · rcases rel_or_rel_of_two s ξ hcomponents hxy u with hux | huy
    · exact Or.inl (hu.trans (invisibleTarget_eq_of_rel s ξ hux))
    · exact Or.inr (Or.inl (hu.trans (invisibleTarget_eq_of_rel s ξ huy)))
  · refine Or.inr (Or.inr ?_)
    rcases rel_or_rel_of_two s ξ hcomponents hxy u with hux | huy
    · rcases rel_or_rel_of_two s ξ hcomponents hxy w with hwx | hwy
      · exact absurd ((observed s ξ).iseqv.trans hux ((observed s ξ).iseqv.symm hwx)) huw
      · exact hw.trans (visibleTarget_eq_of_rel s ξ hux hwy)
    · rcases rel_or_rel_of_two s ξ hcomponents hxy w with hwx | hwy
      · exact hw.trans ((visibleTarget_eq_of_rel s ξ huy hwx).trans
          (visibleTarget_swap (hiddenState s ξ) hxy))
      · exact absurd ((observed s ξ).iseqv.trans huy ((observed s ξ).iseqv.symm hwy)) huw

/-- **The covers of a two-component state, counted into a value.** With report `Y`, merged report
`Z`, `K` true blocks and loads `a` and `b`: `C(a, 2)` invisible covers reach the value with loads
`a - 1, b`, `C(b, 2)` reach the value with loads `a, b - 1`, and `a b` visible covers reach the
connected report. -/
def twoComponentCount (Y Z : ER n) (K a b : ℕ) (v : ER n × (ℕ × ℕ) × (Fin n → ℕ)) : ℕ :=
  (if v = (Y, (K - 1, (a - 1) * b), 0) then a.choose 2 else 0) +
    ((if v = (Y, (K - 1, a * (b - 1)), 0) then b.choose 2 else 0) +
      (if v = (Z, (0, 0), 0) then a * b else 0))

/-- **The count of covers into each value, two components.** The covers of a two-component state
into a value of the coarsest state number `twoComponentCount` of its report, the merged report, its
number of true blocks and its two loads. -/
theorem card_covers_coarsestState_of_two (s : Fin n → Fin n) (ξ : ER n)
    (hcomponents : blocks (observed s ξ) = 2) {x y : Fin n} (hxy : ¬ (observed s ξ).r x y)
    (v : ER n × (ℕ × ℕ) × (Fin n → ℕ)) :
    Nat.card {η : ER n // Covers ξ η ∧ coarsestState s η = v} =
      twoComponentCount (observed s ξ)
        (merge (observed s ξ) (Quotient.mk (observed s ξ) x) (Quotient.mk (observed s ξ) y))
        (blocks ξ) (hiddenLoad s ξ (Quotient.mk (observed s ξ) x))
        (hiddenLoad s ξ (Quotient.mk (observed s ξ) y)) v := by
  have hCD : Quotient.mk (observed s ξ) x ≠ Quotient.mk (observed s ξ) y :=
    fun hq ↦ hxy (Quotient.exact hq)
  have hmergeNe : merge (observed s ξ) (Quotient.mk (observed s ξ) x)
      (Quotient.mk (observed s ξ) y) ≠ observed s ξ := by
    intro h
    have hcov := merge_covers (observed s ξ) hCD
    rw [h] at hcov
    have hblocks := hcov.2
    omega
  have hterm : ∀ (w : ER n × (Fin n → ℕ)) (c : ER n × (ℕ × ℕ) × (Fin n → ℕ)),
      (∀ η, Covers ξ η → hiddenState s η = w → coarsestState s η = c) →
      ((univ.filter fun η ↦ Covers ξ η ∧ coarsestState s η = v).filter
          fun η ↦ hiddenState s η = w).card =
        if v = c then Nat.card {η : ER n // Covers ξ η ∧ hiddenState s η = w} else 0 := by
    intro w c hc
    split_ifs with hvc
    · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext η
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨hcov, -⟩, hw⟩
        exact ⟨hcov, hw⟩
      · rintro ⟨hcov, hw⟩
        exact ⟨⟨hcov, (hc η hcov hw).trans hvc.symm⟩, hw⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro η hη hw
      simp only [mem_filter, mem_univ, true_and] at hη
      exact hvc (hη.2.symm.trans (hc η hη.1 hw))
  have hc1 : ∀ η, Covers ξ η → hiddenState s η = invisibleTarget (hiddenState s ξ) x →
      coarsestState s η = (observed s ξ, (blocks ξ - 1,
        (hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1) *
          hiddenLoad s ξ (Quotient.mk (observed s ξ) y)), 0) := by
    intro η hcov hstate
    have hreport : observed s η = observed s ξ := congrArg Prod.fst hstate
    have hcomponentsη : blocks (observed s η) = 2 := hreport ▸ hcomponents
    have hxyη : ¬ (observed s η).r x y := hreport ▸ hxy
    have hx : hiddenLoad s η (Quotient.mk (observed s η) x) =
        hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1 := by
      have h := congrFun (congrArg Prod.snd hstate) x
      change hiddenLoad s η (Quotient.mk (observed s η) x) =
        if (observed s ξ).r x x then hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1
        else hiddenLoad s ξ (Quotient.mk (observed s ξ) x) at h
      rw [if_pos ((observed s ξ).iseqv.refl x)] at h
      exact h
    have hy : hiddenLoad s η (Quotient.mk (observed s η) y) =
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) := by
      have h := congrFun (congrArg Prod.snd hstate) y
      change hiddenLoad s η (Quotient.mk (observed s η) y) =
        if (observed s ξ).r x y then hiddenLoad s ξ (Quotient.mk (observed s ξ) y) - 1
        else hiddenLoad s ξ (Quotient.mk (observed s ξ) y) at h
      rw [if_neg hxy] at h
      exact h
    have hblocks : blocks η = blocks ξ - 1 := by
      have h := hcov.2
      omega
    rw [coarsestState_of_two s η hcomponentsη hxyη, hx, hy, hblocks, hreport]
  have hc2 : ∀ η, Covers ξ η → hiddenState s η = invisibleTarget (hiddenState s ξ) y →
      coarsestState s η = (observed s ξ, (blocks ξ - 1,
        hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
          (hiddenLoad s ξ (Quotient.mk (observed s ξ) y) - 1)), 0) := by
    intro η hcov hstate
    have hreport : observed s η = observed s ξ := congrArg Prod.fst hstate
    have hcomponentsη : blocks (observed s η) = 2 := hreport ▸ hcomponents
    have hxyη : ¬ (observed s η).r x y := hreport ▸ hxy
    have hx : hiddenLoad s η (Quotient.mk (observed s η) x) =
        hiddenLoad s ξ (Quotient.mk (observed s ξ) x) := by
      have h := congrFun (congrArg Prod.snd hstate) x
      change hiddenLoad s η (Quotient.mk (observed s η) x) =
        if (observed s ξ).r y x then hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1
        else hiddenLoad s ξ (Quotient.mk (observed s ξ) x) at h
      rw [if_neg fun h ↦ hxy ((observed s ξ).iseqv.symm h)] at h
      exact h
    have hy : hiddenLoad s η (Quotient.mk (observed s η) y) =
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) - 1 := by
      have h := congrFun (congrArg Prod.snd hstate) y
      change hiddenLoad s η (Quotient.mk (observed s η) y) =
        if (observed s ξ).r y y then hiddenLoad s ξ (Quotient.mk (observed s ξ) y) - 1
        else hiddenLoad s ξ (Quotient.mk (observed s ξ) y) at h
      rw [if_pos ((observed s ξ).iseqv.refl y)] at h
      exact h
    have hblocks : blocks η = blocks ξ - 1 := by
      have h := hcov.2
      omega
    rw [coarsestState_of_two s η hcomponentsη hxyη, hx, hy, hblocks, hreport]
  have hc3 : ∀ η, Covers ξ η → hiddenState s η = visibleTarget (hiddenState s ξ) x y →
      coarsestState s η = (merge (observed s ξ) (Quotient.mk (observed s ξ) x)
        (Quotient.mk (observed s ξ) y), (0, 0), 0) := by
    intro η _ hstate
    have hreport : observed s η = merge (observed s ξ) (Quotient.mk (observed s ξ) x)
        (Quotient.mk (observed s ξ) y) := congrArg Prod.fst hstate
    have hone : blocks (observed s η) ≤ 1 := by
      rw [hreport]
      have h := (merge_covers (observed s ξ) hCD).2
      omega
    rw [coarsestState_of_one s η hone, hreport]
  have h12 : invisibleTarget (hiddenState s ξ) x ≠ invisibleTarget (hiddenState s ξ) y := by
    intro h
    have hload := congrFun (congrArg Prod.snd h) x
    change (if (observed s ξ).r x x then hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1
        else hiddenLoad s ξ (Quotient.mk (observed s ξ) x)) =
      (if (observed s ξ).r y x then hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1
        else hiddenLoad s ξ (Quotient.mk (observed s ξ) x)) at hload
    rw [if_pos ((observed s ξ).iseqv.refl x),
      if_neg fun h ↦ hxy ((observed s ξ).iseqv.symm h)] at hload
    have hpos := hiddenLoad_pos s ξ (Quotient.mk (observed s ξ) x)
    omega
  have h13 : invisibleTarget (hiddenState s ξ) x ≠ visibleTarget (hiddenState s ξ) x y :=
    fun h ↦ hmergeNe (congrArg Prod.fst h).symm
  have h23 : invisibleTarget (hiddenState s ξ) y ≠ visibleTarget (hiddenState s ξ) x y :=
    fun h ↦ hmergeNe (congrArg Prod.fst h).symm
  have hmaps : ∀ η ∈ univ.filter fun η ↦ Covers ξ η ∧ coarsestState s η = v,
      hiddenState s η ∈ ({invisibleTarget (hiddenState s ξ) x,
        invisibleTarget (hiddenState s ξ) y, visibleTarget (hiddenState s ξ) x y} :
          Finset (ER n × (Fin n → ℕ))) := by
    intro η hη
    simp only [mem_filter, mem_univ, true_and] at hη
    simp only [mem_insert, mem_singleton]
    exact hiddenState_of_covers_two s hcomponents hxy hη.1
  have hnotFirst : invisibleTarget (hiddenState s ξ) x ∉ ({invisibleTarget (hiddenState s ξ) y,
      visibleTarget (hiddenState s ξ) x y} : Finset (ER n × (Fin n → ℕ))) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨h12, h13⟩
  have hnotSecond : invisibleTarget (hiddenState s ξ) y ∉
      ({visibleTarget (hiddenState s ξ) x y} : Finset (ER n × (Fin n → ℕ))) := by
    simp only [mem_singleton]
    exact h23
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_eq_sum_card_fiberwise hmaps,
    sum_insert hnotFirst, sum_insert hnotSecond, sum_singleton, hterm _ _ hc1, hterm _ _ hc2,
    hterm _ _ hc3, card_covers_invisibleTarget s ξ x, card_covers_invisibleTarget s ξ y,
    card_covers_visibleTarget s ξ hxy]
  rfl

/-- With one report component no cover changes the coarsest state. -/
theorem coarsestState_of_covers_of_one (s : Fin n → Fin n) {ξ η : ER n}
    (hcomponents : blocks (observed s ξ) ≤ 1) (hcov : Covers ξ η) :
    coarsestState s η = coarsestState s ξ := by
  obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge ξ η).mp hcov
  obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ A
  haveI : NeZero n := ⟨(Fin.pos u).ne'⟩
  have hreport : observed s (merge ξ (Quotient.mk ξ u) B) = observed s ξ := by
    rcases observed_eq_or_covers s hcov with h | h
    · exact h
    · have hblocks := h.2
      have hpos := blocks_pos (observed s (merge ξ (Quotient.mk ξ u) B))
      omega
  have hcomponents' : blocks (observed s (merge ξ (Quotient.mk ξ u) B)) ≤ 1 :=
    hreport ▸ hcomponents
  rw [coarsestState_of_one s _ hcomponents', coarsestState_of_one s ξ hcomponents, hreport]

/-- **Theorem B, sufficiency.** From two states with the same coarsest state, equally many covers
lead to every other value of the coarsest state: the coarsest state is a strong lumping in
Rosenblatt's form. -/
theorem card_covers_coarsestState_eq (s : Fin n → Fin n) {ξ ξ' : ER n}
    (hsame : coarsestState s ξ = coarsestState s ξ') (v : ER n × (ℕ × ℕ) × (Fin n → ℕ))
    (hv : v ≠ coarsestState s ξ) :
    Nat.card {η : ER n // Covers ξ η ∧ coarsestState s η = v} =
      Nat.card {η : ER n // Covers ξ' η ∧ coarsestState s η = v} := by
  have hreports : observed s ξ = observed s ξ' :=
    (coarsestState_fst s ξ).symm.trans ((congrArg Prod.fst hsame).trans (coarsestState_fst s ξ'))
  by_cases hthree : 3 ≤ blocks (observed s ξ)
  · have hthree' : 3 ≤ blocks (observed s ξ') := hreports ▸ hthree
    have hstate : hiddenState s ξ = hiddenState s ξ' := by
      have h := congrArg (fun c : ER n × (ℕ × ℕ) × (Fin n → ℕ) ↦ c.2.2) hsame
      rw [coarsestState_of_three s ξ hthree, coarsestState_of_three s ξ' hthree'] at h
      exact Prod.ext hreports h
    exact card_covers_eq_of_hiddenState_eq s hstate v
  · by_cases htwo : blocks (observed s ξ) = 2
    · obtain ⟨x, y, hxy⟩ := exists_not_rel_of_two s ξ htwo.ge
      have htwo' : blocks (observed s ξ') = 2 := hreports ▸ htwo
      have hxy' : ¬ (observed s ξ').r x y := hreports ▸ hxy
      have hyx' : ¬ (observed s ξ').r y x := fun h ↦ hxy' ((observed s ξ').iseqv.symm h)
      have hyx : Quotient.mk (observed s ξ) y ≠ Quotient.mk (observed s ξ) x :=
        fun hq ↦ hxy ((observed s ξ).iseqv.symm (Quotient.exact hq))
      have hpair : (blocks ξ, hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
          hiddenLoad s ξ (Quotient.mk (observed s ξ) y)) =
          (blocks ξ', hiddenLoad s ξ' (Quotient.mk (observed s ξ') x) *
            hiddenLoad s ξ' (Quotient.mk (observed s ξ') y)) := by
        have h := congrArg (fun c : ER n × (ℕ × ℕ) × (Fin n → ℕ) ↦ c.2.1) hsame
        rw [coarsestState_of_two s ξ htwo hxy, coarsestState_of_two s ξ' htwo' hxy'] at h
        exact h
      have hblocks : blocks ξ = blocks ξ' := congrArg Prod.fst hpair
      have hproduct : hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
          hiddenLoad s ξ (Quotient.mk (observed s ξ) y) =
          hiddenLoad s ξ' (Quotient.mk (observed s ξ') x) *
            hiddenLoad s ξ' (Quotient.mk (observed s ξ') y) := congrArg Prod.snd hpair
      have hsum : hiddenLoad s ξ (Quotient.mk (observed s ξ) x) +
          hiddenLoad s ξ (Quotient.mk (observed s ξ) y) =
          hiddenLoad s ξ' (Quotient.mk (observed s ξ') x) +
            hiddenLoad s ξ' (Quotient.mk (observed s ξ') y) := by
        rw [hiddenLoad_add_hiddenLoad s ξ htwo hxy, hiddenLoad_add_hiddenLoad s ξ' htwo' hxy',
          hblocks]
      have ha : 1 ≤ hiddenLoad s ξ (Quotient.mk (observed s ξ) x) := hiddenLoad_pos s ξ _
      have hb : 1 ≤ hiddenLoad s ξ (Quotient.mk (observed s ξ) y) := hiddenLoad_pos s ξ _
      have ha' : 1 ≤ hiddenLoad s ξ' (Quotient.mk (observed s ξ') x) := hiddenLoad_pos s ξ' _
      have hb' : 1 ≤ hiddenLoad s ξ' (Quotient.mk (observed s ξ') y) := hiddenLoad_pos s ξ' _
      have hderivatives := survivalDerivatives_eq_of_sum_product ha hb ha' hb' hproduct hsum
      rw [card_covers_coarsestState_of_two s ξ htwo hxy v]
      rcases MinimalRefinement.unorderedPair_of_survivalDerivatives_eq _ _ _ _ ha hb ha' hb'
          hderivatives.1 hderivatives.2 with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [card_covers_coarsestState_of_two s ξ' htwo' hxy' v, hx, hy, ← hblocks, ← hreports]
      · rw [card_covers_coarsestState_of_two s ξ' htwo' hyx' v, hx, hy, ← hblocks, ← hreports,
          merge_comm (observed s ξ) hyx]
    · have hone : blocks (observed s ξ) ≤ 1 := by omega
      have hzero : ∀ ζ : ER n, blocks (observed s ζ) ≤ 1 → coarsestState s ζ = coarsestState s ξ →
          Nat.card {η : ER n // Covers ζ η ∧ coarsestState s η = v} = 0 := by
        intro ζ hζ hsameζ
        rw [Nat.card_eq_zero]
        refine Or.inl ⟨?_⟩
        rintro ⟨η, hcov, hη⟩
        exact hv (hη.symm.trans ((coarsestState_of_covers_of_one s hζ hcov).trans hsameζ))
      have hone' : blocks (observed s ξ') ≤ 1 := hreports ▸ hone
      rw [hzero ξ hone rfl, hzero ξ' hone' hsame.symm]

/-- **The coarsest state meets both hypotheses of minimality.** It determines the report and is a
strong lumping in Rosenblatt's form, so `coarsestState_eq_of_lumping` identifies it as the
coarsest statistic with both properties. -/
theorem coarsestState_determines_report_and_lumps (s : Fin n → Fin n) :
    (∀ ξ ξ' : ER n, coarsestState s ξ = coarsestState s ξ' → observed s ξ = observed s ξ') ∧
      ∀ ξ ξ' : ER n, coarsestState s ξ = coarsestState s ξ' → ∀ v, v ≠ coarsestState s ξ →
        Nat.card {η : ER n // Covers ξ η ∧ coarsestState s η = v} =
          Nat.card {η : ER n // Covers ξ' η ∧ coarsestState s η = v} :=
  ⟨fun ξ ξ' h ↦ (coarsestState_fst s ξ).symm.trans
      ((congrArg Prod.fst h).trans (coarsestState_fst s ξ')),
    fun _ _ h v hv ↦ card_covers_coarsestState_eq s h v hv⟩

end

end Descent.Pangenome.GraphCoalescent.CoarsestRefinement
