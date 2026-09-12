/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiInterfaceClosure
import Descent.Pangenome.GraphCoalescent.Visibility

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# What a merger does to several reports

`MultiInterfaceClosure.card_mergers_eq_lumpedMergerCount` proves the closure of several interfaces
sharing one coalescent under one hypothesis: the lumped state after a merger is a function of the
cells of the common refinement containing the two merging blocks. This module discharges the
report part of that hypothesis with the corpus merge `Coalescent.merge`.

`pairRelation x z` is the equivalence relation identifying `x` with `z` and nothing else, the
merge of two singleton classes at the bottom. `merge_eq_sup_pairRelation` shows that merging the
blocks of `x` and `z` is joining the coalescent state with that relation, and
`observed_merge_eq` that reporting the merged state at an interface is joining the report with
the same relation: in each report the merger joins the components containing `x` and `z`.
`sup_pairRelation_eq_of_rel` shows that the join does not change when `x` and `z` move within
classes of the relation, so `observed_merge_eq_of_cells` concludes that two coalescent states with
the same reports, merging two pairs of individuals in the same cells of the common refinement,
have the same report at every interface afterwards, and `commonRefinement_merge_eq_of_cells`
that they have the same common refinement afterwards. `commonRefinement_eq_of_reports` and
`commonRefinement_mono` record that the common refinement is a function of the reports and is
monotone in the coalescent state.

Not formalized here: the load part of the hypothesis, that the number of true blocks in each cell
after the merger aggregates the old loads over the cells it contains and drops by one for the
merged pair.

## Empirical status

None. The bodies here are lattice algebra of equivalence relations on a finite set: every
statement is an identity between joins and meets of supplied relations, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.MultiInterfaceOutcome

open MultiInterfaceClosure

noncomputable section

variable {n : ℕ}

/-- The equivalence relation identifying two individuals and nothing else: the merge of their two
singleton classes at the bottom state. -/
def pairRelation (x z : Fin n) : Coalescent.ER n :=
  Coalescent.merge ⊥ (Quotient.mk ⊥ x) (Quotient.mk ⊥ z)

/-- The identified pair is related. -/
theorem pairRelation_rel (x z : Fin n) : (pairRelation x z).r x z :=
  Coalescent.merge_rel ⊥ _ _ rfl rfl

/-- Folding a class onto itself changes nothing. -/
theorem mergeMap_self (ξ : Coalescent.ER n) (a c : Quotient ξ) :
    Coalescent.mergeMap ξ a a c = c := by
  by_cases hc : c = a
  · rw [hc, Coalescent.mergeMap_apply_self]
  · exact Coalescent.mergeMap_apply_of_ne ξ a a c hc

/-- A relation that relates the pair contains the pair relation. -/
theorem pairRelation_le_of_rel {ζ : Coalescent.ER n} {x z : Fin n} (hrelated : ζ.r x z) :
    pairRelation x z ≤ ζ := by
  by_cases hsame : x = z
  · subst hsame
    intro u v huv
    have hfold : Coalescent.mergeMap ⊥ (Quotient.mk ⊥ x) (Quotient.mk ⊥ x) (Quotient.mk ⊥ u) =
        Coalescent.mergeMap ⊥ (Quotient.mk ⊥ x) (Quotient.mk ⊥ x) (Quotient.mk ⊥ v) := huv
    rw [mergeMap_self, mergeMap_self] at hfold
    have hequal : u = v := Quotient.exact hfold
    subst hequal
    exact ζ.iseqv.refl u
  · exact merge_le_of_rel hsame hrelated

/-- **A merger is a join with one identified pair.** Merging the blocks of `x` and `z` is joining
the coalescent state with the relation that identifies `x` with `z`. -/
theorem merge_eq_sup_pairRelation (ξ : Coalescent.ER n) (x z : Fin n) :
    Coalescent.merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z) = ξ ⊔ pairRelation x z := by
  refine le_antisymm (fun u v huv ↦ ?_)
    (sup_le (Coalescent.le_merge ξ _ _)
      (pairRelation_le_of_rel (Coalescent.merge_rel ξ _ _ rfl rfl)))
  have hfold : Coalescent.mergeMap ξ (Quotient.mk ξ x) (Quotient.mk ξ z) (Quotient.mk ξ u) =
      Coalescent.mergeMap ξ (Quotient.mk ξ x) (Quotient.mk ξ z) (Quotient.mk ξ v) := huv
  have hleft : ξ ≤ ξ ⊔ pairRelation x z := le_sup_left
  have hright : pairRelation x z ≤ ξ ⊔ pairRelation x z := le_sup_right
  by_cases hblocks : Quotient.mk ξ x = Quotient.mk ξ z
  · rw [← hblocks, mergeMap_self, mergeMap_self] at hfold
    exact hleft (Quotient.exact hfold)
  · rcases (Coalescent.mergeMap_eq_iff ξ hblocks _ _).mp hfold with hsame | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact hleft (Quotient.exact hsame)
    · exact (ξ ⊔ pairRelation x z).iseqv.trans (hleft (Quotient.exact hu))
        ((ξ ⊔ pairRelation x z).iseqv.trans (hright (pairRelation_rel x z))
          (hleft (ξ.iseqv.symm (Quotient.exact hv))))
    · exact (ξ ⊔ pairRelation x z).iseqv.trans (hleft (Quotient.exact hu))
        ((ξ ⊔ pairRelation x z).iseqv.trans
          (hright ((pairRelation x z).iseqv.symm (pairRelation_rel x z)))
          (hleft (ξ.iseqv.symm (Quotient.exact hv))))

/-- **A report after a merger.** Reporting a merged state at an interface is joining the report
with the identified pair: the merger joins the two components containing `x` and `z`. -/
theorem observed_merge_eq (s : Fin n → Fin n) (ξ : Coalescent.ER n) (x z : Fin n) :
    observed s (Coalescent.merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)) =
      observed s ξ ⊔ pairRelation x z := by
  rw [merge_eq_sup_pairRelation, observed, observed, sup_right_comm]

/-- Moving the identified pair within classes of a relation does not change the join. -/
theorem sup_pairRelation_eq_of_rel (ζ : Coalescent.ER n) {x z x' z' : Fin n}
    (hx : ζ.r x x') (hz : ζ.r z z') : ζ ⊔ pairRelation x z = ζ ⊔ pairRelation x' z' := by
  have hrelated : ∀ {a c a' c' : Fin n}, ζ.r a a' → ζ.r c c' →
      (ζ ⊔ pairRelation a c).r a' c' := by
    intro a c a' c' ha hc
    have hleft : ζ ≤ ζ ⊔ pairRelation a c := le_sup_left
    have hright : pairRelation a c ≤ ζ ⊔ pairRelation a c := le_sup_right
    exact (ζ ⊔ pairRelation a c).iseqv.trans (hleft (ζ.iseqv.symm ha))
      ((ζ ⊔ pairRelation a c).iseqv.trans (hright (pairRelation_rel a c)) (hleft hc))
  exact le_antisymm
    (sup_le le_sup_left
      (pairRelation_le_of_rel (hrelated (ζ.iseqv.symm hx) (ζ.iseqv.symm hz))))
    (sup_le le_sup_left (pairRelation_le_of_rel (hrelated hx hz)))

/-- The common refinement is a function of the reports. -/
theorem commonRefinement_eq_of_reports {m : ℕ} (s : Fin m → Fin n → Fin n)
    {ξ ξ' : Coalescent.ER n} (hreports : ∀ j, observed (s j) ξ = observed (s j) ξ') :
    commonRefinement s ξ = commonRefinement s ξ' := by
  unfold commonRefinement
  exact congrArg iInf (funext hreports)

/-- The common refinement is monotone in the coalescent state. -/
theorem commonRefinement_mono {m : ℕ} (s : Fin m → Fin n → Fin n) {ξ η : Coalescent.ER n}
    (h : ξ ≤ η) : commonRefinement s ξ ≤ commonRefinement s η :=
  iInf_mono fun j ↦ observed_mono (s j) h

/-- **A merger changes every report only through the two cells.** Two coalescent states with the
same reports, merging two pairs of individuals that lie in the same cells of the common
refinement, have the same report at every interface after the merger. -/
theorem observed_merge_eq_of_cells {m : ℕ} (s : Fin m → Fin n → Fin n)
    {ξ ξ' : Coalescent.ER n} (hreports : ∀ j, observed (s j) ξ = observed (s j) ξ')
    {x z x' z' : Fin n} (hx : (commonRefinement s ξ).r x x')
    (hz : (commonRefinement s ξ).r z z') (j : Fin m) :
    observed (s j) (Coalescent.merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)) =
      observed (s j) (Coalescent.merge ξ' (Quotient.mk ξ' x') (Quotient.mk ξ' z')) := by
  rw [observed_merge_eq, observed_merge_eq, ← hreports j]
  exact sup_pairRelation_eq_of_rel _ (commonRefinement_le_observed s ξ j hx)
    (commonRefinement_le_observed s ξ j hz)

/-- **A merger changes the common refinement only through the two cells.** Under the hypotheses of
`observed_merge_eq_of_cells`, the two merged states have the same common refinement. -/
theorem commonRefinement_merge_eq_of_cells {m : ℕ} (s : Fin m → Fin n → Fin n)
    {ξ ξ' : Coalescent.ER n} (hreports : ∀ j, observed (s j) ξ = observed (s j) ξ')
    {x z x' z' : Fin n} (hx : (commonRefinement s ξ).r x x')
    (hz : (commonRefinement s ξ).r z z') :
    commonRefinement s (Coalescent.merge ξ (Quotient.mk ξ x) (Quotient.mk ξ z)) =
      commonRefinement s (Coalescent.merge ξ' (Quotient.mk ξ' x') (Quotient.mk ξ' z')) :=
  commonRefinement_eq_of_reports s fun j ↦ observed_merge_eq_of_cells s hreports hx hz j

end

end Descent.Pangenome.GraphCoalescent.MultiInterfaceOutcome
