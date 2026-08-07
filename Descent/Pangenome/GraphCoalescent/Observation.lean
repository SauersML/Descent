/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Interpolation
import Descent.Coalescent.Lumping
import Descent.Pangenome.Linkage.Interface

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# What a pangenome graph can see of a coalescent

Kingman's `n`-coalescent is a Markov chain on `𝓔ₙ`, the equivalence relations on the sample
(`Descent.Coalescent.StateSpace`).  A pangenome graph is not given the sample.  It is given
a panel that has already been merged: at an interface `s : Fin n → Fin n` two haplotypes
occupying the same graph state are, to the graph, the same object
(`Descent.Pangenome.Linkage.Interface`).  So a graph reporting on ancestry reports not the
coalescent state `ξ` but the coarsest thing it can distinguish, which is `ξ` joined with the
identity the interface has already destroyed.

That join is `observed`, and this file is its order theory.  Three facts do all the work
downstream and each is one line of lattice algebra:

* the graph never reports a coalescence that has not happened (`le_observed`) and always
  reports the merge it was built with (`graphKer_le_observed`);
* on states at or above `graphKer s` the report is faithful (`observed_of_le`), which is
  what `Descent.Pangenome.GraphCoalescent.Reduction` turns into a coalescent;
* below it the report is lossy, and `Descent.Pangenome.GraphCoalescent.Visibility` shows the
  loss is not of a kind a Markov chain can absorb.

## The one identification

`blocks_graphKer` is the bridge between the two developments this group joins:
`Coalescent.blocks (graphKer s) = Linkage.width s`.  The number of ancestral lineages the
graph starts with is the number of OCCUPIED graph states at the interface -- the `w` of the
width law, which `Descent.Pangenome.Linkage.Barrier` charges a builder for.  Neither side
could state this: the coalescent half has no interfaces and the linkage half has no
lineages.

## Empirical status

None.  Every declaration here is a statement about a complete lattice of equivalence
relations on a finite set.  What carries empirical weight is the reading of `s` as a real
graph's merge and of `graphKer s` as the resolution at which a real study observes ancestry;
those readings are stated in the docstrings and are not asserted of any dataset.
-/

namespace Descent.Pangenome.GraphCoalescent

/-! ### The merge the graph was built with -/

/-- The identity a pangenome graph has already destroyed at interface `s`: two sampled
haplotypes are one object to the graph exactly when they occupy the same graph state.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is `Setoid.ker` of the interface map, read as
a coalescent state; whether a given graph merges a given pair is the empirical question and
is not settled here. -/
def graphKer {n : ℕ} (s : Fin n → Fin n) : Coalescent.ER n := Setoid.ker s

/-- **Graph identity is interface identity, in both directions at once.**

`graphKer` is `Setoid.ker`, so the coalescent relation it carries and the equation between
graph states are the same proposition rather than two propositions that happen to agree.
Stating that as an `Iff` is what makes it usable: the two one-way readings this replaces
each handed back the premise they were given, so neither could be rewritten with, and a
consumer had to know which of the two names moved in the direction it needed. -/
theorem graphKer_rel_iff {n : ℕ} {s : Fin n → Fin n} {x y : Fin n} :
    (graphKer s).r x y ↔ s x = s y := Iff.rfl

/-- **A faithful interface has destroyed nothing.**  If no two panel haplotypes share a
graph state then `graphKer s` sits below every coalescent state, so joining with it changes
nothing. -/
theorem graphKer_le_of_injective {n : ℕ} {s : Fin n → Fin n} (hs : Function.Injective s)
    (ξ : Coalescent.ER n) : graphKer s ≤ ξ := by
  intro x y hxy
  have hxy' : s x = s y := hxy
  have hxy'' : x = y := hs hxy'
  subst hxy''
  exact ξ.iseqv.refl x

/-! ### The report

`observed s ξ` is what a graph built at interface `s` can say about the coalescent state
`ξ`: the coarsest relation that both records every coalescence that has happened and
respects the merge the graph carries.  In lattice terms it is the join, and that is not a
modelling choice -- it is forced, because a report must be an equivalence relation, must
contain `ξ`, and must contain `graphKer s`, and the join is the least such thing. -/

/-- **What a graph at interface `s` reports of the coalescent state `ξ`.**

Empirical status: NOT AN EMPIRICAL CLAIM.  The join is the least equivalence relation above
both arguments; the modelling content is the choice of `graphKer s` as the resolution, which
`Descent.Pangenome.Linkage.Interface` justifies and this file assumes. -/
def observed {n : ℕ} (s : Fin n → Fin n) (ξ : Coalescent.ER n) : Coalescent.ER n :=
  ξ ⊔ graphKer s

/-- The graph never denies a coalescence that has happened. -/
theorem le_observed {n : ℕ} (s : Fin n → Fin n) (ξ : Coalescent.ER n) : ξ ≤ observed s ξ :=
  le_sup_left

/-- The graph always asserts the merge it was built with. -/
theorem graphKer_le_observed {n : ℕ} (s : Fin n → Fin n) (ξ : Coalescent.ER n) :
    graphKer s ≤ observed s ξ := le_sup_right

/-- The report is monotone: more coalescence cannot be reported as less. -/
theorem observed_mono {n : ℕ} (s : Fin n → Fin n) {ξ η : Coalescent.ER n} (h : ξ ≤ η) :
    observed s ξ ≤ observed s η := sup_le_sup_right h _

/-- The report is the least state that dominates both the truth and the merge. -/
theorem observed_le {n : ℕ} {s : Fin n → Fin n} {ξ ζ : Coalescent.ER n} (hξ : ξ ≤ ζ)
    (hk : graphKer s ≤ ζ) : observed s ξ ≤ ζ := sup_le hξ hk

/-- **Where the report is faithful.**  At or above the graph's own merge, observing changes
nothing. -/
theorem observed_of_le {n : ℕ} {s : Fin n → Fin n} {ξ : Coalescent.ER n}
    (h : graphKer s ≤ ξ) : observed s ξ = ξ := sup_eq_left.mpr h

/-- And nowhere else: the report is faithful exactly on the states the graph can express. -/
theorem observed_eq_self_iff {n : ℕ} (s : Fin n → Fin n) (ξ : Coalescent.ER n) :
    observed s ξ = ξ ↔ graphKer s ≤ ξ := sup_eq_left

/-- **The graph's floor.**  Before any coalescence at all, a graph at interface `s` already
reports `graphKer s`: the merges the builder made are indistinguishable, to the graph, from
coalescences that have already occurred.  This is the whole difficulty in one equation. -/
@[simp] theorem observed_bot {n : ℕ} (s : Fin n → Fin n) : observed s ⊥ = graphKer s := by
  simp [observed]

@[simp] theorem observed_graphKer {n : ℕ} (s : Fin n → Fin n) :
    observed s (graphKer s) = graphKer s := sup_eq_left.mpr le_rfl

/-- Observing an observation says nothing new. -/
theorem observed_idem {n : ℕ} (s : Fin n → Fin n) (ξ : Coalescent.ER n) :
    observed s (observed s ξ) = observed s ξ := by
  simp [observed]

/-- **A faithful interface observes nothing.**  When `s` is injective the graph is a
relabelling of the panel and the report is the coalescent itself. -/
theorem observed_eq_of_injective {n : ℕ} {s : Fin n → Fin n} (hs : Function.Injective s)
    (ξ : Coalescent.ER n) : observed s ξ = ξ :=
  sup_eq_left.mpr (graphKer_le_of_injective hs ξ)

/-- **The bottom and the graph's floor are indistinguishable.**  Two coalescent states as far
apart as the chain's start and the interface's own merge produce the same report, and every
obstruction in this group is a consequence of this one line. -/
theorem observed_bot_eq_observed_graphKer {n : ℕ} (s : Fin n → Fin n) :
    observed s ⊥ = observed s (graphKer s) := by
  rw [observed_bot, observed_graphKer]

/-! ### The identification with `width`

`Descent.Pangenome.Linkage.Interface` counts the OCCUPIED graph states at an interface and
calls it `width`; `Descent.Coalescent.StateSpace` counts the classes of an equivalence
relation and calls it `blocks`.  They are the same number here, and the proof is that both
are the cardinality of the range of `s`. -/

/-- **The graph starts the coalescent at `w` lineages, not `n`.**
`blocks (graphKer s) = width s`.

This is the identification the two developments needed.  `width` is the `w` that
`Descent.Pangenome.Linkage.Barrier` charges an exact representation for; `blocks` is the `k`
that indexes Kingman's rate ladder `d_k = k(k-1)/2`.  A graph that merges its panel down to
`w` states hands the coalescent a sample of `w`, whatever `n` the study wrote down. -/
theorem blocks_graphKer {n : ℕ} (s : Fin n → Fin n) :
    Coalescent.blocks (graphKer s) = Linkage.width s := by
  have h1 : Coalescent.blocks (graphKer s) = Nat.card (Set.range s) :=
    Nat.card_congr (Setoid.quotientKerEquivRange s)
  have h2 : Nat.card (Set.range s) = Fintype.card (Set.range s) := Nat.card_eq_fintype_card
  have h3 : Fintype.card (Set.range s) = (Finset.univ.image s).card := by
    rw [← Set.toFinset_card, Set.toFinset_range]
  rw [h1, h2, h3]
  rfl

/-- The graph's lineage count never exceeds the panel's, because merging cannot create
haplotypes.  `Linkage.width_le_card`, read through `blocks_graphKer`. -/
theorem blocks_graphKer_le {n : ℕ} (s : Fin n → Fin n) :
    Coalescent.blocks (graphKer s) ≤ n := by
  rw [blocks_graphKer]
  simpa using Linkage.width_le_card s

end Descent.Pangenome.GraphCoalescent
