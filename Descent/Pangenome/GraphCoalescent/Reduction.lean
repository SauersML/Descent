/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.Observation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The pangenome graph coalescent: Kingman's, entered at the graph's width

`Descent.Pangenome.GraphCoalescent.Visibility` shows that a graph's report of the panel's
coalescent is not a Markov chain.  This file gives the object that is.

The obstruction there had one source: the report cannot distinguish `⊥` from `graphKer s`,
and those two states have different numbers of available coalescences.  Every state at or
above `graphKer s` is free of it, because on that interval the report is the identity
(`Observation.observed_of_le`) and no information is being suppressed.  So the repair is not
to change the process but to change where it starts.  A pangenome graph does not observe a
coalescent of the `n` panel haplotypes.  It observes a coalescent of its own `w` nodes.

**The pangenome graph coalescent is the Kingman coalescent entered at `Linkage.width s`.**

That is the whole content, and the three theorems below are its three halves: the stratum is
closed (`graphState_of_covers`), the rates on it are Kingman's (`card_covers_graphState`),
and the count it starts from is the graph's width (`Observation.blocks_graphKer`).  Nothing
is postulated; the rate ladder is `Descent.Coalescent.StateSpace.card_covers` unchanged,
because a coalescent restricted to an up-set of its own state space is still itself.

## Why this is not a weakening

`Descent.Coalescent.Lumping` derives the block-count death process from the fact that the
number of available mergers depends on nothing but the block count.  That derivation never
used the bottom state, so it applies verbatim on the interval `[graphKer s, ⊤]`, and the
rates it produces are `d_k = k(k-1)/2` for the same reason as before.  What changes is only
the entrance point `k = w`, and `Descent.Pangenome.GraphCoalescent.Deficit` prices the
difference between entering at `w` and entering at `n`.

## Main results

- `GraphState`: the states a graph at interface `s` can express.
- `graphState_of_covers`: the coalescent never leaves them once it has entered them.
- `observed_eq_of_graphState`: on them the report is faithful, so there is nothing to lump.
- `card_covers_graphState`: **Kingman's ladder, unchanged**, on the graph's stratum.
- `blocks_le_width_of_graphState`: a graph state has at most `w` lineages, so `w` is the
  entrance point and not merely an upper bound reached at some unspecified time.
- `graphMeanTransitTime_eq`: **the headline.**  `E(T) = 2 - 2/w`, K-G (5.7) at the graph's
  own sample size.
-/

namespace Descent.Pangenome.GraphCoalescent

/-! ### The stratum a graph can express -/

/-- **A coalescent state a graph at interface `s` can express**: one at or above the merge
the graph was built with.

Empirical status: NOT AN EMPIRICAL CLAIM.  It names an up-set of `𝓔ₙ`; whether a real
genealogy has passed into it by a given time is the empirical question, and is not settled
here. -/
def GraphState {n : ℕ} (s : Fin n → Fin n) (ξ : Coalescent.ER n) : Prop := graphKer s ≤ ξ

/-- The graph's own floor is a graph state, and it is the least one.  This is the entrance
point of the process. -/
theorem graphState_graphKer {n : ℕ} (s : Fin n → Fin n) : GraphState s (graphKer s) := le_rfl

/-- **Being a graph state is being above the graph's floor, and that is the whole of it.**

`GraphState` names an up-set and adds no condition to the inequality that defines it, so the
predicate and the order relation are one proposition. The one-way reading this replaces
returned its own premise, which made the definitional content invisible: a consumer could
not rewrite with it, and nothing recorded that the predicate is *exactly* `graphKer s ≤ ξ`
rather than something implying it. -/
theorem graphState_iff {n : ℕ} {s : Fin n → Fin n} {ξ : Coalescent.ER n} :
    GraphState s ξ ↔ graphKer s ≤ ξ := Iff.rfl

/-- **The stratum is closed under the coalescent.**  Coalescence only coarsens, so a process
that has reached a graph state stays in graph states forever.  The graph coalescent is
therefore a process in its own right and not a fragment of one. -/
theorem graphState_of_covers {n : ℕ} {s : Fin n → Fin n} {ξ η : Coalescent.ER n}
    (h : GraphState s ξ) (hcov : Coalescent.Covers ξ η) : GraphState s η :=
  le_trans h hcov.1

/-- **On the stratum the report is faithful**, so there is no lumping to do and no criterion
to satisfy.  This is the exact sense in which the object below evades
`Descent.Pangenome.GraphCoalescent.Visibility`: the pathology was a report that hid
information, and here the report hides none.

Assumes: `GraphState s ξ`, i.e. the coalescent has reached the resolution the graph can
express. -/
theorem observed_eq_of_graphState {n : ℕ} {s : Fin n → Fin n} {ξ : Coalescent.ER n}
    (h : GraphState s ξ) : observed s ξ = ξ := observed_of_le h

/-! ### The ladder is Kingman's, unchanged

The point of restating `card_covers` here is that nothing is restated: a coalescent
restricted to an up-set of its own state space has the transition counts it always had, and
the theorem below is the corpus's own `Descent.Coalescent.StateSpace.card_covers` applied to
a graph state.  If the graph coalescent had needed its own rate ladder, it would not have
been a coalescent. -/

/-- **The graph coalescent's rate ladder is `d_k = k(k-1)/2`.**  The number of coalescences
available to a graph state is `C(k, 2)` in its block count, exactly as for any coalescent
state -- so `Descent.Coalescent.Lumping`'s derivation of the block-count death process
applies on the graph's stratum without change.

Assumes: `GraphState s ξ`.  The hypothesis is not used in the proof and is carried to say
which states the claim is being made about; the rate ladder does not know about `s`, and
that is the content. -/
theorem card_covers_graphState {n : ℕ} {s : Fin n → Fin n} {ξ : Coalescent.ER n}
    (_h : GraphState s ξ) :
    (Nat.card {η : Coalescent.ER n // Coalescent.Covers ξ η} : ℝ)
      = Coalescent.deathRate (Coalescent.blocks ξ) :=
  Coalescent.card_covers_eq_deathRate ξ

/-! ### The entrance point

A coarsening can only lose blocks, so every graph state has at most as many lineages as the
graph's floor -- and the floor has `Linkage.width s` of them.  That is what makes `w` the
graph coalescent's sample size rather than an incidental bound. -/

/-- A coarsening cannot gain blocks.  The surjection on classes is
`Descent.Coalescent.StateSpace.blockMap_surjective`; this is its cardinality. -/
theorem blocks_antitone {n : ℕ} {ξ η : Coalescent.ER n} (h : ξ ≤ η) :
    Coalescent.blocks η ≤ Coalescent.blocks ξ := by
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  letI : Fintype (Quotient η) := Fintype.ofFinite _
  have hsurj := Fintype.card_le_of_surjective _ (Coalescent.blockMap_surjective h)
  simpa [Coalescent.blocks, Nat.card_eq_fintype_card] using hsurj

/-- **A graph state has at most `w` lineages.**  The graph coalescent's sample size is the
interface's occupied width, and the panel's `n` never enters.

Assumes: `GraphState s ξ`. -/
theorem blocks_le_width_of_graphState {n : ℕ} {s : Fin n → Fin n} {ξ : Coalescent.ER n}
    (h : GraphState s ξ) : Coalescent.blocks ξ ≤ Linkage.width s := by
  have hb := blocks_antitone h
  rwa [blocks_graphKer] at hb

/-- **The graph coalescent's entrance rate is the pair count of the graph's nodes.**  A
coalescent leaves its starting state at the total rate `C(k, 2)`, one per pair of lineages
(`Descent.Coalescent.Rates.deathRate`, which is `Descent.Core.pairCount`).  For a pangenome
graph the lineages are nodes, so the process starts at `C(w, 2)` and not at `C(n, 2)`.

This is the group's arithmetic stated as a rate rather than as a count, and it is where the
entrance point stops being an observation about block numbers and becomes a number the
process runs at.  A study that assumes its data began coalescing at `C(n, 2)` is off by the
ratio the width law charges, before any time has passed. -/
theorem deathRate_blocks_graphKer {n : ℕ} (s : Fin n → Fin n) :
    Coalescent.deathRate (Coalescent.blocks (graphKer s))
      = Descent.Core.pairCount (Linkage.width s) := by
  rw [blocks_graphKer]
  rfl

/-! ### The object

Everything above is the statement that the process observed by a pangenome graph is a
Kingman coalescent whose sample size is `Linkage.width s`.  Below, that statement is used:
the mean time to the most recent common ancestor is K-G (5.7) evaluated at `w`. -/

/-- **The pangenome graph coalescent's mean transit time.**  `E(T_w)`, the expected time for
a graph at interface `s` to see its `w` nodes reduced to one, in units where a pair
coalesces at rate `1`.

Empirical status: DERIVED.  It is `Coalescent.meanTransitTime` -- K-G (5.7), off the rate
ladder and nothing else -- evaluated at `Linkage.width s` rather than at the panel size, and
`blocks_le_width_of_graphState` is why that is the right argument. -/
noncomputable def graphMeanTransitTime {n : ℕ} (s : Fin n → Fin n) : ℝ :=
  Coalescent.meanTransitTime (Linkage.width s)

/-- **K-G (5.7) at the graph's own sample size**: `E(T) = 2 - 2/w`.

Assumes: `1 ≤ Linkage.width s`, which holds for any nonempty panel by
`Descent.Pangenome.Linkage.Interface.width_pos`. -/
theorem graphMeanTransitTime_eq {n : ℕ} {s : Fin n → Fin n} (hw : 1 ≤ Linkage.width s) :
    graphMeanTransitTime s = 2 - 2 / (Linkage.width s : ℝ) :=
  Coalescent.meanTransitTime_eq_two_sub hw

/-- The graph's tree is shallower than two units however wide the interface is, because
K-G's bound is uniform in the sample size.  A pangenome graph cannot manufacture depth. -/
theorem graphMeanTransitTime_lt_two {n : ℕ} (s : Fin n → Fin n) :
    graphMeanTransitTime s < 2 := Coalescent.meanTransitTime_lt_two _

theorem graphMeanTransitTime_nonneg {n : ℕ} (s : Fin n → Fin n) :
    0 ≤ graphMeanTransitTime s := Coalescent.meanTransitTime_nonneg _

/-- **A faithful interface loses nothing.**  When the graph merges no two panel haplotypes,
its coalescent is the panel's, and the transit time is K-G (5.7) at `n`.

Assumes: `Function.Injective s` -- the interface separates every pair of panel haplotypes. -/
theorem graphMeanTransitTime_of_injective {n : ℕ} {s : Fin n → Fin n}
    (hs : Function.Injective s) :
    graphMeanTransitTime s = Coalescent.meanTransitTime n := by
  have hcard : Linkage.width s = n := by
    have h := Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hs
    simpa [Linkage.width, Finset.card_univ] using h
  rw [graphMeanTransitTime, hcard]

end Descent.Pangenome.GraphCoalescent
