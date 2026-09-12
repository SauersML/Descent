/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.Conservation
import Descent.Pangenome.GraphCoalescent.HiddenLoads
import Descent.Pangenome.GraphCoalescent.HiddenLumpability
import Descent.Pangenome.GraphCoalescent.LahWeights
import Descent.Pangenome.GraphCoalescent.MinimalRefinement
import Descent.Pangenome.GraphCoalescent.MultiInterfaceClosure

namespace Descent.Program

/-!
# The hidden-lineage clock of a pangenome

Reference: the research note of 11 September 2026, "The hidden-lineage clock of a pangenome: exact
Markov closure, a connectivity cumulant, and a multiplicative-coalescent boundary layer", against
this archive. Theorem and equation numbers below are the note's own. Every module listed was
checked on the pinned toolchain with axioms limited to `propext`, `Classical.choice` and
`Quot.sound`. Where a statement is proved in a narrower form, the scope line says so and the
module docstring repeats it.

## The object

A pangenome interface `q = graphKer s` applied to an existing genealogy is an observation, not a
new genealogy started at the interface width. The corpus report `observed s ξ = ξ ⊔ graphKer s`
(`Descent.Pangenome.GraphCoalescent.Observation`) is not Markov when `2 ≤ width s < n`
(`Visibility.not_observablyMarkov_of_width_lt`), and `Reduction` restarts the coalescent at `q`,
whose mean transit time `2 - 2/w` (`graphMeanTransitTime_eq`) is a different clock. The note
restores, for each reported component `C`, the number `L_C` of unresolved ancestral lineages
inside it.

## Theorems

* Theorem A, the hidden-load closure: `HiddenLoads`, `HiddenLumpability`. The load
  `hiddenLoad s ξ C` counts the true blocks inside a report component; the loads add up to the
  true block count (`sum_hiddenLoad`) and start at the fiber sizes (`hiddenLoad_bot`). Every
  cover is invisible, keeping the report and lowering one load by one, or visible, merging two
  components into the load `a + b - 1`: `observed_eq_or_covers`, `hiddenLoad_merge_of_rel_self`,
  `hiddenLoad_merge_of_not_rel_self`. (A1) `card_invisibleCovers`, (A2) `card_visibleCovers`,
  (A3) `sum_choose_two_hiddenLoad_add_sum_pairs`. Rosenblatt's criterion for the hidden state:
  two coalescent states with the same hidden state have equally many covers into every hidden
  state, `card_covers_hiddenState_eq`. (A4): the loads and rates of the three-haplotype example
  and its mean connection time `2/3`, `example_total_rate`, `example_mean_connection_time`.
* Theorem C, (C1) and (C5): `Conservation`. A silent merger lowers the hidden excess by one and a
  visible merger keeps it (`hiddenExcess_of_invisible`, `hiddenExcess_of_visible`); along any
  chain of covers from the singletons to the root exactly `n - w` steps are silent and `w - 1`
  are visible (`card_silentSteps_visibleSteps`); a finer interface merge connects its report no
  later, on every path (`connectedTimes_subset`).
* Theorem B, the coarsest predictive Markov refinement: `MinimalRefinement`. (B1) with three or
  more components the visible merger rates `ρ_CD = L_C L_D` determine every load:
  `load_sq_eq_visibleRates`, `load_eq_of_visibleRates_eq`, `visibleRates_eq_iff`. (B2) with two
  components the first two survival derivatives are `-ab` and `(ab)² + ab(a + b - 2)/2` and
  determine the unordered pair of loads and not its order: `twoComponentGenerator_one`,
  `twoComponentGenerator_twice_one`, `survivalDerivatives_eq_iff`. Sufficiency at two components:
  `twoComponentGenerator_swap`. Minimality: `refines_loads`, `refines_unorderedPair`.
* Theorem D, (D1), the Lah weights: `LahWeights`. The Lah numbers satisfy
  `L(m, j) j! = m! C(m - 1, j - 1)` (`lahNumber_mul_factorial`), and the partitions of a finite
  set weighted by `∏_B |B|!` and counted by blocks are the coefficients of `A_m`:
  `sum_blockWeight_card_eq_lahNumber`, `sum_blockWeight_X_pow_eq_lahPolynomial`. The parts of a
  coalescent state read as a finite partition are its `Coalescent.blocks`:
  `card_parts_ofSetoid`.
* §10, several interfaces sharing one genealogy: `MultiInterfaceClosure`. The common refinement
  of the reports determines every report (`observed_commonRefinement`), and two labeled
  configurations with the same hidden load in every cell of the common refinement offer equally
  many mergers into every lumped target: `card_mergers_eq_of_cellLoad_eq`, and with the corpus
  setoids `card_blockMergers_eq`.

Scope. Theorem A is proved as cover counts with Kingman's unit rate per cover: the
continuous-time chain, the survival function of (A4) and the probabilistic statement of strong
lumpability are not constructed, and the mean `2/3` of (A4) is the first-step arithmetic of the
counted rates. Theorem B is proved as the algebra of the visible rates and of the survival
derivatives through the killed generator. The step from a strong lumping for every initial
labeled state to these rates, which is Rosenblatt's criterion applied to the chain of Theorem A,
and the survival function as a semigroup are not formalized. In §10 the dependence of a merger's
outcome on the two merging cells alone is a hypothesis on the outcome map. Theorem C (the
domination (C2), the Dynkin identity (C3) and the bounds (C4)), Theorem D (the connectivity
cumulant (D2)-(D3), the stopping law (D4)-(D9) and the exact table), Theorem E, Theorem F, the
filter of §9 and the Λ-coalescent extension of §10 are not yet proof-checked.
-/

end Descent.Program
