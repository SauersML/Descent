/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.BalancedFiberExtremum
import Descent.Pangenome.GraphCoalescent.ConnectionClockPathLaw
import Descent.Pangenome.GraphCoalescent.ConnectionClockStochasticOrder
import Descent.Pangenome.GraphCoalescent.ConnectivityClockTable
import Descent.Pangenome.GraphCoalescent.LeadingCoefficientCorollaries
import Descent.Pangenome.GraphCoalescent.ReportedConnectionClock
import Descent.Pangenome.GraphCoalescent.ReportedConnectionTies
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulant
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantDegree
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantCorpus
import Descent.Pangenome.GraphCoalescent.Conservation
import Descent.Pangenome.GraphCoalescent.LambdaLoadClosure
import Descent.Pangenome.GraphCoalescent.MultiInterfaceGenerator
import Descent.Pangenome.GraphCoalescent.FirstConnectionLaw
import Descent.Pangenome.GraphCoalescent.HiddenClockExample
import Descent.Pangenome.GraphCoalescent.HiddenStateChain
import Descent.Pangenome.GraphCoalescent.HiddenLoadFiltering
import Descent.Pangenome.GraphCoalescent.HiddenLoads
import Descent.Pangenome.GraphCoalescent.HiddenLumpability
import Descent.Pangenome.GraphCoalescent.LahWeights
import Descent.Pangenome.GraphCoalescent.LeadingCoefficient
import Descent.Pangenome.GraphCoalescent.LumpingUnorderedPair
import Descent.Pangenome.GraphCoalescent.LumpingVisibleRates
import Descent.Pangenome.GraphCoalescent.MinimalRefinement
import Descent.Pangenome.GraphCoalescent.MultiInterfaceClosure
import Descent.Pangenome.GraphCoalescent.MultiInterfaceLoads
import Descent.Pangenome.GraphCoalescent.MultiInterfaceOutcome
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionExamples
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLaw
import Descent.Pangenome.GraphCoalescent.MultiplicativeObservation
import Descent.Pangenome.GraphCoalescent.PartitionLatticeMobius
import Descent.Pangenome.GraphCoalescent.RankedHistoryLaw
import Descent.Pangenome.GraphCoalescent.VisibleIntensityClock

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
  and its mean connection time `2/3`, `example_total_rate`, `example_mean_connection_time`; as a
  continuous-time statement, `S(t) = e^{-3t}/2 + e^{-t}/2`
  (`HiddenClockExample.exampleSurvival_eq`) with integral `2/3` (`integral_exampleSurvival`), and
  the three clocks `2/3`, `1` and `4/3` differ (`three_clocks_differ`).
* Theorem C, (C1) and (C5): `Conservation`. A silent merger lowers the hidden excess by one and a
  visible merger keeps it (`hiddenExcess_of_invisible`, `hiddenExcess_of_visible`); along any
  chain of covers from the singletons to the root exactly `n - w` steps are silent and `w - 1`
  are visible (`card_silentSteps_visibleSteps`); a finer interface merge connects its report no
  later, on every path (`connectedTimes_subset`).
* Theorem C, (C2)-(C4): `VisibleIntensityClock`. The visible intensity dominates the death rate
  of the report width, `λ_vis ≥ d_r` (`deathRate_le_visibleIntensity`), and Kingman's generator
  sends `2 - 2/r` to `-λ_vis/d_r` (`kingmanGenerator_meanTransitTime_observed`). (C3) in
  first-step form: `meanTransitTime_sub_meanConnectionTime`. (C4):
  `2/(n - w + 1) - 2/n ≤ E τ_q ≤ 2 - 2/w`, strict above when `n > w ≥ 2`,
  `two_div_sub_two_div_le_meanConnectionTime_bot`, `meanConnectionTime_bot_le_two_sub`,
  `meanConnectionTime_bot_lt`; started at `q` the clock is Kingman's `2 - 2/w`,
  `meanConnectionTime_graphKer`. (C2) in Laplace-transform order:
  `kingmanLaplace_le_connectionLaplace`. The law of the connection time built on the corpus
  Kingman holding and jump laws has these first-step values as its integrals, so (C2)-(C4) hold
  for that law: `ConnectionClockPathLaw.lintegral_coe_connectionTimeLaw_bot_le`,
  `ofReal_le_lintegral_coe_connectionTimeLaw_bot`,
  `kingmanLaplace_width_le_lintegral_exp_connectionTimeLaw_bot`. Toward the stochastic order of
  (C2), the Kingman transit law is stochastically increasing in the width
  (`ConnectionClockStochasticOrder.survivalAt_kingmanTransitLaw_le_succ`).
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
* Theorem D, (D2)-(D3), the connectivity cumulant: `ConnectivityCumulant`. The Möbius
  coefficients over the partitions of a nonempty set sum to one on a singleton and to zero
  otherwise (`sum_mobiusCoefficient_finpartition`); the refinements of a partition carry
  `∏_C A_|C|(z)` (`sum_le_eq_prod_lahPolynomial`); (D3) is
  `connectivityCumulant_eq_sum_connected`, with nonnegative integer coefficients
  (`coeff_connectivityCumulant_nonneg`) depending only on the fiber sizes
  (`connectivityCumulant_eq_cumulantOfSizes`), of degree at most `n - w + 1`
  (`ConnectivityCumulantDegree.natDegree_connectivityCumulant_le`). In the corpus vocabulary of
  coalescent states, with `graphKer` and `observed`:
  `ConnectivityCumulantCorpus.connectivityCumulant_graphKer_eq_sum_observed`,
  `natDegree_connectivityCumulant_graphKer_le`. Mathlib's incidence-algebra Möbius function of the
  partition lattice is `(-1)^(|σ|-1) (|σ|-1)!` at every order
  (`PartitionLatticeMobius.mu_finpartition_top`).
* Theorem D, (D4), the ranked history law: `RankedHistoryLaw`. The law of the jump chain after
  `n - k` jumps is `a_{n,k} ∏_B |B|!` (`rankedHistoryLaw`, `blockLaw_toReal_eq_absoluteProb`),
  through the weighted cover count `2 Σ_{ξ ≺ η} w(ξ) = (n - |η|) w(η)`
  (`two_mul_sum_rankWeight_covers`).
* Theorem D, (D5)-(D6), the first-connection law: `FirstConnectionLaw`. The probability that the
  report of the jump chain's `k`-block state is connected is `a_{n,k} [z^k] C_q(z)`
  (`reportConnectedProbability_eq_connectedByLevel`), and the report first connects at the
  `b`-block level with probability `F_b - F_{b+1}` (`firstConnectionProbability_eq_sub`).
* Theorem A, the hidden jump chain: `HiddenStateChain`. The hidden state after one jump has jump
  probabilities `C(L_C, 2) / C(K, 2)` and `L_C L_D / C(K, 2)` depending on the hidden state alone
  (`hiddenKernel_invisibleTarget_toReal`, `hiddenKernel_visibleTarget_toReal`), and the hidden
  trajectory is a Markov chain with that kernel (`hiddenChainLaw_succ`).
* Theorem D, (D5)-(D9) in continuous time: `ReportedConnectionClock`. On the product of the
  jump-chain trajectory law and independent exponential holding times, (D5) is `connectedProb_eq`,
  and the Laplace transform, mean and second moment of the connection time are
  `connectionTime_laplace`, `connectionTime_mean` and `connectionTime_secondMoment`, through
  `Σ_{k=b+1}^n 1/C(k,2) = 2/b - 2/n` (`sum_Ioc_one_div_deathRate`). The two versions of (D5) and
  (D6) agree, and the mean of the trajectory clock is the mean of the first-step law
  (`ReportedConnectionTies.connectedProb_eq_reportConnectedProbability`,
  `stoppingProb_eq_firstConnectionProbability`,
  `connectionTime_mean_eq_lintegral_connectionTimeLaw`).
* Theorem D, the exact table of §6: `ConnectivityClockTable`. The cumulants
  `6z + 4z²`, `24z + 30z² + 6z³`, `24z + 32z² + 8z³`, `24z + 20z²`,
  `720z + 1656z² + 928z³ + 144z⁴` and the means `2/3, 1/2, 7/18, 17/18, 92/225` of the fiber sizes
  `(1,2), (1,3), (2,2), (1,1,2), (2,2,2)`, and the different means of `(1,3)` and `(2,2)`:
  `meanConnectionTime_one_three_ne_two_two`.
* Theorem F, the ingredients of (F1): `MultiplicativeObservation`. While the reports agree, the
  comparison rates exceed the visible rates by at most `J/n` in scaled time
  (`pairProductSum_sub_div_sq_le`) and Kingman's total scaled rate is at most `1/2`
  (`deathRate_div_sq_le_half`); a finite coupled chain with separation hazard at most `J/n` and
  deficit drift at most `1/2` per step separates by step `m` with probability at most
  `m(m - 1)/(4n)` (`separationMass_le`), which at the rings of a rate-one Poisson clock becomes
  `min {1, U²/(4n)}` (`poissonMixture_le_min`).
* Theorem F, (F4): `MultiplicativeConnectionLaw`. The arbitrary-order Möbius identity of the
  partition lattice, `Σ_{σ ≥ τ} (-1)^(|σ|-1) (|σ|-1)! = [τ = ⊤]` (`sum_topMobius_blocks_ge`),
  and the probability that the edges rung by time `u` connect the fibers is
  `Σ_σ (-1)^(|σ|-1) (|σ|-1)! e^(-u κ_σ)` (`connectionProbability_eq_mobius_sum`). Two fibers give
  `1 - e^(-u p₀ p₁)` (`connectionProbability_two`), and three equal fibers give
  `Pr(T_p > u) = 3 e^(-2u/9) - 2 e^(-u/3)` (`connectionSurvival_three_equal`):
  `MultiplicativeConnectionExamples`.
* §10, several interfaces sharing one genealogy: `MultiInterfaceClosure`. The common refinement
  of the reports determines every report (`observed_commonRefinement`), and two labeled
  configurations with the same hidden load in every cell of the common refinement offer equally
  many mergers into every lumped target: `card_mergers_eq_of_cellLoad_eq`, and with the corpus
  setoids `card_blockMergers_eq`. Two coalescent states with the same reports, merging pairs in
  the same cells, have the same reports and common refinement afterwards:
  `MultiInterfaceOutcome.observed_merge_eq_of_cells`, `commonRefinement_merge_eq_of_cells`. With
  the cell loads the closure holds with nothing assumed on how a merger acts: two coalescent
  states with the same lumped state offer equally many mergers into every lumped state,
  `MultiInterfaceLoads.card_blockMergers_eq_of_multiState_eq`, through
  `multiState_merge_eq_of_cells`; the outcome map is built from the mergers themselves in
  `MultiInterfaceGenerator.card_blockMergers_eq_lumpedMergerCount`.
* §10, the Λ-coalescent closure: `LambdaLoadClosure`. The sets of true blocks with a prescribed
  profile number `∏_C C(L_C, h_C)` (`card_subsets_with_profile`), and the profiles of size `b`
  account for `C(K, b)` (`sum_prod_choose_eq_choose`); the total labeled rate into a lumped target
  is `lumpedLambdaRate` of the loads (`sum_mergerRates_eq_lumpedLambdaRate`), so two
  configurations with the same loads offer the same total rate into every target
  (`sum_mergerRates_eq_of_cellLoad_eq`), and the joined load is `Σ L_C - b + 1`
  (`card_touchedBlocks_after_merger`).
* §9, exact filtering and likelihood: `HiddenLoadFiltering`. For a finite hidden jump process
  watched through a report map, the killed propagator solves `P' = P Q_R`
  (`hasDerivAt_killedPropagator`), carries no mass out of the report
  (`killedPropagator_apply_eq_zero`) and satisfies the first-jump equation
  (`killedPropagator_apply_eq_firstJump`), and the final mass of the filter is the likelihood of
  the visible history (`filterPosterior_dotProduct_one`, `filterPosterior_single_dotProduct_one`).
  For the load chain the killed generator carries the internal rates `C(L_C, 2)` and `-C(K, 2)`
  (`killedGenerator_mulVec_loadGenerator`), and a visible merger transfers mass with weight
  `L_C L_D` (`transferMatrix_mulVec_loadGenerator`).
* Theorem E, (E1): `LeadingCoefficient`. For `w ≥ 2` positive fiber sizes,
  `[z^{n - w + 1}] C_c(z) = 2 (∏_i c_i) (2n - w)! / (2n - 2w + 2)!` (`coeff_cumulantOfSizes`, at an
  interface `coeff_connectivityCumulant_top`), through the derivative identity of the reflected
  cumulant and the recursion `(w - 1) L_w(c) = Σ_{i ≠ j} c_i c_j L_{w - 1}(c^{(ij)})`
  (`coeff_deficitCumulant_recursion`).
* Theorem E, the extremal statement: `BalancedFiberExtremum`. Among positive fiber sizes of a
  fixed total the product is maximal exactly on balanced profiles
  (`prod_maximal_iff_isBalancedFibers`), read at the loads of an interface in
  `prod_hiddenLoad_bot_le_of_isBalancedFibers`; the leading coefficient is maximal exactly on
  balanced profiles
  (`LeadingCoefficientCorollaries.leadingCoefficient_maximal_iff_isBalancedFibers`), and (E1)
  agrees with the table rows (`table_two_two_two`).

Scope. Theorem A is proved as cover counts with Kingman's unit rate per cover, and under the
corpus jump chain the hidden state is a Markov chain (`HiddenStateChain.hiddenChainLaw_succ`); the
continuous-time holding times are not constructed.
The survival function of (A4) is `α e^{tQ} 𝟙` of the killed generator, and the identification of
the mean with its integral is not formalized. Theorem B is proved as the algebra of the visible
rates and of the survival
derivatives through the killed generator. With at least three components a strong lumping in
Rosenblatt's form determines every visible rate and the hidden state
(`LumpingVisibleRates.visibleRate_eq_of_lumping`, `hiddenState_eq_of_lumping`); at two components
a strong lumping determines the unordered pair of loads through their sum and product
(`LumpingUnorderedPair.unorderedPair_eq_of_lumping`), and the survival function as a semigroup is
not formalized. The table rows of §6 compute the cumulants from `cumulantOfSizes`
and evaluate transcriptions of (D4)-(D6) and (D8) at the tabulated fiber sizes. In the
Λ-coalescent closure the dependence of a merger's lumped outcome on its profile alone is a
hypothesis on the outcome map. The
connection clock of Theorem C is defined as the first-step solution of the backward equation, and
(C3) is Dynkin's identity for that equation; its identification with the path expectation of the
continuous-time chain is not formalized, and (C2) is proved in Laplace-transform order, which
does not imply the stochastic order of the quantile coupling. (D4) is proved by Kingman's backward
recursion, without enumerating ranked histories. §9 is proved for a finite hidden jump process
given by its generator, with the load chain's generator `loadGenerator` written from the rates of
Theorem A. (E1) is proved from the Möbius sum rather than the ranked-history law. The stopping law
(E2), (F2) and (F3) are not yet proof-checked. (D7)-(D9) are proved for the connection time
defined as the sum of the holding times above the stopping level; its identification with the
first hitting time of the report path is not proved. Of (F1), the coupled skeleton chain,
the path-level coupling inequality and the identification with path measures on càdlàg paths are
not yet recorded here. (F4) is proved for the finite random graph
of edges rung by time `u`, entering the clocks through their distribution functions.
-/

end Descent.Program
