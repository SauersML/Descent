/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.AncestralDecision
import Descent.Pangenome.AncestralLocality.ClosureReachability
import Descent.Pangenome.AncestralLocality.LightConeApproximationBound
import Descent.Pangenome.AncestralLocality.ReachabilityClosureTie
import Descent.Pangenome.AncestralLocality.OneAlleleDuality
import Descent.Pangenome.AncestralLocality.SupportChainDynkin
import Descent.Pangenome.AncestralLocality.FeatureKingmanLimit
import Descent.Pangenome.AncestralLocality.AnnotatedKernel
import Descent.Pangenome.AncestralLocality.DecisionDualMoments
import Descent.Pangenome.AncestralLocality.CylinderWindowProjection
import Descent.Pangenome.AncestralLocality.CircuitCoupling
import Descent.Pangenome.AncestralLocality.SupercriticalLowerBound
import Descent.Pangenome.AncestralLocality.SupportChainMultiset
import Descent.Pangenome.AncestralLocality.SupercriticalUpperBound
import Descent.Pangenome.AncestralLocality.FeatureKingmanLimitLineages
import Descent.Pangenome.AncestralLocality.SupercriticalSprinkling
import Descent.Pangenome.AncestralLocality.InfiniteGenomeRate
import Descent.Pangenome.AncestralLocality.SupercriticalSecondMoment
import Descent.Portability.ResamplingInfiniteGenome
import Descent.Portability.ResamplingWindowSemigroup
import Descent.Portability.ResamplingWindowConsistency
import Descent.Pangenome.AncestralLocality.CoalescentDualSemigroup
import Descent.Pangenome.AncestralLocality.HeredityKernel
import Descent.Pangenome.AncestralLocality.HereditaryClosure
import Descent.Pangenome.AncestralLocality.OperationalAutonomy
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality
import Descent.Pangenome.AncestralLocality.JointNonautonomy
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Descent.Pangenome.AncestralLocality.LocalityBounds
import Descent.Pangenome.AncestralLocality.LocalityCoupling
import Descent.Pangenome.AncestralLocality.LocalityCouplingBounds
import Descent.Pangenome.AncestralLocality.LocalityTransition
import Descent.Pangenome.AncestralLocality.CylinderSamplingAlgebra
import Descent.Pangenome.AncestralLocality.CylinderSamplingPolynomials
import Descent.Pangenome.AncestralLocality.RandomClosure
import Descent.Pangenome.AncestralLocality.RootExchangeability
import Descent.Pangenome.AncestralLocality.SamplingDuality
import Descent.Pangenome.AncestralLocality.SupercriticalBranches
import Descent.Portability.AncestralForwardGenerator
import Descent.Portability.AncestralSamplingLimit
import Descent.Portability.AncestralWitnessDrift
import Descent.Pangenome.AncestralLocality.SupercriticalReach
import Descent.Pangenome.AncestralLocality.DecisionJumpExpansion
import Descent.Pangenome.AncestralLocality.DecisionWindowJumps
import Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup
import Descent.Pangenome.AncestralLocality.JumpFellerSemigroup
import Descent.Pangenome.AncestralLocality.DecisionDysonDual

namespace Descent.Program

/-!
# Ancestral locality

Reference: the research note of 11 September 2026, "Ancestral locality: a heredity-first
foundation for pangenomic population theory", against this archive. Theorem and equation numbers
below are the note's own. Every module listed was checked on the pinned toolchain with axioms
limited to `propext`, `Classical.choice` and `Quot.sound`. Where a statement is proved in a
narrower form, the scope line says so and the module docstring repeats it.

## The object

The hereditary closure of an observation is the least additional genomic information that makes
the observation reproductively autonomous. In the neutral compatibility-copying model it is graph
reachability, so it undergoes a percolation transition while every single feature keeps the
ordinary Wright-Fisher law; a support-aware ancestral decision circuit gives genome-size
independent complexity bounds and a quantitative light cone.

## Theorems

* Theorem 1, the minimal hereditary context: `HereditaryClosure`, on the kernels and observations
  of `HeredityKernel`: the reproduction operator (2.1) maps the simplex to itself
  (`reproduce_mem_stdSimplex`), and hereditary autonomy (2.2) has a block form
  (`hereditarilyAutonomous_iff`). The refinement `Φ_K` of (3.1) (`refinement_rel_iff`) reaches a
  fixed point within `|H| - |P|` steps (3.2) (`hereditaryClosure_eq_iterate`), and `P_*` is the
  greatest autonomous partition below `P` (`isGreatest_hereditaryClosure`). For an observation
  `π` the closure map is hereditarily autonomous (`hereditarilyAutonomous_closureMap`), and every
  hereditarily autonomous observation that determines `π` determines it
  (`ker_le_hereditaryClosure_of_hereditarilyAutonomous`). §3.1: relabeling the states transports
  the closure (`hereditaryClosure_transportKernel`). §3.2 in the vocabulary of kernels:
  `exists_autonomous_pair_not_autonomous_join`.
* §2.2, the remark on ancestry: `AnnotatedKernel`. The state marginal of an annotated kernel with
  correspondence witnesses is a heredity kernel (`isHeredityKernel_stateMarginal`), and two
  annotated kernels with one state marginal, hence one hereditary closure, can have different
  witness laws (`performed_visible_same_closure_different_witnessLaw`).
* Theorem 2, the operational characterization: `OperationalAutonomy`. For a kernel that does not
  see the order of the parents, `π` is hereditarily autonomous exactly when `π_# R_K(p)` depends
  only on `π_# p` (`hereditarilyAutonomous_iff_pushforward_reproduce_determined`); when autonomy
  fails, two laws with one observed marginal have different observed next generations
  (`exists_pushforward_eq_reproduce_ne_of_not_hereditarilyAutonomous`). Every compatibility kernel
  is a heredity kernel (`isHeredityKernel_compatibilityKernel`), a single feature is autonomous
  (`hereditarilyAutonomous_feature`), and the witness observation `(a, b)` is not
  (`witness_not_hereditarilyAutonomous`).
* Theorem 3, every feature is exactly neutral: `CompatibilityNeutrality`. With the ordered child
  (4.1), its exchange kernel (4.2) and the compatibility kernel `K_G` (4.3), (4.4) holds for every
  checking graph (`compatibilityKernel_marginal`) and its population form `(R_{K_G}(p))_k = p_k`
  (`featureMass_reproduce_compatibilityKernel`). Two sampled lineages at one feature share a
  source with probability `1/N` per generation, so `P(T_N > m) = (1 - 1/N)^m` and
  `P(T_N > ⌊tN⌋) → e^{-t}` (`FeatureKingmanLimit.featurePairSurvival_eq`,
  `tendsto_featurePairSurvival`); for `k` lineages the block-counting chain has Kingman's rates on
  the `N`-generation scale (`FeatureKingmanLimitLineages.tendsto_mul_blockTransition_pred`). §4.1:
  the finite-population kernel `Q_N` (4.5)
  keeps every allele law and is a probability vector for `R ≤ N`, and the offspring count at a
  feature is `Binomial(N, p_k)` (4.6) (`offspringCount_eq_binomial`). §5.2: the eight-state witness
  has one observed law and drifts `-1/4` and `0` (`witness_drift`), so no observed transition law
  predicts both and the observation `(a, b)` is not autonomous
  (`witness_no_observed_transition_law`, `witness_not_autonomous`).
* Theorem 4, closure is reachability: `ClosureReachability`. For `|A| ≥ 2` one refinement step
  turns `P_{π_A}` into `P_{π_{A ∪ N⁺(A)}}`, (5.2) (`refinementStep_agreeOn`), with the difference
  formula (5.3) (`sum_checkKernel_mixedBlocks_sub`, `mixedBlocks_sub_pos`); iterating gives (5.1),
  the closure is the observation on `Reach_G(A)` (`iterate_refinementStep_agreeOn_eq_reach`), and
  an observation of at most one feature is its own closure
  (`iterate_refinementStep_agreeOn_of_card_le_one`). §5.1 (5.4): on a connected graph, the path
  graph included, every query of two or more features has full-genome closure
  (`iterate_refinementStep_eq_univ_of_connected`, `iterate_refinementStep_eq_univ_path`), and the
  pair observation is not autonomous (`not_autonomous_pair_path`). In the vocabulary of Theorem 1,
  `ReachabilityClosureTie`: the two refinement steps are one setoid
  (`refinementStep_eq_refinement`), the closure of `π_A` for `|A| ≥ 2` is `π_{Reach_G(A)}`
  (`hereditaryClosure_ker_observeOn`), and `agreeOn (directedReach r A)` is the greatest
  autonomous partition refining `agreeOn A` (`isGreatest_agreeOn_directedReach`).
* §3.2, autonomous observations are not closed under joins: `JointNonautonomy`. On the
  eight-state witness both single features are autonomous and their joint observation is not
  (`autonomous_features_joint_not_autonomous`).
* Theorem 5, the locality transition: `LocalityTransition`. For `G(m, α/m)` as a finite law on
  edge sets, the expected reach of `A` satisfies `E|Reach(A)| ≤ |A|/(1 - α)` for `0 ≤ α < 1` and
  every genome size (`graphExpect_card_reach_le`), through the count of present simple paths
  (`card_reach_singleton_le_sum`, `graphExpect_card_presentPaths`). §6.1: the rates `β / deg(i)`
  are positive exactly on present edges. For `α > 1` the survival equation `s = 1 - e^{-αs}` has a
  unique root in `(0, 1)` (`existsUnique_survival_root`, `giantFraction_mem_Ioo`). Given the giant
  component theorem (`GiantComponentLaw`, proved for `0 ≤ α < 1` by `giantComponentLaw_of_lt_one`),
  the reach fraction is near `0` or `giantFraction α` with probability tending to one
  (`SupercriticalReach.tendsto_graphProb_reach_near_zero_or_giant`). By exchangeability of the
  roots (`RootExchangeability.choose_mul_graphProb_disjoint_bigSet`) the two branches carry the
  weights `(1 - s)^k` and `1 - (1 - s)^k` (`SupercriticalBranches.tendsto_graphProb_reach_small`,
  `tendsto_graphProb_reach_giant`). With the degree-normalized rates the closure itself is the
  observation on the reach of `G(m, α/m)`, so (6.1) bounds the closure
  (`RandomClosure.iterate_refinementStep_degreeRate`, `graphExpect_card_directedReach_le`).
  Without the giant component theorem, for `α > 1` every feature eventually lies in a component
  of at least `K` features with probability at least `s - ε`
  (`SupercriticalLowerBound.eventually_graphProb_card_reach_ge`), so large components hold at
  least `(s - ε) m` features in expectation (`eventually_graphExpect_card_large_ge`). The upper
  half holds outright: for queries of at most `k` features
  `limsup_m P(|Reach(A)| ≥ εm) ≤ 1 - (1 - s)^k`
  (`SupercriticalUpperBound.limsup_graphProb_card_reach_ge_le`), and sprinkling merges the large
  components (`SupercriticalSprinkling.tendsto_graphProb_exists_card_reach_ge`), given that the
  number of features in large components concentrates, whose second moment is bounded
  (`SupercriticalSecondMoment.graphExpect_largeCount_sq_le`).
* §4.1 and §7.1, the diffusion generator: `AncestralForwardGenerator`. For `c = 1` the
  finite-population chain (4.5) on the `N`-generation scale has generator (7.1) on polynomial
  observables (`tendsto_nextGenerationMean`), and on the eight-state witness the derivatives of
  (5.5) are `-1/4` and `0` (`AncestralWitnessDrift.witness_generator`). The generator is reached
  by pure jumps on sampling observables: a resampling jump `p ↦ ε δ_x + (1 - ε) p` and a decision
  jump `p ↦ ε R_{K_T}(p) + (1 - ε) p` deviate from the backward generator by explicit `O(ε)`
  bounds (`DecisionJumpExpansion.abs_resample_sub_le`, `abs_decision_sub_le`). On a finite window
  these jumps are positive, constant-preserving operators on the continuous observables of the
  simplex, and their generators approach (7.1) with decisions on sampling functions
  (`DecisionWindowJumps.jumpApproximation_operator`, `abs_jumpGenerator_sub_le`). Their limit
  is the semigroup of the window with decisions: the jump approximations agree with the Dyson
  dual series on sampling functions up to `O(ε)`
  (`DecisionWindowSemigroup.norm_jumpOperator_sub_dualSeries_le`), the limit is a Feller
  semigroup equal to the dual series on sampling functions, which is (7.5) in Dyson form
  (`decisionWindowSemigroup_samplingFunction`), and its generator on sampling functions is (7.1)
  (`tendsto_decisionWindowSemigroup_slope`). The two ingredients are the Feller semigroup
  `e^{t(J - λ)}` of a positive bounded jump generator
  (`JumpFellerSemigroup.jumpSemigroup_operator`) and the Dyson components of the backward circuit,
  majorised by Yule weights with a bounded cubic moment (`DecisionDysonDual.norm_dysonTerm_le`,
  `sum_yuleMoment_mul_le`).
* Theorem 6 at generator level: `SamplingDuality`. On a sampling observable the resampling term of
  (7.1) is coalescence and the drift term is decision branching, so the forward generator applied
  to `H_f` is the backward circuit applied to `f` (`forwardGenerator_samplingObservable`); the
  formal-derivative and line-derivative generators agree on polynomial observables
  (`AncestralSamplingLimit.forwardGenerator_eq_samplingDuality`). Without decisions, `r = 0`: the
  coalescence operator has the exact exponential `S_t = e^{t L_c}`, the sampling functional turns
  it into the resampling generator
  (`CoalescentDualSemigroup.samplingFunctional_coalescenceOperator`), `t ↦ H_{S_t f}(p)` solves
  the backward equation (`hasDerivAt_samplingObservable_dualSemigroup`), and every moment family
  obeying the moment equation is `m_t(f) = m_0(S_t f)` (`moments_eq_dualSemigroup`), the
  uniqueness form of (7.5). At one allele the resampling generator on `x^n` is `c` times the corpus
  diffusion generator on powers (`OneAlleleDuality.resamplingGenerator_allCarriers`). With
  decisions, two moment families bounded by the sup norm that obey the moment equation of the
  backward circuit and agree at time zero agree at every time
  (`DecisionDualMoments.moments_eq_of_momentEquation`), through Duhamel's formula along the
  coalescence gain (`hasDerivAt_duhamel`).
* §7, ancestral decisions: `AncestralDecision`. The sampling observable (7.2), the coalescence
  substitution (`samplingObservable_coalesceArguments`), decision branching (7.3)
  (`samplingObservable_decisionBranch`) and the sampling identity (7.4) (`sampling_identity`,
  `sampling_identity_exchangeKernel`). The support tags (7.6): an omitted decision leaves the
  observable unchanged (`samplingObservable_decisionBranch_of_not_mem`), the updated observable is
  determined by the updated tags (`tagDetermined_decisionBranch`,
  `tagDetermined_coalesceArguments`), the support count rises by at most three at a decision and
  not at a coalescence (`tagCount_decisionTags_le`, `tagCount_coalesceTags_le`), and the decisions
  that are not omitted have total rate at most `D Z` (`decisionRate_le`).
* Theorems 7 and 8, the support drift (8.1): `LocalityBounds`. A decision along `i → j` raises the
  weighted support count by at most `w i + 2 w j` (`weightedCount_branchSupports_le`) and a
  coalescence does not raise it (`weightedCount_coalesceSupports_le`); with `Σ_j r i j ≤ D` and
  `w j ≤ κ w i` on every edge of positive rate the ancestral generator obeys
  `L Z^{(w)} ≤ D (1 + 2κ) Z^{(w)}` (`supportGenerator_weightedCount_le`) and the plain count
  `L Z ≤ 3 D Z` (`supportGenerator_supportSize_le`). (8.2) and (8.3) hold for marginal laws of
  the tagged support state that satisfy Dynkin's formula for the support generator
  (`integral_supportSize_le`,
  `integral_branchings_le`, through the Grönwall step `le_mul_exp_of_hasDerivWithinAt`), and (9.1)
  and (9.2) follow by Markov's inequality on the light-cone weight
  (`measureReal_escapeSet_le_exp`, `exp_div_pow_eq_of_radius`), with no escape when `DT = 0`
  (`eq_zero_of_forall_escape_bound`). For the circuit truncated after `M` decisions the laws are
  the matrix exponential of its generator and obey Dynkin's formula
  (`SupportChainDynkin.hasDerivAt_sum_jumpChainLaw_mul`), so (8.2), (8.3), (9.1) and (9.2) hold
  with no hypothesis and constants independent of `M` (`sum_supportChainLaw_mul_tagCount_le`,
  `sum_supportChainLaw_mul_count_le`, `sum_supportChainLaw_escape_le`,
  `sum_supportChainLaw_escape_le_radius`). While fewer than `M` decisions have been taken the
  chain's generator is `supportGenerator` on multisets of supports
  (`SupportChainMultiset.supportChainGenerator_mulVec_comp_supportsOf`), and the mass of frozen
  states tends to zero as `M → ∞` (`tendsto_sum_supportChainLaw_frozen`).
* Theorem 9, the operator half: `InfiniteGenomeLimit`. On a compact space with a point-separating
  subalgebra of observables, Feller semigroups along an exhaustion that satisfy a light-cone
  approximation bound converge on every continuous observable (`cauchySeq_operator`), and the
  limit is a Feller semigroup: contraction, positivity, the constant, the semigroup law and strong
  continuity (`norm_limitValue_le`, `limitValue_nonneg`, `limitValue_one`, `limitValue_add`,
  `tendsto_limitValue_zero`), at every time (`FellerSemigroup.continuous_operator`). Two Feller
  semigroups agreeing on a separating subalgebra agree (`operator_eq_of_eqOn`), so the limit is
  independent of the exhaustion (`limitSemigroup_eq_of_tendsto`). On `P({0,1}^V)`, `V` countable,
  the genome laws form a compact space (`CylinderSamplingAlgebra.compactSpace_probabilityMeasure`)
  on which the cylinder sampling algebra is dense (`samplingAlgebra_topologicalClosure_eq_top`),
  and every sampling polynomial of several genomes lies in it
  (`CylinderSamplingPolynomials.samplingPolynomial_mem_samplingAlgebra`). There the limit is
  `InfiniteGenomeLimit.infiniteGenomeSemigroup`: the finite-genome operators converge to it on
  every observable (`tendsto_infiniteGenomeSemigroup`), it is determined by the cylinder sampling
  polynomials (`operator_eq_infiniteGenomeSemigroup`), and it does not depend on the exhaustion
  (`infiniteGenomeSemigroup_eq_of_tendsto`). Without decisions, on a finite window the pure
  resampling semigroup acts on sampling polynomials as the coalescent dual
  (`ResamplingWindowSemigroup.windowSemigroup_samplingPolynomial`), larger windows read through the
  marginal run the smaller window's semigroup
  (`ResamplingWindowConsistency.windowSemigroup_comp_windowMarginal`), and every cylinder sampling
  polynomial reads a finite window (`CylinderWindowProjection.exists_windowPullback`), where a
  consistent contracting family of window operators extends to a contraction of `C(P(H))`
  (`norm_extendedOperator_le`); the glued semigroup is Theorem 9 without decisions, with no
  hypothesis (`ResamplingInfiniteGenome.infiniteGenomeSemigroup_resampling`). With a rate: along
  balls of radius `ℓ_m`,
  `‖T^m_t f - T_t f‖ ≤ 2‖f‖ min {1, n|A| e^{DT} (2eDT/ℓ_m)^{ℓ_m}}`
  (`InfiniteGenomeRate.norm_operator_sub_infiniteGenomeSemigroup_le`), given the sampling duality
  and agreement until escape.
* Corollary 8.1, the light cone as a coupling: `LocalityCoupling`. Two sample laws obtained by
  evaluating one circuit on inputs that coincide off an escape event are within total variation
  the probability of escape (`totalVariation_mixtureLaw_le`); for a circuit reading only inspected
  coordinates on inputs agreeing on a ball, this is (9.3) (`totalVariation_local_le`). The
  support-tag circuit truncated to the induced checking graph on a ball keeps the internal rates
  unchanged (`truncatedRate_of_mem`) and coincides with the full circuit along every run with no
  outside-checking event (`runCircuit_truncatedStep_eq`, `totalVariation_truncated_le`). §9.1:
  `20 e³ ∈ [401.7, 401.72]` (`twenty_mul_exp_three_mem_Icc`) and
  `20 e (2e/20)^20 ≤ 2.64 × 10⁻¹⁰` (`escapeBound_twenty_le`). For the circuit truncated after `M`
  decisions the coupling is its own law: inputs agreeing on the ball give sample laws within the
  escape probability (`CircuitCoupling.totalVariation_supportChainLaw_inputs_le`, at the radius of
  (9.2) `totalVariation_supportChainLaw_inputs_le_radius`), and so does the checking graph
  truncated to the ball (`totalVariation_truncatedSupportChain_le`).

Scope. The single-feature Kingman limit behind Theorem 3 is proved for the pair survival law and
for the one-step rates of the block-counting chain, not as convergence of path laws.
Theorems 7 and 8 take Dynkin's formula for the support generator along the marginal laws, and
for (8.3) the compensator formula, as hypotheses, together with integrability and continuity; the
path law of the backward circuit is not constructed. For the circuit truncated after `M` decisions
they hold outright; the limit `M → ∞` is not taken. Corollary 8.1 is stated on a common finite
probability
space; with the explicit escape bounds of Theorem 8 for the marginal laws of the circuit it reads
`d_TV ≤ min {1, n|A| e^{DT} (2eDT/ℓ)^ℓ}`
(`LocalityCouplingBounds.totalVariation_integralLaw_le_radius`). The supercritical limit (6.2) is
proved for
its support, conditional on the Erdős-Rényi giant component theorem as the named hypothesis
`GiantComponentLaw` (proved only for `0 ≤ α < 1`), and so are its weights `1 - (1 - s)^k` and
`(1 - s)^k`. Theorem 6 is proved at generator level, and as the uniqueness form of (7.5), for
`r = 0` and with decisions, with the moment equation as a hypothesis; the forward diffusion on
`P(H)` and the backward jump process are not constructed. Theorem 1 defines `P_*` as the
`|H|`-th iterate of `Φ_K`, which is the first fixed point, and Theorem 2 uses only the symmetry of
the kernel. Theorem 4 and its
restatement through the closure of Theorem 1 take nonnegative rates.
Of Theorem 9, the finite-genome semigroups are data, and the light-cone approximation is
discharged (`LightConeApproximationBound.norm_operator_sub_le_lightConeEscape`) from three
hypotheses: the sampling duality at every exhaustion index, agreement of the evaluations until
escape, and Dynkin's formula for the marginal laws of the circuit.
-/

end Descent.Program
