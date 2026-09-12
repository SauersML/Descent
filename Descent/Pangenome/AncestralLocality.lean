/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CylinderWindowProjection
import Descent.Pangenome.AncestralLocality.CylinderSamplingPolynomials
import Descent.Pangenome.AncestralLocality.AncestralDecision
import Descent.Pangenome.AncestralLocality.ClosureReachability
import Descent.Pangenome.AncestralLocality.CoalescentDualSemigroup
import Descent.Pangenome.AncestralLocality.CylinderSamplingAlgebra
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality
import Descent.Pangenome.AncestralLocality.DecisionDualMoments
import Descent.Pangenome.AncestralLocality.FeatureKingmanLimit
import Descent.Pangenome.AncestralLocality.HereditaryClosure
import Descent.Pangenome.AncestralLocality.HeredityKernel
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Descent.Pangenome.AncestralLocality.JointNonautonomy
import Descent.Pangenome.AncestralLocality.LightConeApproximationBound
import Descent.Pangenome.AncestralLocality.LocalityBounds
import Descent.Pangenome.AncestralLocality.LocalityCoupling
import Descent.Pangenome.AncestralLocality.LocalityCouplingBounds
import Descent.Pangenome.AncestralLocality.LocalityTransition
import Descent.Pangenome.AncestralLocality.OneAlleleDuality
import Descent.Pangenome.AncestralLocality.OperationalAutonomy
import Descent.Pangenome.AncestralLocality.RandomClosure
import Descent.Pangenome.AncestralLocality.ReachabilityClosureTie
import Descent.Pangenome.AncestralLocality.RootExchangeability
import Descent.Pangenome.AncestralLocality.SamplingDuality
import Descent.Pangenome.AncestralLocality.SupercriticalBranches
import Descent.Pangenome.AncestralLocality.SupercriticalReach
import Descent.Pangenome.AncestralLocality.SupportChainDynkin
import Descent.Pangenome.AncestralLocality.AnnotatedKernel
import Descent.Pangenome.AncestralLocality.CircuitCoupling
import Descent.Pangenome.AncestralLocality.SupercriticalLowerBound
import Descent.Pangenome.AncestralLocality.BreadthFirstDomination
import Descent.Pangenome.AncestralLocality.SupportChainMultiset
import Descent.Pangenome.AncestralLocality.SupercriticalUpperBound
import Descent.Pangenome.AncestralLocality.FeatureKingmanLimitLineages
import Descent.Pangenome.AncestralLocality.SupercriticalSprinkling
import Descent.Pangenome.AncestralLocality.InfiniteGenomeRate
import Descent.Pangenome.AncestralLocality.SelectionDecisions
import Descent.Pangenome.AncestralLocality.SupercriticalSecondMoment
import Descent.Pangenome.AncestralLocality.InhomogeneousLocalityTransition
import Descent.Pangenome.AncestralLocality.SelectionClosure
import Descent.Pangenome.AncestralLocality.SelectionTies
import Descent.Pangenome.AncestralLocality.SelectionLightCone
import Descent.Pangenome.AncestralLocality.DecisionJumpExpansion
import Descent.Pangenome.AncestralLocality.DecisionWindowJumps
import Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup
import Descent.Pangenome.AncestralLocality.JumpFellerSemigroup
import Descent.Pangenome.AncestralLocality.DecisionDysonDual
import Descent.Pangenome.AncestralLocality.SupercriticalUnconditional
import Descent.Pangenome.AncestralLocality.SupercriticalConcentration
import Descent.Pangenome.AncestralLocality.SupercriticalGiantLaw
import Descent.Pangenome.AncestralLocality.SupercriticalGiantComponentTheorem
import Descent.Pangenome.AncestralLocality.SelectionSemigroupPerturbation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# `AncestralLocality` -- heredity-first closure of pangenomic observations

The layer head for the research note "Ancestral locality" of 11 September 2026, transcribed as
`ANCESTRAL_LOCALITY.md`. A module of the group is imported here once its proof check has passed
on the bytes on main.

1. `CompatibilityNeutrality` -- the checked-exchange model of §4: ordered children, exchange
   kernels and the compatibility kernel `K_G`; Theorem 3, that every single feature is exactly
   neutral; the finite-population law with its exact binomial count law (§4.1); and the
   eight-state witness of §5.2, two populations with one observed law and two next-generation
   observed laws.

2. `LocalityTransition` -- Theorem 5 and §6.1 in the finite: the law of `G(m, p)` on edge sets,
   the simple-path bound (6.1) `E|Reach(A)| ≤ |A|/(1 - α)` for `0 ≤ α < 1`, the degree-normalized
   rates with `sup_i Σ_j r_ij ≤ β` for every graph, and the unique root `giantFraction α` in
   `(0, 1)` of `s = 1 - e^{-α s}` for `α > 1`.

3. `SupercriticalReach` -- (6.2) conditional on the Erdős–Rényi theorem: probabilities under
   `G(m, p)`, the tie-free giant-component event, `GiantComponentLaw` carrying the classical
   theorem with its subcritical half proved from (6.1) (witness `giantComponentLaw_half`), and the
   support of the limit law: the reach fraction concentrates near `0` or near `giantFraction α`.

3. `InfiniteGenomeLimit` -- the operator half of Theorem 9 on any compact space with a separating
   subalgebra: Feller semigroups along an exhaustion that obey the light-cone approximation bound
   converge on every observable, the limit is a Feller semigroup with strong continuity at every
   time, and two Feller semigroups agreeing on the subalgebra agree, so the limit does not depend
   on the exhaustion.

4. `LocalityBounds` -- Theorems 7 and 8 and Corollary 8.1: a decision raises the weighted
   support count by at most `w i + 2 w j` and a coalescence does not raise it, so
   `L_anc Z ≤ 3 D Z` and, with light-cone weights, `L_anc Z^{(a)} ≤ D (1 + 2a) Z^{(a)}`. Along
   marginal laws satisfying the Dynkin formula these give (8.2), (8.3) and the escape bound
   (9.1), with the radius identity behind (9.2); outcomes equal off an event are within its
   probability in total variation.

5. `JointNonautonomy` -- §3.2: two observations can each be autonomous while their joint
   observation is not. Under the witness rule of §5.2 the features `a` and `b` each have the
   neutral observed kernel of Theorem 3, and their joint observation `(a, b)` has no kernel.

6. `ClosureReachability` -- Theorem 4 and §5.1: for `|A| ≥ 2` one hereditary refinement step
   of the checking kernel turns `P_{π_A}` into `P_{π_{A ∪ N⁺_G(A)}}` (5.2), through the
   difference formula (5.3); iterating gives `P_{π_{Reach_G(A)}}` (5.1), and singletons and the
   empty observation are their own closure. On a connected undirected graph, the path included,
   every query on two or more features closes to the whole genome, and a pair observation with
   an outside checker is not autonomous (5.4). The checking kernel on the edge rates of a graph
   is the compatibility kernel, and `ReachabilityClosureTie` identifies the refinement step with
   `Φ_K` of the heredity layer.

7. `AncestralDecision` -- §7: sampling observables `H_f(p) = ∑_x f(x) ∏_a p(x_a)` (7.2), the
   coalescence and decision-branching substitutions (7.3), and the sampling identity (7.4) for
   any rule and for the ordered child. §7.3 adds the support tags (7.6): an event at a target
   outside the tag is omitted, the observable stays determined by the updated tags, one decision
   adds at most three coordinate occurrences, a coalescence adds none, and the decision rate is
   at most `D Z`.

8. `SamplingDuality` -- Theorem 6 at generator level: the forward generator (7.1), with
   line-derivative partials of sampling observables, applied to `H_f` at a probability vector is
   the backward circuit read through sampling observables: the resampling term is coalescence
   at rate `c` per pair and the drift term is decision branching at rate `r_e` per argument. The
   backward generator is a jump generator with exit rate `c d_n + n R`, where `d_n` is Kingman's
   pair count. The semigroup form (7.5) is not proved.

9. `RootExchangeability` -- the exact finite core of the weights in (6.2): `G(m, p)` is invariant
   under relabeling the features, so the chance that a query misses the large components depends
   only on its size, and `C(m, k) P(A misses the large set) = E[C(m - |large|, k)]`; with the
   bounds `((n + 1 - k)/m)^k ≤ C(n, k)/C(m, k) ≤ (n/m)^k`.

10. `SupercriticalBranches` -- (6.2) assuming `GiantComponentLaw α`: for `α > 1` and queries of
    eventually `k` features, `P(|C_m(A)|/m ≤ ε) → (1 - s)^k` for `0 < ε < s` and
    `P(||C_m(A)|/m - s| ≤ ε) → 1 - (1 - s)^k` for `0 < 2ε < s`.

11. `RandomClosure` -- Theorem 4 joined to Theorem 5: with the degree-normalized rates of §6.1 on
    the present edges, `directedReach` is `reach` of the symmetric graph, so the hereditary
    closure of `π_A` on `G(m, α/m)` is `π` on that reach and (6.1) bounds its support.

12. `HeredityKernel` -- §2: symmetric two-parent heredity kernels, the mass `K(x,y;B)` of a set,
    observations and their fiber partitions `Setoid.ker π`, and hereditary autonomy (2.2), both
    as the existence of an observed kernel `K̄` and as a property of a `Setoid`; for a surjective
    observation every such `K̄` is itself a heredity kernel.

13. `HereditaryClosure` -- §3: the refinement `Φ_K` (3.1) and its termination within `|H| - |P|`
    strict steps (3.2); Theorem 1, that the closure `P_*` is the greatest autonomous partition
    refining the observation, and for observations the coarsest autonomous one determining it;
    invariance under relabeling (§3.1); and a gated-exchange kernel with two autonomous features
    whose joint observation is not autonomous (§3.2).

14. `CoalescentDualSemigroup` -- the duality (7.5) without decisions: the coalescence generator
    `L_c` on observations of fixed arity, its exponential `S_t` with the semigroup law, the
    backward equation `∂_t H_{S_t f}(p) = resamplingGenerator c H_{S_t f} (p)`, and the moment form
    `m_t(f) = m_0(S_t f)` for every linear moment family obeying `d/dt m_t(f) = m_t(L_c f)`.

15. `OperationalAutonomy` -- Theorem 2: for a kernel that does not see the order of the parents,
    an observation is hereditarily autonomous exactly when its observed next generation depends
    only on its observed law, read off point masses and two-point mixtures; compatibility kernels
    are heredity kernels, one feature is autonomous, and the witness observation is not.

16. `ReachabilityClosureTie` -- Theorem 4 in the vocabulary of Theorem 1: the refinement step and
    autonomy of `ClosureReachability` are those of `HereditaryClosure`, the closure of `π_A` for
    `|A| ≥ 2` is `π_{Reach_G(A)}`, and the universal property of the closure reads as a statement
    about reachability.

17. `LightConeApproximationBound` -- the light-cone approximation of Theorem 9, discharged with
    the error `2 ‖f‖_∞ Pr(E_{ℓ,T})` from the sampling duality at every exhaustion index, agreement
    of the evaluations until escape, and Dynkin's formula for the marginal laws of the circuit.

18. `OneAlleleDuality` -- Theorem 6 read at one allele: on `P(Bool)` the all-carriers moment is
    `x^n`, its coalescence is `x^{n-1}`, and the resampling generator (7.1) on it is `c` times the
    Wright-Fisher diffusion generator on `x^n` of `Descent.Coalescent.Duality`, so the note's
    sampling duality agrees with Kingman's moment duality.

19. `SupportChainDynkin` -- Theorems 7 and 8 without a Dynkin hypothesis: the support circuit
    truncated after `M` decisions as a finite jump chain with laws `δ_{x₀} e^{tQ}`, Dynkin's
    formula and its compensator form for those laws, and (8.2), (8.3), (9.1) and (9.2) with
    constants that do not depend on `M`.

20. `DecisionDualMoments` -- the duality (7.5) with decisions, in moment form: two families of
    moment functionals on observations of every arity, bounded by the sup norm and obeying the
    moment equation of the backward circuit, that agree at time zero agree at every time, through
    Duhamel's formula along the coalescence gain and induction on the number of branchings.

21. `FeatureKingmanLimit` -- the pair Kingman limit behind Theorem 3: the finite-population law
    (4.5) annotated with each offspring's source at one feature has the genome marginal `Q_N` and
    a uniform source, two distinct offspring share a source with probability `1/N`, the pair
    coalescence time over a history is geometric, and on the `N`-generation scale it converges in
    distribution to `Exp(1)`.

This file contains no declarations.
-/
