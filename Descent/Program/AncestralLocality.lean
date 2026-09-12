/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Descent.Pangenome.AncestralLocality.LocalityBounds
import Descent.Pangenome.AncestralLocality.LocalityCoupling
import Descent.Pangenome.AncestralLocality.LocalityTransition
import Descent.Pangenome.AncestralLocality.SupercriticalReach

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

* Theorem 3, every feature is exactly neutral: `CompatibilityNeutrality`. (4.4) for every
  checking graph (`compatibilityKernel_marginal`) and its population form `(R_{K_G}(p))_k = p_k`
  (`featureMass_reproduce_compatibilityKernel`). §4.1: the finite-population kernel `Q_N` (4.5)
  keeps every allele law and is a probability vector for `R ≤ N`, and the offspring count at a
  feature is `Binomial(N, p_k)` (4.6) (`offspringCount_eq_binomial`). §5.2: the eight-state witness
  has one observed law and drifts `-1/4` and `0` (`witness_drift`), so no observed transition law
  predicts both and the observation `(a, b)` is not autonomous
  (`witness_no_observed_transition_law`, `witness_not_autonomous`).
* Theorem 5, the locality transition: `LocalityTransition`. For `G(m, α/m)` as a finite law on
  edge sets, the expected reach of `A` satisfies `E|Reach(A)| ≤ |A|/(1 - α)` for `0 ≤ α < 1` and
  every genome size (`graphExpect_card_reach_le`), through the count of present simple paths
  (`card_reach_singleton_le_sum`, `graphExpect_card_presentPaths`). §6.1: the rates `β / deg(i)`
  are positive exactly on present edges. For `α > 1` the survival equation `s = 1 - e^{-αs}` has a
  unique root in `(0, 1)` (`existsUnique_survival_root`, `giantFraction_mem_Ioo`). Given the giant
  component theorem (`GiantComponentLaw`, proved for `0 ≤ α < 1` by `giantComponentLaw_of_lt_one`),
  the reach fraction is near `0` or `giantFraction α` with probability tending to one
  (`SupercriticalReach.tendsto_graphProb_reach_near_zero_or_giant`).
* Theorems 7 and 8, the support drift: `LocalityBounds`. A decision along `i → j` raises the
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
  (`eq_zero_of_forall_escape_bound`).
* Theorem 9, the operator half: `InfiniteGenomeLimit`. On a compact space with a point-separating
  subalgebra of observables, Feller semigroups along an exhaustion that satisfy a light-cone
  approximation bound converge on every continuous observable (`cauchySeq_operator`), and the
  limit is a Feller semigroup: contraction, positivity, the constant, the semigroup law and strong
  continuity (`norm_limitValue_le`, `limitValue_nonneg`, `limitValue_one`, `limitValue_add`,
  `tendsto_limitValue_zero`), at every time (`FellerSemigroup.continuous_operator`). Two Feller
  semigroups agreeing on a separating subalgebra agree (`operator_eq_of_eqOn`), so the limit is
  independent of the exhaustion (`limitSemigroup_eq_of_tendsto`).
* Corollary 8.1, the light cone as a coupling: `LocalityCoupling`. Two sample laws obtained by
  evaluating one circuit on inputs that coincide off an escape event are within total variation
  the probability of escape (`totalVariation_mixtureLaw_le`); for a circuit reading only inspected
  coordinates on inputs agreeing on a ball, this is (9.3) (`totalVariation_local_le`). The
  support-tag circuit truncated to the induced checking graph on a ball keeps the internal rates
  unchanged (`truncatedRate_of_mem`) and coincides with the full circuit along every run with no
  outside-checking event (`runCircuit_truncatedStep_eq`, `totalVariation_truncated_le`). §9.1:
  `20 e³ ∈ [401.7, 401.72]` (`twenty_mul_exp_three_mem_Icc`) and
  `20 e (2e/20)^20 ≤ 2.64 × 10⁻¹⁰` (`escapeBound_twenty_le`).

Scope. The single-feature Kingman limit behind Theorem 3 is classical and is not re-proved.
Theorems 7 and 8 take Dynkin's formula for the support generator along the marginal laws, and
for (8.3) the compensator formula, as hypotheses, together with integrability and continuity; the
path law of the backward circuit is not constructed. Corollary 8.1 is stated on a common finite
probability
space, with the escape probability as a parameter. The supercritical limit (6.2) is proved for
its support, conditional on the Erdős-Rényi giant component theorem as the named hypothesis
`GiantComponentLaw` (proved only for `0 ≤ α < 1`); its weights `1 - (1 - s)^k` and `(1 - s)^k`
are not proved. Theorems 1 and 2 (hereditary closure and its operational characterization),
Theorem 4 (closure is reachability) and Theorem 6 (sampling duality) are not yet proof-checked.
Of Theorem 9, the finite-genome semigroups and the light-cone bound are hypotheses
(`LightConeApproximation`), and the space `P({0,1}^V)` with its cylinder sampling algebra is not
yet constructed.
-/

end Descent.Program
