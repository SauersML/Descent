/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.StarOrdered
import Mathlib.Logic.Equiv.Fintype
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic
import Calibrator.ObservationalCeiling

namespace Calibrator

namespace TrafficInvariantSeparation

open scoped Matrix Topology

/-!
# Hardness by invariant separation and exact finite Curie--Weiss pressure

A procedure class that cannot tell two designs apart inherits, on the harder of
the two, the whole gap between their optima. That template is what turns an
invariance statement into a lower bound, and it is the load-bearing step of the
traffic-invariant programme: every hardness claim there routes through it.

This file formalises the exact finite and analytic core of that programme and
keeps the matched-Bayes hinge outside the proved statements.

## What is proved here

* `suboptimal_of_invariant_separation` -- the template itself. If every
  procedure in a class has the same limiting risk on two designs, and the second
  design's optimum is `Δ` better, then every procedure in the class is at least
  `Δ` from optimal on the first. The proof is three inequalities and it loses no
  constant factor; in particular there is no `1/2`.

* `algorithmicRiskSignature_isCoarsestSufficientInvariant` -- the abstract
  correspondence has its full universal property: the complete risk signature
  is sufficient, and every other invariant supporting one uniform risk
  reconstruction map refines it.

* `rankOneGraphSum_le_inv`,
  `finiteRankOneTrafficCorrection_tendsto_zero`, and
  `finiteRankOneTraffic_invisible_variationalPressure_visible` -- the
  arithmetic behind traffic-invisibility of a rank-one spike, closure under
  the finite nonempty spike-edge expansion of every fixed graph, and its
  direct combination with supercritical variational-pressure separation. The
  graph-theoretic input (`|E| ≥ |V|` after contraction) is derived by
  `vertices_le_edges_of_positive_evenDegrees_of_handshake` and propagated
  termwise by
  `finiteRankOneTrafficCorrection_tendsto_zero_of_positiveEvenDegreeData`.

* `rankOneTraffic_groundState_pressure_counterexample` -- one positive spike
  simultaneously has vanishing fixed-traffic correction, unchanged lower
  ground state, a strictly raised aligned-state energy, and positive
  supercritical variational pressure.

* `cw_rate_lower_bound`, `cw_rate_upper_bound`, and
  `cwVariationalPressureGap_eq_zero_iff` -- Pinsker's inequality and a
  complementary logarithmic upper bound prove the exact critical point for the
  SUPREMAL variational pressure itself: below it the gap vanishes identically,
  and above it an explicit interior magnetisation makes the supremum positive.

* `finiteLogSum_ge_weightedLogRatio`,
  `finiteCWPressureGap_ge_cwObjective`, and
  `finiteCWPressureGap_tendsto_variationalPressure` -- the genuine
  binomially grouped finite Rademacher partition function dominates every
  Curie--Weiss objective by an exact biased-binomial Gibbs inequality, while
  each type is bounded above by the exponential variational pressure.  The
  resulting `log (p+1) / p` squeeze identifies the full finite pressure limit.
  Since the error is coupling-independent, convergence is uniform on the whole
  nonnegative half-line.  Hence pressure is uniformly positive for every
  `tλ > 1` while fixed traffic vanishes, without Stirling asymptotics, an LDP,
  or Varadhan.

* `fixedTraffic_invisible_logRuntime_visible` -- every fixed diagonal traffic
  coordinate loses a block of mass `4⁻ᵏ`, while `k` power iterations amplify its
  normalized squared output back to one.

* `limitingTraffic_insufficient_for_unstableDegreeOne` -- the same
  mesoscopic block already defeats an unrestricted degree-one polynomial:
  its normalized trace discrepancy vanishes, while coefficient growth at the
  reciprocal resolution keeps an order-one separation.

* `invariantPolynomial_graphSum_factorization` and `truncatedTraffic_hardness`
  -- an explicit permutation extending the occupied-label bijection proves
  coefficient constancy on equality-pattern graphs; equality of a truncated
  traffic profile then transfers the complete Bayes gap to the degree-limited
  class.

* `truncatedTrafficRisk_abs_sub_le_coefficientMass_mul` -- the corrected
  limiting theorem: traffic error is multiplied by coefficient `ℓ¹` mass.
  Fixed degree is sufficient only after this quantitative stability is
  controlled.

* `highTemperatureTrafficLimit_eq_of_geometricTruncation` -- a common finite
  traffic expansion with a uniform geometric polymer tail determines the
  limiting pressure.  The model-specific cluster-expansion certificate is an
  explicit hypothesis.

* `exists_probabilityWeights_matchingMoments_through_degree` -- for every
  `D`, two explicit finite probability laws on `[1,2]` agree on moments
  `0,…,D` and differ at `D+1`; square Vandermonde invertibility proves that the
  separating next moment cannot vanish.

* `exponentialProfileDistance_eq_zero_iff`,
  `exponentialProfileDistance_triangle`, and
  `exponentialProfileDistance_tendsto_zero_iff_coordinatewise` -- the explicit
  weighted formula induces exactly simultaneous convergence of every
  enumerated pressure coordinate;
  `exponentialProfileDistance_le_geometricTail_of_prefix_eq` gives the exact
  `2·2⁻ᴷ` error after matching the first `K` coordinates; and
  `boundedExponentialProfile_compact_subsequence_in_distance` -- the explicit
  weighted LD/right-profile formula is separating and triangular, and every
  bounded profile sequence has a subsequence converging in that distance.
  `exponentialProfilePointMetricSpace` and
  `exponentialProfilePointCompactSpace` bundle the formula as the standard
  metric and compact topology on a dedicated carrier.

* `lipschitzPressureProfiles_dist_le_of_net` and
  `lipschitzPressureProfiles_eq_of_eqOn_dense` -- a finite rational tilt net
  controls the whole pressure profile by `2Kρ + ε`, and dense rational
  coordinates uniquely determine every uniformly Lipschitz extension.
  `lipschitzPressureProfiles_tendsto_of_tendstoOn_dense` transfers convergence
  on that dense family to every tilt, and
  `lipschitzPressureProfiles_tendstoUniformly_of_tendstoOn_dense` upgrades it
  to uniform convergence on compact tilt domains.

* `isCompact_boundedLipschitzPressureFamily` and
  `boundedLipschitzPressureFamily_tendsto_subseq` -- the full functional
  right-profile family is compact by Arzelà--Ascoli, so every uniformly bounded
  equi-Lipschitz pressure sequence has a uniformly convergent subsequence whose
  limit remains in the same family.

* `randomDesign_gap_of_scalarGap` and
  `matchedInformationError_le_of_wishartFrobenius` -- the matched random-design
  question reduces to its scalar Gaussian counterpart with a sharp two-error
  ledger.  Matrix I--MMSE sensitivity, nuclear/Frobenius comparison, and the
  Wishart Frobenius scale yield the explicit
  `signal * variance * operatorBound / 2 * sqrt ((p+1)/n)` error, so every
  positive scalar gap eventually survives as aspect ratio diverges.

* `matchedInformationPath_nuclear_bound`,
  `matchedDensity_lowRank_tendsto_zero_of_nuclearEstimate`, and
  `matchedDensity_eventualGap_not_sublinearRank` -- a certified matrix I--MMSE
  path plus posterior-covariance trace control yields the nuclear estimate;
  that estimate gives both directions of the extensive-rank boundary.  A
  vanishing rank fraction forces the matched information-density gap to
  vanish, while a persistent gap `delta` forces eventual rank fraction at
  least `delta / constant`.

## Why the sub-critical statement matters

The gap is zero on a whole interval `0 ≤ t ≤ λ⁻¹` and strictly positive beyond
it. So every Taylor coefficient at the origin agrees -- not finitely many of
them -- while the functions differ. That is the sharpest available statement of

  traffic moments are LOCAL TAYLOR DATA, not global free-energy data,

and it is why a hierarchy built from graph sums alone cannot be complete. The
same separation appears in `Calibrator.BlindnessRegistry` in a different guise:
a probe returning one number on two objects certifies neither.

## What is NOT settled

Matched Bayes traffic sufficiency at arbitrary signal-to-noise remains open, and
the rank-one construction cannot decide it: a
perturbation of rank `o(p)` moves the exponential pressure by order one and the
matched mutual-information density by `o(1)`, so a negative witness there needs
EXTENSIVE rank. That contrast -- one perturbation, four procedure classes, two
of which see it and two of which do not -- is the reason the invariant hierarchy
is procedure-dependent rather than a single chain.  No argument here treats
Nishimori exchangeability as replica symmetry, overlap concentration, or
analyticity; each of those would require an additional theorem and none is
silently assumed by the matched-Bayes boundary results below.
-/

section InvariantSeparation

/-- The complete limiting-risk signature of a design for a uniform procedure class.  Algorithms,
models, and losses are all arguments, so a procedure cannot contain the design identity as
nonuniform advice. -/
def algorithmicRiskSignature
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) (design : Design) :
    Algorithm → Model → Loss → ℝ :=
  fun algorithm model loss ↦ risk algorithm design model loss

/-- Two designs are indistinguishable by the entire uniform class exactly when all entries of
their limiting-risk signatures agree. -/
def AlgorithmicallyEquivalent
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) (left right : Design) : Prop :=
  ∀ algorithm model loss, risk algorithm left model loss = risk algorithm right model loss

/-- All risks of the uniform procedure class factor through a proposed design
invariant when one common reconstruction map recovers the complete risk
signature from that invariant.  Requiring a common map is what excludes
nonuniform design advice. -/
def RiskSignaturesFactorThrough
    {Algorithm Design Model Loss Invariant : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ)
    (invariant : Design → Invariant) : Prop :=
  ∃ reconstruct : Invariant → Algorithm → Model → Loss → ℝ,
    ∀ design,
      reconstruct (invariant design) = algorithmicRiskSignature risk design

/-- The abstract correspondence is an equality of risk signatures, not an extra conjecture. -/
theorem algorithmicallyEquivalent_iff_signature_eq
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) (left right : Design) :
    AlgorithmicallyEquivalent risk left right ↔
      algorithmicRiskSignature risk left = algorithmicRiskSignature risk right := by
  constructor
  · intro h
    funext algorithm model loss
    exact h algorithm model loss
  · intro h algorithm model loss
    exact congrFun (congrFun (congrFun h algorithm) model) loss

/-- The canonical complete risk signature is itself a sufficient invariant:
its reconstruction map is the identity. -/
theorem riskSignatures_factorThrough_algorithmicRiskSignature
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) :
    RiskSignaturesFactorThrough risk (algorithmicRiskSignature risk) := by
  exact ⟨fun signature ↦ signature, fun _design ↦ rfl⟩

/-- Every sufficient design invariant refines the canonical risk signature.
If the proposed invariant identifies two designs, its common reconstruction
map forces their complete risk signatures to agree.  This is the missing
coarseness direction in the abstract correspondence. -/
theorem algorithmicRiskSignature_eq_of_sufficientInvariant_eq
    {Algorithm Design Model Loss Invariant : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ)
    (invariant : Design → Invariant)
    (hfactor : RiskSignaturesFactorThrough risk invariant)
    (left right : Design) (hsame : invariant left = invariant right) :
    algorithmicRiskSignature risk left = algorithmicRiskSignature risk right := by
  obtain ⟨reconstruct, hreconstruct⟩ := hfactor
  rw [← hreconstruct left, ← hreconstruct right, hsame]

/-- A sufficient invariant cannot identify algorithmically distinguishable
designs.  Equivalently, its equality relation is contained in the canonical
algorithmic-equivalence relation. -/
theorem algorithmicallyEquivalent_of_sufficientInvariant_eq
    {Algorithm Design Model Loss Invariant : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ)
    (invariant : Design → Invariant)
    (hfactor : RiskSignaturesFactorThrough risk invariant)
    (left right : Design) (hsame : invariant left = invariant right) :
    AlgorithmicallyEquivalent risk left right := by
  rw [algorithmicallyEquivalent_iff_signature_eq]
  exact algorithmicRiskSignature_eq_of_sufficientInvariant_eq
    risk invariant hfactor left right hsame

/-- **Universal property of the abstract algorithmic correspondence.**  The
complete risk signature is sufficient, and every other sufficient invariant
refines it.  Hence, up to relabelling of realized signature values, it is the
unique coarsest invariant through which every uniform procedure's risk factors. -/
theorem algorithmicRiskSignature_isCoarsestSufficientInvariant
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) :
    RiskSignaturesFactorThrough risk (algorithmicRiskSignature risk) ∧
      ∀ (Invariant : Type*) (invariant : Design → Invariant),
        RiskSignaturesFactorThrough risk invariant →
          ∀ left right, invariant left = invariant right →
            algorithmicRiskSignature risk left =
              algorithmicRiskSignature risk right := by
  refine ⟨riskSignatures_factorThrough_algorithmicRiskSignature risk, ?_⟩
  intro Invariant invariant hfactor left right hsame
  exact algorithmicRiskSignature_eq_of_sufficientInvariant_eq
    risk invariant hfactor left right hsame

/-- **Hardness by invariant separation.**

    `risk a` is the limiting risk of procedure `a` on the first design and
    `risk' a` its limiting risk on the second. `h_equiv` says the class cannot
    distinguish them; `h_opt'` says `bayes'` is optimal on the second.

    The conclusion is that `a`'s excess risk on the FIRST design is at least the
    difference of the two optima. No factor is lost: the bound is the full gap.

    Empirical status: NOT AN EMPIRICAL CLAIM. This is a statement about risks of
    procedures, not about any population, and its content is exhausted by the
    inequality below. -/
theorem suboptimal_of_invariant_separation
    {A : Type*} (risk risk' : A → ℝ) (bayes bayes' : ℝ)
    (h_equiv : ∀ a, risk a = risk' a)
    (h_opt' : ∀ a, bayes' ≤ risk' a)
    (a : A) :
    bayes' - bayes ≤ risk a - bayes := by
  have h := h_opt' a
  rw [h_equiv a]
  linarith

/-- **The separation is vacuous exactly when the two optima agree.** Stated so
    that the template cannot be quoted as a bound when it delivers nothing: a
    class blind to two designs of equal difficulty is not thereby shown to be
    suboptimal on either. -/
theorem invariant_separation_trivial_iff
    (bayes bayes' : ℝ) :
    bayes' - bayes ≤ 0 ↔ bayes' ≤ bayes := by
  constructor <;> intro h <;> linarith

/-- **An invariant separation is an instance of the observational ceiling.**

    `Calibrator.ObservationalCeiling` states the law this file's template is a
    quantitative form of: a probe returning the same data on two objects
    certifies neither, so no criterion factoring through it decides any property
    separating them. Here the probe is the algorithmic invariant, and the
    property is "the optimum is at least as good as `thr`".

    Relating the two is what makes this module contradictable from outside it: if
    the separation pair were wrong, `ProbeBlindness.no_criterion` would deliver a
    false conclusion about the corpus's own blindness law rather than only about
    a private definition here. -/
def separationBlindness {Design Invariant : Type*}
    (invariant : Design → Invariant) (bayes : Design → ℝ)
    (d d' : Design) (thr : ℝ)
    (same : invariant d = invariant d')
    (hd : bayes d ≤ thr) (hd' : ¬ bayes d' ≤ thr) :
    ProbeBlindness invariant (fun x ↦ bayes x ≤ thr) where
  positive := d
  negative := d'
  same_data := same
  holds := hd
  fails := hd'

/-- **No rule reading only the invariant decides which design is easier.**
    The observational ceiling applied to the separation pair. -/
theorem no_invariant_criterion_for_optimum {Design Invariant : Type*}
    (invariant : Design → Invariant) (bayes : Design → ℝ)
    (d d' : Design) (thr : ℝ)
    (same : invariant d = invariant d')
    (hd : bayes d ≤ thr) (hd' : ¬ bayes d' ≤ thr) :
    ¬ ∃ decide : Invariant → Prop,
        ∀ x : Design, bayes x ≤ thr ↔ decide (invariant x) :=
  (separationBlindness invariant bayes d d' thr same hd hd').no_criterion

/-- **The bridge, named in a statement rather than only in a proof.**

    `separationBlindness` really is a `ProbeBlindness` of the corpus's own kind,
    carrying the first design as its positive witness. Stating that puts this
    module's definitions beside `ObservationalCeiling`'s in one theorem, which is
    what makes a divergence between them a compile error instead of a silent
    fork. -/
@[simp] theorem separationBlindness_positive {Design Invariant : Type*}
    (invariant : Design → Invariant) (bayes : Design → ℝ)
    (d d' : Design) (thr : ℝ)
    (same : invariant d = invariant d')
    (hd : bayes d ≤ thr) (hd' : ¬ bayes d' ≤ thr) :
    (separationBlindness invariant bayes d d' thr same hd hd' :
      ProbeBlindness invariant (fun x ↦ bayes x ≤ thr)).positive = d := rfl

end InvariantSeparation

section RankOneInvisibility

/-- **The rank-one spike's normalised graph sum, bounded.**

    For a balanced sign vector scaled by `p^(-1/2)`, a connected test graph with
    every vertex degree even contributes `p ^ (|V| - |E| - 1)`. Such a graph has
    `|E| ≥ |V|`, so the exponent is at most `-1`.

    The graph-theoretic input is the hypothesis `hev : v ≤ e`; what is proved is
    that it forces the bound. Odd-degree graphs contribute zero by balancedness
    and need no bound. -/
theorem rankOneGraphSum_le_inv
    (p : ℝ) (v e : ℕ) (hp : 1 ≤ p) (hev : v ≤ e) :
    p ^ v / p ^ (e + 1) ≤ 1 / p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hmono : p ^ v ≤ p ^ e := pow_le_pow_right₀ hp hev
  have hpe : (0 : ℝ) < p ^ e := pow_pos hp0 e
  rw [pow_succ, div_le_div_iff₀ (by positivity) hp0]
  calc p ^ v * p = p ^ v * p := rfl
    _ ≤ p ^ e * p := by nlinarith [hpe]
    _ = 1 * (p ^ e * p) := by ring

/-- **The graph-count input follows from handshaking.**  A finite contracted
graph in which every surviving vertex has degree at least two and whose degree
sum is twice its edge count satisfies `|V| ≤ |E|`.  Connected all-even graphs
with a nonempty edge set supply the minimum-degree premise automatically. -/
theorem vertices_le_edges_of_minDegree_two_of_handshake
    {Vertex : Type*} [Fintype Vertex]
    (degree : Vertex → ℕ) (edges : ℕ)
    (hminimum : ∀ vertex, 2 ≤ degree vertex)
    (hhandshake : ∑ vertex, degree vertex = 2 * edges) :
    Fintype.card Vertex ≤ edges := by
  classical
  have hsum : ∑ _vertex : Vertex, 2 ≤ ∑ vertex, degree vertex := by
    apply Finset.sum_le_sum
    intro vertex _hvertex
    exact hminimum vertex
  have htwice : 2 * Fintype.card Vertex ≤ 2 * edges := by
    calc
      2 * Fintype.card Vertex = ∑ _vertex : Vertex, 2 := by simp [mul_comm]
      _ ≤ ∑ vertex, degree vertex := hsum
      _ = 2 * edges := hhandshake
  exact Nat.le_of_mul_le_mul_left htwice (by omega)

/-- A positive even natural-number degree is at least two.  This is the local
arithmetic that turns “connected/non-isolated and Eulerian” into the minimum
degree premise used by the handshaking bound. -/
theorem two_le_degree_of_positive_even
    (degree : ℕ) (hpositive : 0 < degree) (heven : Even degree) :
    2 ≤ degree := by
  obtain ⟨half, hdegree⟩ := heven
  omega

/-- A finite graph with positive even degree at every surviving vertex and the
handshaking identity satisfies `|V| ≤ |E|`.  Positivity is the only connectivity
consequence needed by the count; evenness upgrades it to minimum degree two. -/
theorem vertices_le_edges_of_positive_evenDegrees_of_handshake
    {Vertex : Type*} [Fintype Vertex]
    (degree : Vertex → ℕ) (edges : ℕ)
    (hpositive : ∀ vertex, 0 < degree vertex)
    (heven : ∀ vertex, Even (degree vertex))
    (hhandshake : ∑ vertex, degree vertex = 2 * edges) :
    Fintype.card Vertex ≤ edges := by
  apply vertices_le_edges_of_minDegree_two_of_handshake degree edges
  · intro vertex
    exact two_le_degree_of_positive_even
      (degree vertex) (hpositive vertex) (heven vertex)
  · exact hhandshake

/-- Closed evaluation of a balanced rank-one kernel on an all-even connected test graph after
the vertex sums in the graph homomorphism count have factorized. -/
noncomputable def balancedRankOneGraphSum (p : ℕ) (vertices edges : ℕ) : ℝ :=
  (p : ℝ) ^ vertices / (p : ℝ) ^ (edges + 1)

/-- At `p = 0` the denominator is `0 ^ (edges + 1) = 0`, so Mathlib returns `0` for the whole
ratio.  A zero-dimensional traffic sum has no balanced value; the biological range is `p ≥ 1`. -/
theorem balancedRankOneGraphSum_at_zero_dimension_is_junk (vertices edges : ℕ) :
    balancedRankOneGraphSum 0 vertices edges = 0 := by
  simp [balancedRankOneGraphSum]


/-- The closed rank-one graph coordinate obeys the universal `1/p` bound. -/
theorem balancedRankOneGraphSum_le_inv
    (p vertices edges : ℕ) (hp : 1 ≤ p) (hev : vertices ≤ edges) :
    balancedRankOneGraphSum p vertices edges ≤ 1 / (p : ℝ) := by
  apply rankOneGraphSum_le_inv (p : ℝ) vertices edges
  · exact_mod_cast hp
  · exact hev

/-- A positive rank-one spike can leave every fixed connected traffic coordinate unchanged in
the limit: every nonzero all-even contribution is squeezed by `1/p`, while an odd-degree
coordinate is exactly zero by balancedness. -/
theorem balancedRankOneGraphSum_tendsto_zero (vertices edges : ℕ) (hev : vertices ≤ edges) :
    Filter.Tendsto (fun p : ℕ ↦ balancedRankOneGraphSum (p + 1) vertices edges)
      Filter.atTop (nhds 0) := by
  have hnonneg : ∀ p : ℕ, 0 ≤ balancedRankOneGraphSum (p + 1) vertices edges := by
    intro p
    unfold balancedRankOneGraphSum
    positivity
  have hupper : ∀ p : ℕ,
      balancedRankOneGraphSum (p + 1) vertices edges ≤ 1 / ((p + 1 : ℕ) : ℝ) := by
    intro p
    exact balancedRankOneGraphSum_le_inv (p + 1) vertices edges (Nat.succ_le_succ (Nat.zero_le p))
      hev
  have hdenom : Filter.Tendsto (fun p : ℕ ↦ ((p + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1) using 1
  have hinv : Filter.Tendsto (fun p : ℕ ↦ 1 / ((p + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [one_div] using hdenom.inv_tendsto_atTop
  exact squeeze_zero hnonneg hupper hinv

/-- Closed balanced-spike coordinate for an arbitrary connected test graph: odd-degree graphs
vanish exactly, while all-even graphs use the factorized rank-one graph sum. -/
noncomputable def balancedRankOneTrafficCoordinate
    (hasOddDegree : Bool) (p vertices edges : ℕ) : ℝ :=
  if hasOddDegree then 0 else balancedRankOneGraphSum p vertices edges

/-- Reference evaluations: an odd-degree term contributes nothing, and an even-degree term
contributes the balanced graph sum.  Both branches, since pinning one leaves the other free. -/
theorem balancedRankOneTrafficCoordinate_at_reference_point (p vertices edges : ℕ) :
    balancedRankOneTrafficCoordinate true p vertices edges = 0 ∧
      balancedRankOneTrafficCoordinate false p vertices edges
        = balancedRankOneGraphSum p vertices edges := by
  constructor <;> simp [balancedRankOneTrafficCoordinate]


/-- Every fixed connected graph coordinate of the balanced positive rank-one
spike vanishes.  Odd-degree coordinates vanish identically; the edge bound is
therefore required only in the all-even branch. -/
theorem balancedRankOneTrafficCoordinate_tendsto_zero
    (hasOddDegree : Bool) (vertices edges : ℕ)
    (hev : hasOddDegree = false → vertices ≤ edges) :
    Filter.Tendsto
      (fun p : ℕ ↦ balancedRankOneTrafficCoordinate hasOddDegree (p + 1) vertices edges)
      Filter.atTop (nhds 0) := by
  cases hodd : hasOddDegree with
  | false =>
      simpa [balancedRankOneTrafficCoordinate, hodd] using
        balancedRankOneGraphSum_tendsto_zero vertices edges (hev hodd)
  | true =>
      simp [balancedRankOneTrafficCoordinate]

/-- A fixed graph expansion contains only finitely many nonempty choices of
rank-one spike edges.  After contracting its identity edges, each choice has a
coefficient and one balanced rank-one coordinate.  This definition records the
complete correction obtained by summing those contracted terms. -/
noncomputable def finiteRankOneTrafficCorrection
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ) (population : ℕ) : ℝ :=
  ∑ term,
    coefficient term *
      balancedRankOneTrafficCoordinate (hasOddDegree term) population
        (vertices term) (edges term)

/-- **Finite expansion closes rank-one traffic invisibility.**  If every
contracted nonempty spike graph satisfies the connected all-even edge bound
`|V| ≤ |E|` whenever it is nonzero, then their entire fixed-graph correction
vanishes.  This is the analytic step from one contracted term to the expansion
of `(aI + λP)`; the graph contraction supplies `hconnected`. -/
theorem finiteRankOneTrafficCorrection_tendsto_zero
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term) :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0) := by
  classical
  have hterm : ∀ term : Term,
      Filter.Tendsto
        (fun population : ℕ ↦ coefficient term *
          balancedRankOneTrafficCoordinate (hasOddDegree term) (population + 1)
            (vertices term) (edges term))
        Filter.atTop (nhds 0) := by
    intro term
    simpa using
      (balancedRankOneTrafficCoordinate_tendsto_zero
        (hasOddDegree term) (vertices term) (edges term) (hconnected term)).const_mul
          (coefficient term)
  have hsum := tendsto_finset_sum Finset.univ
    (fun term _hterm ↦ hterm term)
  simpa [finiteRankOneTrafficCorrection] using hsum

/-- The finite traffic correction vanishes from graph-local degree data, with
no pre-assumed cardinal inequality.  Each all-even contracted term supplies
its degree function, minimum degree two, and handshaking identity; odd-degree
terms require no graph bound because balancedness kills them exactly. -/
theorem finiteRankOneTrafficCorrection_tendsto_zero_of_degreeData
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (degree : ∀ term, Fin (vertices term) → ℕ)
    (hminimum : ∀ term, hasOddDegree term = false →
      ∀ vertex, 2 ≤ degree term vertex)
    (hhandshake : ∀ term, hasOddDegree term = false →
      ∑ vertex, degree term vertex = 2 * edges term) :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0) := by
  apply finiteRankOneTrafficCorrection_tendsto_zero
  intro term heven
  have hbound := vertices_le_edges_of_minDegree_two_of_handshake
    (degree term) (edges term) (hminimum term heven) (hhandshake term heven)
  simpa using hbound

/-- **Connected-Eulerian degree data suffice for finite traffic
invisibility.**  On every all-even contracted term, positive degrees exclude
isolated vertices, degree parity supplies the minimum-degree-two bound, and
handshaking supplies `|V| ≤ |E|`.  Odd-degree terms still vanish without any of
these hypotheses. -/
theorem finiteRankOneTrafficCorrection_tendsto_zero_of_positiveEvenDegreeData
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (degree : ∀ term, Fin (vertices term) → ℕ)
    (hpositive : ∀ term, hasOddDegree term = false →
      ∀ vertex, 0 < degree term vertex)
    (heven : ∀ term, hasOddDegree term = false →
      ∀ vertex, Even (degree term vertex))
    (hhandshake : ∀ term, hasOddDegree term = false →
      ∑ vertex, degree term vertex = 2 * edges term) :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0) := by
  apply finiteRankOneTrafficCorrection_tendsto_zero_of_degreeData
    coefficient hasOddDegree vertices edges degree
  · intro term hallEven vertex
    exact two_le_degree_of_positive_even
      (degree term vertex) (hpositive term hallEven vertex) (heven term hallEven vertex)
  · exact hhandshake

/-! ### Positive-cone and ground-state certificates -/

/-- Balanced finite coordinates: `p` positive-sign and `p` negative-sign
locations. -/
abbrev BalancedRankOneCoordinate (population : ℕ) :=
  Sum (Fin population) (Fin population)

/-- The balanced hidden sign vector. -/
def balancedRankOneSign (population : ℕ) :
    BalancedRankOneCoordinate population → ℝ
  | Sum.inl _coordinate => 1
  | Sum.inr _coordinate => -1

/-- The hidden sign vector has exactly zero coordinate sum. -/
theorem balancedRankOneSign_sum_eq_zero (population : ℕ) :
    ∑ coordinate, balancedRankOneSign population coordinate = 0 := by
  simp [balancedRankOneSign]

/-- Its squared Euclidean norm is exactly the ambient dimension `2p`. -/
theorem balancedRankOneSign_dot_self (population : ℕ) :
    balancedRankOneSign population ⬝ᵥ balancedRankOneSign population =
      (2 * population : ℕ) := by
  simp [dotProduct, balancedRankOneSign]
  ring

/-- The normalized outer-product projector onto the balanced hidden
direction.  The positive-population premise is imposed on the theorems that
use its normalization. -/
noncomputable def balancedRankOneProjector (population : ℕ) :
    Matrix (BalancedRankOneCoordinate population)
      (BalancedRankOneCoordinate population) ℝ :=
  (((2 * population : ℕ) : ℝ)⁻¹) •
    Matrix.vecMulVec (balancedRankOneSign population) (balancedRankOneSign population)

/-- The normalized balanced outer product is positive semidefinite. -/
theorem balancedRankOneProjector_posSemidef (population : ℕ) :
    (balancedRankOneProjector population).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · simpa using Matrix.posSemidef_vecMulVec_self_star
      (balancedRankOneSign population)
  · positivity

/-- The concrete finite covariance witness `aI + λP`. -/
noncomputable def balancedRankOneCovariance
    (baseline spikeStrength : ℝ) (population : ℕ) :
    Matrix (BalancedRankOneCoordinate population)
      (BalancedRankOneCoordinate population) ℝ :=
  Matrix.diagonal (fun _coordinate ↦ baseline) +
    spikeStrength • balancedRankOneProjector population

/-- For nonnegative baseline and spike strength, the concrete covariance lies
in the positive-semidefinite cone. -/
theorem balancedRankOneCovariance_posSemidef
    (baseline spikeStrength : ℝ) (population : ℕ)
    (hbaseline : 0 ≤ baseline) (hspike : 0 ≤ spikeStrength) :
    (balancedRankOneCovariance baseline spikeStrength population).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.diagonal (fun _coordinate ↦ hbaseline)
  · exact (balancedRankOneProjector_posSemidef population).smul hspike

/-- Quadratic form of a real finite covariance matrix. -/
noncomputable def finiteMatrixQuadraticForm
    {Coordinate : Type*} [Fintype Coordinate]
    (matrix : Matrix Coordinate Coordinate ℝ) (vector : Coordinate → ℝ) : ℝ :=
  vector ⬝ᵥ (matrix *ᵥ vector)

/-- The concrete rank-one covariance has exactly the baseline energy plus the
squared hidden-direction alignment. -/
theorem balancedRankOneCovariance_quadraticForm
    (baseline spikeStrength : ℝ) (population : ℕ)
    (vector : BalancedRankOneCoordinate population → ℝ) :
    finiteMatrixQuadraticForm
        (balancedRankOneCovariance baseline spikeStrength population) vector =
      baseline * (∑ coordinate, vector coordinate ^ 2) +
        spikeStrength * (((2 * population : ℕ) : ℝ)⁻¹) *
          (balancedRankOneSign population ⬝ᵥ vector) ^ 2 := by
  classical
  have hdiagonalMulVec :
      Matrix.diagonal (fun _coordinate ↦ baseline) *ᵥ vector =
        baseline • vector := by
    ext coordinate
    simp [Matrix.mulVec]
  have hdiagonal :
      vector ⬝ᵥ
          (Matrix.diagonal (fun _coordinate ↦ baseline) *ᵥ vector) =
        baseline * ∑ coordinate, vector coordinate ^ 2 := by
    rw [hdiagonalMulVec]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, pow_two]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _hcoordinate
    ring
  rw [finiteMatrixQuadraticForm, balancedRankOneCovariance,
    Matrix.add_mulVec, dotProduct_add, hdiagonal]
  simp only [balancedRankOneProjector, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct_smul]
  simp
  rw [dotProduct_comm vector (balancedRankOneSign population)]
  ring

/-- A Rademacher-valued vector has squared norm equal to the ambient
dimension `2p`. -/
theorem balancedRademacher_squaredNorm
    (population : ℕ) (vector : BalancedRankOneCoordinate population → ℝ)
    (hrademacher : ∀ coordinate, vector coordinate ^ 2 = 1) :
    ∑ coordinate, vector coordinate ^ 2 = (2 * population : ℕ) := by
  calc
    (∑ coordinate, vector coordinate ^ 2) = ∑ _coordinate, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      exact hrademacher coordinate
    _ = (2 * population : ℕ) := by
      simp [BalancedRankOneCoordinate]
      ring

/-- On Rademacher vectors, the concrete covariance energy is exactly the
baseline extensive term plus the normalized Curie--Weiss alignment energy. -/
theorem balancedRankOneCovariance_rademacherEnergy
    (baseline spikeStrength : ℝ) (population : ℕ)
    (vector : BalancedRankOneCoordinate population → ℝ)
    (hrademacher : ∀ coordinate, vector coordinate ^ 2 = 1) :
    finiteMatrixQuadraticForm
        (balancedRankOneCovariance baseline spikeStrength population) vector =
      baseline * (2 * population : ℕ) +
        spikeStrength * (((2 * population : ℕ) : ℝ)⁻¹) *
          (balancedRankOneSign population ⬝ᵥ vector) ^ 2 := by
  rw [balancedRankOneCovariance_quadraticForm,
    balancedRademacher_squaredNorm population vector hrademacher]

/-- **Hamiltonian bridge to finite Curie--Weiss pressure.**  After subtracting
the baseline covariance energy and multiplying by `temperature/2`, the matrix
Hamiltonian is exactly `tλ/(2N) * alignment²` with `N=2p`, the exponent used
by `finiteCWPartition`. -/
theorem balancedRankOneCovariance_rademacherExponent_eq_finiteCW
    (baseline spikeStrength temperature : ℝ) (population : ℕ)
    (vector : BalancedRankOneCoordinate population → ℝ)
    (hrademacher : ∀ coordinate, vector coordinate ^ 2 = 1) :
    temperature / 2 *
        (finiteMatrixQuadraticForm
            (balancedRankOneCovariance baseline spikeStrength population) vector -
          baseline * (2 * population : ℕ)) =
      (temperature * spikeStrength) /
          (2 * ((2 * population : ℕ) : ℝ)) *
        (balancedRankOneSign population ⬝ᵥ vector) ^ 2 := by
  rw [balancedRankOneCovariance_rademacherEnergy
    baseline spikeStrength population vector hrademacher]
  ring

/-- The constant-one vector on an arbitrary coordinate type. -/
def constantOneVector {Coordinate : Type*} : Coordinate → ℝ :=
  fun _coordinate ↦ 1

@[simp] theorem constantOneVector_apply {Coordinate : Type*}
    (coordinate : Coordinate) : constantOneVector coordinate = 1 := rfl

/-- The all-one Rademacher vector is orthogonal to the balanced hidden
direction. -/
def balancedRankOneOrthogonalSpin (population : ℕ) :
    BalancedRankOneCoordinate population → ℝ :=
  constantOneVector

/-- The explicit orthogonal spin is genuinely Rademacher-valued. -/
theorem balancedRankOneOrthogonalSpin_isRademacher (population : ℕ) :
    ∀ coordinate, balancedRankOneOrthogonalSpin population coordinate ^ 2 = 1 := by
  intro coordinate
  simp [balancedRankOneOrthogonalSpin]

/-- Balancedness makes the all-one spin exactly orthogonal to the hidden
direction, at every finite population. -/
theorem balancedRankOneOrthogonalSpin_alignment_eq_zero (population : ℕ) :
    balancedRankOneSign population ⬝ᵥ
        balancedRankOneOrthogonalSpin population = 0 := by
  simpa [dotProduct, balancedRankOneOrthogonalSpin] using
    balancedRankOneSign_sum_eq_zero population

/-- The hidden sign vector itself is an explicit aligned Rademacher spin. -/
theorem balancedRankOneSign_isRademacher (population : ℕ) :
    ∀ coordinate, balancedRankOneSign population coordinate ^ 2 = 1 := by
  intro coordinate
  cases coordinate <;> simp [balancedRankOneSign]

/-- **Concrete matrix-level ground-state certificate.**  Every Rademacher
spin has energy at least the unspiked baseline, the explicit all-one spin
attains it, and the explicit hidden-sign spin has strictly larger energy when
the spike and population are positive.  Thus the lower ground state is
unchanged even though the same covariance has a supercritical pressure
transition. -/
theorem balancedRankOneCovariance_groundState_certificate
    (baseline spikeStrength : ℝ) (population : ℕ)
    (hspike : 0 < spikeStrength) (hpopulation : 0 < population) :
    (∀ vector : BalancedRankOneCoordinate population → ℝ,
      (∀ coordinate, vector coordinate ^ 2 = 1) →
        baseline * (2 * population : ℕ) ≤
          finiteMatrixQuadraticForm
            (balancedRankOneCovariance baseline spikeStrength population) vector) ∧
      finiteMatrixQuadraticForm
          (balancedRankOneCovariance baseline spikeStrength population)
          (balancedRankOneOrthogonalSpin population) =
        baseline * (2 * population : ℕ) ∧
      baseline * (2 * population : ℕ) <
        finiteMatrixQuadraticForm
          (balancedRankOneCovariance baseline spikeStrength population)
          (balancedRankOneSign population) := by
  have hdimension : 0 < (((2 * population : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hpopulation
  constructor
  · intro vector hrademacher
    rw [balancedRankOneCovariance_rademacherEnergy
      baseline spikeStrength population vector hrademacher]
    have hcorrection : 0 ≤
        spikeStrength * (((2 * population : ℕ) : ℝ)⁻¹) *
          (balancedRankOneSign population ⬝ᵥ vector) ^ 2 := by
      positivity
    linarith
  constructor
  · rw [balancedRankOneCovariance_rademacherEnergy
      baseline spikeStrength population (balancedRankOneOrthogonalSpin population)
      (balancedRankOneOrthogonalSpin_isRademacher population),
      balancedRankOneOrthogonalSpin_alignment_eq_zero]
    ring
  · rw [balancedRankOneCovariance_rademacherEnergy
      baseline spikeStrength population (balancedRankOneSign population)
      (balancedRankOneSign_isRademacher population),
      balancedRankOneSign_dot_self]
    have hcorrection : 0 <
        spikeStrength * (((2 * population : ℕ) : ℝ)⁻¹) *
          (((2 * population : ℕ) : ℝ)) ^ 2 := by
      positivity
    linarith

/-- Per-coordinate quadratic energy of a rank-one positive spike, expressed through the spin's
alignment with the hidden direction. -/
noncomputable def rankOneEnergyDensity (baseline spikeStrength population alignment : ℝ) : ℝ :=
  baseline + spikeStrength * (alignment / population) ^ 2

/-- With no population the alignment share divides by zero and Mathlib returns `0`, so the
density reports the baseline alone: the spike contributes nothing where the true reading is
that the share is undefined. -/
theorem rankOneEnergyDensity_at_zero_population_is_junk
    (baseline spikeStrength alignment : ℝ) :
    rankOneEnergyDensity baseline spikeStrength 0 alignment = baseline := by
  simp [rankOneEnergyDensity]


/-- A positive-semidefinite rank-one spike can only raise the energy. -/
theorem rankOneEnergyDensity_ge_baseline
    (baseline spikeStrength population alignment : ℝ) (hspike : 0 ≤ spikeStrength) :
    baseline ≤ rankOneEnergyDensity baseline spikeStrength population alignment := by
  unfold rankOneEnergyDensity
  have : 0 ≤ spikeStrength * (alignment / population) ^ 2 := by positivity
  linarith

/-- An orthogonal spin has exactly the unspiked ground-state energy. -/
@[simp] theorem rankOneEnergyDensity_orthogonal
    (baseline spikeStrength population : ℝ) :
    rankOneEnergyDensity baseline spikeStrength population 0 = baseline := by
  simp [rankOneEnergyDensity]

/-- A fully aligned spin exposes the complete spike strength. -/
theorem rankOneEnergyDensity_aligned
    (baseline spikeStrength population : ℝ) (hpopulation : population ≠ 0) :
    rankOneEnergyDensity baseline spikeStrength population population =
      baseline + spikeStrength := by
  simp [rankOneEnergyDensity, hpopulation]

/-- **Ground-state dichotomy failure, as an exact certificate.**  If the spin class contains one
configuration orthogonal to the hidden direction, every spiked energy is at least the baseline
and that configuration attains it.  Yet an aligned configuration has larger energy when the
spike is positive.  Thus identical lower ground-state energy does not control the upper tail. -/
theorem rankOne_groundState_certificate
    {Spin : Type*} (alignment : Spin → ℝ) (orthogonal : Spin)
    (baseline spikeStrength population : ℝ) (hspike : 0 ≤ spikeStrength)
    (horthogonal : alignment orthogonal = 0) :
    (∀ spin, baseline ≤
        rankOneEnergyDensity baseline spikeStrength population (alignment spin)) ∧
      rankOneEnergyDensity baseline spikeStrength population (alignment orthogonal) = baseline := by
  constructor
  · intro spin
    exact rankOneEnergyDensity_ge_baseline baseline spikeStrength population (alignment spin)
      hspike
  · rw [horthogonal, rankOneEnergyDensity_orthogonal]

end RankOneInvisibility

section CurieWeissWindow

/-- The Curie-Weiss rate function for a balanced Rademacher magnetisation.

    Empirical status: NOT AN EMPIRICAL CLAIM. This is the Cramer rate function of
    a fair coin, fixed by that description alone; no measurement bears on it. -/
noncomputable def cwRate (m : ℝ) : ℝ :=
  (1 + m) / 2 * Real.log (1 + m) + (1 - m) / 2 * Real.log (1 - m)

/-- The endpoint rate is `log 2`; the vanishing factor multiplies `log 0` and contributes zero. -/
@[simp] theorem cwRate_one : cwRate 1 = Real.log 2 := by
  unfold cwRate
  norm_num

/-- The negative endpoint has the same Bernoulli rate as the positive
endpoint. -/
@[simp] theorem cwRate_neg_one : cwRate (-1) = Real.log 2 := by
  unfold cwRate
  norm_num

/-- The quantity whose supremum over `m` is the overlap-pressure gap.

    Empirical status: NOT AN EMPIRICAL CLAIM. -/
noncomputable def cwObjective (tlam m : ℝ) : ℝ :=
  tlam / 2 * m ^ 2 - cwRate m

/-- Pinsker gap for the balanced Bernoulli pair. -/
noncomputable def cwPinskerGap (m : ℝ) : ℝ :=
  cwRate m - m ^ 2 / 2

/-- Reference evaluation, at a point where the body is NONZERO.

The previous point was `cwPinskerGap 0 = 0`. Zero magnetisation is where the
rate function and the quadratic both vanish, so every rescaling `c * body`
satisfied it and the theorem rejected nothing -- `scale_competitor_ne_iff`.

The endpoint is the one place a transcendental body has an exact rational-plus-
log value: `cwRate_one` gives `cwRate 1 = log 2`, so the gap is `log 2 - 1/2`,
about `0.1931`. Being nonzero is the whole point; a body with `m ^ 2` in place of
`m ^ 2 / 2` gives `log 2 - 1` here instead. -/
theorem cwPinskerGap_at_reference_point :
    cwPinskerGap 1 = Real.log 2 - 1 / 2 := by
  unfold cwPinskerGap
  rw [cwRate_one]
  norm_num


/-- Derivative of the Pinsker gap on the open magnetisation interval. -/
noncomputable def cwPinskerGapDerivative (m : ℝ) : ℝ :=
  (Real.log (1 + m) - Real.log (1 - m)) / 2 - m

/-- Reference evaluation, at a point where the body is NONZERO.

The previous point was `cwPinskerGapDerivative 0 = 0`, the unique zero of this
function on `[0, 1)` -- `cwPinskerGapDerivative_nonneg` and the strict growth
above it are what make it unique. So the old point was the ONE place no
rescaling could be rejected.

`m = 1/2` is chosen rather than the endpoint on purpose: at `m = 1` the body
evaluates `Real.log 0`, which Mathlib sends to junk-zero, and a reference value
read off a junk branch certifies nothing. At `m = 1/2` the two logarithms
combine exactly, `log (3/2) - log (1/2) = log 3`, giving `log 3 / 2 - 1/2`,
about `0.0493`. Value confirmed against the corpus's own executable form. -/
theorem cwPinskerGapDerivative_at_reference_point :
    cwPinskerGapDerivative (1 / 2) = Real.log 3 / 2 - 1 / 2 := by
  have h : Real.log (1 + 1 / 2) - Real.log (1 - 1 / 2) = Real.log 3 := by
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  unfold cwPinskerGapDerivative
  rw [h]


/-- Exact derivative of the Bernoulli Pinsker gap away from the two endpoints. -/
theorem hasDerivAt_cwPinskerGap {m : ℝ} (hm : |m| < 1) :
    HasDerivAt cwPinskerGap (cwPinskerGapDerivative m) m := by
  have hplus : 1 + m ≠ 0 := by
    rw [abs_lt] at hm
    linarith
  have hminus : 1 - m ≠ 0 := by
    rw [abs_lt] at hm
    linarith
  have hplusBase : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 m := by
    simpa using (hasDerivAt_const m 1).add (hasDerivAt_id m)
  have hminusBase : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) m := by
    simpa using (hasDerivAt_const m 1).sub (hasDerivAt_id m)
  have hplusTerm : HasDerivAt
      (fun x : ℝ ↦ (1 + x) / 2 * Real.log (1 + x))
      (Real.log (1 + m) / 2 + 1 / 2) m := by
    convert (hplusBase.div_const 2).mul (hplusBase.log hplus) using 1
    all_goals field_simp
  have hminusTerm : HasDerivAt
      (fun x : ℝ ↦ (1 - x) / 2 * Real.log (1 - x))
      (-Real.log (1 - m) / 2 - 1 / 2) m := by
    convert (hminusBase.div_const 2).mul (hminusBase.log hminus) using 1
    all_goals field_simp
    all_goals ring
  have hrate : HasDerivAt cwRate
      ((Real.log (1 + m) - Real.log (1 - m)) / 2) m := by
    unfold cwRate
    convert hplusTerm.add hminusTerm using 1
    all_goals ring
  have hquadratic : HasDerivAt (fun x : ℝ ↦ x ^ 2 / 2) m m := by
    convert ((hasDerivAt_id m).pow 2).div_const 2 using 1
    all_goals norm_num
  unfold cwPinskerGap cwPinskerGapDerivative
  convert hrate.sub hquadratic using 1

/-- On the nonnegative half interval, the Pinsker-gap derivative is nonnegative.  The analytic
input is Mathlib's elementary bound `2x/(x+2) ≤ log(1+x)`. -/
theorem cwPinskerGapDerivative_nonneg {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    0 ≤ cwPinskerGapDerivative m := by
  have hden : 1 - m ≠ 0 := by linarith
  have hx : 0 ≤ 2 * m / (1 - m) := div_nonneg (by positivity) (by linarith)
  have hlog := Real.le_log_one_add_of_nonneg hx
  have harg : 1 + 2 * m / (1 - m) = (1 + m) / (1 - m) := by
    field_simp
    ring
  have hlhs : 2 * (2 * m / (1 - m)) / (2 * m / (1 - m) + 2) = 2 * m := by
    field_simp
    ring
  rw [harg, hlhs, Real.log_div (by linarith : 1 + m ≠ 0) hden] at hlog
  unfold cwPinskerGapDerivative
  linarith

/-- The Bernoulli Pinsker gap is even. -/
theorem cwPinskerGap_neg (m : ℝ) : cwPinskerGap (-m) = cwPinskerGap m := by
  unfold cwPinskerGap cwRate
  simp only [sub_neg_eq_add, neg_sq]
  ring_nf

/-- Pinsker's inequality on the nonnegative open half interval. -/
theorem cwPinskerGap_nonneg_of_nonneg_of_lt_one
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) : 0 ≤ cwPinskerGap m := by
  have hcontinuous : ContinuousOn cwPinskerGap (Set.Ico (0 : ℝ) 1) := by
    intro x hx
    have habs : |x| < 1 := (abs_lt).2 ⟨by linarith [hx.1], hx.2⟩
    exact (hasDerivAt_cwPinskerGap habs).continuousAt.continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ cwPinskerGap (interior (Set.Ico (0 : ℝ) 1)) := by
    intro x hx
    rw [interior_Ico] at hx
    have habs : |x| < 1 := (abs_lt).2 ⟨by linarith [hx.1], hx.2⟩
    exact (hasDerivAt_cwPinskerGap habs).differentiableAt.differentiableWithinAt
  have hmonotone : MonotoneOn cwPinskerGap (Set.Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico (0 : ℝ) 1) hcontinuous hdifferentiable
    intro x hx
    rw [interior_Ico] at hx
    have habs : |x| < 1 := (abs_lt).2 ⟨by linarith [hx.1], hx.2⟩
    rw [(hasDerivAt_cwPinskerGap habs).deriv]
    exact cwPinskerGapDerivative_nonneg hx.1.le hx.2
  have hzero : cwPinskerGap 0 = 0 := by simp [cwPinskerGap, cwRate]
  rw [← hzero]
  exact hmonotone (by norm_num) ⟨hm0, hm1⟩ hm0

/-- The endpoint Pinsker gap is positive. -/
theorem cwPinskerGap_one_pos : 0 < cwPinskerGap 1 := by
  rw [cwPinskerGap, cwRate_one]
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  norm_num at hlog ⊢
  linarith

/-- **Bernoulli Pinsker inequality in the magnetisation coordinate.** -/
theorem cw_rate_lower_bound (m : ℝ) (hm : |m| ≤ 1) :
    m ^ 2 / 2 ≤ cwRate m := by
  have hgap : 0 ≤ cwPinskerGap m := by
    by_cases hinterior : |m| < 1
    · by_cases hm0 : 0 ≤ m
      · exact cwPinskerGap_nonneg_of_nonneg_of_lt_one hm0 ((abs_lt.mp hinterior).2)
      · rw [← cwPinskerGap_neg m]
        apply cwPinskerGap_nonneg_of_nonneg_of_lt_one
        · linarith
        · linarith [(abs_lt.mp hinterior).1]
    · have habs : |m| = 1 := le_antisymm hm (not_lt.mp hinterior)
      have hsq : m * m = 1 * 1 := by
        rw [← abs_eq_iff_mul_self_eq]
        simpa using habs
      rcases mul_self_eq_mul_self_iff.mp hsq with hm1 | hm1
      · rw [hm1]
        exact cwPinskerGap_one_pos.le
      · rw [hm1, cwPinskerGap_neg]
        exact cwPinskerGap_one_pos.le
  unfold cwPinskerGap at hgap
  linarith

/-- Elementary upper bound on the Rademacher rate near the origin.  Unlike a Taylor expansion,
it is global on the nonnegative open interval and follows only from `log x ≤ x - 1`. -/
theorem cw_rate_upper_bound {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    cwRate m ≤ m ^ 2 * (1 + m) / (2 * (1 - m)) := by
  have hplus : 0 < 1 + m := by linarith
  have hminus : 0 < 1 - m := by linarith
  have hsq : 0 < 1 - m ^ 2 := by nlinarith
  have hproduct : 1 - m ^ 2 = (1 + m) * (1 - m) := by ring
  have hlogProduct :
      Real.log (1 - m ^ 2) = Real.log (1 + m) + Real.log (1 - m) := by
    rw [hproduct, Real.log_mul (ne_of_gt hplus) (ne_of_gt hminus)]
  have hlogRatio :
      Real.log ((1 + m) / (1 - m)) = Real.log (1 + m) - Real.log (1 - m) := by
    rw [Real.log_div (ne_of_gt hplus) (ne_of_gt hminus)]
  have hproductBound : Real.log (1 - m ^ 2) ≤ -(m ^ 2) := by
    have := Real.log_le_sub_one_of_pos hsq
    linarith
  have hratioBound : Real.log ((1 + m) / (1 - m)) ≤ 2 * m / (1 - m) := by
    have hratioPos : 0 < (1 + m) / (1 - m) := div_pos hplus hminus
    have := Real.log_le_sub_one_of_pos hratioPos
    have hratio : (1 + m) / (1 - m) - 1 = 2 * m / (1 - m) := by
      field_simp
      ring
    rwa [hratio] at this
  have hproductScaled :
      Real.log (1 - m ^ 2) / 2 ≤ -(m ^ 2) / 2 := by linarith
  have hratioScaled :
      m / 2 * Real.log ((1 + m) / (1 - m)) ≤
        m / 2 * (2 * m / (1 - m)) :=
    mul_le_mul_of_nonneg_left hratioBound (by positivity)
  calc
    cwRate m = Real.log (1 - m ^ 2) / 2 +
        m / 2 * Real.log ((1 + m) / (1 - m)) := by
      unfold cwRate
      rw [hlogProduct, hlogRatio]
      ring
    _ ≤ -(m ^ 2) / 2 + m / 2 * (2 * m / (1 - m)) := by linarith
    _ = m ^ 2 * (1 + m) / (2 * (1 - m)) := by
      field_simp
      ring

/-- **Below the critical point the pressure gap vanishes identically.**

    At `tlam ≤ 1` the objective is non-positive at every admissible `m`, so its
    supremum is `0` and the two designs have EQUAL pressure -- not equal to
    leading order, equal. The critical point is therefore exactly `t = λ⁻¹`.

    The analytic input is `cw_rate_lower_bound`, Pinsker's inequality for a Bernoulli pair
    against the fair coin, proved above from Mathlib's logarithm bound and the mean-value theorem.

    Empirical status: NOT AN EMPIRICAL CLAIM. -/
theorem curieWeiss_subcritical
    (tlam : ℝ) (htl1 : tlam ≤ 1) (m : ℝ) (hm : |m| ≤ 1) :
    cwObjective tlam m ≤ 0 := by
  have hsq : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
  have h1 : tlam / 2 * m ^ 2 ≤ m ^ 2 / 2 := by nlinarith
  have h2 : m ^ 2 / 2 ≤ cwRate m := cw_rate_lower_bound m hm
  unfold cwObjective
  linarith

/-- **At zero magnetisation the objective is zero**, so the supremum below the
    critical point is attained and equals `0` rather than merely being bounded
    by it. Without this the previous theorem would leave open that the gap is
    negative, which a pressure difference of this form cannot be. -/
@[simp] theorem cwObjective_at_zero (tlam : ℝ) : cwObjective tlam 0 = 0 := by
  unfold cwObjective cwRate
  norm_num

/-- **The rate function vanishes at zero**, the normalisation the previous two
    results rely on. -/
@[simp] theorem cwRate_zero : cwRate 0 = 0 := by
  unfold cwRate; norm_num

/-- At full magnetisation the variational pressure objective is `tλ/2 - log 2`. -/
theorem cwObjective_at_one (tlam : ℝ) :
    cwObjective tlam 1 = tlam / 2 - Real.log 2 := by
  simp [cwObjective]

/-- The two fully aligned endpoints have the same Curie--Weiss objective. -/
theorem cwObjective_at_neg_one (tlam : ℝ) :
    cwObjective tlam (-1) = tlam / 2 - Real.log 2 := by
  simp [cwObjective]

/-- **A completely elementary positive-temperature separation.**  Whenever
`2 log 2 < tλ`, the single fully aligned state already makes the overlap-pressure variational
objective positive.  This weaker-than-sharp window is sufficient to refute positive-cone traffic
sufficiency without importing the local series proof of the exact threshold. -/
theorem curieWeiss_supercritical_witness (tlam : ℝ) (hlarge : 2 * Real.log 2 < tlam) :
    0 < cwObjective tlam 1 := by
  rw [cwObjective_at_one]
  linarith

/-- The sharp `tλ > 1` implication reduces exactly to the local strict upper bound on the
Rademacher rate function.  This theorem keeps the remaining analytic input visible: it does not
smuggle the desired phase transition into a structure field. -/
theorem curieWeiss_supercritical_of_local_rate_upper_bound
    (tlam m : ℝ) (hrate : cwRate m < tlam / 2 * m ^ 2) :
    0 < cwObjective tlam m := by
  unfold cwObjective
  linarith

/-- **Above the critical point the variational pressure is strictly positive.**  The explicit
trial magnetisation lies below `(tλ-1)/(tλ+1)`; the global logarithm bound above then beats its
quadratic energy.  No power-series or unformalized Varadhan step is used here. -/
theorem curieWeiss_supercritical (tlam : ℝ) (hcritical : 1 < tlam) :
    ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m := by
  let m : ℝ := (tlam - 1) / (2 * (tlam + 1))
  have hden : 0 < 2 * (tlam + 1) := by linarith
  have hm0 : 0 < m := by
    dsimp [m]
    exact div_pos (by linarith) hden
  have hm1 : m < 1 := by
    dsimp [m]
    rw [div_lt_one hden]
    linarith
  have hratio : (1 + m) / (1 - m) < tlam := by
    have hmden : 0 < 1 - m := by linarith
    rw [div_lt_iff₀ hmden]
    have htden : tlam + 1 ≠ 0 := by linarith
    have hmIdentity : (1 + tlam) * m = (tlam - 1) / 2 := by
      dsimp [m]
      field_simp
      ring
    nlinarith [hmIdentity]
  have hrate := cw_rate_upper_bound hm0.le hm1
  have hstrict : cwRate m < tlam / 2 * m ^ 2 := by
    calc
      cwRate m ≤ m ^ 2 * (1 + m) / (2 * (1 - m)) := hrate
      _ = m ^ 2 / 2 * ((1 + m) / (1 - m)) := by
        field_simp
      _ < m ^ 2 / 2 * tlam := by
        exact mul_lt_mul_of_pos_left hratio (by positivity)
      _ = tlam / 2 * m ^ 2 := by ring
  refine ⟨m, (abs_lt).2 ⟨by linarith, hm1⟩, ?_⟩
  exact curieWeiss_supercritical_of_local_rate_upper_bound tlam m hstrict

/-- The exact Curie–Weiss critical dichotomy for the variational pressure coordinate. -/
theorem curieWeiss_critical_dichotomy (tlam : ℝ) :
    (tlam ≤ 1 → ∀ m : ℝ, |m| ≤ 1 → cwObjective tlam m ≤ 0) ∧
      (1 < tlam → ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m) :=
  ⟨fun hcritical m hm ↦ curieWeiss_subcritical tlam hcritical m hm,
    curieWeiss_supercritical tlam⟩

/-- Values attained by the Curie--Weiss variational objective on the admissible
magnetisation interval. -/
noncomputable def cwPressureValueSet (tlam : ℝ) : Set ℝ :=
  cwObjective tlam '' Set.Icc (-1) 1

/-- The actual variational pressure gap, rather than only its pointwise
objective. -/
noncomputable def cwVariationalPressureGap (tlam : ℝ) : ℝ :=
  sSup (cwPressureValueSet tlam)

/-- Zero magnetisation makes the pressure-value set nonempty. -/
theorem cwPressureValueSet_nonempty (tlam : ℝ) :
    (cwPressureValueSet tlam).Nonempty := by
  refine ⟨0, 0, ?_, ?_⟩
  · constructor <;> norm_num
  · exact cwObjective_at_zero tlam

/-- The admissible pressure values are bounded above.  Pinsker's inequality
already supplies a uniform bound, so compactness or endpoint continuity is not
needed merely to define the supremum. -/
theorem cwPressureValueSet_bddAbove (tlam : ℝ) :
    BddAbove (cwPressureValueSet tlam) := by
  refine ⟨|tlam| / 2, ?_⟩
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  have habs : |m| ≤ 1 := (abs_le).2 hm
  have hrate : m ^ 2 / 2 ≤ cwRate m := cw_rate_lower_bound m habs
  have hrate0 : 0 ≤ cwRate m := le_trans (by positivity) hrate
  have hsq0 : 0 ≤ m ^ 2 := sq_nonneg m
  have hsq1 : m ^ 2 ≤ 1 := by
    have hproduct : 0 ≤ (1 - m) * (1 + m) :=
      mul_nonneg (by linarith [hm.2]) (by linarith [hm.1])
    nlinarith
  calc
    cwObjective tlam m ≤ tlam / 2 * m ^ 2 := by
      unfold cwObjective
      linarith
    _ ≤ |tlam| / 2 * m ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self tlam]) hsq0
    _ ≤ |tlam| / 2 := by
      nlinarith [abs_nonneg tlam]

/-- The variational pressure gap is always nonnegative because zero
magnetisation is admissible. -/
theorem cwVariationalPressureGap_nonneg (tlam : ℝ) :
    0 ≤ cwVariationalPressureGap tlam := by
  unfold cwVariationalPressureGap
  apply le_csSup (cwPressureValueSet_bddAbove tlam)
  exact ⟨0, by norm_num, cwObjective_at_zero tlam⟩

/-- Every admissible objective value lies below the variational pressure
supremum by construction. -/
theorem cwObjective_le_variationalPressureGap
    (tlam m : ℝ) (hm : |m| ≤ 1) :
    cwObjective tlam m ≤ cwVariationalPressureGap tlam := by
  unfold cwVariationalPressureGap
  apply le_csSup (cwPressureValueSet_bddAbove tlam)
  exact ⟨m, (abs_le).1 hm, rfl⟩

/-- Changing coupling changes each admissible Curie--Weiss objective by at
most half the coupling displacement. -/
theorem cwObjective_le_add_half_abs_coupling
    (left right m : ℝ) (hm : |m| ≤ 1) :
    cwObjective left m ≤ cwObjective right m + |left - right| / 2 := by
  have hsqNonnegative : 0 ≤ m ^ 2 := sq_nonneg m
  have hsqUpper : m ^ 2 ≤ 1 := by
    rw [abs_le] at hm
    nlinarith
  have hcoupling : (left - right) / 2 ≤ |left - right| / 2 := by
    linarith [le_abs_self (left - right)]
  have habsHalf : 0 ≤ |left - right| / 2 :=
    div_nonneg (abs_nonneg _) (by norm_num)
  calc
    cwObjective left m =
        cwObjective right m + (left - right) / 2 * m ^ 2 := by
      unfold cwObjective
      ring
    _ ≤ cwObjective right m + |left - right| / 2 * m ^ 2 := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_right hcoupling hsqNonnegative) _
    _ ≤ cwObjective right m + |left - right| / 2 := by
      simpa using add_le_add_left
        (mul_le_mul_of_nonneg_left hsqUpper habsHalf) (cwObjective right m)

/-- The variational pressure inherits the same one-sided coupling comparison
after taking the supremum over magnetisations. -/
theorem cwVariationalPressureGap_le_add_half_abs_coupling
    (left right : ℝ) :
    cwVariationalPressureGap left ≤
      cwVariationalPressureGap right + |left - right| / 2 := by
  unfold cwVariationalPressureGap
  apply csSup_le (cwPressureValueSet_nonempty left)
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  have habs : |m| ≤ 1 := (abs_le).2 hm
  exact (cwObjective_le_add_half_abs_coupling left right m habs).trans
    (add_le_add_right (cwObjective_le_variationalPressureGap right m habs) _)

/-- Sharp global modulus of continuity of the variational pressure. -/
theorem cwVariationalPressureGap_abs_sub_le_half_abs
    (left right : ℝ) :
    |cwVariationalPressureGap left - cwVariationalPressureGap right| ≤
      |left - right| / 2 := by
  rw [abs_le]
  constructor
  · have hreverse :=
      cwVariationalPressureGap_le_add_half_abs_coupling right left
    rw [abs_sub_comm] at hreverse
    linarith
  · have hforward :=
      cwVariationalPressureGap_le_add_half_abs_coupling left right
    linarith

/-- The variational pressure is globally `1/2`-Lipschitz in coupling. -/
theorem cwVariationalPressureGap_lipschitzWith :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal) cwVariationalPressureGap := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  rw [Real.dist_eq, Real.dist_eq]
  simpa [abs_sub_comm, mul_comm] using
    cwVariationalPressureGap_abs_sub_le_half_abs left right

/-- In particular the variational pressure profile is continuous globally. -/
theorem continuous_cwVariationalPressureGap :
    Continuous cwVariationalPressureGap :=
  cwVariationalPressureGap_lipschitzWith.continuous

/-- Increasing the positive quadratic coupling cannot decrease any objective
value. -/
theorem cwObjective_mono_coupling {left right : ℝ} (hle : left ≤ right)
    (m : ℝ) :
    cwObjective left m ≤ cwObjective right m := by
  unfold cwObjective
  nlinarith [sq_nonneg m]

/-- The variational pressure is monotone in coupling. -/
theorem monotone_cwVariationalPressureGap :
    Monotone cwVariationalPressureGap := by
  intro left right hle
  unfold cwVariationalPressureGap
  apply csSup_le (cwPressureValueSet_nonempty left)
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  exact (cwObjective_mono_coupling hle m).trans
    (cwObjective_le_variationalPressureGap right m ((abs_le).2 hm))

/-- Each fixed-magnetisation objective is affine in the coupling parameter. -/
theorem cwObjective_affine_coupling
    (left right weightLeft weightRight m : ℝ)
    (hweights : weightLeft + weightRight = 1) :
    cwObjective (weightLeft * left + weightRight * right) m =
      weightLeft * cwObjective left m +
        weightRight * cwObjective right m := by
  unfold cwObjective
  have hrightWeight : weightRight = 1 - weightLeft := by linarith
  rw [hrightWeight]
  ring

/-- The variational pressure satisfies the two-point Jensen inequality because
it is the supremum of affine coupling objectives. -/
theorem cwVariationalPressureGap_convexCombination
    (left right weightLeft weightRight : ℝ)
    (hleft : 0 ≤ weightLeft) (hright : 0 ≤ weightRight)
    (hweights : weightLeft + weightRight = 1) :
    cwVariationalPressureGap (weightLeft * left + weightRight * right) ≤
      weightLeft * cwVariationalPressureGap left +
        weightRight * cwVariationalPressureGap right := by
  unfold cwVariationalPressureGap
  apply csSup_le (cwPressureValueSet_nonempty
    (weightLeft * left + weightRight * right))
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  have habs : |m| ≤ 1 := (abs_le).2 hm
  rw [cwObjective_affine_coupling left right weightLeft weightRight m hweights]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (cwObjective_le_variationalPressureGap left m habs) hleft)
    (mul_le_mul_of_nonneg_left
      (cwObjective_le_variationalPressureGap right m habs) hright)

/-- The complete variational pressure profile is convex on the real coupling
line. -/
theorem convexOn_cwVariationalPressureGap :
    ConvexOn ℝ Set.univ cwVariationalPressureGap := by
  constructor
  · exact convex_univ
  · intro left _hleft right _hright weightLeft weightRight
      hweightLeft hweightRight hweights
    simpa only [smul_eq_mul] using
      cwVariationalPressureGap_convexCombination left right weightLeft weightRight
        hweightLeft hweightRight hweights

/-- Below and at the critical point, the supremum is exactly zero. -/
theorem cwVariationalPressureGap_eq_zero_of_subcritical
    (tlam : ℝ) (hcritical : tlam ≤ 1) :
    cwVariationalPressureGap tlam = 0 := by
  apply le_antisymm
  · unfold cwVariationalPressureGap
    apply csSup_le (cwPressureValueSet_nonempty tlam)
    intro value hvalue
    rcases hvalue with ⟨m, hm, rfl⟩
    exact curieWeiss_subcritical tlam hcritical m ((abs_le).2 hm)
  · exact cwVariationalPressureGap_nonneg tlam

/-- Above the critical point, an interior witness lies below the supremum and
makes the pressure gap strictly positive. -/
theorem cwVariationalPressureGap_pos_of_supercritical
    (tlam : ℝ) (hcritical : 1 < tlam) :
    0 < cwVariationalPressureGap tlam := by
  obtain ⟨m, hm, hpositive⟩ := curieWeiss_supercritical tlam hcritical
  have hmember : cwObjective tlam m ∈ cwPressureValueSet tlam :=
    ⟨m, (abs_le).1 hm.le, rfl⟩
  have hle : cwObjective tlam m ≤ cwVariationalPressureGap tlam := by
    exact le_csSup (cwPressureValueSet_bddAbove tlam) hmember
  exact hpositive.trans_le hle

/-- **Exact critical point for the supremal pressure itself.** -/
theorem cwVariationalPressureGap_eq_zero_iff (tlam : ℝ) :
    cwVariationalPressureGap tlam = 0 ↔ tlam ≤ 1 := by
  constructor
  · intro hzero
    by_contra hnot
    have hpositive := cwVariationalPressureGap_pos_of_supercritical tlam (lt_of_not_ge hnot)
    linarith
  · exact cwVariationalPressureGap_eq_zero_of_subcritical tlam

/-! ### A genuine finite-volume pressure counterexample

The development below identifies the genuine finite-volume limit directly.
A biased-binomial trial law gives the Gibbs lower bound, while the matching
product-law factorisation bounds every type above by the exponential
variational pressure.  Since there are only `population + 1` types, the two
bounds differ by at most `log (population + 1) / population`.  The aligned-state
estimate is retained as a simpler explicit certificate.
-/

/-- Magnetisation of the type with `upSpins` positive spins in a population of
size `population`. -/
noncomputable def finiteCWMagnetization
    (population upSpins : ℕ) : ℝ :=
  2 * (upSpins : ℝ) - population

/-- Magnetisation density of one finite Rademacher type. -/
noncomputable def finiteCWEmpiricalMagnetization
    (population upSpins : ℕ) : ℝ :=
  finiteCWMagnetization population upSpins / population

/-- Positive-spin probability in the biased Rademacher trial law associated
with magnetisation `m`. -/
noncomputable def cwPositiveTrialWeight (m : ℝ) : ℝ :=
  (1 + m) / 2

/-- Negative-spin probability in the same trial law. -/
noncomputable def cwNegativeTrialWeight (m : ℝ) : ℝ :=
  (1 - m) / 2

/-- For a nonempty population, rescaling the empirical magnetisation recovers
the unnormalized magnetisation exactly. -/
theorem finiteCWEmpiricalMagnetization_scale
    (population upSpins : ℕ) (hpopulation : 0 < population) :
    (population : ℝ) * finiteCWEmpiricalMagnetization population upSpins =
      finiteCWMagnetization population upSpins := by
  unfold finiteCWEmpiricalMagnetization
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hpopulation.ne')

/-- For an interior type, the empirical magnetisation lies strictly inside
`(-1,1)`. -/
theorem finiteCWEmpiricalMagnetization_abs_lt_one
    (population upSpins : ℕ)
    (hpositive : 0 < upSpins) (hinterior : upSpins < population) :
    |finiteCWEmpiricalMagnetization population upSpins| < 1 := by
  have hpopulation : (0 : ℝ) < population := by
    exact_mod_cast hpositive.trans_le hinterior.le
  have hupPositive : (0 : ℝ) < upSpins := by exact_mod_cast hpositive
  have hupInterior : (upSpins : ℝ) < population := by exact_mod_cast hinterior
  rw [abs_lt]
  constructor
  · unfold finiteCWEmpiricalMagnetization finiteCWMagnetization
    apply (lt_div_iff₀ hpopulation).mpr
    linarith
  · unfold finiteCWEmpiricalMagnetization finiteCWMagnetization
    apply (div_lt_iff₀ hpopulation).mpr
    linarith

/-- Every admissible finite magnetisation has magnitude at most the population
size, hence squared energy at most `population²`. -/
theorem finiteCWMagnetization_sq_le_population_sq
    (population upSpins : ℕ)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    finiteCWMagnetization population upSpins ^ 2 ≤ (population : ℝ) ^ 2 := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  have hupNonnegative : (0 : ℝ) ≤ upSpins := by positivity
  have hupUpper : (upSpins : ℝ) ≤ population := by exact_mod_cast hle
  unfold finiteCWMagnetization
  nlinarith

/-- The positive-spin parameter induced by the empirical magnetisation is the
observed positive-spin fraction. -/
theorem cwPositiveTrialWeight_empirical
    (population upSpins : ℕ) (hpopulation : 0 < population) :
    cwPositiveTrialWeight
        (finiteCWEmpiricalMagnetization population upSpins) =
      (upSpins : ℝ) / population := by
  unfold cwPositiveTrialWeight finiteCWEmpiricalMagnetization finiteCWMagnetization
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  field_simp
  ring

/-- The complementary trial parameter is the observed negative-spin fraction. -/
theorem cwNegativeTrialWeight_empirical
    (population upSpins : ℕ) (hpopulation : 0 < population)
    (hle : upSpins ≤ population) :
    cwNegativeTrialWeight
        (finiteCWEmpiricalMagnetization population upSpins) =
      (population - upSpins : ℕ) / (population : ℝ) := by
  unfold cwNegativeTrialWeight finiteCWEmpiricalMagnetization finiteCWMagnetization
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  rw [Nat.cast_sub hle]
  field_simp
  ring

/-- Binomial type weight under a trial product law with positive-spin weight
`q` and negative-spin weight `r`. -/
noncomputable def biasedBinomialTypeWeight
    (population : ℕ) (q r : ℝ) (upSpins : ℕ) : ℝ :=
  (Nat.choose population upSpins : ℝ) *
    q ^ upSpins * r ^ (population - upSpins)

/-- If the two trial weights add to one, the binomial type weights form a
probability law exactly. -/
theorem biasedBinomialTypeWeight_sum
    (population : ℕ) (q r : ℝ) (hqr : q + r = 1) :
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population q r upSpins) = 1 := by
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
        biasedBinomialTypeWeight population q r upSpins) =
        (q + r) ^ population := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro upSpins _hupSpins
      simp only [biasedBinomialTypeWeight]
      ring
    _ = 1 := by rw [hqr, one_pow]

/-- The exact first moment of the biased binomial type law.  This is proved
from Pascal splitting rather than imported as a probabilistic fact. -/
theorem biasedBinomialTypeWeight_firstMoment
    (population : ℕ) (q r : ℝ) (hqr : q + r = 1) :
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population q r upSpins * upSpins) =
        population * q := by
  induction population with
  | zero => simp [biasedBinomialTypeWeight]
  | succ population ih =>
      have hsplit := Finset.sum_choose_succ_mul (R := ℝ)
        (fun upSpins downSpins ↦
          q ^ upSpins * r ^ downSpins * (upSpins : ℝ)) population
      have hsplit' :
          (∑ upSpins ∈ Finset.range (population + 2),
              biasedBinomialTypeWeight (population + 1) q r upSpins * upSpins) =
            (∑ upSpins ∈ Finset.range (population + 1),
              (Nat.choose population upSpins : ℝ) *
                (q ^ upSpins * r ^ (population + 1 - upSpins) * upSpins)) +
            ∑ upSpins ∈ Finset.range (population + 1),
              (Nat.choose population upSpins : ℝ) *
                (q ^ (upSpins + 1) * r ^ (population - upSpins) * (upSpins + 1)) := by
        simpa only [biasedBinomialTypeWeight, Nat.cast_add, Nat.cast_one,
          Nat.succ_eq_add_one, mul_assoc] using hsplit
      rw [hsplit']
      have hfirst :
          (∑ upSpins ∈ Finset.range (population + 1),
            (Nat.choose population upSpins : ℝ) *
              (q ^ upSpins * r ^ (population + 1 - upSpins) * upSpins)) =
            r * ∑ upSpins ∈ Finset.range (population + 1),
              biasedBinomialTypeWeight population q r upSpins * upSpins := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro upSpins hupSpins
        have hle : upSpins ≤ population :=
          Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
        rw [Nat.succ_sub hle, pow_succ]
        simp only [biasedBinomialTypeWeight]
        ring
      have hsecond :
          (∑ upSpins ∈ Finset.range (population + 1),
            (Nat.choose population upSpins : ℝ) *
              (q ^ (upSpins + 1) * r ^ (population - upSpins) * (upSpins + 1))) =
            q * (∑ upSpins ∈ Finset.range (population + 1),
              biasedBinomialTypeWeight population q r upSpins * upSpins) +
            q * (∑ upSpins ∈ Finset.range (population + 1),
              biasedBinomialTypeWeight population q r upSpins) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro upSpins _hupSpins
        simp only [biasedBinomialTypeWeight, pow_succ]
        ring
      rw [hfirst, hsecond, ih,
        biasedBinomialTypeWeight_sum population q r hqr]
      push_cast
      have hr : r = 1 - q := by linarith
      rw [hr]
      ring

/-- **Finite Gibbs variational inequality.**  For any strictly positive trial
probability weights and strictly positive masses, the log of the total mass is
at least the trial expectation of the log likelihood ratio.  This is the exact
finite change-of-measure inequality needed below; no asymptotic principle is
used. -/
theorem finiteLogSum_ge_weightedLogRatio
    {Index : Type*} (indices : Finset Index)
    (weight mass : Index → ℝ)
    (hindices : indices.Nonempty)
    (hweight : ∀ index ∈ indices, 0 < weight index)
    (hmass : ∀ index ∈ indices, 0 < mass index)
    (hweightSum : ∑ index ∈ indices, weight index = 1) :
    (∑ index ∈ indices,
        weight index * Real.log (mass index / weight index)) ≤
      Real.log (∑ index ∈ indices, mass index) := by
  have hjensen :
      Real.exp (∑ index ∈ indices,
        weight index * Real.log (mass index / weight index)) ≤
        ∑ index ∈ indices,
          weight index * Real.exp (Real.log (mass index / weight index)) := by
    simpa only [smul_eq_mul] using
      (convexOn_exp.map_sum_le
        (t := indices) (w := weight)
        (p := fun index ↦ Real.log (mass index / weight index))
        (fun index hindex ↦ (hweight index hindex).le)
        hweightSum
        (fun index _hindex ↦ Set.mem_univ
          (Real.log (mass index / weight index))))
  have harithmetic :
      (∑ index ∈ indices,
        weight index *
          Real.exp (Real.log (mass index / weight index))) =
        ∑ index ∈ indices, mass index := by
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Real.exp_log (div_pos (hmass index hindex) (hweight index hindex))]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ (mass index) (hweight index hindex).ne'
  rw [harithmetic] at hjensen
  have hmassSum : 0 < ∑ index ∈ indices, mass index :=
    Finset.sum_pos (fun index hindex ↦ hmass index hindex) hindices
  have hlogged := Real.log_le_log (Real.exp_pos _) hjensen
  simpa using hlogged

/-- The exact Curie--Weiss/Rademacher partition function after dividing by the
`2^population` configurations.  Grouping configurations by their number of
positive spins produces the binomial coefficient in the sum. -/
noncomputable def finiteCWPartition
    (population : ℕ) (tlam : ℝ) : ℝ :=
  ((2 : ℝ) ^ population)⁻¹ *
    ∑ upSpins ∈ Finset.range (population + 1),
      (Nat.choose population upSpins : ℝ) *
        Real.exp
          (tlam / (2 * (population : ℝ)) *
            finiteCWMagnetization population upSpins ^ 2)

/-- Normalized finite-volume pressure difference from the unspiked baseline. -/
noncomputable def finiteCWPressureGap
    (population : ℕ) (tlam : ℝ) : ℝ :=
  Real.log (finiteCWPartition population tlam) / population

@[simp] theorem cwTrialWeights_sum (m : ℝ) :
    cwPositiveTrialWeight m + cwNegativeTrialWeight m = 1 := by
  simp [cwPositiveTrialWeight, cwNegativeTrialWeight]
  ring

theorem cwPositiveTrialWeight_pos {m : ℝ} (hm : |m| < 1) :
    0 < cwPositiveTrialWeight m := by
  rw [abs_lt] at hm
  unfold cwPositiveTrialWeight
  linarith

theorem cwNegativeTrialWeight_pos {m : ℝ} (hm : |m| < 1) :
    0 < cwNegativeTrialWeight m := by
  rw [abs_lt] at hm
  unfold cwNegativeTrialWeight
  linarith

/-- Contribution of one magnetisation type to the normalized finite
Curie--Weiss partition function. -/
noncomputable def finiteCWTypeMass
    (population : ℕ) (tlam : ℝ) (upSpins : ℕ) : ℝ :=
  ((2 : ℝ) ^ population)⁻¹ *
    (Nat.choose population upSpins : ℝ) *
      Real.exp
        (tlam / (2 * (population : ℝ)) *
          finiteCWMagnetization population upSpins ^ 2)

/-- The partition function is exactly the sum of its positive type masses. -/
theorem finiteCWTypeMass_sum (population : ℕ) (tlam : ℝ) :
    (∑ upSpins ∈ Finset.range (population + 1),
      finiteCWTypeMass population tlam upSpins) =
        finiteCWPartition population tlam := by
  rw [finiteCWPartition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro upSpins _hupSpins
  simp only [finiteCWTypeMass]
  ring

/-- Every admissible magnetisation type has strictly positive trial weight. -/
theorem biasedBinomialTypeWeight_pos
    (population upSpins : ℕ) (m : ℝ)
    (hm : |m| < 1) (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    0 < biasedBinomialTypeWeight population
      (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  exact mul_pos
    (mul_pos
      (by exact_mod_cast Nat.choose_pos hle)
      (pow_pos (cwPositiveTrialWeight_pos hm) _))
    (pow_pos (cwNegativeTrialWeight_pos hm) _)

/-- Every admissible type also has strictly positive partition mass. -/
theorem finiteCWTypeMass_pos
    (population upSpins : ℕ) (tlam : ℝ)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    0 < finiteCWTypeMass population tlam upSpins := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  unfold finiteCWTypeMass
  exact mul_pos
    (mul_pos (by positivity) (by exact_mod_cast Nat.choose_pos hle))
    (Real.exp_pos _)

/-- **The tilted binomial weights, summed and first-moment, in one specialisation.**

Both spin means below open by instantiating the general binomial identities at the
Curie--Weiss trial weights, and each carried its own copy of that step. -/
theorem cwBinomialTypeWeight_sum_and_firstMoment (population : ℕ) (m : ℝ) :
    (∑ upSpins ∈ Finset.range (population + 1),
        biasedBinomialTypeWeight population (cwPositiveTrialWeight m)
          (cwNegativeTrialWeight m) upSpins) = 1 ∧
      (∑ upSpins ∈ Finset.range (population + 1),
        biasedBinomialTypeWeight population (cwPositiveTrialWeight m)
          (cwNegativeTrialWeight m) upSpins * upSpins) =
        population * cwPositiveTrialWeight m :=
  ⟨biasedBinomialTypeWeight_sum population _ _ (cwTrialWeights_sum m),
    biasedBinomialTypeWeight_firstMoment population _ _ (cwTrialWeights_sum m)⟩

/-- Under the biased binomial trial law, expected magnetisation is exactly
`population * m`. -/
theorem biasedBinomialTypeWeight_magnetizationMean
    (population : ℕ) (m : ℝ) :
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population
          (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins *
        finiteCWMagnetization population upSpins) =
      population * m := by
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  obtain ⟨hsum, hfirst⟩ := cwBinomialTypeWeight_sum_and_firstMoment population m
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population q r upSpins *
        finiteCWMagnetization population upSpins) =
        2 * (∑ upSpins ∈ Finset.range (population + 1),
          biasedBinomialTypeWeight population q r upSpins * upSpins) -
        population * (∑ upSpins ∈ Finset.range (population + 1),
          biasedBinomialTypeWeight population q r upSpins) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro upSpins _hupSpins
      simp only [finiteCWMagnetization]
      ring
    _ = 2 * (population * q) - population := by rw [hfirst, hsum]; ring
    _ = population * m := by
      dsimp [q, cwPositiveTrialWeight]
      ring

/-- The expected number of negative spins is the complementary binomial
mean. -/
theorem biasedBinomialTypeWeight_downSpinMean
    (population : ℕ) (m : ℝ) :
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population
          (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins *
        (population - upSpins)) =
      population * cwNegativeTrialWeight m := by
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  obtain ⟨hsum, hfirst⟩ := cwBinomialTypeWeight_sum_and_firstMoment population m
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population q r upSpins *
        (population - upSpins)) =
        population * (∑ upSpins ∈ Finset.range (population + 1),
          biasedBinomialTypeWeight population q r upSpins) -
        ∑ upSpins ∈ Finset.range (population + 1),
          biasedBinomialTypeWeight population q r upSpins * upSpins := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro upSpins _hupSpins
      ring
    _ = population - population * q := by rw [hsum, hfirst]; ring
    _ = population * r := by
      have hr : r = 1 - q := by
        dsimp [q, r]
        rw [← cwTrialWeights_sum m]
        ring
      rw [hr]
      ring

/-- Jensen's inequality for the square gives the exact lower bound on the
trial second moment needed by the Curie--Weiss energy. -/
theorem biasedBinomialTypeWeight_magnetizationSecondMoment
    (population : ℕ) (m : ℝ) (hm : |m| < 1) :
    ((population : ℝ) * m) ^ 2 ≤
      ∑ upSpins ∈ Finset.range (population + 1),
        biasedBinomialTypeWeight population
            (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins *
          finiteCWMagnetization population upSpins ^ 2 := by
  let weight := fun upSpins ↦ biasedBinomialTypeWeight population
    (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins
  have hweightNonnegative : ∀ upSpins ∈ Finset.range (population + 1),
      0 ≤ weight upSpins := fun upSpins hupSpins ↦
    (biasedBinomialTypeWeight_pos population upSpins m hm hupSpins).le
  have hweightSum :
      (∑ upSpins ∈ Finset.range (population + 1), weight upSpins) = 1 :=
    biasedBinomialTypeWeight_sum population
      (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) (cwTrialWeights_sum m)
  have hjensen := Real.pow_arith_mean_le_arith_mean_pow_of_even
    (Finset.range (population + 1)) weight
    (finiteCWMagnetization population) hweightNonnegative hweightSum (by decide : Even 2)
  rw [show (∑ upSpins ∈ Finset.range (population + 1),
      weight upSpins * finiteCWMagnetization population upSpins) =
        population * m by
      exact biasedBinomialTypeWeight_magnetizationMean population m] at hjensen
  exact hjensen

/-- The entropy cost of the biased Bernoulli trial law is exactly the
Curie--Weiss rate function used in the variational objective. -/
theorem cwTrialEntropy_eq_rate {m : ℝ} (hm : |m| < 1) :
    Real.log 2 +
        cwPositiveTrialWeight m * Real.log (cwPositiveTrialWeight m) +
        cwNegativeTrialWeight m * Real.log (cwNegativeTrialWeight m) =
      cwRate m := by
  have hplus : 0 < 1 + m := by
    rw [abs_lt] at hm
    linarith
  have hminus : 0 < 1 - m := by
    rw [abs_lt] at hm
    linarith
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  rw [show Real.log (cwPositiveTrialWeight m) =
      Real.log (1 + m) - Real.log 2 by
        rw [cwPositiveTrialWeight, Real.log_div hplus.ne' htwo],
    show Real.log (cwNegativeTrialWeight m) =
      Real.log (1 - m) - Real.log 2 by
        rw [cwNegativeTrialWeight, Real.log_div hminus.ne' htwo]]
  unfold cwRate cwPositiveTrialWeight cwNegativeTrialWeight
  ring

/-- Exact pointwise log likelihood ratio between one Curie--Weiss type mass
and the corresponding biased-binomial trial mass.  The binomial coefficient
cancels, leaving energy minus the product-law entropy cost. -/
theorem finiteCWTypeMass_logRatio
    (population upSpins : ℕ) (tlam m : ℝ)
    (hm : |m| < 1) (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    Real.log
        (finiteCWTypeMass population tlam upSpins /
          biasedBinomialTypeWeight population
            (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins) =
      tlam / (2 * (population : ℝ)) *
          finiteCWMagnetization population upSpins ^ 2 -
        population * Real.log 2 -
        upSpins * Real.log (cwPositiveTrialWeight m) -
        (population - upSpins) * Real.log (cwNegativeTrialWeight m) := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  have hchooseNat : 0 < Nat.choose population upSpins := Nat.choose_pos hle
  have hchoose : (Nat.choose population upSpins : ℝ) ≠ 0 := by
    exact_mod_cast hchooseNat.ne'
  have hq : cwPositiveTrialWeight m ≠ 0 := (cwPositiveTrialWeight_pos hm).ne'
  have hr : cwNegativeTrialWeight m ≠ 0 := (cwNegativeTrialWeight_pos hm).ne'
  have hpowTwo : (2 : ℝ) ^ population ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Real.log_div
      (finiteCWTypeMass_pos population upSpins tlam hupSpins).ne'
      (biasedBinomialTypeWeight_pos population upSpins m hm hupSpins).ne']
  unfold finiteCWTypeMass biasedBinomialTypeWeight
  rw [Real.log_mul (mul_ne_zero (inv_ne_zero hpowTwo) hchoose)
        (Real.exp_ne_zero _),
    Real.log_mul (inv_ne_zero hpowTwo) hchoose,
    Real.log_inv, Real.log_pow, Real.log_exp,
    Real.log_mul (mul_ne_zero hchoose (pow_ne_zero _ hq))
      (pow_ne_zero _ hr),
    Real.log_mul hchoose (pow_ne_zero _ hq),
    Real.log_pow, Real.log_pow]
  rw [Nat.cast_sub hle]
  ring

/-- At the empirical magnetisation of an interior type, its exact log
likelihood ratio against the matching product law is the population-scaled
Curie--Weiss objective. -/
theorem finiteCWTypeMass_matched_logRatio_eq_objective
    (population upSpins : ℕ) (tlam : ℝ)
    (hpositive : 0 < upSpins) (hinterior : upSpins < population) :
    Real.log
        (finiteCWTypeMass population tlam upSpins /
          biasedBinomialTypeWeight population
            (cwPositiveTrialWeight
              (finiteCWEmpiricalMagnetization population upSpins))
            (cwNegativeTrialWeight
              (finiteCWEmpiricalMagnetization population upSpins)) upSpins) =
      (population : ℝ) *
        cwObjective tlam
          (finiteCWEmpiricalMagnetization population upSpins) := by
  let m := finiteCWEmpiricalMagnetization population upSpins
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  have hpopulation : 0 < population := hpositive.trans_le hinterior.le
  have hle : upSpins ≤ population := hinterior.le
  have hm : |m| < 1 :=
    finiteCWEmpiricalMagnetization_abs_lt_one population upSpins
      hpositive hinterior
  have hupSpins : upSpins ∈ Finset.range (population + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hscale : (population : ℝ) * m =
      finiteCWMagnetization population upSpins :=
    finiteCWEmpiricalMagnetization_scale population upSpins hpopulation
  have hqScale : (population : ℝ) * q = upSpins := by
    dsimp [q, m]
    rw [cwPositiveTrialWeight_empirical population upSpins hpopulation]
    field_simp
  have hrScale : (population : ℝ) * r = population - upSpins := by
    dsimp [r, m]
    rw [cwNegativeTrialWeight_empirical population upSpins hpopulation hle]
    rw [Nat.cast_sub hle]
    field_simp
  rw [finiteCWTypeMass_logRatio population upSpins tlam m hm hupSpins]
  rw [← hqScale]
  unfold cwObjective
  rw [← cwTrialEntropy_eq_rate hm]
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  rw [← hscale]
  dsimp [m, q, r, cwPositiveTrialWeight, cwNegativeTrialWeight]
  field_simp
  ring

/-- The matched biased-binomial type weight is a genuine probability mass and
therefore is at most one. -/
theorem biasedBinomialTypeWeight_le_one
    (population upSpins : ℕ) (q r : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r = 1)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    biasedBinomialTypeWeight population q r upSpins ≤ 1 := by
  have hnonnegative : ∀ index ∈ Finset.range (population + 1),
      0 ≤ biasedBinomialTypeWeight population q r index := by
    intro index _hindex
    unfold biasedBinomialTypeWeight
    positivity
  have hsingle := Finset.single_le_sum hnonnegative hupSpins
  rw [biasedBinomialTypeWeight_sum population q r hqr] at hsingle
  exact hsingle

/-- Exponentiating the matched log-ratio identity gives an exact factorisation
of every interior Curie--Weiss type mass into a product-law probability and an
exponential variational reward. -/
theorem finiteCWTypeMass_eq_matchedWeight_mul_expObjective
    (population upSpins : ℕ) (tlam : ℝ)
    (hpositive : 0 < upSpins) (hinterior : upSpins < population) :
    finiteCWTypeMass population tlam upSpins =
      biasedBinomialTypeWeight population
          (cwPositiveTrialWeight
            (finiteCWEmpiricalMagnetization population upSpins))
          (cwNegativeTrialWeight
            (finiteCWEmpiricalMagnetization population upSpins)) upSpins *
        Real.exp ((population : ℝ) *
          cwObjective tlam
            (finiteCWEmpiricalMagnetization population upSpins)) := by
  let m := finiteCWEmpiricalMagnetization population upSpins
  let weight := biasedBinomialTypeWeight population
    (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins
  have hle : upSpins ≤ population := hinterior.le
  have hupSpins : upSpins ∈ Finset.range (population + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hm : |m| < 1 :=
    finiteCWEmpiricalMagnetization_abs_lt_one population upSpins
      hpositive hinterior
  have hweight : 0 < weight :=
    biasedBinomialTypeWeight_pos population upSpins m hm hupSpins
  have hmass : 0 < finiteCWTypeMass population tlam upSpins :=
    finiteCWTypeMass_pos population upSpins tlam hupSpins
  have hlog := finiteCWTypeMass_matched_logRatio_eq_objective
    population upSpins tlam hpositive hinterior
  have hexp := congrArg Real.exp hlog
  have hratio : finiteCWTypeMass population tlam upSpins / weight =
      Real.exp ((population : ℝ) * cwObjective tlam m) := by
    simpa [weight, m, Real.exp_log (div_pos hmass hweight)] using hexp
  have hmassEq : finiteCWTypeMass population tlam upSpins =
      Real.exp ((population : ℝ) * cwObjective tlam m) * weight :=
    (div_eq_iff hweight.ne').mp hratio
  simpa [weight, m, mul_comm] using hmassEq

/-- Every interior magnetisation type has mass at most one throughout the
complete subcritical and critical regime. -/
theorem finiteCWTypeMass_interior_le_one_of_subcritical
    (population upSpins : ℕ) (tlam : ℝ)
    (hcritical : tlam ≤ 1)
    (hpositive : 0 < upSpins) (hinterior : upSpins < population) :
    finiteCWTypeMass population tlam upSpins ≤ 1 := by
  let m := finiteCWEmpiricalMagnetization population upSpins
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  let weight := biasedBinomialTypeWeight population q r upSpins
  have hpopulation : 0 < population := hpositive.trans_le hinterior.le
  have hm : |m| < 1 :=
    finiteCWEmpiricalMagnetization_abs_lt_one population upSpins
      hpositive hinterior
  have hupSpins : upSpins ∈ Finset.range (population + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hinterior.le)
  have hweightNonnegative : 0 ≤ weight :=
    (biasedBinomialTypeWeight_pos population upSpins m hm hupSpins).le
  have hweightUpper : weight ≤ 1 :=
    biasedBinomialTypeWeight_le_one population upSpins q r
      (cwPositiveTrialWeight_pos hm).le (cwNegativeTrialWeight_pos hm).le
      (cwTrialWeights_sum m) hupSpins
  have hobjective : cwObjective tlam m ≤ 0 :=
    curieWeiss_subcritical tlam hcritical m hm.le
  have hpopulationNonnegative : (0 : ℝ) ≤ population := by positivity
  have hscaled : (population : ℝ) * cwObjective tlam m ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpopulationNonnegative hobjective
  have hexpUpper : Real.exp ((population : ℝ) * cwObjective tlam m) ≤ 1 := by
    simpa using (Real.exp_le_one_iff.mpr hscaled)
  rw [finiteCWTypeMass_eq_matchedWeight_mul_expObjective population upSpins
    tlam hpositive hinterior]
  exact (mul_le_mul hweightUpper hexpUpper (Real.exp_pos _).le (by norm_num)).trans_eq
    (one_mul 1)

/-- The fully aligned type mass is exactly the exponential of the endpoint
variational objective times the population. -/
theorem finiteCWTypeMass_aligned_eq_exp_objective
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    finiteCWTypeMass population tlam population =
      Real.exp ((population : ℝ) * cwObjective tlam 1) := by
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  have htwoPow : (2 : ℝ) ^ population =
      Real.exp ((population : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    finiteCWTypeMass population tlam population =
        ((2 : ℝ) ^ population)⁻¹ *
          Real.exp (tlam * population / 2) := by
      unfold finiteCWTypeMass
      simp [finiteCWMagnetization]
      field_simp
      ring
    _ = Real.exp (-((population : ℝ) * Real.log 2)) *
          Real.exp (tlam * population / 2) := by
      rw [htwoPow, Real.exp_neg]
    _ = Real.exp ((population : ℝ) *
          (tlam / 2 - Real.log 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp ((population : ℝ) * cwObjective tlam 1) := by
      rw [cwObjective_at_one]

/-- The fully anti-aligned type has the same exact endpoint mass. -/
theorem finiteCWTypeMass_zero_eq_exp_objective
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    finiteCWTypeMass population tlam 0 =
      Real.exp ((population : ℝ) * cwObjective tlam (-1)) := by
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  have htwoPow : (2 : ℝ) ^ population =
      Real.exp ((population : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    finiteCWTypeMass population tlam 0 =
        ((2 : ℝ) ^ population)⁻¹ *
          Real.exp (tlam * population / 2) := by
      unfold finiteCWTypeMass finiteCWMagnetization
      simp
      field_simp
    _ = Real.exp (-((population : ℝ) * Real.log 2)) *
          Real.exp (tlam * population / 2) := by
      rw [htwoPow, Real.exp_neg]
    _ = Real.exp ((population : ℝ) *
          (tlam / 2 - Real.log 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp ((population : ℝ) * cwObjective tlam (-1)) := by
      unfold cwObjective
      rw [cwRate_neg_one]
      ring_nf

/-- Endpoint types also have mass at most one at and below the critical
coupling. -/
theorem finiteCWTypeMass_endpoint_le_one_of_subcritical
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population)
    (hcritical : tlam ≤ 1) :
    finiteCWTypeMass population tlam 0 ≤ 1 ∧
      finiteCWTypeMass population tlam population ≤ 1 := by
  have hpopulationNonnegative : (0 : ℝ) ≤ population := by positivity
  have hnegativeObjective : cwObjective tlam (-1) ≤ 0 :=
    curieWeiss_subcritical tlam hcritical (-1) (by norm_num)
  have hpositiveObjective : cwObjective tlam 1 ≤ 0 :=
    curieWeiss_subcritical tlam hcritical 1 (by norm_num)
  constructor
  · rw [finiteCWTypeMass_zero_eq_exp_objective population tlam hpopulation]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hpopulationNonnegative hnegativeObjective
  · rw [finiteCWTypeMass_aligned_eq_exp_objective population tlam hpopulation]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hpopulationNonnegative hpositiveObjective

/-- The unique zero-population type has unit mass. -/
theorem finiteCWTypeMass_eq_one_of_population_eq_zero
    (population upSpins : ℕ) (tlam : ℝ)
    (hupSpins : upSpins ∈ Finset.range (population + 1))
    (hpopulation : population = 0) :
    finiteCWTypeMass population tlam upSpins = 1 := by
  have hupZero : upSpins = 0 := Nat.eq_zero_of_le_zero
    (hpopulation ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins))
  subst population
  subst upSpins
  simp [finiteCWTypeMass, finiteCWMagnetization]

/-- Every admissible type mass is at most one throughout the complete
subcritical/critical window. -/
theorem finiteCWTypeMass_le_one_of_subcritical
    (population upSpins : ℕ) (tlam : ℝ) (hcritical : tlam ≤ 1)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    finiteCWTypeMass population tlam upSpins ≤ 1 := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  by_cases hpopulation : population = 0
  · exact (finiteCWTypeMass_eq_one_of_population_eq_zero
      population upSpins tlam hupSpins hpopulation).le
  · have hpopulationPositive : 0 < population := Nat.pos_of_ne_zero hpopulation
    by_cases hupZero : upSpins = 0
    · subst upSpins
      exact (finiteCWTypeMass_endpoint_le_one_of_subcritical population tlam
        hpopulationPositive hcritical).1
    · by_cases hupAligned : upSpins = population
      · subst upSpins
        exact (finiteCWTypeMass_endpoint_le_one_of_subcritical population tlam
          hpopulationPositive hcritical).2
      · exact finiteCWTypeMass_interior_le_one_of_subcritical population upSpins
          tlam hcritical (Nat.pos_of_ne_zero hupZero)
          (lt_of_le_of_ne hle hupAligned)

/-- Every finite magnetisation type is bounded by the exponential of the
population-scaled variational pressure.  For interior types this follows from
the exact matched-product factorisation and the fact that a probability mass
is at most one; the two endpoint identities close the boundary cases. -/
theorem finiteCWTypeMass_le_exp_variationalPressure
    (population upSpins : ℕ) (tlam : ℝ)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    finiteCWTypeMass population tlam upSpins ≤
      Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  by_cases hpopulation : population = 0
  · rw [finiteCWTypeMass_eq_one_of_population_eq_zero
      population upSpins tlam hupSpins hpopulation, hpopulation]
    simp
  · have hpopulationPositive : 0 < population := Nat.pos_of_ne_zero hpopulation
    have hpopulationNonnegative : (0 : ℝ) ≤ population := by positivity
    by_cases hupZero : upSpins = 0
    · subst upSpins
      rw [finiteCWTypeMass_zero_eq_exp_objective population tlam
        hpopulationPositive]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (cwObjective_le_variationalPressureGap tlam (-1) (by norm_num))
        hpopulationNonnegative
    · by_cases hupAligned : upSpins = population
      · subst upSpins
        rw [finiteCWTypeMass_aligned_eq_exp_objective population tlam
          hpopulationPositive]
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left
          (cwObjective_le_variationalPressureGap tlam 1 (by norm_num))
          hpopulationNonnegative
      · have hpositive : 0 < upSpins := Nat.pos_of_ne_zero hupZero
        have hinterior : upSpins < population :=
          lt_of_le_of_ne hle hupAligned
        let m := finiteCWEmpiricalMagnetization population upSpins
        let q := cwPositiveTrialWeight m
        let r := cwNegativeTrialWeight m
        let weight := biasedBinomialTypeWeight population q r upSpins
        have hm : |m| < 1 :=
          finiteCWEmpiricalMagnetization_abs_lt_one population upSpins
            hpositive hinterior
        have hweightUpper : weight ≤ 1 :=
          biasedBinomialTypeWeight_le_one population upSpins q r
            (cwPositiveTrialWeight_pos hm).le
            (cwNegativeTrialWeight_pos hm).le
            (cwTrialWeights_sum m) hupSpins
        have hobjective : cwObjective tlam m ≤
            cwVariationalPressureGap tlam :=
          cwObjective_le_variationalPressureGap tlam m hm.le
        have hscaled : (population : ℝ) * cwObjective tlam m ≤
            (population : ℝ) * cwVariationalPressureGap tlam :=
          mul_le_mul_of_nonneg_left hobjective hpopulationNonnegative
        have hexpUpper : Real.exp ((population : ℝ) * cwObjective tlam m) ≤
            Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) :=
          Real.exp_le_exp.mpr hscaled
        rw [finiteCWTypeMass_eq_matchedWeight_mul_expObjective population
          upSpins tlam hpositive hinterior]
        exact (mul_le_mul hweightUpper hexpUpper (Real.exp_pos _).le
          (by norm_num)).trans_eq (one_mul _)

/-- Summing the termwise bound shows that the finite partition function has
at most the number of magnetisation types, namely `population + 1`. -/
theorem finiteCWPartition_le_typeCount_of_subcritical
    (population : ℕ) (tlam : ℝ) (hcritical : tlam ≤ 1) :
    finiteCWPartition population tlam ≤ population + 1 := by
  rw [← finiteCWTypeMass_sum]
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
        finiteCWTypeMass population tlam upSpins) ≤
        ∑ _upSpins ∈ Finset.range (population + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro upSpins hupSpins
      exact finiteCWTypeMass_le_one_of_subcritical population upSpins tlam
        hcritical hupSpins
    _ = population + 1 := by simp

/-- The whole finite partition function is at most the number of
magnetisation types times the exponential variational pressure. -/
theorem finiteCWPartition_le_typeCount_mul_expVariational
    (population : ℕ) (tlam : ℝ) :
    finiteCWPartition population tlam ≤
      (population + 1 : ℕ) *
        Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
  rw [← finiteCWTypeMass_sum]
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
        finiteCWTypeMass population tlam upSpins) ≤
        ∑ _upSpins ∈ Finset.range (population + 1),
          Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
      apply Finset.sum_le_sum
      intro upSpins hupSpins
      exact finiteCWTypeMass_le_exp_variationalPressure population upSpins
        tlam hupSpins
    _ = (population + 1 : ℕ) *
        Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
      simp

/-- At every positive population, the finite pressure exceeds the
variational pressure by at most the normalized logarithm of the number of
types. -/
theorem finiteCWPressureGap_le_variational_add_typeCount
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    finiteCWPressureGap population tlam ≤
      cwVariationalPressureGap tlam +
        Real.log ((population : ℝ) + 1) / (population : ℝ) := by
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have htypeCountPositive : (0 : ℝ) < population + 1 := by positivity
  have hpartitionPositive : 0 < finiteCWPartition population tlam := by
    rw [← finiteCWTypeMass_sum]
    exact Finset.sum_pos
      (fun upSpins hupSpins ↦
        finiteCWTypeMass_pos population upSpins tlam hupSpins)
      ⟨0, by simp⟩
  have hpartitionUpper : finiteCWPartition population tlam ≤
      ((population : ℝ) + 1) *
        Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
    simpa [Nat.cast_add] using
      finiteCWPartition_le_typeCount_mul_expVariational population tlam
  have hlogUpper : Real.log (finiteCWPartition population tlam) ≤
      Real.log (((population : ℝ) + 1) *
        Real.exp ((population : ℝ) * cwVariationalPressureGap tlam)) :=
    Real.log_le_log hpartitionPositive hpartitionUpper
  rw [finiteCWPressureGap]
  apply (div_le_iff₀ hpopulationReal).mpr
  calc
    Real.log (finiteCWPartition population tlam) ≤
        Real.log (((population : ℝ) + 1) *
          Real.exp ((population : ℝ) * cwVariationalPressureGap tlam)) :=
      hlogUpper
    _ = Real.log ((population : ℝ) + 1) +
        (population : ℝ) * cwVariationalPressureGap tlam := by
      rw [Real.log_mul htypeCountPositive.ne' (Real.exp_ne_zero _), Real.log_exp]
    _ = (cwVariationalPressureGap tlam +
        Real.log ((population : ℝ) + 1) / population) * population := by
      field_simp
      ring

/-- Nonnegative coupling can only increase the normalized Rademacher
partition function above its exactly normalized zero-coupling value. -/
theorem finiteCWPartition_one_le_of_nonnegative
    (population : ℕ) (tlam : ℝ) (htlam : 0 ≤ tlam) :
    1 ≤ finiteCWPartition population tlam := by
  have hzeroPartition : finiteCWPartition population 0 = 1 := by
    have hsum :
        (∑ upSpins ∈ Finset.range (population + 1),
          (Nat.choose population upSpins : ℝ)) = (2 : ℝ) ^ population := by
      exact_mod_cast Nat.sum_range_choose population
    simp [finiteCWPartition, hsum]
  rw [← hzeroPartition]
  unfold finiteCWPartition
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro upSpins _hupSpins
  have henergy : 0 ≤ tlam / (2 * (population : ℝ)) *
      finiteCWMagnetization population upSpins ^ 2 := by
    positivity
  have hexp : 1 ≤ Real.exp
      (tlam / (2 * (population : ℝ)) *
        finiteCWMagnetization population upSpins ^ 2) :=
    Real.one_le_exp henergy
  simp only [zero_div, zero_mul, Real.exp_zero, mul_one]
  have hchoose : 0 ≤ (Nat.choose population upSpins : ℝ) := Nat.cast_nonneg _
  simpa using mul_le_mul_of_nonneg_left hexp hchoose

/-- The genuine finite-volume pressure is squeezed between zero and the log
number of magnetisation types throughout the subcritical/critical regime. -/
theorem finiteCWPressureGap_subcritical_bounds
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population)
    (htlam : 0 ≤ tlam) (hcritical : tlam ≤ 1) :
    0 ≤ finiteCWPressureGap population tlam ∧
      finiteCWPressureGap population tlam ≤
        Real.log (population + 1) / population := by
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have hpartitionLower :=
    finiteCWPartition_one_le_of_nonnegative population tlam htlam
  have hpartitionUpper :=
    finiteCWPartition_le_typeCount_of_subcritical population tlam hcritical
  have hpartitionPositive : 0 < finiteCWPartition population tlam :=
    lt_of_lt_of_le zero_lt_one hpartitionLower
  constructor
  · unfold finiteCWPressureGap
    exact div_nonneg (Real.log_nonneg hpartitionLower) hpopulationReal.le
  · unfold finiteCWPressureGap
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hpartitionPositive hpartitionUpper) hpopulationReal.le

/-- The normalized logarithm of the number of Curie--Weiss types vanishes.
The proof factors the shifted ratio into `log x / x` and a shift ratio tending
to one. -/
theorem finiteCWTypeCount_log_div_tendsto_zero :
    Filter.Tendsto
      (fun population : ℕ ↦
        Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
  have hshiftTwo : Filter.Tendsto
      (fun population : ℕ ↦ ((population + 2 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 2) using 1
  have hshiftOne : Filter.Tendsto
      (fun population : ℕ ↦ ((population + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1) using 1
  have hlogDivReal : Filter.Tendsto
      (fun x : ℝ ↦ Real.log x / x) Filter.atTop (nhds 0) := by
    simpa only [id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogDivShift : Filter.Tendsto
      (fun population : ℕ ↦
        Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 2 : ℕ) : ℝ))
      Filter.atTop (nhds 0) :=
    hlogDivReal.comp hshiftTwo
  have hinvShiftOne : Filter.Tendsto
      (fun population : ℕ ↦ (((population + 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    hshiftOne.inv_tendsto_atTop
  have hshiftRatio : Filter.Tendsto
      (fun population : ℕ ↦
        ((population + 2 : ℕ) : ℝ) /
          ((population + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
    have hone : Filter.Tendsto (fun _population : ℕ ↦ (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    have hadd := hone.add hinvShiftOne
    convert hadd using 1
    · funext population
      have hdenominator : (((population + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · norm_num
  have hproduct := hlogDivShift.mul hshiftRatio
  convert hproduct using 1
  · funext population
    have hpositiveOne : (0 : ℝ) < population + 1 := by positivity
    have hpositiveTwo : (0 : ℝ) < population + 2 := by positivity
    field_simp
  · norm_num

/-- **Exact finite-pressure subcritical limit.**  At every nonnegative
coupling at or below the Curie--Weiss threshold, the genuine normalized
finite-volume pressure converges to zero. -/
theorem finiteCWPressureGap_tendsto_zero_of_subcritical
    (tlam : ℝ) (htlam : 0 ≤ tlam) (hcritical : tlam ≤ 1) :
    Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds 0) := by
  have hnonnegative : ∀ population : ℕ,
      0 ≤ finiteCWPressureGap (population + 1) tlam := by
    intro population
    exact (finiteCWPressureGap_subcritical_bounds (population + 1) tlam
      (Nat.succ_pos population) htlam hcritical).1
  have hupper : ∀ population : ℕ,
      finiteCWPressureGap (population + 1) tlam ≤
        Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ) := by
    intro population
    have hbound := (finiteCWPressureGap_subcritical_bounds (population + 1) tlam
      (Nat.succ_pos population) htlam hcritical).2
    convert hbound using 1
    all_goals norm_num [Nat.cast_add]
    all_goals ring
  exact squeeze_zero hnonnegative hupper finiteCWTypeCount_log_div_tendsto_zero

/-- **Finite-volume Curie--Weiss variational lower bound.**  Every interior
magnetisation supplies its variational objective as a lower bound for the
genuine normalized finite Rademacher pressure.  The proof is an exact biased
binomial change of measure plus Jensen; it uses neither Stirling asymptotics
nor an LDP. -/
theorem finiteCWPressureGap_ge_cwObjective
    (population : ℕ) (tlam m : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) (hm : |m| < 1) :
    cwObjective tlam m ≤ finiteCWPressureGap population tlam := by
  let indices := Finset.range (population + 1)
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  let weight := fun upSpins ↦ biasedBinomialTypeWeight population q r upSpins
  let mass := finiteCWTypeMass population tlam
  let magnetization := finiteCWMagnetization population
  let energyScale := tlam / (2 * (population : ℝ))
  have hindices : indices.Nonempty := ⟨0, by simp [indices]⟩
  have hweightPositive : ∀ upSpins ∈ indices, 0 < weight upSpins := by
    intro upSpins hupSpins
    exact biasedBinomialTypeWeight_pos population upSpins m hm hupSpins
  have hmassPositive : ∀ upSpins ∈ indices, 0 < mass upSpins := by
    intro upSpins hupSpins
    exact finiteCWTypeMass_pos population upSpins tlam hupSpins
  have hweightSum : (∑ upSpins ∈ indices, weight upSpins) = 1 :=
    biasedBinomialTypeWeight_sum population q r (cwTrialWeights_sum m)
  have hfirstMoment :
      (∑ upSpins ∈ indices, weight upSpins * upSpins) = population * q :=
    biasedBinomialTypeWeight_firstMoment population q r (cwTrialWeights_sum m)
  have hdownMoment :
      (∑ upSpins ∈ indices, weight upSpins * (population - upSpins)) =
        population * r :=
    biasedBinomialTypeWeight_downSpinMean population m
  have hsecondMoment :
      ((population : ℝ) * m) ^ 2 ≤
        ∑ upSpins ∈ indices, weight upSpins * magnetization upSpins ^ 2 :=
    biasedBinomialTypeWeight_magnetizationSecondMoment population m hm
  have hvariational :
      (∑ upSpins ∈ indices,
          weight upSpins * Real.log (mass upSpins / weight upSpins)) ≤
        Real.log (finiteCWPartition population tlam) := by
    have h := finiteLogSum_ge_weightedLogRatio indices weight mass hindices
      hweightPositive hmassPositive hweightSum
    rw [show (∑ upSpins ∈ indices, mass upSpins) =
        finiteCWPartition population tlam by
      exact finiteCWTypeMass_sum population tlam] at h
    exact h
  have henergy :
      (∑ upSpins ∈ indices,
        weight upSpins * (energyScale * magnetization upSpins ^ 2)) =
        energyScale *
          ∑ upSpins ∈ indices, weight upSpins * magnetization upSpins ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro upSpins _hupSpins
    ring
  have hbaselineEntropy :
      (∑ upSpins ∈ indices,
        weight upSpins * (population * Real.log 2)) =
        population * Real.log 2 := by
    rw [← Finset.sum_mul, hweightSum]
    ring
  have hpositiveEntropy :
      (∑ upSpins ∈ indices,
        weight upSpins * (upSpins * Real.log q)) =
        (population * q) * Real.log q := by
    calc
      (∑ upSpins ∈ indices,
        weight upSpins * (upSpins * Real.log q)) =
          (∑ upSpins ∈ indices, weight upSpins * upSpins) * Real.log q := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro upSpins _hupSpins
        ring
      _ = _ := by rw [hfirstMoment]
  have hnegativeEntropy :
      (∑ upSpins ∈ indices,
        weight upSpins * ((population - upSpins) * Real.log r)) =
        (population * r) * Real.log r := by
    calc
      (∑ upSpins ∈ indices,
        weight upSpins * ((population - upSpins) * Real.log r)) =
          (∑ upSpins ∈ indices,
            weight upSpins * (population - upSpins)) * Real.log r := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro upSpins _hupSpins
        ring
      _ = _ := by rw [hdownMoment]
  have hweightedIdentity :
      (∑ upSpins ∈ indices,
          weight upSpins * Real.log (mass upSpins / weight upSpins)) =
        energyScale *
            ∑ upSpins ∈ indices, weight upSpins * magnetization upSpins ^ 2 -
          population * Real.log 2 -
          (population * q) * Real.log q -
          (population * r) * Real.log r := by
    calc
      (∑ upSpins ∈ indices,
          weight upSpins * Real.log (mass upSpins / weight upSpins)) =
          ∑ upSpins ∈ indices,
            weight upSpins *
              (energyScale * magnetization upSpins ^ 2 -
                population * Real.log 2 -
                upSpins * Real.log q -
                (population - upSpins) * Real.log r) := by
        apply Finset.sum_congr rfl
        intro upSpins hupSpins
        rw [finiteCWTypeMass_logRatio population upSpins tlam m hm hupSpins]
      _ =
          (∑ upSpins ∈ indices,
            weight upSpins * (energyScale * magnetization upSpins ^ 2)) -
          (∑ upSpins ∈ indices,
            weight upSpins * (population * Real.log 2)) -
          (∑ upSpins ∈ indices,
            weight upSpins * (upSpins * Real.log q)) -
          ∑ upSpins ∈ indices,
            weight upSpins * ((population - upSpins) * Real.log r) := by
        repeat' rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro upSpins _hupSpins
        ring
      _ = _ := by
        rw [henergy, hbaselineEntropy, hpositiveEntropy, hnegativeEntropy]
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have henergyScaleNonnegative : 0 ≤ energyScale := by
    dsimp [energyScale]
    positivity
  have htrialLower :
      (population : ℝ) * cwObjective tlam m ≤
        ∑ upSpins ∈ indices,
          weight upSpins * Real.log (mass upSpins / weight upSpins) := by
    rw [hweightedIdentity]
    have henergyLower :=
      mul_le_mul_of_nonneg_left hsecondMoment henergyScaleNonnegative
    calc
      (population : ℝ) * cwObjective tlam m =
          energyScale * (((population : ℝ) * m) ^ 2) -
            population * Real.log 2 -
            (population * q) * Real.log q -
            (population * r) * Real.log r := by
        unfold cwObjective
        dsimp [q, r]
        rw [← cwTrialEntropy_eq_rate hm]
        dsimp [energyScale]
        field_simp [hpopulationReal.ne']
        ring
      _ ≤ energyScale *
            ∑ upSpins ∈ indices,
              weight upSpins * magnetization upSpins ^ 2 -
            population * Real.log 2 -
            (population * q) * Real.log q -
            (population * r) * Real.log r := by linarith
  rw [finiteCWPressureGap]
  apply (le_div_iff₀ hpopulationReal).mpr
  exact (by simpa [mul_comm] using htrialLower.trans hvariational)

/-- The genuine finite pressure is strictly positive at every nonzero
population throughout the complete supercritical regime `1 < tlam`. -/
theorem finiteCWPressureGap_pos_of_supercritical
    (population : ℕ) (tlam : ℝ)
    (hpopulation : 0 < population) (hcritical : 1 < tlam) :
    0 < finiteCWPressureGap population tlam := by
  obtain ⟨m, hm, hobjective⟩ := curieWeiss_supercritical tlam hcritical
  exact hobjective.trans_le
    (finiteCWPressureGap_ge_cwObjective population tlam m hpopulation
      (le_trans (by norm_num) hcritical.le) hm)

/-- One interior variational witness gives a positive population-uniform lower
bound on the genuine finite pressure at every supercritical coupling. -/
theorem finiteCWPressureGap_supercritical_uniformWitness
    (tlam : ℝ) (hcritical : 1 < tlam) :
    ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m ∧
      ∀ population : ℕ, 0 < population →
        cwObjective tlam m ≤ finiteCWPressureGap population tlam := by
  obtain ⟨m, hm, hobjective⟩ := curieWeiss_supercritical tlam hcritical
  exact ⟨m, hm, hobjective, fun population hpopulation ↦
    finiteCWPressureGap_ge_cwObjective population tlam m hpopulation
      (le_trans (by norm_num) hcritical.le) hm⟩

/-- Hence the actual finite pressure gap cannot converge to zero anywhere in
the full supercritical regime. -/
theorem finiteCWPressureGap_not_tendsto_zero_of_supercritical
    (tlam : ℝ) (hcritical : 1 < tlam) :
    ¬ Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds 0) := by
  obtain ⟨m, hm, hobjective, hlower⟩ :=
    finiteCWPressureGap_supercritical_uniformWitness tlam hcritical
  intro hzero
  have hbelow : ∀ᶠ population in Filter.atTop,
      finiteCWPressureGap (population + 1) tlam < cwObjective tlam m :=
    hzero.eventually_lt_const hobjective
  obtain ⟨population, hpopulation⟩ := Filter.eventually_atTop.mp hbelow
  have hlt := hpopulation population le_rfl
  exact (not_lt_of_ge (hlower (population + 1) (Nat.succ_pos population))) hlt

/-- **Exact phase boundary for the actual finite-volume pressure sequence.**
For nonnegative coupling, convergence of the normalized pressure gap to zero
is equivalent to lying at or below the Curie--Weiss threshold.  The reverse
direction uses the population-uniform interior witness, not an unproved
thermodynamic-limit identification. -/
theorem finiteCWPressureGap_tendsto_zero_iff
    (tlam : ℝ) (htlam : 0 ≤ tlam) :
    Filter.Tendsto
        (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
        Filter.atTop (nhds 0) ↔
      tlam ≤ 1 := by
  constructor
  · intro hzero
    by_contra hcritical
    exact finiteCWPressureGap_not_tendsto_zero_of_supercritical tlam
      (lt_of_not_ge hcritical) hzero
  · intro hcritical
    exact finiteCWPressureGap_tendsto_zero_of_subcritical tlam htlam hcritical

/-- At zero coupling the binomially grouped partition function is normalized
to one.  This also verifies that the `2^population` denominator is the genuine
uniform Rademacher normalization. -/
@[simp] theorem finiteCWPartition_zero (population : ℕ) :
    finiteCWPartition population 0 = 1 := by
  have hsum :
      (∑ upSpins ∈ Finset.range (population + 1),
        (Nat.choose population upSpins : ℝ)) = (2 : ℝ) ^ population := by
    exact_mod_cast Nat.sum_range_choose population
  simp [finiteCWPartition, hsum]

/-- Consequently the finite-volume pressure gap vanishes at zero coupling. -/
@[simp] theorem finiteCWPressureGap_zero (population : ℕ) :
    finiteCWPressureGap population 0 = 0 := by
  simp [finiteCWPressureGap]

/-- The fully aligned type has magnetisation exactly the population size. -/
@[simp] theorem finiteCWMagnetization_aligned (population : ℕ) :
    finiteCWMagnetization population population = population := by
  simp [finiteCWMagnetization]
  ring

/-- One fully aligned Rademacher state supplies an explicit lower bound on the
whole finite partition function. -/
theorem finiteCWPartition_aligned_lower_bound
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    ((2 : ℝ) ^ population)⁻¹ *
        Real.exp (tlam * population / 2) ≤
      finiteCWPartition population tlam := by
  have htermNonnegative : ∀ upSpins ∈ Finset.range (population + 1),
      0 ≤ (Nat.choose population upSpins : ℝ) *
        Real.exp
          (tlam / (2 * (population : ℝ)) *
            finiteCWMagnetization population upSpins ^ 2) := by
    intro upSpins _hupSpins
    positivity
  have halignedMem : population ∈ Finset.range (population + 1) := by
    simp
  have halignedTerm :
      (Nat.choose population population : ℝ) *
          Real.exp
            (tlam / (2 * (population : ℝ)) *
              finiteCWMagnetization population population ^ 2) ≤
        ∑ upSpins ∈ Finset.range (population + 1),
          (Nat.choose population upSpins : ℝ) *
            Real.exp
              (tlam / (2 * (population : ℝ)) *
                finiteCWMagnetization population upSpins ^ 2) :=
    Finset.single_le_sum htermNonnegative halignedMem
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  have hnormalizedTerm :
      (Nat.choose population population : ℝ) *
          Real.exp
            (tlam / (2 * (population : ℝ)) *
              finiteCWMagnetization population population ^ 2) =
        Real.exp (tlam * population / 2) := by
    simp [finiteCWMagnetization]
    field_simp
    ring
  rw [finiteCWPartition, ← hnormalizedTerm]
  exact mul_le_mul_of_nonneg_left halignedTerm (by positivity)

/-- The finite Rademacher partition function is strictly positive at every
population size and coupling, so its logarithm never uses the nonpositive junk
branch of `Real.log`. -/
theorem finiteCWPartition_pos (population : ℕ) (tlam : ℝ) :
    0 < finiteCWPartition population tlam := by
  by_cases hzero : population = 0
  · subst population
    simp [finiteCWPartition]
  · have hpopulation : 0 < population := Nat.pos_of_ne_zero hzero
    exact (show
        0 < ((2 : ℝ) ^ population)⁻¹ *
          Real.exp (tlam * population / 2) by positivity).trans_le
      (finiteCWPartition_aligned_lower_bound population tlam hpopulation)

/-- Typewise coupling comparison: changing coupling from `right` to `left`
costs at most the maximal energy factor `exp (population * |left-right| / 2)`. -/
theorem finiteCWTypeMass_le_exp_half_abs_mul_typeMass
    (population upSpins : ℕ) (left right : ℝ)
    (hpopulation : 0 < population)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    finiteCWTypeMass population left upSpins ≤
      Real.exp (|left - right| * population / 2) *
        finiteCWTypeMass population right upSpins := by
  let magnetization := finiteCWMagnetization population upSpins
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have hmagnetization : magnetization ^ 2 ≤ (population : ℝ) ^ 2 :=
    finiteCWMagnetization_sq_le_population_sq population upSpins hupSpins
  have hdiff : left - right ≤ |left - right| := le_abs_self _
  have hscale : 0 ≤ magnetization ^ 2 / (2 * (population : ℝ)) := by
    positivity
  have hfirst : (left - right) *
      (magnetization ^ 2 / (2 * (population : ℝ))) ≤
      |left - right| *
        (magnetization ^ 2 / (2 * (population : ℝ))) :=
    mul_le_mul_of_nonneg_right hdiff hscale
  have hsecond : |left - right| / (2 * (population : ℝ)) *
      magnetization ^ 2 ≤ |left - right| * population / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hmagnetization
      (show 0 ≤ |left - right| / (2 * (population : ℝ)) by positivity)
    calc
      |left - right| / (2 * (population : ℝ)) * magnetization ^ 2 ≤
          |left - right| / (2 * (population : ℝ)) *
            (population : ℝ) ^ 2 := hmul
      _ = |left - right| * population / 2 := by
        field_simp
  have henergy : left / (2 * (population : ℝ)) * magnetization ^ 2 ≤
      |left - right| * population / 2 +
        right / (2 * (population : ℝ)) * magnetization ^ 2 := by
    calc
      left / (2 * (population : ℝ)) * magnetization ^ 2 =
          right / (2 * (population : ℝ)) * magnetization ^ 2 +
            (left - right) *
              (magnetization ^ 2 / (2 * (population : ℝ))) := by ring
      _ ≤ right / (2 * (population : ℝ)) * magnetization ^ 2 +
            |left - right| *
              (magnetization ^ 2 / (2 * (population : ℝ))) :=
        add_le_add_left hfirst _
      _ ≤ right / (2 * (population : ℝ)) * magnetization ^ 2 +
            |left - right| * population / 2 :=
        add_le_add_left (by
          calc
            |left - right| *
                (magnetization ^ 2 / (2 * (population : ℝ))) =
                |left - right| / (2 * (population : ℝ)) *
                  magnetization ^ 2 := by ring
            _ ≤ |left - right| * population / 2 := hsecond) _
      _ = _ := by ring
  have hexponential : Real.exp
      (left / (2 * (population : ℝ)) * magnetization ^ 2) ≤
      Real.exp (|left - right| * population / 2) *
        Real.exp (right / (2 * (population : ℝ)) * magnetization ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr henergy
  unfold finiteCWTypeMass
  dsimp [magnetization] at hexponential ⊢
  calc
    ((2 : ℝ) ^ population)⁻¹ * (Nat.choose population upSpins : ℝ) *
        Real.exp (left / (2 * (population : ℝ)) *
          finiteCWMagnetization population upSpins ^ 2) ≤
      ((2 : ℝ) ^ population)⁻¹ * (Nat.choose population upSpins : ℝ) *
        (Real.exp (|left - right| * population / 2) *
          Real.exp (right / (2 * (population : ℝ)) *
            finiteCWMagnetization population upSpins ^ 2)) :=
      mul_le_mul_of_nonneg_left hexponential (by positivity)
    _ = Real.exp (|left - right| * population / 2) *
        (((2 : ℝ) ^ population)⁻¹ * (Nat.choose population upSpins : ℝ) *
          Real.exp (right / (2 * (population : ℝ)) *
            finiteCWMagnetization population upSpins ^ 2)) := by ring

/-- Each finite type mass is monotone in coupling because its squared
magnetisation energy is nonnegative. -/
theorem finiteCWTypeMass_mono_coupling
    (population upSpins : ℕ) {left right : ℝ}
    (hpopulation : 0 < population) (hle : left ≤ right) :
    finiteCWTypeMass population left upSpins ≤
      finiteCWTypeMass population right upSpins := by
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  unfold finiteCWTypeMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hle (by positivity)) (sq_nonneg _)

/-- Summing the typewise comparison gives the corresponding exact partition
function comparison. -/
theorem finiteCWPartition_le_exp_half_abs_mul_partition
    (population : ℕ) (left right : ℝ) (hpopulation : 0 < population) :
    finiteCWPartition population left ≤
      Real.exp (|left - right| * population / 2) *
        finiteCWPartition population right := by
  rw [← finiteCWTypeMass_sum, ← finiteCWTypeMass_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro upSpins hupSpins
  exact finiteCWTypeMass_le_exp_half_abs_mul_typeMass
    population upSpins left right hpopulation hupSpins

/-- The finite partition function is monotone in coupling. -/
theorem finiteCWPartition_mono_coupling
    (population : ℕ) {left right : ℝ}
    (hpopulation : 0 < population) (hle : left ≤ right) :
    finiteCWPartition population left ≤ finiteCWPartition population right := by
  rw [← finiteCWTypeMass_sum, ← finiteCWTypeMass_sum]
  apply Finset.sum_le_sum
  intro upSpins _hupSpins
  exact finiteCWTypeMass_mono_coupling population upSpins hpopulation hle

/-- One-sided finite pressure comparison in coupling. -/
theorem finiteCWPressureGap_sub_le_half_abs
    (population : ℕ) (left right : ℝ) (hpopulation : 0 < population) :
    finiteCWPressureGap population left - finiteCWPressureGap population right ≤
      |left - right| / 2 := by
  have hpartition := finiteCWPartition_le_exp_half_abs_mul_partition
    population left right hpopulation
  have hlog := Real.log_le_log (finiteCWPartition_pos population left)
    hpartition
  rw [Real.log_mul (Real.exp_ne_zero _)
      (finiteCWPartition_pos population right).ne', Real.log_exp] at hlog
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  rw [finiteCWPressureGap, finiteCWPressureGap]
  calc
    Real.log (finiteCWPartition population left) / population -
        Real.log (finiteCWPartition population right) / population =
      (Real.log (finiteCWPartition population left) -
        Real.log (finiteCWPartition population right)) / population := by ring
    _ ≤ (|left - right| * population / 2) / population :=
      div_le_div_of_nonneg_right (by linarith) hpopulationReal.le
    _ = |left - right| / 2 := by
      field_simp

/-- **Exact finite-volume regularity.**  At every positive population, the
normalized Curie--Weiss pressure is globally `1/2`-Lipschitz in coupling. -/
theorem finiteCWPressureGap_abs_sub_le_half_abs
    (population : ℕ) (left right : ℝ) (hpopulation : 0 < population) :
    |finiteCWPressureGap population left - finiteCWPressureGap population right| ≤
      |left - right| / 2 := by
  rw [abs_le]
  constructor
  · have hreverse := finiteCWPressureGap_sub_le_half_abs
      population right left hpopulation
    rw [abs_sub_comm] at hreverse
    linarith
  · exact finiteCWPressureGap_sub_le_half_abs population left right hpopulation

/-- Bundled finite-volume half-Lipschitz regularity. -/
theorem finiteCWPressureGap_lipschitzWith
    (population : ℕ) (hpopulation : 0 < population) :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal)
      (finiteCWPressureGap population) := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  rw [Real.dist_eq, Real.dist_eq]
  simpa [abs_sub_comm, mul_comm] using
    finiteCWPressureGap_abs_sub_le_half_abs population left right hpopulation

/-- Every positive finite-volume pressure is monotone in coupling. -/
theorem monotone_finiteCWPressureGap
    (population : ℕ) (hpopulation : 0 < population) :
    Monotone (finiteCWPressureGap population) := by
  intro left right hle
  have hpartition := finiteCWPartition_mono_coupling population hpopulation hle
  have hlog := Real.log_le_log (finiteCWPartition_pos population left) hpartition
  unfold finiteCWPressureGap
  exact div_le_div_of_nonneg_right hlog (by positivity)

/-- The aligned-state contribution gives a finite-volume lower bound with no
large-deviation or Varadhan premise. -/
theorem finiteCWPressureGap_ge_aligned
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    tlam / 2 - Real.log 2 ≤ finiteCWPressureGap population tlam := by
  have hbasePositive :
      0 < ((2 : ℝ) ^ population)⁻¹ * Real.exp (tlam * population / 2) := by
    positivity
  have hpartitionBound :=
    finiteCWPartition_aligned_lower_bound population tlam hpopulation
  have hlogBound :
      Real.log (((2 : ℝ) ^ population)⁻¹ *
          Real.exp (tlam * population / 2)) ≤
        Real.log (finiteCWPartition population tlam) :=
    Real.log_le_log hbasePositive hpartitionBound
  have hpopulationReal : (0 : ℝ) < population := by
    exact_mod_cast hpopulation
  rw [finiteCWPressureGap]
  apply (le_div_iff₀ hpopulationReal).mpr
  calc
    (tlam / 2 - Real.log 2) * population =
        tlam * population / 2 - population * Real.log 2 := by ring
    _ = Real.log (((2 : ℝ) ^ population)⁻¹ *
        Real.exp (tlam * population / 2)) := by
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
        Real.log_inv, Real.log_pow, Real.log_exp]
      ring
    _ ≤ Real.log (finiteCWPartition population tlam) := hlogBound

/-- The genuine finite pressure dominates the complete variational supremum
at every positive population and nonnegative coupling.  Interior objective
values use the finite Gibbs inequality; both endpoints use the exact aligned
state contribution. -/
theorem cwVariationalPressureGap_le_finiteCWPressureGap
    (population : ℕ) (tlam : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) :
    cwVariationalPressureGap tlam ≤ finiteCWPressureGap population tlam := by
  unfold cwVariationalPressureGap
  apply csSup_le (cwPressureValueSet_nonempty tlam)
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  by_cases hnegative : m = -1
  · subst m
    simpa [cwObjective_at_neg_one] using
      finiteCWPressureGap_ge_aligned population tlam hpopulation
  · by_cases hpositive : m = 1
    · subst m
      simpa [cwObjective_at_one] using
        finiteCWPressureGap_ge_aligned population tlam hpopulation
    · have hstrictLower : -1 < m :=
        lt_of_le_of_ne hm.1 (Ne.symm hnegative)
      have hstrictUpper : m < 1 :=
        lt_of_le_of_ne hm.2 hpositive
      exact finiteCWPressureGap_ge_cwObjective population tlam m hpopulation
        htlam ((abs_lt).2 ⟨hstrictLower, hstrictUpper⟩)

/-- The complete finite-to-variational squeeze: the only discrepancy is at
most the logarithm of the number of magnetisation types divided by population. -/
theorem finiteCWPressureGap_variational_bounds
    (population : ℕ) (tlam : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) :
    cwVariationalPressureGap tlam ≤ finiteCWPressureGap population tlam ∧
      finiteCWPressureGap population tlam ≤
        cwVariationalPressureGap tlam +
          Real.log (population + 1) / population :=
  ⟨cwVariationalPressureGap_le_finiteCWPressureGap population tlam
      hpopulation htlam,
    finiteCWPressureGap_le_variational_add_typeCount population tlam hpopulation⟩

/-- The finite pressure approximation has an explicit coupling-independent
absolute error. -/
theorem finiteCWPressureGap_abs_sub_variational_le_typeCount
    (population : ℕ) (tlam : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) :
    |finiteCWPressureGap population tlam - cwVariationalPressureGap tlam| ≤
      Real.log (population + 1) / population := by
  obtain ⟨hlower, hupper⟩ :=
    finiteCWPressureGap_variational_bounds population tlam hpopulation htlam
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

/-- **Full thermodynamic-limit identification.**  For every nonnegative
coupling, the genuine finite Rademacher pressure converges to the supremal
Curie--Weiss variational pressure.  The proof is a finite type-count squeeze;
no LDP, Stirling formula, or Varadhan lemma is assumed. -/
theorem finiteCWPressureGap_tendsto_variationalPressure
    (tlam : ℝ) (htlam : 0 ≤ tlam) :
    Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds (cwVariationalPressureGap tlam)) := by
  have herrorNonnegative : ∀ population : ℕ,
      0 ≤ finiteCWPressureGap (population + 1) tlam -
        cwVariationalPressureGap tlam := by
    intro population
    exact sub_nonneg.mpr
      (cwVariationalPressureGap_le_finiteCWPressureGap (population + 1) tlam
        (Nat.succ_pos population) htlam)
  have herrorUpper : ∀ population : ℕ,
      finiteCWPressureGap (population + 1) tlam -
          cwVariationalPressureGap tlam ≤
        Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ) := by
    intro population
    have hupper := finiteCWPressureGap_le_variational_add_typeCount
      (population + 1) tlam (Nat.succ_pos population)
    have hraw : finiteCWPressureGap (population + 1) tlam -
        cwVariationalPressureGap tlam ≤
          Real.log (((population + 1 : ℕ) : ℝ) + 1) /
            ((population + 1 : ℕ) : ℝ) :=
      sub_le_iff_le_add.mpr (by simpa [add_comm] using hupper)
    convert hraw using 1
    all_goals norm_num [Nat.cast_add]
    all_goals ring
  have herror : Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam -
        cwVariationalPressureGap tlam)
      Filter.atTop (nhds 0) :=
    squeeze_zero herrorNonnegative herrorUpper
      finiteCWTypeCount_log_div_tendsto_zero
  have hconstant : Filter.Tendsto
      (fun _population : ℕ ↦ cwVariationalPressureGap tlam)
      Filter.atTop (nhds (cwVariationalPressureGap tlam)) :=
    tendsto_const_nhds
  convert hconstant.add herror using 1 <;> simp [add_comm]

/-- **Uniform thermodynamic-limit identification on the whole positive
cone.**  Because the type-count error is independent of coupling, finite
Curie--Weiss pressure converges uniformly to the variational pressure on the
entire half-line `[0,∞)`, not merely on compact coupling windows. -/
theorem finiteCWPressureGap_tendstoUniformlyOn_nonnegative :
    TendstoUniformlyOn
      (fun population : ℕ ↦ fun tlam : ℝ ↦
        finiteCWPressureGap (population + 1) tlam)
      cwVariationalPressureGap Filter.atTop (Set.Ici 0) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ population : ℕ in Filter.atTop,
      Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ) < epsilon :=
    finiteCWTypeCount_log_div_tendsto_zero.eventually_lt_const hepsilon
  filter_upwards [hsmall] with population hpopulationSmall
  intro tlam htlam
  have herror := finiteCWPressureGap_abs_sub_variational_le_typeCount
    (population + 1) tlam (Nat.succ_pos population) htlam
  rw [Real.dist_eq, abs_sub_comm]
  exact herror.trans_lt (by
    convert hpopulationSmall using 1
    all_goals norm_num [Nat.cast_add]
    all_goals ring)

/-- **Actual positive finite-volume pressure separation.**  Above the explicit
aligned-state threshold, every positive population size already has strictly
positive normalized Rademacher pressure.  No limiting interchange, LDP, or
analyticity assumption occurs in the statement. -/
theorem finiteCWPressureGap_pos_of_aligned
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population)
    (hlarge : 2 * Real.log 2 < tlam) :
    0 < finiteCWPressureGap population tlam := by
  have hthreshold : 0 < tlam / 2 - Real.log 2 := by linarith
  exact hthreshold.trans_le
    (finiteCWPressureGap_ge_aligned population tlam hpopulation)

/-- The aligned-state lower bound is uniform in population, so above its
threshold the genuine finite pressure gap cannot disappear in the
thermodynamic limit. -/
theorem finiteCWPressureGap_not_tendsto_zero_of_aligned
    (tlam : ℝ) (hlarge : 2 * Real.log 2 < tlam) :
    ¬ Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds 0) := by
  intro hzero
  have hthreshold : 0 < tlam / 2 - Real.log 2 := by linarith
  have hbelow : ∀ᶠ population in Filter.atTop,
      finiteCWPressureGap (population + 1) tlam <
        tlam / 2 - Real.log 2 :=
    hzero.eventually_lt_const hthreshold
  obtain ⟨population, hpopulation⟩ := Filter.eventually_atTop.mp hbelow
  have hlt := hpopulation population le_rfl
  have hle := finiteCWPressureGap_ge_aligned
    (population + 1) tlam (Nat.succ_pos population)
  exact (not_lt_of_ge hle) hlt

/-- The unspiked `aI` contribution to the normalized one-replica quadratic
Rademacher pressure. -/
noncomputable def finiteBaselineRademacherPressure
    (baseline temperature : ℝ) : ℝ :=
  temperature * baseline / 2

/-- The normalized pressure of `aI + λ uuᵀ` for the balanced-sign rank-one
direction.  The Curie--Weiss coupling is exactly `temperature * spikeStrength`;
the baseline and spike contributions therefore separate additively. -/
noncomputable def finiteRankOneRademacherPressure
    (baseline : ℝ) (population : ℕ)
    (temperature spikeStrength : ℝ) : ℝ :=
  finiteBaselineRademacherPressure baseline temperature +
    finiteCWPressureGap population (temperature * spikeStrength)

/-- The difference between the spiked and unspiked finite pressures is exactly
the normalized Curie--Weiss pressure gap, not merely bounded by it. -/
theorem finiteRankOneRademacherPressure_sub_baseline
    (baseline : ℝ) (population : ℕ)
    (temperature spikeStrength : ℝ) :
    finiteRankOneRademacherPressure baseline population temperature spikeStrength -
        finiteBaselineRademacherPressure baseline temperature =
      finiteCWPressureGap population (temperature * spikeStrength) := by
  simp [finiteRankOneRademacherPressure]

/-- Throughout the exact supercritical regime, the genuine spiked finite
pressure is strictly larger than the unspiked pressure for every nonempty
population. -/
theorem finiteRankOneRademacherPressure_gt_baseline
    (baseline : ℝ) (population : ℕ)
    (temperature spikeStrength : ℝ) (hpopulation : 0 < population)
    (hcritical : 1 < temperature * spikeStrength) :
    finiteBaselineRademacherPressure baseline temperature <
      finiteRankOneRademacherPressure
        baseline population temperature spikeStrength := by
  rw [finiteRankOneRademacherPressure]
  exact lt_add_of_pos_right _
    (finiteCWPressureGap_pos_of_supercritical
      population (temperature * spikeStrength) hpopulation hcritical)

/-- The exact-criticality statement for the finite rank-one pressure sequence. -/
def FiniteRankOnePressureCriticalStatement
    (baseline temperature spikeStrength : ℝ) : Prop :=
  Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneRademacherPressure baseline (population + 1)
            temperature spikeStrength -
          finiteBaselineRademacherPressure baseline temperature)
      Filter.atTop (nhds 0) ↔
    temperature * spikeStrength ≤ 1

/-- The variational-limit statement for the complete finite rank-one pressure. -/
def FiniteRankOnePressureVariationalLimitStatement
    (baseline temperature spikeStrength : ℝ) : Prop :=
  Filter.Tendsto
    (fun population : ℕ ↦
      finiteRankOneRademacherPressure baseline (population + 1)
        temperature spikeStrength)
    Filter.atTop
    (nhds (finiteBaselineRademacherPressure baseline temperature +
      cwVariationalPressureGap (temperature * spikeStrength)))

/-- The uniform nonnegative-spike convergence statement. -/
def FiniteRankOnePressureUniformLimitStatement
    (baseline temperature : ℝ) : Prop :=
  TendstoUniformlyOn
    (fun population : ℕ ↦ fun spikeStrength : ℝ ↦
      finiteRankOneRademacherPressure baseline (population + 1)
        temperature spikeStrength)
    (fun spikeStrength ↦
      finiteBaselineRademacherPressure baseline temperature +
        cwVariationalPressureGap (temperature * spikeStrength))
    Filter.atTop (Set.Ici 0)

/-- For nonnegative effective coupling, the genuine finite rank-one pressure
difference converges to zero exactly at and below the Curie--Weiss threshold. -/
theorem finiteRankOneRademacherPressure_difference_tendsto_zero_iff
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    FiniteRankOnePressureCriticalStatement baseline temperature spikeStrength := by
  unfold FiniteRankOnePressureCriticalStatement
  simpa only [finiteRankOneRademacherPressure_sub_baseline] using
    finiteCWPressureGap_tendsto_zero_iff
      (temperature * spikeStrength) hcoupling

/-- The complete finite rank-one pressure converges to the baseline plus the
Curie--Weiss variational pressure at every nonnegative effective coupling. -/
theorem finiteRankOneRademacherPressure_tendsto_variational
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    FiniteRankOnePressureVariationalLimitStatement
      baseline temperature spikeStrength := by
  have hbaseline : Filter.Tendsto
      (fun _population : ℕ ↦
        finiteBaselineRademacherPressure baseline temperature)
      Filter.atTop
      (nhds (finiteBaselineRademacherPressure baseline temperature)) :=
    tendsto_const_nhds
  have hgap := finiteCWPressureGap_tendsto_variationalPressure
    (temperature * spikeStrength) hcoupling
  simpa only [finiteRankOneRademacherPressure] using hbaseline.add hgap

/-- The same thermodynamic limit holds along the even dimensions `2(p+1)`
used by the concrete balanced covariance matrices. -/
theorem balancedRankOneCovariancePressure_tendsto_variational
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneRademacherPressure baseline (2 * (population + 1))
          temperature spikeStrength)
      Filter.atTop
      (nhds (finiteBaselineRademacherPressure baseline temperature +
        cwVariationalPressureGap (temperature * spikeStrength))) := by
  have hevenIndex : Filter.Tendsto (fun population : ℕ ↦ 2 * population + 1)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro threshold
    filter_upwards [Filter.eventually_ge_atTop threshold] with population hpopulation
    omega
  have hpressure := (finiteRankOneRademacherPressure_tendsto_variational
    baseline temperature spikeStrength hcoupling).comp hevenIndex
  simpa only [Function.comp_apply] using hpressure

/-- The complete concrete positive-cone counterexample, packaged so that its
matrix, traffic, ground-state, and thermodynamic statements cannot silently
refer to different witnesses. -/
structure ConcreteBalancedPSDPressureWitness
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (baseline spikeStrength temperature : ℝ) : Prop where
  covariancePSD : ∀ population : ℕ,
    (balancedRankOneCovariance baseline spikeStrength (population + 1)).PosSemidef
  trafficInvisible :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0)
  finiteHamiltonian : ∀ population : ℕ,
    ∀ vector : BalancedRankOneCoordinate (population + 1) → ℝ,
      (∀ coordinate, vector coordinate ^ 2 = 1) →
        temperature / 2 *
            (finiteMatrixQuadraticForm
                (balancedRankOneCovariance baseline spikeStrength (population + 1))
                vector - baseline * (2 * (population + 1) : ℕ)) =
          (temperature * spikeStrength) /
              (2 * ((2 * (population + 1) : ℕ) : ℝ)) *
            (balancedRankOneSign (population + 1) ⬝ᵥ vector) ^ 2
  lowerGroundStateUnchanged : ∀ population : ℕ,
    (∀ vector : BalancedRankOneCoordinate (population + 1) → ℝ,
      (∀ coordinate, vector coordinate ^ 2 = 1) →
        baseline * (2 * (population + 1) : ℕ) ≤
          finiteMatrixQuadraticForm
            (balancedRankOneCovariance baseline spikeStrength (population + 1))
            vector) ∧
      finiteMatrixQuadraticForm
          (balancedRankOneCovariance baseline spikeStrength (population + 1))
          (balancedRankOneOrthogonalSpin (population + 1)) =
        baseline * (2 * (population + 1) : ℕ) ∧
      baseline * (2 * (population + 1) : ℕ) <
        finiteMatrixQuadraticForm
          (balancedRankOneCovariance baseline spikeStrength (population + 1))
          (balancedRankOneSign (population + 1))
  pressureConverges :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneRademacherPressure baseline (2 * (population + 1))
          temperature spikeStrength)
      Filter.atTop
      (nhds (finiteBaselineRademacherPressure baseline temperature +
        cwVariationalPressureGap (temperature * spikeStrength)))
  pressureStrictlyPositive :
    0 < cwVariationalPressureGap (temperature * spikeStrength)

/-- **One actual balanced PSD covariance sequence refutes both proposed
dichotomies.**  Under `a ≥ 0`, `λ > 0`, and `tλ > 1`, the same matrices
`aI + λP` satisfy every field of `ConcreteBalancedPSDPressureWitness`. -/
theorem concreteBalancedPSDPressureWitness
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (baseline spikeStrength temperature : ℝ)
    (hbaseline : 0 ≤ baseline) (hspike : 0 < spikeStrength)
    (hcritical : 1 < temperature * spikeStrength) :
    ConcreteBalancedPSDPressureWitness coefficient hasOddDegree vertices edges
      baseline spikeStrength temperature := by
  have hcoupling : 0 ≤ temperature * spikeStrength := by linarith
  exact
    { covariancePSD := fun population ↦
        balancedRankOneCovariance_posSemidef baseline spikeStrength (population + 1)
          hbaseline hspike.le
      trafficInvisible :=
        finiteRankOneTrafficCorrection_tendsto_zero coefficient hasOddDegree
          vertices edges hconnected
      finiteHamiltonian := fun population vector hrademacher ↦
        balancedRankOneCovariance_rademacherExponent_eq_finiteCW
          baseline spikeStrength temperature (population + 1) vector hrademacher
      lowerGroundStateUnchanged := fun population ↦
        balancedRankOneCovariance_groundState_certificate baseline spikeStrength
          (population + 1) hspike (Nat.succ_pos population)
      pressureConverges :=
        balancedRankOneCovariancePressure_tendsto_variational
          baseline temperature spikeStrength hcoupling
      pressureStrictlyPositive :=
        cwVariationalPressureGap_pos_of_supercritical
          (temperature * spikeStrength) hcritical }

/-- At fixed nonnegative temperature, convergence of the complete rank-one
pressure is uniform over every nonnegative spike strength, including the
unbounded half-line. -/
theorem finiteRankOneRademacherPressure_tendstoUniformlyOn_nonnegativeSpike
    (baseline temperature : ℝ) (htemperature : 0 ≤ temperature) :
    FiniteRankOnePressureUniformLimitStatement baseline temperature := by
  unfold FiniteRankOnePressureUniformLimitStatement
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ population : ℕ in Filter.atTop,
      Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ) < epsilon :=
    finiteCWTypeCount_log_div_tendsto_zero.eventually_lt_const hepsilon
  filter_upwards [hsmall] with population hpopulationSmall
  intro spikeStrength hspikeStrength
  have hcoupling : 0 ≤ temperature * spikeStrength :=
    mul_nonneg htemperature hspikeStrength
  have herror := finiteCWPressureGap_abs_sub_variational_le_typeCount
    (population + 1) (temperature * spikeStrength)
    (Nat.succ_pos population) hcoupling
  have hstrict : |finiteCWPressureGap (population + 1)
      (temperature * spikeStrength) -
        cwVariationalPressureGap (temperature * spikeStrength)| < epsilon :=
    herror.trans_lt (by
      convert hpopulationSmall using 1
      all_goals norm_num [Nat.cast_add]
      all_goals ring)
  simpa [finiteRankOneRademacherPressure, Real.dist_eq, abs_sub_comm] using hstrict

/-- **Positive-cone traffic counterexample at the exact variational level.**
Every fixed graph has finitely many nonempty spike-edge terms; once identity
edges are contracted, their complete correction vanishes by the connected
rank-one bound.  Nevertheless the Curie--Weiss variational pressure is strictly
positive above `tλ = 1`.

The full finite-pressure theorem below additionally identifies this
variational pressure as the genuine thermodynamic limit. -/
theorem finiteRankOneTraffic_invisible_variationalPressure_visible
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (tlam : ℝ) (hcritical : 1 < tlam) :
    Filter.Tendsto
        (fun population : ℕ ↦
          finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
            (population + 1))
        Filter.atTop (nhds 0) ∧
      0 < cwVariationalPressureGap tlam :=
  ⟨finiteRankOneTrafficCorrection_tendsto_zero
      coefficient hasOddDegree vertices edges hconnected,
    cwVariationalPressureGap_pos_of_supercritical tlam hcritical⟩

/-- **The finite-volume properties one rank-one spike has at once**, as one
proposition: every fixed traffic correction vanishes, the genuine pressure
converges to the variational value, and one positive interior witness uniformly
lower-bounds every finite pressure, so that pressure cannot vanish
asymptotically.

Named for the same reason as `RankOneSpikeRefutesBothDichotomies`: the theorem that proves
it, the genomic restatement that cites that theorem, and the obstruction registry each
carried the conjunction in full, so a change to one copy would have been a silent divergence
rather than a build error.

Empirical status: NOT AN EMPIRICAL CLAIM. This names four propositions, each
proved below at finite volume on an explicit spike, so there is no measurement
that could agree or disagree with it. What a measurement could bear on is
whether a real LD spike is rank-one, which nothing here asserts. An UNTESTED
marker would read as a measurement owed, and none is. -/
def RankOneSpikeInvisibleWithFinitePressure {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ) (tlam : ℝ) : Prop :=
  Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds (cwVariationalPressureGap tlam)) ∧
    ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m ∧
      (∀ population : ℕ,
        cwObjective tlam m ≤ finiteCWPressureGap (population + 1) tlam) ∧
      ¬ Filter.Tendsto
        (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
        Filter.atTop (nhds 0)

/-- **Positive-cone traffic counterexample for the genuine finite partition
function throughout the full supercritical regime.**  Every fixed traffic
correction vanishes, while for every coupling above `1` one interior trial law
supplies a positive population-uniform lower bound on normalized Rademacher
pressure.  The companion finite-pressure theorem proves convergence to zero
at and below `1`; neither statement requires an LDP or Varadhan premise. -/
theorem finiteRankOneTraffic_invisible_finitePressure_visible
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (tlam : ℝ) (hcritical : 1 < tlam) :
    RankOneSpikeInvisibleWithFinitePressure coefficient hasOddDegree vertices edges tlam := by
  obtain ⟨m, hm, hobjective, hlower⟩ :=
    finiteCWPressureGap_supercritical_uniformWitness tlam hcritical
  exact ⟨finiteRankOneTrafficCorrection_tendsto_zero
      coefficient hasOddDegree vertices edges hconnected,
    finiteCWPressureGap_tendsto_variationalPressure tlam
      (le_trans (by norm_num) hcritical.le),
    ⟨m, hm, hobjective,
      ⟨fun population ↦ hlower (population + 1) (Nat.succ_pos population),
        finiteCWPressureGap_not_tendsto_zero_of_supercritical tlam hcritical⟩⟩⟩

/-- **The four properties one positive rank-one spike has at once**, as one proposition.

The theorem below establishes it, `UnifiedBiology` restates it in genomic vocabulary and
cites that theorem, and the obstruction registry carries it as a field.  Written out, the
conjunction stood in the corpus three times, and a change to any one copy would have been a
silent divergence between them rather than a build error.

Empirical status: NOT AN EMPIRICAL CLAIM. This names a conjunction of four
propositions, each proved below on an explicit spike, so there is no measurement
that could agree or disagree with it. What a measurement could bear on is
whether a real LD spike is rank-one, which nothing here asserts. An UNTESTED
marker would read as a measurement owed, and none is. -/
def RankOneSpikeRefutesBothDichotomies
    {Term Spin : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (alignment : Spin → ℝ) (orthogonal aligned : Spin)
    (baseline spikeStrength population temperature : ℝ) : Prop :=
  Filter.Tendsto
      (fun size : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges (size + 1))
      Filter.atTop (nhds 0) ∧
    (∀ state, baseline ≤
      rankOneEnergyDensity baseline spikeStrength population (alignment state)) ∧
    rankOneEnergyDensity baseline spikeStrength population (alignment orthogonal) =
      baseline ∧
    baseline <
      rankOneEnergyDensity baseline spikeStrength population (alignment aligned) ∧
    0 < cwVariationalPressureGap (temperature * spikeStrength)

/-- **One exact witness refutes both the positive-cone traffic conjecture and
the lower-ground-state dichotomy at the variational level.**  The same positive
rank-one spike has all four properties:

1. every fixed traffic correction vanishes after its finite contraction
   expansion;
2. no state has energy below the unspiked baseline;
3. an orthogonal state attains that baseline exactly, while an aligned state
   has strictly larger energy; and
4. its Curie--Weiss variational pressure is positive when `temperature * λ > 1`.

The population and aligned-state hypotheses exclude the zero-dimensional and
zero-response junk cases explicitly. -/
theorem rankOneTraffic_groundState_pressure_counterexample
    {Term Spin : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (alignment : Spin → ℝ) (orthogonal aligned : Spin)
    (baseline spikeStrength population temperature : ℝ)
    (hspike : 0 < spikeStrength) (hpopulation : population ≠ 0)
    (horthogonal : alignment orthogonal = 0)
    (haligned : alignment aligned = population)
    (hcritical : 1 < temperature * spikeStrength) :
    RankOneSpikeRefutesBothDichotomies coefficient hasOddDegree vertices edges
      alignment orthogonal aligned baseline spikeStrength population temperature := by
  have htraffic := finiteRankOneTrafficCorrection_tendsto_zero
    coefficient hasOddDegree vertices edges hconnected
  obtain ⟨hlower, hground⟩ := rankOne_groundState_certificate
    alignment orthogonal baseline spikeStrength population hspike.le horthogonal
  have hupper : baseline <
      rankOneEnergyDensity baseline spikeStrength population (alignment aligned) := by
    rw [haligned, rankOneEnergyDensity_aligned baseline spikeStrength population hpopulation]
    linarith
  exact ⟨htraffic, hlower, hground, hupper,
    cwVariationalPressureGap_pos_of_supercritical
      (temperature * spikeStrength) hcritical⟩

end CurieWeissWindow

section MesoscopicAmplification

/-- Difference between the diagonal traffic coordinate of `aI` and that of a diagonal matrix
whose exceptional fraction is `4⁻ᵏ` and exceptional value is `a + 2`. -/
noncomputable def diagonalTrafficCorrection (baseline : ℝ) (edges iteration : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ iteration * ((baseline + 2) ^ edges - baseline ^ edges)

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem diagonalTrafficCorrection_at_reference_point :
    diagonalTrafficCorrection 1 1 1 = 1 / 2 := by
  norm_num [diagonalTrafficCorrection]


/-- Every fixed traffic coordinate misses the exceptional diagonal block. -/
theorem diagonalTrafficCorrection_tendsto_zero (baseline : ℝ) (edges : ℕ) :
    Filter.Tendsto (fun iteration ↦ diagonalTrafficCorrection baseline edges iteration)
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun iteration : ℕ ↦ (1 / 4 : ℝ) ^ iteration)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  simpa [diagonalTrafficCorrection] using
    hpow.mul_const ((baseline + 2) ^ edges - baseline ^ edges)

/-- A concrete `16^k`-coordinate realization of the mesoscopic example.  The
second coordinate indexes `4^k` blocks; the exceptional subspace is the slice
whose second coordinate has value zero and therefore has exactly `4^k`
coordinates. -/
abbrev MesoscopicGFOMCoordinate (iteration : ℕ) :=
  Fin (4 ^ iteration) × Fin (4 ^ iteration)

/-- The exceptional coordinate slice supporting the amplified output. -/
abbrev MesoscopicGFOMExceptionalCoordinate (iteration : ℕ) :=
  {coordinate : MesoscopicGFOMCoordinate iteration // coordinate.2.val = 0}

/-- The concrete ambient dimension is exactly `16^k`. -/
theorem mesoscopicGFOM_dimension (iteration : ℕ) :
    Fintype.card (MesoscopicGFOMCoordinate iteration) = 16 ^ iteration := by
  simp [MesoscopicGFOMCoordinate, ← mul_pow]

/-- The concrete exceptional rank is exactly `4^k`. -/
theorem mesoscopicGFOM_exceptionalRank (iteration : ℕ) :
    Fintype.card (MesoscopicGFOMExceptionalCoordinate iteration) = 4 ^ iteration := by
  classical
  let equivalence : MesoscopicGFOMExceptionalCoordinate iteration ≃ Fin (4 ^ iteration) :=
    { toFun := fun coordinate ↦ coordinate.1.1
      invFun := fun coordinate ↦
        ⟨(coordinate, ⟨0, pow_pos (by norm_num) iteration⟩), rfl⟩
      left_inv := by
        intro coordinate
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Fin.ext
          exact coordinate.property.symm
      right_inv := fun _coordinate ↦ rfl }
  simpa using Fintype.card_congr equivalence

/-- The actual diagonal GFOM step `(M-aI)x`: multiply the exceptional slice
by two and annihilate the bulk. -/
def mesoscopicGFOMStep (iteration : ℕ)
    (vector : MesoscopicGFOMCoordinate iteration → ℝ) :
    MesoscopicGFOMCoordinate iteration → ℝ :=
  fun coordinate ↦ if coordinate.2.val = 0 then 2 * vector coordinate else 0

/-- Repeated application of the concrete diagonal step. -/
def mesoscopicGFOMIterate (iteration : ℕ) :
    ℕ → (MesoscopicGFOMCoordinate iteration → ℝ) →
      MesoscopicGFOMCoordinate iteration → ℝ
  | 0, vector => vector
  | runtime + 1, vector =>
      mesoscopicGFOMStep iteration (mesoscopicGFOMIterate iteration runtime vector)

/-- Every positive-time iterate has the exact expected coordinate formula:
the exceptional slice is multiplied by `2^t` and every bulk coordinate is
zero. -/
theorem mesoscopicGFOMIterate_succ_apply
    (iteration runtime : ℕ)
    (vector : MesoscopicGFOMCoordinate iteration → ℝ)
    (coordinate : MesoscopicGFOMCoordinate iteration) :
    mesoscopicGFOMIterate iteration (runtime + 1) vector coordinate =
      if coordinate.2.val = 0 then
        (2 : ℝ) ^ (runtime + 1) * vector coordinate else 0 := by
  induction runtime with
  | zero =>
      simp [mesoscopicGFOMIterate, mesoscopicGFOMStep]
  | succ runtime ih =>
      by_cases hexceptional : coordinate.2.val = 0
      · rw [mesoscopicGFOMIterate]
        simp only [mesoscopicGFOMStep, hexceptional, ↓reduceIte, ih, pow_succ]
        ring
      · rw [mesoscopicGFOMIterate]
        simp only [mesoscopicGFOMStep, hexceptional, ↓reduceIte]

/-- Deterministic unit input used to expose the exact normalized amplification
without adding an unnecessary probabilistic layer. -/
def mesoscopicGFOMUnitInput (iteration : ℕ) :
    MesoscopicGFOMCoordinate iteration → ℝ :=
  constantOneVector

/-- Both deterministic inputs are restrictions of the same constant-one
vector, despite living on different finite coordinate spaces. -/
theorem balancedRankOneOrthogonalSpin_eq_mesoscopicGFOMUnitInput
    (population iteration : ℕ)
    (balancedCoordinate : BalancedRankOneCoordinate population)
    (mesoscopicCoordinate : MesoscopicGFOMCoordinate iteration) :
    balancedRankOneOrthogonalSpin population balancedCoordinate =
      mesoscopicGFOMUnitInput iteration mesoscopicCoordinate := by
  rfl

/-- Normalized squared output of the genuine finite diagonal iteration. -/
noncomputable def mesoscopicGFOMActualEnergy (iteration runtime : ℕ) : ℝ :=
  (∑ coordinate : MesoscopicGFOMCoordinate iteration,
    mesoscopicGFOMIterate iteration runtime
      (mesoscopicGFOMUnitInput iteration) coordinate ^ 2) /
    (16 : ℝ) ^ iteration

/-- Exactly `4^k` coordinates lie in the exceptional slice. -/
theorem mesoscopicGFOM_sum_exceptionalSlice
    (iteration : ℕ) (value : ℝ) :
    (∑ coordinate : MesoscopicGFOMCoordinate iteration,
      if coordinate.2.val = 0 then value else 0) =
      (4 : ℝ) ^ iteration * value := by
  classical
  have hsize : 0 < 4 ^ iteration := pow_pos (by norm_num) iteration
  have hinner : ∀ first : Fin (4 ^ iteration),
      (∑ second : Fin (4 ^ iteration),
        if second.val = 0 then value else 0) = value := by
    intro first
    let zero : Fin (4 ^ iteration) := ⟨0, hsize⟩
    rw [Finset.sum_eq_single zero]
    · simp [zero]
    · intro second _hsecond hne
      have hnonzero : second.val ≠ 0 := by
        intro hzero
        apply hne
        apply Fin.ext
        exact hzero
      simp [hnonzero]
    · simp
  rw [Fintype.sum_prod_type]
  calc
    (∑ first : Fin (4 ^ iteration),
      ∑ second : Fin (4 ^ iteration),
        if second.val = 0 then value else 0) =
        ∑ _first : Fin (4 ^ iteration), value := by
      apply Finset.sum_congr rfl
      intro first _hfirst
      exact hinner first
    _ = (4 : ℝ) ^ iteration * value := by simp

/-- Normalized squared output of the diagonal power iteration: the exceptional mass `4⁻ᵏ` is
amplified by `4ᵗ`. -/
noncomputable def mesoscopicGFOMEnergy (iteration runtime : ℕ) : ℝ :=
  (4 : ℝ) ^ runtime * (1 / 4 : ℝ) ^ iteration

/-- At every positive runtime, the energy of the concrete `16^k`-dimensional
iteration is exactly the scalar amplification ledger. -/
theorem mesoscopicGFOMActualEnergy_succ_eq_proxy
    (iteration runtime : ℕ) :
    mesoscopicGFOMActualEnergy iteration (runtime + 1) =
      mesoscopicGFOMEnergy iteration (runtime + 1) := by
  have hsum :
      (∑ coordinate : MesoscopicGFOMCoordinate iteration,
        mesoscopicGFOMIterate iteration (runtime + 1)
          (mesoscopicGFOMUnitInput iteration) coordinate ^ 2) =
        (4 : ℝ) ^ iteration * ((2 : ℝ) ^ (runtime + 1)) ^ 2 := by
    simpa [mesoscopicGFOMIterate_succ_apply, mesoscopicGFOMUnitInput] using
      mesoscopicGFOM_sum_exceptionalSlice iteration
        (((2 : ℝ) ^ (runtime + 1)) ^ 2)
  have hamplification : ((2 : ℝ) ^ (runtime + 1)) ^ 2 =
      (4 : ℝ) ^ (runtime + 1) := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hmass : (4 : ℝ) ^ iteration / (16 : ℝ) ^ iteration =
      (1 / 4 : ℝ) ^ iteration := by
    rw [← div_pow]
    norm_num
  rw [mesoscopicGFOMActualEnergy, hsum, hamplification, mesoscopicGFOMEnergy]
  calc
    (4 : ℝ) ^ iteration * (4 : ℝ) ^ (runtime + 1) /
        (16 : ℝ) ^ iteration =
      (4 : ℝ) ^ (runtime + 1) *
        ((4 : ℝ) ^ iteration / (16 : ℝ) ^ iteration) := by ring
    _ = (4 : ℝ) ^ (runtime + 1) * (1 / 4 : ℝ) ^ iteration := by rw [hmass]

/-- At logarithmic runtime `t = k`, the vanishing mass and amplification cancel exactly. -/
@[simp] theorem mesoscopicGFOMEnergy_logRuntime (iteration : ℕ) :
    mesoscopicGFOMEnergy iteration iteration = 1 := by
  rw [mesoscopicGFOMEnergy, ← mul_pow]
  norm_num

/-- At every fixed runtime, the same normalized output vanishes. -/
theorem mesoscopicGFOMEnergy_fixedRuntime_tendsto_zero (runtime : ℕ) :
    Filter.Tendsto (fun iteration ↦ mesoscopicGFOMEnergy iteration runtime)
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun iteration : ℕ ↦ (1 / 4 : ℝ) ^ iteration)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  simpa [mesoscopicGFOMEnergy] using hpow.const_mul ((4 : ℝ) ^ runtime)

/-- Every fixed positive runtime of the actual finite diagonal iteration has
vanishing normalized output energy. -/
theorem mesoscopicGFOMActualEnergy_fixedPositiveRuntime_tendsto_zero
    (runtime : ℕ) :
    Filter.Tendsto
      (fun iteration ↦ mesoscopicGFOMActualEnergy iteration (runtime + 1))
      Filter.atTop (nhds 0) := by
  simpa only [mesoscopicGFOMActualEnergy_succ_eq_proxy] using
    mesoscopicGFOMEnergy_fixedRuntime_tendsto_zero (runtime + 1)

/-- At the genuine logarithmic runtime `t=k`, for every positive `k`, the
actual normalized squared output is exactly one. -/
theorem mesoscopicGFOMActualEnergy_logRuntime (iteration : ℕ)
    (hiteration : 0 < iteration) :
    mesoscopicGFOMActualEnergy iteration iteration = 1 := by
  obtain ⟨runtime, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hiteration)
  rw [mesoscopicGFOMActualEnergy_succ_eq_proxy]
  exact mesoscopicGFOMEnergy_logRuntime (runtime + 1)

/-- The dimensions `pₖ = 16ᵏ` and exceptional ranks `rₖ = 4ᵏ` have mass exactly `4⁻ᵏ`. -/
theorem mesoscopic_rank_fraction (iteration : ℕ) :
    (4 : ℝ) ^ iteration / (16 : ℝ) ^ iteration = (1 / 4 : ℝ) ^ iteration := by
  rw [← div_pow]
  norm_num

/-- Fixed traffic and logarithmic-time iteration therefore have incompatible limits. -/
theorem limitingTraffic_does_not_control_logarithmicIteration (runtime : ℕ) :
    Filter.Tendsto (fun iteration ↦ diagonalTrafficCorrection 1 runtime iteration)
        Filter.atTop (nhds 0) ∧
      mesoscopicGFOMEnergy runtime runtime = 1 :=
  ⟨diagonalTrafficCorrection_tendsto_zero 1 runtime,
    mesoscopicGFOMEnergy_logRuntime runtime⟩

/-- The fixed-coordinate/logarithmic-runtime separation contract. -/
def FixedTrafficLogRuntimeSeparation : Prop :=
    (∀ edges : ℕ,
      Filter.Tendsto (fun iteration ↦ diagonalTrafficCorrection 1 edges iteration)
        Filter.atTop (nhds 0)) ∧
      ∀ iteration : ℕ, mesoscopicGFOMEnergy iteration iteration = 1

/-- The complete fixed-coordinate/logarithmic-runtime separation in one statement. -/
theorem fixedTraffic_invisible_logRuntime_visible : FixedTrafficLogRuntimeSeparation :=
  ⟨diagonalTrafficCorrection_tendsto_zero 1, mesoscopicGFOMEnergy_logRuntime⟩

/-- The concrete finite-matrix version of the logarithmic-runtime separation. -/
def ConcreteGFOMLogRuntimeSeparation : Prop :=
  (∀ iteration : ℕ,
    Fintype.card (MesoscopicGFOMCoordinate iteration) = 16 ^ iteration ∧
      Fintype.card (MesoscopicGFOMExceptionalCoordinate iteration) = 4 ^ iteration) ∧
  (∀ edges : ℕ,
    Filter.Tendsto (fun iteration ↦ diagonalTrafficCorrection 1 edges iteration)
      Filter.atTop (nhds 0)) ∧
  (∀ runtime : ℕ,
    Filter.Tendsto
      (fun iteration ↦ mesoscopicGFOMActualEnergy iteration (runtime + 1))
      Filter.atTop (nhds 0)) ∧
  ∀ iteration : ℕ, 0 < iteration →
    mesoscopicGFOMActualEnergy iteration iteration = 1

/-- **Concrete matrix-iteration counterexample.**  The actual finite diagonal
operator has dimension `16^k` and exceptional rank `4^k`; every fixed traffic
coordinate and every fixed positive-time output energy vanish, while the
positive logarithmic-time output energy is exactly one. -/
theorem concreteGFOM_fixedTrafficInvisible_logRuntimeVisible :
    ConcreteGFOMLogRuntimeSeparation :=
  ⟨fun iteration ↦
      ⟨mesoscopicGFOM_dimension iteration, mesoscopicGFOM_exceptionalRank iteration⟩,
    diagonalTrafficCorrection_tendsto_zero 1,
    mesoscopicGFOMActualEnergy_fixedPositiveRuntime_tendsto_zero,
    mesoscopicGFOMActualEnergy_logRuntime⟩

/-! ### Coefficient amplification already breaks limiting traffic at degree one -/

/-- A degree-one invariant polynomial may multiply its normalized trace
coordinate by a size-dependent coefficient.  On the `16^k`-dimensional
diagonal witness, the coefficient `4^k = p_k / r_k` exactly resolves the
exceptional block of relative mass `4⁻ᵏ`. -/
noncomputable def amplifiedDegreeOneTrafficDifference
    (baseline : ℝ) (iteration : ℕ) : ℝ :=
  (4 : ℝ) ^ iteration * diagonalTrafficCorrection baseline 1 iteration

/-- The unamplified degree-one traffic discrepancy vanishes. -/
theorem degreeOneTrafficDifference_tendsto_zero (baseline : ℝ) :
    Filter.Tendsto
      (fun iteration ↦ diagonalTrafficCorrection baseline 1 iteration)
      Filter.atTop (nhds 0) :=
  diagonalTrafficCorrection_tendsto_zero baseline 1

/-- The growing coefficient recovers the spike height exactly at every size.
This is the finite statement behind the correction that fixed degree alone
does not imply factorization through *limiting* traffic. -/
@[simp] theorem amplifiedDegreeOneTrafficDifference_eq_two
    (baseline : ℝ) (iteration : ℕ) :
    amplifiedDegreeOneTrafficDifference baseline iteration = 2 := by
  rw [amplifiedDegreeOneTrafficDifference, diagonalTrafficCorrection]
  rw [show (baseline + 2) ^ 1 - baseline ^ 1 = 2 by ring]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- **Unrestricted degree-one polynomials do not factor through limiting
traffic.**  The normalized degree-one coordinate tends to zero, while the
same coordinate with coefficient growth `4^k` remains equal to two. -/
theorem limitingTraffic_insufficient_for_unstableDegreeOne (baseline : ℝ) :
    Filter.Tendsto
        (fun iteration ↦ diagonalTrafficCorrection baseline 1 iteration)
        Filter.atTop (nhds 0) ∧
      ∀ iteration,
        amplifiedDegreeOneTrafficDifference baseline iteration = 2 :=
  ⟨degreeOneTrafficDifference_tendsto_zero baseline,
    amplifiedDegreeOneTrafficDifference_eq_two baseline⟩

end MesoscopicAmplification

section SpectralSDPSeparation

/-- One distinguished outlier coordinate together with `population` bulk
coordinates. -/
abbrev FiniteOutlierCoordinate (population : ℕ) := Option (Fin population)

/-- The baseline diagonal spectrum is constant. -/
def finiteBulkDiagonal (baseline : ℝ) (population : ℕ) :
    FiniteOutlierCoordinate population → ℝ :=
  fun _coordinate ↦ baseline

/-- A single positive spectral outlier, of normalized mass `1/(p+1)`. -/
def finiteOutlierDiagonal (baseline spikeStrength : ℝ) (population : ℕ) :
    FiniteOutlierCoordinate population → ℝ
  | none => baseline + spikeStrength
  | some _coordinate => baseline

/-- Normalized spectral moment of a finite diagonal design. -/
noncomputable def normalizedDiagonalSpectralMoment
    (population edges : ℕ)
    (diagonal : FiniteOutlierCoordinate population → ℝ) : ℝ :=
  (∑ coordinate, diagonal coordinate ^ edges) / (population + 1 : ℕ)

/-- Normalized empirical spectral average of an arbitrary fixed test
function. -/
noncomputable def normalizedDiagonalSpectralObservable
    (population : ℕ) (observable : ℝ → ℝ)
    (diagonal : FiniteOutlierCoordinate population → ℝ) : ℝ :=
  (∑ coordinate, observable (diagonal coordinate)) / (population + 1 : ℕ)

/-- The finite witness has exactly `p+1` spectral coordinates. -/
theorem finiteOutlierCoordinate_card (population : ℕ) :
    Fintype.card (FiniteOutlierCoordinate population) = population + 1 := by
  simp [FiniteOutlierCoordinate]

/-- The exact normalized-moment correction caused by the single outlier. -/
theorem normalizedDiagonalSpectralMoment_outlier_sub_bulk
    (baseline spikeStrength : ℝ) (population edges : ℕ) :
    normalizedDiagonalSpectralMoment population edges
        (finiteOutlierDiagonal baseline spikeStrength population) -
      normalizedDiagonalSpectralMoment population edges
        (finiteBulkDiagonal baseline population) =
      ((baseline + spikeStrength) ^ edges - baseline ^ edges) /
        (population + 1 : ℕ) := by
  simp [normalizedDiagonalSpectralMoment, finiteOutlierDiagonal,
    finiteBulkDiagonal]
  field_simp
  ring

/-- Every fixed normalized spectral moment misses the bounded rank-one
outlier asymptotically. -/
theorem normalizedDiagonalSpectralMoment_outlier_sub_bulk_tendsto_zero
    (baseline spikeStrength : ℝ) (edges : ℕ) :
    Filter.Tendsto
      (fun population ↦
        normalizedDiagonalSpectralMoment population edges
            (finiteOutlierDiagonal baseline spikeStrength population) -
          normalizedDiagonalSpectralMoment population edges
            (finiteBulkDiagonal baseline population))
      Filter.atTop (nhds 0) := by
  simpa only [normalizedDiagonalSpectralMoment_outlier_sub_bulk, Function.comp_def] using
    (tendsto_const_div_atTop_nhds_zero_nat
        ((baseline + spikeStrength) ^ edges - baseline ^ edges)).comp
      (Filter.tendsto_add_atTop_nat 1)

/-- The exact empirical-average correction for any fixed spectral test
function. -/
theorem normalizedDiagonalSpectralObservable_outlier_sub_bulk
    (baseline spikeStrength : ℝ) (population : ℕ) (observable : ℝ → ℝ) :
    normalizedDiagonalSpectralObservable population observable
        (finiteOutlierDiagonal baseline spikeStrength population) -
      normalizedDiagonalSpectralObservable population observable
        (finiteBulkDiagonal baseline population) =
      (observable (baseline + spikeStrength) - observable baseline) /
        (population + 1 : ℕ) := by
  simp [normalizedDiagonalSpectralObservable, finiteOutlierDiagonal,
    finiteBulkDiagonal]
  field_simp
  ring

/-- The single outlier is invisible to every fixed empirical spectral
observable, which directly expresses equality of the limiting bulk spectral
law rather than only equality of its moments. -/
theorem normalizedDiagonalSpectralObservable_outlier_sub_bulk_tendsto_zero
    (baseline spikeStrength : ℝ) (observable : ℝ → ℝ) :
    Filter.Tendsto
      (fun population ↦
        normalizedDiagonalSpectralObservable population observable
            (finiteOutlierDiagonal baseline spikeStrength population) -
          normalizedDiagonalSpectralObservable population observable
            (finiteBulkDiagonal baseline population))
      Filter.atTop (nhds 0) := by
  simpa only [normalizedDiagonalSpectralObservable_outlier_sub_bulk, Function.comp_def] using
    (tendsto_const_div_atTop_nhds_zero_nat
        (observable (baseline + spikeStrength) - observable baseline)).comp
      (Filter.tendsto_add_atTop_nat 1)

/-- A value is the maximum of a finite diagonal spectrum when it upper-bounds
every coordinate and is attained. -/
def IsDiagonalMaximum {Coordinate : Type*}
    (diagonal : Coordinate → ℝ) (maximum : ℝ) : Prop :=
  (∀ coordinate, diagonal coordinate ≤ maximum) ∧
    ∃ coordinate, diagonal coordinate = maximum

/-- The constant bulk spectrum has maximum equal to its baseline. -/
theorem finiteBulkDiagonal_hasMaximum (baseline : ℝ) (population : ℕ) :
    IsDiagonalMaximum (finiteBulkDiagonal baseline population) baseline := by
  exact ⟨fun _coordinate ↦ le_rfl,
    ⟨none, rfl⟩⟩

/-- A nonnegative outlier raises the exact spectral maximum by its full
strength, independently of its vanishing normalized mass. -/
theorem finiteOutlierDiagonal_hasMaximum
    (baseline spikeStrength : ℝ) (population : ℕ) (hspike : 0 ≤ spikeStrength) :
    IsDiagonalMaximum
      (finiteOutlierDiagonal baseline spikeStrength population)
      (baseline + spikeStrength) := by
  constructor
  · intro coordinate
    cases coordinate with
    | none => exact le_rfl
    | some coordinate =>
        simp only [finiteOutlierDiagonal]
        linarith
  · exact ⟨none, rfl⟩

/-- Feasible points of the trace-one positive-semidefinite matrix program. -/
def IsTraceOnePSDMatrix {Coordinate : Type*} [Fintype Coordinate]
    (matrix : Matrix Coordinate Coordinate ℝ) : Prop :=
  matrix.PosSemidef ∧ Matrix.trace matrix = 1

/-- Objective of the trace-one SDP with diagonal design spectrum. -/
noncomputable def diagonalTraceOneSDPObjective
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (diagonal : Coordinate → ℝ) (matrix : Matrix Coordinate Coordinate ℝ) : ℝ :=
  Matrix.trace (Matrix.diagonal diagonal * matrix)

/-- A number is the SDP optimum when it upper-bounds every feasible value and
is attained by one feasible matrix. -/
def IsDiagonalTraceOneSDPOptimum
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (diagonal : Coordinate → ℝ) (optimum : ℝ) : Prop :=
  (∀ matrix, IsTraceOnePSDMatrix matrix →
    diagonalTraceOneSDPObjective diagonal matrix ≤ optimum) ∧
  ∃ matrix, IsTraceOnePSDMatrix matrix ∧
    diagonalTraceOneSDPObjective diagonal matrix = optimum

/-- Every diagonal entry of a real positive-semidefinite matrix is
nonnegative. -/
theorem posSemidef_diagonalEntry_nonnegative
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {matrix : Matrix Coordinate Coordinate ℝ} (hmatrix : matrix.PosSemidef)
    (coordinate : Coordinate) :
    0 ≤ matrix coordinate coordinate := by
  simpa using hmatrix.2 (Pi.single coordinate 1)

/-- The diagonal SDP objective is the diagonal weighted sum. -/
theorem diagonalTraceOneSDPObjective_eq_sum
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (diagonal : Coordinate → ℝ) (matrix : Matrix Coordinate Coordinate ℝ) :
    diagonalTraceOneSDPObjective diagonal matrix =
      ∑ coordinate, diagonal coordinate * matrix coordinate coordinate := by
  unfold diagonalTraceOneSDPObjective
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

/-- **Exact trace-one SDP solution for a diagonal objective.**  The optimum is
the largest diagonal entry.  The upper bound uses PSD diagonal
nonnegativity and trace one; a rank-one diagonal projector attains it. -/
theorem diagonalTraceOneSDPOptimum_of_isDiagonalMaximum
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (diagonal : Coordinate → ℝ) (maximum : ℝ)
    (hmaximum : IsDiagonalMaximum diagonal maximum) :
    IsDiagonalTraceOneSDPOptimum diagonal maximum := by
  constructor
  · intro matrix hfeasible
    rw [diagonalTraceOneSDPObjective_eq_sum]
    calc
      (∑ coordinate, diagonal coordinate * matrix coordinate coordinate) ≤
          ∑ coordinate, maximum * matrix coordinate coordinate := by
        apply Finset.sum_le_sum
        intro coordinate _hcoordinate
        exact mul_le_mul_of_nonneg_right (hmaximum.1 coordinate)
          (posSemidef_diagonalEntry_nonnegative hfeasible.1 coordinate)
      _ = maximum * Matrix.trace matrix := by
        rw [Matrix.trace, Finset.mul_sum]
        rfl
      _ = maximum := by rw [hfeasible.2, mul_one]
  · obtain ⟨coordinate, hcoordinate⟩ := hmaximum.2
    let witness : Matrix Coordinate Coordinate ℝ :=
      Matrix.diagonal (Pi.single coordinate 1)
    refine ⟨witness, ?_, ?_⟩
    · constructor
      · apply Matrix.PosSemidef.diagonal
        intro index
        by_cases hindex : index = coordinate <;> simp [Pi.single_apply, hindex]
      · simp [witness, Matrix.trace]
    · simp [witness, diagonalTraceOneSDPObjective_eq_sum, Pi.single_apply,
        hcoordinate]

/-- The full finite/infinite separation contract for a bulk-invisible spectral
outlier and the trace-one SDP it changes. -/
def BulkSpectralLawExtremalSDPSeparation
    (baseline spikeStrength : ℝ) : Prop :=
    (∀ observable : ℝ → ℝ,
      Filter.Tendsto
        (fun population ↦
          normalizedDiagonalSpectralObservable population observable
              (finiteOutlierDiagonal baseline spikeStrength population) -
            normalizedDiagonalSpectralObservable population observable
              (finiteBulkDiagonal baseline population))
        Filter.atTop (nhds 0)) ∧
    ∀ population : ℕ,
      IsDiagonalMaximum (finiteBulkDiagonal baseline population) baseline ∧
      IsDiagonalMaximum (finiteOutlierDiagonal baseline spikeStrength population)
        (baseline + spikeStrength) ∧
      IsDiagonalTraceOneSDPOptimum (finiteBulkDiagonal baseline population) baseline ∧
      IsDiagonalTraceOneSDPOptimum
        (finiteOutlierDiagonal baseline spikeStrength population)
        (baseline + spikeStrength) ∧
      baseline < baseline + spikeStrength

/-- **Bulk spectral law does not determine extremal spectral or SDP data.**
The baseline and one-outlier sequences have asymptotically identical averages
for every fixed spectral test function.  Nevertheless, at every finite size,
their spectral maxima and trace-one PSD SDP optima differ by exactly the
positive spike strength. -/
theorem bulkSpectralLaw_invisible_extremalSpectrumAndSDP_visible
    (baseline spikeStrength : ℝ) (hspike : 0 < spikeStrength) :
    BulkSpectralLawExtremalSDPSeparation baseline spikeStrength := by
  rw [BulkSpectralLawExtremalSDPSeparation]
  refine ⟨normalizedDiagonalSpectralObservable_outlier_sub_bulk_tendsto_zero
      baseline spikeStrength, ?_⟩
  intro population
  have hbulk := finiteBulkDiagonal_hasMaximum baseline population
  have houtlier := finiteOutlierDiagonal_hasMaximum baseline spikeStrength population
    hspike.le
  exact ⟨hbulk, houtlier,
    diagonalTraceOneSDPOptimum_of_isDiagonalMaximum _ _ hbulk,
    diagonalTraceOneSDPOptimum_of_isDiagonalMaximum _ _ houtlier, by linarith⟩

end SpectralSDPSeparation

section PolynomialTraffic

/-- Two endpoint-label assignments have the same equality pattern exactly when
they induce the same partition of the endpoint slots.  This relation is the
precise combinatorial content of having the same directed multigraph shape. -/
def SameEqualityPattern {Slot Label : Type*}
    (left right : Slot → Label) : Prop :=
  ∀ first second, left first = left second ↔ right first = right second

/-- Every endpoint-label assignment establishes its own equality pattern. -/
theorem sameEqualityPattern_refl
    {Slot Label : Type*} (assignment : Slot → Label) :
    SameEqualityPattern assignment assignment := by
  intro first second
  rfl

/-- Equality-pattern equivalence is symmetric. -/
theorem sameEqualityPattern_symm
    {Slot Label : Type*} {left right : Slot → Label}
    (hpattern : SameEqualityPattern left right) :
    SameEqualityPattern right left := by
  intro first second
  exact (hpattern first second).symm

/-- Equality-pattern equivalence is transitive. -/
theorem sameEqualityPattern_trans
    {Slot Label : Type*} {left middle right : Slot → Label}
    (hleft : SameEqualityPattern left middle)
    (hright : SameEqualityPattern middle right) :
    SameEqualityPattern left right := by
  intro first second
  exact (hleft first second).trans (hright first second)

/-- The canonical orbit relation on endpoint-label assignments. -/
def sameEqualityPatternSetoid (Slot Label : Type*) : Setoid (Slot → Label) where
  r := SameEqualityPattern
  iseqv := ⟨sameEqualityPattern_refl, @sameEqualityPattern_symm Slot Label,
    @sameEqualityPattern_trans Slot Label⟩

/-- The canonical finite traffic-graph shape is the quotient of endpoint
assignments by equality pattern.  It records precisely a directed multigraph
with its ordered endpoint slots, and nothing about the particular labels. -/
def EqualityPattern (Slot Label : Type*) :=
  Quotient (sameEqualityPatternSetoid Slot Label)

noncomputable instance equalityPatternFintype
    (Slot Label : Type*) [Fintype Slot] [Fintype Label] :
    Fintype (EqualityPattern Slot Label) := by
  letI : DecidableEq (EqualityPattern Slot Label) := Classical.decEq _
  letI : DecidableEq Slot := Classical.decEq _
  exact Fintype.ofSurjective (Quotient.mk (sameEqualityPatternSetoid Slot Label))
    Quotient.mk_surjective

noncomputable instance equalityPatternDecidableEq
    (Slot Label : Type*) : DecidableEq (EqualityPattern Slot Label) :=
  Classical.decEq _

/-- Send an assignment to its canonical equality-pattern traffic shape. -/
def equalityPatternShape {Slot Label : Type*}
    (assignment : Slot → Label) : EqualityPattern Slot Label :=
  Quotient.mk (sameEqualityPatternSetoid Slot Label) assignment

/-- Equality of canonical traffic shapes is exactly equality of endpoint
partitions. -/
theorem equalityPatternShape_eq_iff
    {Slot Label : Type*} (left right : Slot → Label) :
    equalityPatternShape left = equalityPatternShape right ↔
      SameEqualityPattern left right := by
  exact Quotient.eq

/-- The occupied labels of two assignments with the same equality pattern are
equivalent: send the label at a slot on the left to the label at
the same slot on the right.  Choice only selects a representative slot; the
equality-pattern hypothesis proves the result independent of that choice. -/
noncomputable def equalityPatternRangeEquiv
    {Slot Label : Type*} (left right : Slot → Label)
    (hpattern : SameEqualityPattern left right) :
    Set.range left ≃ Set.range right where
  toFun value :=
    ⟨right (Classical.choose value.property),
      ⟨Classical.choose value.property, rfl⟩⟩
  invFun value :=
    ⟨left (Classical.choose value.property),
      ⟨Classical.choose value.property, rfl⟩⟩
  left_inv value := by
    apply Subtype.ext
    have hleft := Classical.choose_spec value.property
    have hright := Classical.choose_spec
      ((⟨right (Classical.choose value.property),
        ⟨Classical.choose value.property, rfl⟩⟩ : Set.range right).property)
    exact (hpattern _ _).mpr (hright.trans rfl) |>.trans hleft
  right_inv value := by
    apply Subtype.ext
    have hright := Classical.choose_spec value.property
    have hleft := Classical.choose_spec
      ((⟨left (Classical.choose value.property),
        ⟨Classical.choose value.property, rfl⟩⟩ : Set.range left).property)
    exact (hpattern _ _).mp (hleft.trans rfl) |>.trans hright

/-- On a finite label set, the equivalence between occupied labels extends to
a permutation of the entire label set.

Empirical status: NOT AN EMPIRICAL CLAIM. -/
noncomputable def equalityPatternPermutation
    {Slot Label : Type*} [Finite Label] (left right : Slot → Label)
    (hpattern : SameEqualityPattern left right) : Equiv.Perm Label := by
  classical
  exact Equiv.extendSubtype (equalityPatternRangeEquiv left right hpattern)

/-- The extended permutation sends every label used by the first monomial to
the corresponding label used by the second monomial. -/
theorem equalityPatternPermutation_apply
    {Slot Label : Type*} [Finite Label] (left right : Slot → Label)
    (hpattern : SameEqualityPattern left right) (slot : Slot) :
    equalityPatternPermutation left right hpattern (left slot) = right slot := by
  classical
  change Equiv.extendSubtype (equalityPatternRangeEquiv left right hpattern) (left slot) =
    right slot
  rw [Equiv.extendSubtype_apply_of_mem _ _ (Set.mem_range_self slot)]
  change right (Classical.choose (Set.mem_range_self slot)) = right slot
  apply (hpattern _ _).mp
  exact Classical.choose_spec (Set.mem_range_self slot)

/-- Permutation invariance forces coefficients to be constant on equality
patterns.  This discharges the representation-theoretic step that the raw
orbit-sum identity alone cannot prove. -/
theorem coefficient_eq_of_sameEqualityPattern
    {Slot Label : Type*} [Finite Label]
    (coefficient : (Slot → Label) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Label) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial)
    (left right : Slot → Label) (hpattern : SameEqualityPattern left right) :
    coefficient left = coefficient right := by
  let permutation := equalityPatternPermutation left right hpattern
  have hmap : permutation ∘ left = right := by
    funext slot
    exact equalityPatternPermutation_apply left right hpattern slot
  rw [← hmap, hinvariant]

/-- **Orbit sums are graph polynomials.**  `shape` records the equality pattern of the endpoint
indices of a monomial—equivalently its directed multigraph.  Once permutation invariance makes
the coefficient depend only on this shape, regrouping monomials gives an exact finite graph-sum
factorization.  The same statement covers rooted shapes by including the output slot in `Graph`. -/
theorem polynomial_orbitSum_factorization
    {Monomial Graph : Type*} [Fintype Monomial] [Fintype Graph] [DecidableEq Graph]
    (shape : Monomial → Graph) (coefficient : Graph → ℝ) (value : Monomial → ℝ) :
    (∑ monomial, coefficient (shape monomial) * value monomial) =
      ∑ graph, coefficient graph *
        ∑ monomial, if shape monomial = graph then value monomial else 0 := by
  classical
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro monomial _
  simp

/-- Coefficient assigned to an equality-pattern graph by choosing any monomial of that shape. -/
noncomputable def graphShapeCoefficient
    {Monomial Graph : Type*} (shape : Monomial → Graph) (coefficient : Monomial → ℝ)
    (graph : Graph) : ℝ := by
  classical
  exact if h : ∃ monomial, shape monomial = graph then
    coefficient (Classical.choose h) else 0

/-- Shape-invariant monomial coefficients factor through the graph shape. -/
theorem graphShapeCoefficient_comp_of_shapeInvariant
    {Monomial Graph : Type*} (shape : Monomial → Graph) (coefficient : Monomial → ℝ)
    (hinvariant : ∀ left right, shape left = shape right →
      coefficient left = coefficient right) (monomial : Monomial) :
    graphShapeCoefficient shape coefficient (shape monomial) = coefficient monomial := by
  let h : ∃ candidate, shape candidate = shape monomial := ⟨monomial, rfl⟩
  rw [graphShapeCoefficient, dif_pos h]
  exact hinvariant _ _ (Classical.choose_spec h)

/-- **Permutation-invariant polynomial factorization, after equality patterns are identified with
graphs.**  Invariance makes each monomial coefficient constant on its shape class; the resulting
polynomial is exactly a linear combination of the corresponding graph sums.  Taking `Graph` to
be rooted equality patterns gives the equivariant vector version without changing the proof. -/
theorem invariantPolynomial_graphSum_factorization_of_shapeInvariant
    {Monomial Graph : Type*} [Fintype Monomial] [Fintype Graph] [DecidableEq Graph]
    (shape : Monomial → Graph) (coefficient value : Monomial → ℝ)
    (hinvariant : ∀ left right, shape left = shape right →
      coefficient left = coefficient right) :
    (∑ monomial, coefficient monomial * value monomial) =
      ∑ graph, graphShapeCoefficient shape coefficient graph *
        ∑ monomial, if shape monomial = graph then value monomial else 0 := by
  calc
    (∑ monomial, coefficient monomial * value monomial) =
        ∑ monomial, graphShapeCoefficient shape coefficient (shape monomial) * value monomial := by
      apply Finset.sum_congr rfl
      intro monomial _
      rw [graphShapeCoefficient_comp_of_shapeInvariant shape coefficient hinvariant]
    _ = _ := polynomial_orbitSum_factorization shape
      (graphShapeCoefficient shape coefficient) value

/-- **Exact finite permutation-invariant polynomial/traffic factorization.**
Monomials are endpoint-label assignments.  If `shape` completely records their
equality pattern, permutation invariance of the polynomial coefficients implies
shape invariance, and the polynomial factors through the corresponding graph
sums.  Rooted equivariant polynomials use the same theorem after including the
distinguished output slot in `Slot`. -/
theorem invariantPolynomial_graphSum_factorization
    {Slot Label Graph : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    [Fintype Graph] [DecidableEq Graph]
    (shape : (Slot → Label) → Graph)
    (coefficient value : (Slot → Label) → ℝ)
    (hshape : ∀ left right, shape left = shape right →
      SameEqualityPattern left right)
    (hinvariant : ∀ (permutation : Equiv.Perm Label) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    (∑ monomial, coefficient monomial * value monomial) =
      ∑ graph, graphShapeCoefficient shape coefficient graph *
        ∑ monomial, if shape monomial = graph then value monomial else 0 := by
  apply invariantPolynomial_graphSum_factorization_of_shapeInvariant
  intro left right hsame
  exact coefficient_eq_of_sameEqualityPattern coefficient hinvariant left right
    (hshape left right hsame)

/-- The equality asserted by canonical finite traffic factorization. -/
noncomputable def CanonicalTrafficFactorizationStatement
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (coefficient value : (Slot → Label) → ℝ) : Prop :=
  (∑ monomial, coefficient monomial * value monomial) =
    ∑ graph : EqualityPattern Slot Label,
      graphShapeCoefficient equalityPatternShape coefficient graph *
        ∑ monomial,
          if equalityPatternShape monomial = graph then value monomial else 0

/-- The equality asserted by the rooted canonical finite traffic factorization. -/
noncomputable def RootedCanonicalTrafficFactorizationStatement
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (coefficient value : (Option Slot → Label) → ℝ) : Prop :=
  (∑ monomial, coefficient monomial * value monomial) =
    ∑ graph : EqualityPattern (Option Slot) Label,
      graphShapeCoefficient equalityPatternShape coefficient graph *
        ∑ monomial,
          if equalityPatternShape monomial = graph then value monomial else 0

/-- **Canonical invariant-polynomial/traffic factorization.**  The graph index
is now the actual quotient by endpoint equality pattern, so no external shape
map or shape-completeness hypothesis remains.  Permutation invariance of the
formal monomial coefficients alone yields exact finite factorization. -/
theorem invariantPolynomial_canonicalTraffic_factorization
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (coefficient value : (Slot → Label) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Label) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    CanonicalTrafficFactorizationStatement coefficient value := by
  apply invariantPolynomial_graphSum_factorization equalityPatternShape
    coefficient value
  · intro left right hshape
    exact (equalityPatternShape_eq_iff left right).mp hshape
  · exact hinvariant

/-- **Canonical rooted factorization.**  `none` is the distinguished output
slot and `some slot` are matrix-entry endpoint slots.  Hence this is the exact
finite rooted-traffic form used for permutation-equivariant vector outputs. -/
theorem rootedInvariantPolynomial_canonicalTraffic_factorization
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (coefficient value : (Option Slot → Label) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Label) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    RootedCanonicalTrafficFactorizationStatement coefficient value :=
  invariantPolynomial_canonicalTraffic_factorization coefficient value hinvariant

/-- The exact scalar degree-bounded traffic factorization statement.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
noncomputable def DegreeAtMostTrafficFactorizationStatement
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ)) : Prop :=
  (∑ degree : Fin (D + 1),
    ∑ monomial, coefficient degree monomial * value degree monomial) =
    ∑ degree : Fin (D + 1),
      ∑ graph : EqualityPattern (Fin (degree : ℕ) × Bool) Label,
        graphShapeCoefficient equalityPatternShape (coefficient degree) graph *
          ∑ monomial,
            if equalityPatternShape monomial = graph then value degree monomial else 0

/-- The exact rooted degree-bounded traffic factorization statement.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
noncomputable def DegreeAtMostRootedTrafficFactorizationStatement
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ)) : Prop :=
  (∑ degree : Fin (D + 1),
    ∑ monomial, coefficient degree monomial * value degree monomial) =
    ∑ degree : Fin (D + 1),
      ∑ graph : EqualityPattern (Option (Fin (degree : ℕ) × Bool)) Label,
        graphShapeCoefficient equalityPatternShape (coefficient degree) graph *
          ∑ monomial,
            if equalityPatternShape monomial = graph then value degree monomial else 0

/-- **Exact degree-at-most-`D` traffic factorization.**  The homogeneous
degree `d` component uses endpoint slots `Fin d × Bool`, namely the ordered
tail and head of each of its `d` matrix-entry factors.  Summing over
`d : Fin (D + 1)` therefore proves factorization through canonical traffic
graphs with at most `D` edges, rather than leaving the edge bound implicit. -/
theorem degreeAtMostInvariantPolynomial_canonicalTraffic_factorization
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial) :
    DegreeAtMostTrafficFactorizationStatement coefficient value := by
  apply Finset.sum_congr rfl
  intro degree _hdegree
  exact invariantPolynomial_canonicalTraffic_factorization
    (coefficient degree) (value degree) (hinvariant degree)

/-- **Rooted degree-at-most-`D` factorization.**  Adding one `Option` slot to
each degree-`d` endpoint family marks the output coordinate, so the same exact
edge bound holds for permutation-equivariant vector-polynomial coordinates. -/
theorem degreeAtMostRootedInvariantPolynomial_canonicalTraffic_factorization
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial) :
    DegreeAtMostRootedTrafficFactorizationStatement coefficient value := by
  apply Finset.sum_congr rfl
  intro degree _hdegree
  exact rootedInvariantPolynomial_canonicalTraffic_factorization
    (coefficient degree) (value degree) (hinvariant degree)

/-- The complete canonical traffic profile seen by scalar polynomials of total
degree at most `D`.  At homogeneous degree `d`, it stores every graph sum on
the equality-pattern quotient of the `2d` ordered matrix endpoints.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
def DegreeAtMostCanonicalTrafficProfile (D : ℕ) (Label : Type*) :=
  (degree : Fin (D + 1)) →
    EqualityPattern (Fin (degree : ℕ) × Bool) Label → ℝ

/-- The equality-pattern sum common to scalar and rooted traffic profiles. -/
noncomputable def equalityPatternProfile
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (value : (Slot → Label) → ℝ) (graph : EqualityPattern Slot Label) : ℝ :=
  ∑ monomial,
    if equalityPatternShape monomial = graph then value monomial else 0

/-- Evaluate the canonical degree-limited traffic profile of a family of
monomial values.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
noncomputable def degreeAtMostCanonicalTrafficProfile
    {D : ℕ} {Label : Type*} [Fintype Label]
    (value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ)) :
    DegreeAtMostCanonicalTrafficProfile D Label :=
  fun degree graph ↦ equalityPatternProfile (value degree) graph

/-- The rooted profile seen by degree-limited equivariant vector-polynomial
coordinates.  The additional `Option` slot marks the output label.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
def DegreeAtMostRootedCanonicalTrafficProfile (D : ℕ) (Label : Type*) :=
  (degree : Fin (D + 1)) →
    EqualityPattern (Option (Fin (degree : ℕ) × Bool)) Label → ℝ

/-- Evaluate the rooted canonical traffic profile of a family of rooted
monomial values.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
noncomputable def degreeAtMostRootedCanonicalTrafficProfile
    {D : ℕ} {Label : Type*} [Fintype Label]
    (value : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ)) :
    DegreeAtMostRootedCanonicalTrafficProfile D Label :=
  fun degree graph ↦ equalityPatternProfile (value degree) graph

/-- Scalar and rooted degree-limited profiles are the two endpoint-slot
specializations of the same equality-pattern sum. -/
theorem degreeAtMostTrafficProfiles_are_equalityPatternProfiles
    {D : ℕ} {Label : Type*} [Fintype Label]
    (value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (rootedValue : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ)) :
    (∀ degree graph,
      degreeAtMostCanonicalTrafficProfile value degree graph =
        equalityPatternProfile (value degree) graph) ∧
    (∀ degree graph,
      degreeAtMostRootedCanonicalTrafficProfile rootedValue degree graph =
        equalityPatternProfile (rootedValue degree) graph) := by
  exact ⟨fun _degree _graph ↦ rfl, fun _degree _graph ↦ rfl⟩

/-- The scalar factorization theorem expressed as literal factorization
through the canonical profile map. -/
theorem degreeAtMostInvariantPolynomial_factorsThroughCanonicalTrafficProfile
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial) :
    (∑ degree : Fin (D + 1),
      ∑ monomial, coefficient degree monomial * value degree monomial) =
      ∑ degree : Fin (D + 1),
        ∑ graph : EqualityPattern (Fin (degree : ℕ) × Bool) Label,
          graphShapeCoefficient equalityPatternShape (coefficient degree) graph *
            degreeAtMostCanonicalTrafficProfile value degree graph := by
  simpa only [degreeAtMostCanonicalTrafficProfile, equalityPatternProfile] using
    degreeAtMostInvariantPolynomial_canonicalTraffic_factorization
      coefficient value hinvariant

/-- Equal canonical traffic profiles make every invariant scalar polynomial
of degree at most `D` exactly equal.  This is the finite algorithmic
indistinguishability statement, not only an expansion formula. -/
theorem degreeAtMostInvariantPolynomial_eq_of_canonicalTrafficProfile_eq
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial)
    (htraffic : degreeAtMostCanonicalTrafficProfile leftValue =
      degreeAtMostCanonicalTrafficProfile rightValue) :
    (∑ degree : Fin (D + 1),
      ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
      ∑ degree : Fin (D + 1),
        ∑ monomial, coefficient degree monomial * rightValue degree monomial := by
  rw [degreeAtMostInvariantPolynomial_factorsThroughCanonicalTrafficProfile
      coefficient leftValue hinvariant,
    degreeAtMostInvariantPolynomial_factorsThroughCanonicalTrafficProfile
      coefficient rightValue hinvariant,
    htraffic]

/-- Equal rooted profiles likewise make every rooted equivariant-polynomial
coordinate of degree at most `D` exactly equal. -/
theorem degreeAtMostRootedInvariantPolynomial_eq_of_canonicalTrafficProfile_eq
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial)
    (htraffic : degreeAtMostRootedCanonicalTrafficProfile leftValue =
      degreeAtMostRootedCanonicalTrafficProfile rightValue) :
    (∑ degree : Fin (D + 1),
      ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
      ∑ degree : Fin (D + 1),
        ∑ monomial, coefficient degree monomial * rightValue degree monomial := by
  have hleft := degreeAtMostRootedInvariantPolynomial_canonicalTraffic_factorization
    coefficient leftValue hinvariant
  have hright := degreeAtMostRootedInvariantPolynomial_canonicalTraffic_factorization
    coefficient rightValue hinvariant
  rw [hleft, hright]
  apply Finset.sum_congr rfl
  intro degree _hdegree
  apply Finset.sum_congr rfl
  intro graph _hgraph
  have hcomponent := congrFun (congrFun htraffic degree) graph
  dsimp only [degreeAtMostRootedCanonicalTrafficProfile] at hcomponent
  simp only [equalityPatternProfile] at hcomponent
  rw [hcomponent]

/-- **Direct fixed-degree invariant-separation hardness theorem.**  A single
pair of equal canonical traffic profiles equalizes the risk of every uniform
permutation-invariant degree-`D` polynomial procedure.  If the right Bayes risk
is optimal there, the entire Bayes gap lower-bounds every procedure's excess
risk on the left, with no factor loss and no prepackaged risk-factorization
assumption. -/
theorem degreeAtMostInvariantPolynomial_hardness_of_canonicalTrafficProfile_eq
    {Algorithm : Type*} {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient : Algorithm → (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (leftValue rightValue : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (hinvariant : ∀ algorithm degree (permutation : Equiv.Perm Label) monomial,
      coefficient algorithm degree (permutation ∘ monomial) =
        coefficient algorithm degree monomial)
    (htraffic : degreeAtMostCanonicalTrafficProfile leftValue =
      degreeAtMostCanonicalTrafficProfile rightValue)
    (bayesLeft bayesRight : ℝ)
    (hoptimalRight : ∀ algorithm,
      bayesRight ≤ ∑ degree : Fin (D + 1),
        ∑ monomial,
          coefficient algorithm degree monomial * rightValue degree monomial)
    (algorithm : Algorithm) :
    bayesRight - bayesLeft ≤
      (∑ degree : Fin (D + 1),
        ∑ monomial,
          coefficient algorithm degree monomial * leftValue degree monomial) -
        bayesLeft := by
  apply suboptimal_of_invariant_separation
    (fun candidate ↦ ∑ degree : Fin (D + 1),
      ∑ monomial,
        coefficient candidate degree monomial * leftValue degree monomial)
    (fun candidate ↦ ∑ degree : Fin (D + 1),
      ∑ monomial,
        coefficient candidate degree monomial * rightValue degree monomial)
    bayesLeft bayesRight
  · intro candidate
    exact degreeAtMostInvariantPolynomial_eq_of_canonicalTrafficProfile_eq
      (coefficient candidate) leftValue rightValue (hinvariant candidate) htraffic
  · exact hoptimalRight

/-- A scalar risk that has access only to traffic coordinates with at most `D` edges. -/
structure TruncatedTrafficRisk (D : ℕ) where
  coefficient : Fin (D + 1) → ℝ

/-- Evaluation of a truncated-traffic risk functional.

Convention: `D` is polynomial/edge degree, not the population-genetic
linkage-disequilibrium coefficient traditionally also denoted `D`. -/
noncomputable def TruncatedTrafficRisk.evaluate
    {D : ℕ} (risk : TruncatedTrafficRisk D) (traffic : Fin (D + 1) → ℝ) : ℝ :=
  ∑ graph, risk.coefficient graph * traffic graph

/-- **The total-traffic functional**: unit weight on every retained graph
coordinate.

`TruncatedTrafficRisk` had no exhibited inhabitant, so the stability bound below
was stated over an empty-for-all-we-knew class. This member also fixes the
orientation of the bound: its coefficient `ℓ¹` mass is the number of retained
coordinates, so the bound reads "degree controls the number of coordinates, and
therefore the amplification" on a functional where that is visible.

Convention: `D` is polynomial/edge degree, not the population-genetic
linkage-disequilibrium coefficient traditionally also denoted `D`. The two differ
by ploidy and nothing here is about haplotype frequencies; the same note is
carried by `TruncatedTrafficRisk.evaluate` above, and it is repeated rather than
cross-referenced because this definition takes the argument on its own. -/
def TruncatedTrafficRisk.totalTraffic (D : ℕ) : TruncatedTrafficRisk D where
  coefficient := fun _graph ↦ 1

instance TruncatedTrafficRisk.instNonempty (D : ℕ) :
    Nonempty (TruncatedTrafficRisk D) :=
  ⟨TruncatedTrafficRisk.totalTraffic D⟩

/-- The total-traffic functional evaluates to the traffic sum, which is what
makes it the one whose amplification is exactly the coordinate count. -/
theorem TruncatedTrafficRisk.evaluate_totalTraffic {D : ℕ}
    (traffic : Fin (D + 1) → ℝ) :
    (TruncatedTrafficRisk.totalTraffic D).evaluate traffic = ∑ graph, traffic graph := by
  unfold TruncatedTrafficRisk.evaluate TruncatedTrafficRisk.totalTraffic
  simp

/-- **Quantitative finite-traffic stability.**  If every retained graph
coordinate changes by at most `epsilon`, the value of a graph polynomial
changes by at most `epsilon` times the coefficient `ℓ¹` mass.  This is the
missing hypothesis when exact finite factorization is passed to a limiting
traffic statement: fixed degree controls the number of coordinates, but not
the size-dependent coefficients multiplying them. -/
theorem truncatedTrafficRisk_abs_sub_le_coefficientMass_mul
    {D : ℕ} (risk : TruncatedTrafficRisk D)
    (left right : Fin (D + 1) → ℝ) (epsilon : ℝ)
    (hcoordinate : ∀ graph, |left graph - right graph| ≤ epsilon) :
    |risk.evaluate left - risk.evaluate right| ≤
      (∑ graph, |risk.coefficient graph|) * epsilon := by
  rw [TruncatedTrafficRisk.evaluate, TruncatedTrafficRisk.evaluate,
    ← Finset.sum_sub_distrib]
  calc
    |∑ graph, (risk.coefficient graph * left graph -
        risk.coefficient graph * right graph)| =
        |∑ graph, risk.coefficient graph * (left graph - right graph)| := by
          congr 1
          apply Finset.sum_congr rfl
          intro graph _hgraph
          ring
    _ ≤ ∑ graph, |risk.coefficient graph * (left graph - right graph)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ graph, |risk.coefficient graph| * |left graph - right graph| := by
      apply Finset.sum_congr rfl
      intro graph _hgraph
      rw [abs_mul]
    _ ≤ ∑ graph, |risk.coefficient graph| * epsilon := by
      apply Finset.sum_le_sum
      intro graph _hgraph
      exact mul_le_mul_of_nonneg_left (hcoordinate graph) (abs_nonneg _)
    _ = (∑ graph, |risk.coefficient graph|) * epsilon := by
      rw [Finset.sum_mul]

/-- A uniform coefficient-mass bound converts quantitative convergence of a
fixed truncated traffic profile into convergence of every stable polynomial
evaluation. -/
theorem truncatedTrafficRisk_tendsto_zero_of_boundedCoefficientMass
    {D : ℕ} (risk : ℕ → TruncatedTrafficRisk D)
    (left right : ℕ → Fin (D + 1) → ℝ)
    (discrepancy coefficientBound : ℝ)
    (hdiscrepancy : ∀ index graph,
      |left index graph - right index graph| ≤
        discrepancy * (1 / 2 : ℝ) ^ index)
    (hcoefficient : ∀ index,
      (∑ graph, |(risk index).coefficient graph|) ≤ coefficientBound)
    (hdiscrepancyNonneg : 0 ≤ discrepancy) :
    Filter.Tendsto
      (fun index ↦ (risk index).evaluate (left index) -
        (risk index).evaluate (right index))
      Filter.atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero (fun index ↦ abs_nonneg _)
  · intro index
    calc
      |(risk index).evaluate (left index) -
          (risk index).evaluate (right index)| ≤
          (∑ graph, |(risk index).coefficient graph|) *
            (discrepancy * (1 / 2 : ℝ) ^ index) :=
        truncatedTrafficRisk_abs_sub_le_coefficientMass_mul
          (risk index) (left index) (right index)
          (discrepancy * (1 / 2 : ℝ) ^ index) (hdiscrepancy index)
      _ ≤ coefficientBound * (discrepancy * (1 / 2 : ℝ) ^ index) := by
        exact mul_le_mul_of_nonneg_right (hcoefficient index)
          (mul_nonneg hdiscrepancyNonneg (by positivity))
  · have hpow : Filter.Tendsto (fun index : ℕ ↦ (1 / 2 : ℝ) ^ index)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
    simpa [mul_assoc] using
      hpow.const_mul (coefficientBound * discrepancy)

/-! ### Certified high-temperature passage from traffic to pressure -/

/-- **High-temperature traffic sufficiency from an absolutely convergent
truncation certificate.**  Suppose both limiting pressures are approximated
by the same depth-`D` traffic polynomial and both tails obey the uniform
polymer bound `C q^(D+1)/(1-q)` with `0 ≤ q < 1`.  Then the two limiting
pressures are equal.

This theorem formalizes the analytic passage after a cluster expansion has
supplied its certificate.  It deliberately does not assert that a biological
posterior satisfies a Dobrushin or polymer condition; that model-specific
step remains an explicit hypothesis rather than an imported axiom. -/
theorem highTemperatureTrafficLimit_eq_of_geometricTruncation
    (leftLimit rightLimit C q : ℝ) (commonTruncation : ℕ → ℝ)
    (hqNonneg : 0 ≤ q) (hq : q < 1)
    (hleft : ∀ depth,
      |leftLimit - commonTruncation depth| ≤
        C * q ^ (depth + 1) / (1 - q))
    (hright : ∀ depth,
      |rightLimit - commonTruncation depth| ≤
        C * q ^ (depth + 1) / (1 - q)) :
    leftLimit = rightLimit := by
  have hbound : ∀ depth,
      |leftLimit - rightLimit| ≤
        2 * (C * q ^ (depth + 1) / (1 - q)) := by
    intro depth
    have htriangle : |leftLimit - rightLimit| ≤
        |leftLimit - commonTruncation depth| +
          |rightLimit - commonTruncation depth| := by
      have h := abs_sub_le leftLimit (commonTruncation depth) rightLimit
      rwa [abs_sub_comm (commonTruncation depth) rightLimit] at h
    linarith [hleft depth, hright depth]
  have hqAbs : |q| < 1 := by
    rw [abs_of_nonneg hqNonneg]
    exact hq
  have hpow : Filter.Tendsto (fun depth : ℕ ↦ q ^ depth)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hqAbs
  have htail : Filter.Tendsto
      (fun depth : ℕ ↦ 2 * (C * q ^ (depth + 1) / (1 - q)))
      Filter.atTop (nhds 0) := by
    convert hpow.const_mul (2 * C * q / (1 - q)) using 1
    · funext depth
      rw [pow_succ]
      ring
    · simp
  have hconstant : Filter.Tendsto (fun _depth : ℕ ↦ |leftLimit - rightLimit|)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun _depth ↦ abs_nonneg _) hbound htail
  have hzero : |leftLimit - rightLimit| = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstant
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- Equal traffic through degree `D` makes every degree-`D` graph-polynomial risk identical. -/
theorem truncatedTrafficRisk_eq_of_profile_eq
    {D : ℕ} (risk : TruncatedTrafficRisk D) (left right : Fin (D + 1) → ℝ)
    (htraffic : left = right) :
    risk.evaluate left = risk.evaluate right := by
  rw [htraffic]

/-- The invariant-separation lower bound specialized to any class whose risks factor through one
truncated traffic profile. -/
theorem truncatedTraffic_hardness
    {Algorithm : Type*} {D : ℕ} (risk : Algorithm → TruncatedTrafficRisk D)
    (left right : Fin (D + 1) → ℝ) (htraffic : left = right)
    (bayesLeft bayesRight : ℝ)
    (hoptimalRight : ∀ algorithm, bayesRight ≤ (risk algorithm).evaluate right)
    (algorithm : Algorithm) :
    bayesRight - bayesLeft ≤ (risk algorithm).evaluate left - bayesLeft := by
  apply suboptimal_of_invariant_separation
    (fun candidate ↦ (risk candidate).evaluate left)
    (fun candidate ↦ (risk candidate).evaluate right)
    bayesLeft bayesRight
  · intro candidate
    exact truncatedTrafficRisk_eq_of_profile_eq (risk candidate) left right htraffic
  · exact hoptimalRight

/-! ### Strictness of every truncated moment/traffic level -/

/-- `D + 2` distinct positive nodes in `[1,2]`.  They support a signed
annihilator of moments through degree `D`.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def momentSeparationNode (D : ℕ) (index : Fin (D + 2)) : ℝ :=
  1 + (index : ℝ) / (D + 1 : ℝ)

/-- The node divisor is `D + 1` for `D : ℕ`, which is at least one, so this quotient has no
junk point.  Recorded here rather than left for the scanner to re-derive each run. -/
theorem momentSeparationNode_divisor_ne_zero (D : ℕ) : ((D : ℝ) + 1) ≠ 0 := by
  positivity


/-- Rectangular Vandermonde map taking weights on `D + 2` nodes to moments of
degrees `0,…,D`.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def truncatedMomentMap (D : ℕ) :
    (Fin (D + 2) → ℝ) →ₗ[ℝ] (Fin (D + 1) → ℝ) :=
  (Matrix.rectVandermonde (momentSeparationNode D) (fun _ ↦ 1) (D + 1)).vecMulLinear

/-- The moment-separation nodes are injectively indexed. -/
theorem momentSeparationNode_injective (D : ℕ) :
    Function.Injective (momentSeparationNode D) := by
  intro left right heq
  have hden : (D + 1 : ℝ) ≠ 0 := by positivity
  have hfrac : (left : ℝ) / (D + 1 : ℝ) =
      (right : ℝ) / (D + 1 : ℝ) := by
    unfold momentSeparationNode at heq
    linarith
  have hcast : (left : ℝ) = (right : ℝ) := (div_left_inj' hden).mp hfrac
  apply Fin.ext
  exact_mod_cast hcast

/-- Every node lies in the uniformly well-conditioned interval `[1,2]`. -/
theorem momentSeparationNode_mem_Icc (D : ℕ) (index : Fin (D + 2)) :
    momentSeparationNode D index ∈ Set.Icc (1 : ℝ) 2 := by
  have hden : (0 : ℝ) < D + 1 := by positivity
  have hindex0 : (0 : ℝ) ≤ index := by positivity
  have hindex1 : (index : ℝ) ≤ D + 1 := by
    exact_mod_cast Nat.le_of_lt_succ index.isLt
  constructor
  · unfold momentSeparationNode
    have hfrac0 : (0 : ℝ) ≤ (index : ℝ) / (D + 1 : ℝ) :=
      div_nonneg hindex0 hden.le
    linarith
  · unfold momentSeparationNode
    have := (div_le_one hden).2 hindex1
    linarith

/-- **Every truncated moment hierarchy has a nontrivial next-order
direction.**  For every `D` there is a nonzero signed weight vector whose
moments of degrees `0,…,D` vanish but whose degree-`D+1` moment is nonzero.

The existence is dimension-theoretic (`D+2` weights and `D+1` constraints).
The final nonvanishing is not assumed: if it also vanished, invertibility of
the square Vandermonde matrix on the distinct nodes would force the weight
vector to be zero. -/
theorem exists_truncatedMoment_annihilator (D : ℕ) :
    ∃ weight : Fin (D + 2) → ℝ,
      weight ≠ 0 ∧
        (∀ degree : Fin (D + 1),
          ∑ index : Fin (D + 2),
            weight index * momentSeparationNode D index ^ (degree : ℕ) = 0) ∧
        ∑ index : Fin (D + 2),
          weight index * momentSeparationNode D index ^ (D + 1) ≠ 0 := by
  have hdim :
      Module.finrank ℝ (Fin (D + 1) → ℝ) <
        Module.finrank ℝ (Fin (D + 2) → ℝ) := by
    simp
  have hker : LinearMap.ker (truncatedMomentMap D) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨weight, hweightKernel, hweightNe⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hmapZero : truncatedMomentMap D weight = 0 :=
    LinearMap.mem_ker.mp hweightKernel
  have hlow : ∀ degree : Fin (D + 1),
      ∑ index : Fin (D + 2),
        weight index * momentSeparationNode D index ^ (degree : ℕ) = 0 := by
    intro degree
    have hcoordinate := congrFun hmapZero degree
    simpa [truncatedMomentMap, Matrix.vecMul, dotProduct,
      Matrix.rectVandermonde_apply] using hcoordinate
  refine ⟨weight, hweightNe, hlow, ?_⟩
  intro hhigh
  apply hweightNe
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (momentSeparationNode_injective D)
  intro degree
  refine Fin.lastCases ?_ (fun lowDegree ↦ ?_) degree
  · simpa using hhigh
  · simpa using hlow lowDegree

/-- Uniform reference mass on the `D + 2` nodes.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def momentUniformWeight (D : ℕ) : ℝ :=
  1 / (D + 2 : ℝ)

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem momentUniformWeight_at_reference_point :
    momentUniformWeight 1 = 1 / 3 := by
  norm_num [momentUniformWeight]



/-- A strictly positive scale small enough that perturbing the uniform law by
any signed weight vector preserves positivity coordinatewise.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def momentPerturbationScale
    (D : ℕ) (weight : Fin (D + 2) → ℝ) : ℝ :=
  1 / ((D + 2 : ℝ) * (1 + ∑ index, |weight index|))

/-- The perturbed member of the moment-matched pair.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def perturbedMomentWeight
    (D : ℕ) (weight : Fin (D + 2) → ℝ) (index : Fin (D + 2)) : ℝ :=
  momentUniformWeight D + momentPerturbationScale D weight * weight index

/-- The reference member of the moment-matched pair.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def referenceMomentWeight
    (D : ℕ) (_index : Fin (D + 2)) : ℝ :=
  momentUniformWeight D

theorem momentPerturbationScale_pos
    (D : ℕ) (weight : Fin (D + 2) → ℝ) :
    0 < momentPerturbationScale D weight := by
  unfold momentPerturbationScale
  positivity

/-- The perturbation at any coordinate is strictly smaller than the uniform
mass at that coordinate. -/
theorem momentPerturbation_abs_lt_uniform
    (D : ℕ) (weight : Fin (D + 2) → ℝ) (index : Fin (D + 2)) :
    momentPerturbationScale D weight * |weight index| < momentUniformWeight D := by
  have hcard : (0 : ℝ) < D + 2 := by positivity
  have hsum0 : (0 : ℝ) ≤ ∑ candidate, |weight candidate| := by positivity
  have hsumPos : (0 : ℝ) < 1 + ∑ candidate, |weight candidate| := by linarith
  have hsingle : |weight index| ≤ ∑ candidate, |weight candidate| := by
    exact Finset.single_le_sum (fun candidate _ ↦ abs_nonneg (weight candidate))
      (Finset.mem_univ index)
  have hstrict : |weight index| < 1 + ∑ candidate, |weight candidate| := by
    linarith
  unfold momentPerturbationScale momentUniformWeight
  calc
    1 / ((D + 2 : ℝ) * (1 + ∑ candidate, |weight candidate|)) * |weight index| =
        |weight index| / ((D + 2 : ℝ) *
          (1 + ∑ candidate, |weight candidate|)) := by ring
    _ < (1 + ∑ candidate, |weight candidate|) /
        ((D + 2 : ℝ) * (1 + ∑ candidate, |weight candidate|)) :=
      div_lt_div_of_pos_right hstrict (mul_pos hcard hsumPos)
    _ = 1 / (D + 2 : ℝ) := by field_simp

/-- The perturbed weights are strictly positive, hence nonnegative. -/
theorem perturbedMomentWeight_pos
    (D : ℕ) (weight : Fin (D + 2) → ℝ) (index : Fin (D + 2)) :
    0 < perturbedMomentWeight D weight index := by
  have hscale := momentPerturbationScale_pos D weight
  have hsmall := momentPerturbation_abs_lt_uniform D weight index
  have hlower : -|weight index| ≤ weight index := neg_abs_le (weight index)
  have hscaled :
      -(momentPerturbationScale D weight * |weight index|) ≤
        momentPerturbationScale D weight * weight index := by
    nlinarith
  unfold perturbedMomentWeight
  linarith

/-- The reference weights sum to one. -/
theorem referenceMomentWeight_sum_one (D : ℕ) :
    ∑ index : Fin (D + 2), referenceMomentWeight D index = 1 := by
  simp [referenceMomentWeight, momentUniformWeight]
  field_simp

/-- A zero-total-mass signed direction preserves normalization. -/
theorem perturbedMomentWeight_sum_one
    (D : ℕ) (weight : Fin (D + 2) → ℝ)
    (hzero : ∑ index, weight index = 0) :
    ∑ index, perturbedMomentWeight D weight index = 1 := by
  simp_rw [perturbedMomentWeight]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, mul_zero, add_zero]
  exact referenceMomentWeight_sum_one D

/-- Vanishing of a signed moment makes the two probability laws agree at that
degree. -/
theorem perturbedMoment_eq_referenceMoment
    (D degree : ℕ) (weight : Fin (D + 2) → ℝ)
    (hvanish : ∑ index,
      weight index * momentSeparationNode D index ^ degree = 0) :
    (∑ index, perturbedMomentWeight D weight index *
        momentSeparationNode D index ^ degree) =
      ∑ index, referenceMomentWeight D index *
        momentSeparationNode D index ^ degree := by
  simp_rw [perturbedMomentWeight, referenceMomentWeight, add_mul]
  rw [Finset.sum_add_distrib]
  have hscaled :
      (∑ index : Fin (D + 2),
        momentPerturbationScale D weight * weight index *
          momentSeparationNode D index ^ degree) = 0 := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    simpa [mul_assoc] using congrArg (momentPerturbationScale D weight * ·) hvanish
  rw [hscaled, add_zero]

/-- A nonzero signed moment remains different after the positive
normalization. -/
theorem perturbedMoment_ne_referenceMoment
    (D degree : ℕ) (weight : Fin (D + 2) → ℝ)
    (hnonzero : ∑ index,
      weight index * momentSeparationNode D index ^ degree ≠ 0) :
    (∑ index, perturbedMomentWeight D weight index *
        momentSeparationNode D index ^ degree) ≠
      ∑ index, referenceMomentWeight D index *
        momentSeparationNode D index ^ degree := by
  intro hequal
  have hscaleNe : momentPerturbationScale D weight ≠ 0 :=
    ne_of_gt (momentPerturbationScale_pos D weight)
  have hscaled : momentPerturbationScale D weight *
      (∑ index, weight index * momentSeparationNode D index ^ degree) = 0 := by
    have hdifference := sub_eq_zero.mpr hequal
    simpa [perturbedMomentWeight, referenceMomentWeight, add_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] using hdifference
  exact hnonzero ((mul_eq_zero.mp hscaled).resolve_left hscaleNe)

/-- The diagonal traffic profile through `D` edges generated by a finite
spectral probability law.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
noncomputable def finiteDiagonalTrafficProfile
    (D : ℕ) (weight : Fin (D + 2) → ℝ) : Fin (D + 1) → ℝ :=
  fun degree ↦ ∑ index,
    weight index * momentSeparationNode D index ^ (degree : ℕ)

/-- Its first coordinate beyond the truncation.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
noncomputable def finiteDiagonalNextTrafficCoordinate
    (D : ℕ) (weight : Fin (D + 2) → ℝ) : ℝ :=
  ∑ index, weight index * momentSeparationNode D index ^ (D + 1)

/-- The complete finite probability-pair contract used by strictness of the
diagonal traffic hierarchy.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
def IsMomentMatchedProbabilityPair
    (D : ℕ) (left right : Fin (D + 2) → ℝ) : Prop :=
  (∀ index, momentSeparationNode D index ∈ Set.Icc (1 : ℝ) 2) ∧
    (∀ index, 0 ≤ left index) ∧
    (∀ index, 0 ≤ right index) ∧
    (∑ index, left index = 1) ∧
    (∑ index, right index = 1) ∧
    finiteDiagonalTrafficProfile D left = finiteDiagonalTrafficProfile D right

/-- The next diagonal coordinate distinguishes a moment-matched pair.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
def SeparatesAtNextDiagonalTraffic
    (D : ℕ) (left right : Fin (D + 2) → ℝ) : Prop :=
  finiteDiagonalNextTrafficCoordinate D left ≠
    finiteDiagonalNextTrafficCoordinate D right

/-- One pair is simultaneously invisible to every truncated traffic risk and
visible at the next traffic coordinate.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
def IsBlindPairForEveryTruncatedTrafficRisk
    (D : ℕ) (left right : Fin (D + 2) → ℝ) : Prop :=
  IsMomentMatchedProbabilityPair D left right ∧
    (∀ risk : TruncatedTrafficRisk D,
      risk.evaluate (finiteDiagonalTrafficProfile D left) =
        risk.evaluate (finiteDiagonalTrafficProfile D right)) ∧
    SeparatesAtNextDiagonalTraffic D left right

/-- **Strictness of the truncated traffic hierarchy at every degree.**  There
are two probability laws supported on `D + 2` points in `[1,2]` whose moments
agree through degree `D` and differ at degree `D+1`.  For diagonal covariance
sequences these moments are exactly the connected traffic coordinates indexed
by edge count. -/
theorem exists_probabilityWeights_matchingMoments_through_degree (D : ℕ) :
    ∃ left right : Fin (D + 2) → ℝ,
      IsMomentMatchedProbabilityPair D left right ∧
        SeparatesAtNextDiagonalTraffic D left right := by
  obtain ⟨weight, _hweightNe, hlow, hhigh⟩ := exists_truncatedMoment_annihilator D
  have hzero : ∑ index, weight index = 0 := by
    simpa using hlow (0 : Fin (D + 1))
  let left := perturbedMomentWeight D weight
  let right := referenceMomentWeight D
  have hprofile : finiteDiagonalTrafficProfile D left =
      finiteDiagonalTrafficProfile D right := by
    funext degree
    exact perturbedMoment_eq_referenceMoment D degree weight (hlow degree)
  refine ⟨left, right, ?_, ?_⟩
  · exact ⟨momentSeparationNode_mem_Icc D,
      fun index ↦ (perturbedMomentWeight_pos D weight index).le,
      fun _index ↦ by unfold right referenceMomentWeight momentUniformWeight; positivity,
      perturbedMomentWeight_sum_one D weight hzero,
      referenceMomentWeight_sum_one D, hprofile⟩
  · exact perturbedMoment_ne_referenceMoment D (D + 1) weight hhigh

/-- **A common hard pair for the entire degree-`D` graph-polynomial class.**
The two laws are genuine probability laws on `[1,2]`; every truncated traffic
risk gives exactly the same value on them, while their next diagonal traffic
coordinate differs. -/
theorem exists_probabilityPair_blindToEveryTruncatedTrafficRisk (D : ℕ) :
    ∃ left right : Fin (D + 2) → ℝ,
      IsBlindPairForEveryTruncatedTrafficRisk D left right := by
  obtain ⟨left, right, hpair, hnext⟩ :=
    exists_probabilityWeights_matchingMoments_through_degree D
  rcases hpair with ⟨hnodes, hleft, hright, hleftSum, hrightSum, hprofile⟩
  refine ⟨left, right,
    ⟨⟨hnodes, hleft, hright, hleftSum, hrightSum, hprofile⟩, ?_, hnext⟩⟩
  intro risk
  exact truncatedTrafficRisk_eq_of_profile_eq risk _ _ hprofile

end PolynomialTraffic

section ExponentialProfileCompactness

/-! ### Countable LD/right-convergence compactification

The nonperturbative profile is a countable collection of normalized pressure
coordinates.  Uniform operator and support bounds place every coordinate in a
fixed compact interval.  The product below is therefore the exact compact
state space behind the diagonal-subsequence argument; unlike a prose appeal to
"diagonalization", the theorem returns one common subsequence on which every
coordinate converges.
-/

/-- **Quantitative dense-parameter control for pressure profiles.**  If a set
of enumerated parameters is a `radius`-net, two uniformly `K`-Lipschitz
profiles that differ there by at most `coordinateError` differ everywhere by
at most `2 K radius + coordinateError`.  This is the finite-resolution theorem
behind extending rational tilt coordinates to all tilts. -/
theorem lipschitzPressureProfiles_dist_le_of_net
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (left right : Parameter → ℝ)
    (hleft : LipschitzWith K left) (hright : LipschitzWith K right)
    (net : Set Parameter) (radius coordinateError : ℝ)
    (hnet : ∀ parameter, ∃ representative ∈ net,
      dist parameter representative ≤ radius)
    (hagrees : ∀ representative ∈ net,
      dist (left representative) (right representative) ≤ coordinateError) :
    ∀ parameter,
      dist (left parameter) (right parameter) ≤
        2 * (K : ℝ) * radius + coordinateError := by
  intro parameter
  obtain ⟨representative, hrepresentative, hdistance⟩ := hnet parameter
  have hleftBound :
      dist (left parameter) (left representative) ≤ (K : ℝ) * radius :=
    hleft.dist_le_mul_of_le hdistance
  have hrightBound :
      dist (right representative) (right parameter) ≤ (K : ℝ) * radius := by
    apply hright.dist_le_mul_of_le
    simpa [dist_comm] using hdistance
  have hmiddle := hagrees representative hrepresentative
  calc
    dist (left parameter) (right parameter) ≤
        dist (left parameter) (left representative) +
          dist (left representative) (right parameter) :=
      dist_triangle _ _ _
    _ ≤ dist (left parameter) (left representative) +
        (dist (left representative) (right representative) +
          dist (right representative) (right parameter)) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ 2 * (K : ℝ) * radius + coordinateError := by
      linarith

/-- **Dense rational pressure coordinates determine the full Lipschitz
profile uniquely.**  This is the zero-resolution limit of the preceding net
bound and is the exact uniqueness statement used by the countable
right-convergence compactification. -/
theorem lipschitzPressureProfiles_eq_of_eqOn_dense
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (left right : Parameter → ℝ)
    (hleft : LipschitzWith K left) (hright : LipschitzWith K right)
    (parameters : Set Parameter) (hdense : Dense parameters)
    (hagrees : Set.EqOn left right parameters) :
    left = right :=
  Continuous.ext_on hdense hleft.continuous hright.continuous hagrees

/-- **Dense rational convergence extends to every tilt.**  A sequence of
uniformly `K`-Lipschitz pressure profiles that converges pointwise on a dense
parameter family to a `K`-Lipschitz limit converges pointwise everywhere.  The
proof uses one nearby dense parameter and a three-term metric bound, so no
unproved Arzelà--Ascoli step is hidden. -/
theorem lipschitzPressureProfiles_tendsto_of_tendstoOn_dense
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (profiles : ℕ → Parameter → ℝ) (limit : Parameter → ℝ)
    (hprofiles : ∀ index, LipschitzWith K (profiles index))
    (hlimit : LipschitzWith K limit)
    (parameters : Set Parameter) (hdense : Dense parameters)
    (hconverges : ∀ parameter ∈ parameters,
      Filter.Tendsto (fun index ↦ profiles index parameter)
        Filter.atTop (nhds (limit parameter))) :
    ∀ parameter,
      Filter.Tendsto (fun index ↦ profiles index parameter)
        Filter.atTop (nhds (limit parameter)) := by
  intro parameter
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hscale : 0 < 3 * ((K : ℝ) + 1) := by positivity
  obtain ⟨representative, hrepresentative, hdistance⟩ :=
    hdense.exists_dist_lt parameter (div_pos hepsilon hscale)
  have hlocal : (K : ℝ) * dist parameter representative < epsilon / 3 := by
    calc
      (K : ℝ) * dist parameter representative ≤
          ((K : ℝ) + 1) * dist parameter representative := by
        exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < ((K : ℝ) + 1) * (epsilon / (3 * ((K : ℝ) + 1))) :=
        mul_lt_mul_of_pos_left hdistance (by positivity)
      _ = epsilon / 3 := by
        field_simp
  have hmiddle := (Metric.tendsto_nhds.mp
    (hconverges representative hrepresentative)) (epsilon / 3) (by positivity)
  filter_upwards [hmiddle] with index hmiddleIndex
  have hleftLocal :
      dist (profiles index parameter) (profiles index representative) < epsilon / 3 :=
    (hprofiles index).dist_le_mul parameter representative |>.trans_lt hlocal
  have hrightLocal :
      dist (limit representative) (limit parameter) < epsilon / 3 := by
    have := hlimit.dist_le_mul representative parameter
    rw [dist_comm representative parameter] at this
    exact this.trans_lt hlocal
  calc
    dist (profiles index parameter) (limit parameter) ≤
        dist (profiles index parameter) (profiles index representative) +
          dist (profiles index representative) (limit parameter) :=
      dist_triangle _ _ _
    _ ≤ dist (profiles index parameter) (profiles index representative) +
        (dist (profiles index representative) (limit representative) +
          dist (limit representative) (limit parameter)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < epsilon := by linarith

/-- **Compact tilt domains upgrade dense convergence to uniform convergence.**
Uniform `K`-Lipschitz control supplies equicontinuity; compactness supplies a
finite radius net; convergence at its finitely many points supplies one common
index.  The resulting conclusion is `TendstoUniformly`, not merely pointwise
convergence at each tilt. -/
theorem lipschitzPressureProfiles_tendstoUniformly_of_tendstoOn_dense
    {Parameter : Type*} [PseudoMetricSpace Parameter] [CompactSpace Parameter]
    (K : NNReal) (profiles : ℕ → Parameter → ℝ) (limit : Parameter → ℝ)
    (hprofiles : ∀ index, LipschitzWith K (profiles index))
    (hlimit : LipschitzWith K limit)
    (parameters : Set Parameter) (hdense : Dense parameters)
    (hconverges : ∀ parameter ∈ parameters,
      Filter.Tendsto (fun index ↦ profiles index parameter)
        Filter.atTop (nhds (limit parameter))) :
    TendstoUniformly profiles limit Filter.atTop := by
  have hpointwise := lipschitzPressureProfiles_tendsto_of_tendstoOn_dense
    K profiles limit hprofiles hlimit parameters hdense hconverges
  rw [Metric.tendstoUniformly_iff]
  intro epsilon hepsilon
  let radius : ℝ := epsilon / (6 * ((K : ℝ) + 1))
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have htotallyBounded : TotallyBounded (Set.univ : Set Parameter) :=
    CompactSpace.isCompact_univ.totallyBounded
  obtain ⟨net, _hnetUniv, hnetFinite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded htotallyBounded radius hradius
  have heventually : ∀ᶠ index in Filter.atTop,
      ∀ representative ∈ hnetFinite.toFinset,
        dist (profiles index representative) (limit representative) < epsilon / 3 := by
    rw [Finset.eventually_all]
    intro representative _hrepresentative
    exact (Metric.tendsto_nhds.mp (hpointwise representative))
      (epsilon / 3) (by positivity)
  filter_upwards [heventually] with index hindex
  intro parameter
  have hnetApprox : ∀ candidate, ∃ representative ∈ net,
      dist candidate representative ≤ radius := by
    intro candidate
    have hcandidate := hcover (Set.mem_univ candidate)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hcandidate
    obtain ⟨nearby, hnearby, hnearbyDistance⟩ := hcandidate
    exact ⟨nearby, hnearby, hnearbyDistance.le⟩
  have hagrees : ∀ candidate ∈ net,
      dist (profiles index candidate) (limit candidate) ≤ epsilon / 3 := by
    intro candidate hcandidate
    exact (hindex candidate (hnetFinite.mem_toFinset.mpr hcandidate)).le
  have hbound := lipschitzPressureProfiles_dist_le_of_net
    K (profiles index) limit (hprofiles index) hlimit net radius (epsilon / 3)
      hnetApprox hagrees parameter
  have hradiusNonneg : 0 ≤ radius := hradius.le
  have hspatial : 2 * (K : ℝ) * radius ≤ epsilon / 3 := by
    calc
      2 * (K : ℝ) * radius ≤ 2 * ((K : ℝ) + 1) * radius := by
        gcongr
        linarith
      _ = epsilon / 3 := by
        dsimp [radius]
        field_simp
        norm_num
  rw [dist_comm]
  exact hbound.trans_lt (by linarith)

/-- Bounded continuous pressure functions with one common Lipschitz constant
and one common range interval.  This is the functional, rather than merely
coordinatewise, right-profile family used by Arzelà--Ascoli. -/
def boundedLipschitzPressureFamily
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (bound : ℝ) :
    Set (BoundedContinuousFunction Parameter ℝ) :=
  {profile | LipschitzWith K profile ∧
    ∀ parameter, profile parameter ∈ Set.Icc (-bound) bound}

/-- The bounded common-Lipschitz pressure family is closed in the uniform
metric on bounded continuous functions. -/
theorem isClosed_boundedLipschitzPressureFamily
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (bound : ℝ) :
    IsClosed (boundedLipschitzPressureFamily (Parameter := Parameter) K bound) := by
  rw [show boundedLipschitzPressureFamily (Parameter := Parameter) K bound =
      {profile | ∀ x y,
        dist (profile x) (profile y) ≤ (K : ℝ) * dist x y} ∩
      {profile | ∀ x, profile x ∈ Set.Icc (-bound) bound} by
    ext profile
    simp only [boundedLipschitzPressureFamily, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [lipschitzWith_iff_dist_le_mul]]
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
      isClosed_le
        (BoundedContinuousFunction.continuous_eval_const.dist
          BoundedContinuousFunction.continuous_eval_const)
        continuous_const
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun x ↦
      isClosed_Icc.preimage BoundedContinuousFunction.continuous_eval_const

/-- **Functional right-profile compactness (Arzelà--Ascoli).**  On a compact
tilt domain, uniformly bounded pressure functions sharing one Lipschitz
constant form a compact set in the uniform metric. -/
theorem isCompact_boundedLipschitzPressureFamily
    {Parameter : Type*} [PseudoMetricSpace Parameter] [CompactSpace Parameter]
    (K : NNReal) (bound : ℝ) :
    IsCompact (boundedLipschitzPressureFamily (Parameter := Parameter) K bound) := by
  let family := boundedLipschitzPressureFamily (Parameter := Parameter) K bound
  have hclosed : IsClosed family := isClosed_boundedLipschitzPressureFamily K bound
  have hrange : ∀ (profile : BoundedContinuousFunction Parameter ℝ)
      (parameter : Parameter),
      profile ∈ family → profile parameter ∈ Set.Icc (-bound) bound := by
    intro profile parameter hprofile
    exact hprofile.2 parameter
  have hequicontinuous : Equicontinuous ((↑) : family → Parameter → ℝ) := by
    exact (LipschitzWith.uniformEquicontinuous
      ((↑) : family → Parameter → ℝ) K
      (fun profile ↦ profile.property.1)).equicontinuous
  have hclosure := BoundedContinuousFunction.arzela_ascoli
    (Set.Icc (-bound) bound) isCompact_Icc family hrange hequicontinuous
  simpa [hclosed.closure_eq] using hclosure

/-- Every bounded equi-Lipschitz pressure sequence on a compact tilt domain
has a uniformly convergent subsequence whose limit remains in the same family. -/
theorem boundedLipschitzPressureFamily_tendsto_subseq
    {Parameter : Type*} [PseudoMetricSpace Parameter] [CompactSpace Parameter]
    (K : NNReal) (bound : ℝ)
    (profiles : ℕ → BoundedContinuousFunction Parameter ℝ)
    (hprofiles : ∀ index,
      profiles index ∈ boundedLipschitzPressureFamily K bound) :
    ∃ limit ∈ boundedLipschitzPressureFamily (Parameter := Parameter) K bound,
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit) :=
  (isCompact_boundedLipschitzPressureFamily K bound).tendsto_subseq hprofiles

/-- A bounded countable exponential/LD profile.  Coordinate `j` packages one
choice of prior, replica number, and rational tilt from the fixed countable
dense family. -/
abbrev BoundedExponentialProfile (bound : ℝ) :=
  ℕ → Set.Icc (-bound) bound

/-- A dedicated carrier for the explicit exponential/right-profile metric.
It is definitionally the same bounded coordinate family, but unlike the raw
function type it receives the weighted product metric rather than an unrelated
function-space metric instance. -/
def ExponentialProfilePoint (bound : ℝ) := BoundedExponentialProfile bound

/-- Mathlib's metric on a countable product of metric spaces, transported to
the dedicated profile carrier:

    dist x y = ∑' j, min (2⁻ʲ) (dist (x j) (y j)).

`PiCountable.metricSpace` fixes `toUniformSpace := Pi.uniformSpace _`, so this
distance carries the product uniformity *by construction* rather than by a
separate argument.  That is what makes distance convergence and simultaneous
coordinate convergence the same statement below, and it is why this file no
longer carries its own capped-coordinate metric: the whole construction, and
the Tannery/coercivity argument that it induces the product topology, is
`Mathlib.Topology.MetricSpace.PiNat`.

The earlier bespoke formula was `∑' j, 2⁻ʲ · min 1 |x j - y j|`.  Mathlib's
caps the weight rather than the discrepancy; both are separating, both have
total mass two, and both metrize the product topology, so every downstream
statement is unchanged. -/
noncomputable instance exponentialProfilePointMetricSpace (bound : ℝ) :
    MetricSpace (ExponentialProfilePoint bound) :=
  PiCountable.metricSpace

/-- The explicit weighted distance on the countable exponential/LD profile.

Convention: the index is the enumeration position of a prior/replica/tilt
coordinate, not a biological locus. -/
noncomputable def exponentialProfileDistance
    {bound : ℝ} (left right : BoundedExponentialProfile bound) : ℝ :=
  dist (show ExponentialProfilePoint bound from left)
    (show ExponentialProfilePoint bound from right)

/-- Distance in the bundled right-profile metric is exactly the weighted
capped-coordinate formula, not merely topologically equivalent to it. -/
@[simp] theorem exponentialProfilePoint_dist_eq
    {bound : ℝ} (left right : ExponentialProfilePoint bound) :
    dist left right = exponentialProfileDistance left right := rfl

/-- The explicit series form of the profile distance.  `Encodable.encode` on
`ℕ` is the identity, so the weight at coordinate `j` is exactly `2⁻ʲ`. -/
theorem exponentialProfileDistance_eq_tsum
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right =
      ∑' coordinate : ℕ,
        min ((1 / 2 : ℝ) ^ coordinate)
          (dist (left coordinate) (right coordinate)) :=
  PiCountable.dist_eq_tsum (F := fun _ : ℕ ↦ Set.Icc (-bound) bound) left right

theorem exponentialProfileDistance_summable
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    Summable (fun coordinate : ℕ ↦
      min ((1 / 2 : ℝ) ^ coordinate)
        (dist (left coordinate) (right coordinate))) :=
  PiCountable.dist_summable (F := fun _ : ℕ ↦ Set.Icc (-bound) bound) left right

theorem exponentialProfileDistance_nonneg
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    0 ≤ exponentialProfileDistance left right :=
  dist_nonneg

@[simp] theorem exponentialProfileDistance_self
    {bound : ℝ} (profile : BoundedExponentialProfile bound) :
    exponentialProfileDistance profile profile = 0 :=
  dist_self (show ExponentialProfilePoint bound from profile)

theorem exponentialProfileDistance_comm
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right = exponentialProfileDistance right left :=
  dist_comm (show ExponentialProfilePoint bound from left)
    (show ExponentialProfilePoint bound from right)

theorem exponentialProfileDistance_triangle
    {bound : ℝ} (left middle right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right ≤
      exponentialProfileDistance left middle + exponentialProfileDistance middle right :=
  dist_triangle (show ExponentialProfilePoint bound from left)
    (show ExponentialProfilePoint bound from middle)
    (show ExponentialProfilePoint bound from right)

theorem exponentialProfileDistance_eq_zero_iff
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right = 0 ↔ left = right :=
  dist_eq_zero (x := show ExponentialProfilePoint bound from left)
    (y := show ExponentialProfilePoint bound from right)

/-- The explicit right-profile metric has uniform diameter at most two.  The
constant is exact for the zero-based weights `2⁻ʲ`: their total mass is two,
and every coordinate term is capped by its weight. -/
theorem exponentialProfileDistance_le_two
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right ≤ 2 := by
  rw [exponentialProfileDistance_eq_tsum]
  calc
    ∑' coordinate : ℕ,
        min ((1 / 2 : ℝ) ^ coordinate)
          (dist (left coordinate) (right coordinate)) ≤
        ∑' coordinate : ℕ, (1 / 2 : ℝ) ^ coordinate :=
      (exponentialProfileDistance_summable left right).tsum_le_tsum
        (fun _ ↦ min_le_left _ _) summable_geometric_two
    _ = 2 := tsum_geometric_two

/-- Agreement on the first `prefixLength` pressure coordinates controls the
entire nonperturbative profile with the exact remaining geometric tail.  This
is the quantitative finite-coordinate approximation property behind the
countable right-convergence compactification. -/
theorem exponentialProfileDistance_le_geometricTail_of_prefix_eq
    {bound : ℝ} (left right : BoundedExponentialProfile bound)
    (prefixLength : ℕ)
    (hprefix : ∀ coordinate < prefixLength, left coordinate = right coordinate) :
    exponentialProfileDistance left right ≤
      2 * (1 / 2 : ℝ) ^ prefixLength := by
  have hsummable := exponentialProfileDistance_summable left right
  have hprefixSum :
      ∑ coordinate ∈ Finset.range prefixLength,
        min ((1 / 2 : ℝ) ^ coordinate)
          (dist (left coordinate) (right coordinate)) = 0 := by
    refine Finset.sum_eq_zero fun coordinate hcoordinate ↦ ?_
    rw [hprefix coordinate (Finset.mem_range.mp hcoordinate), dist_self]
    exact min_eq_right (by positivity)
  have hsplit := hsummable.sum_add_tsum_nat_add prefixLength
  rw [hprefixSum, zero_add] at hsplit
  rw [exponentialProfileDistance_eq_tsum, ← hsplit]
  calc
    ∑' coordinate : ℕ,
        min ((1 / 2 : ℝ) ^ (coordinate + prefixLength))
          (dist (left (coordinate + prefixLength))
            (right (coordinate + prefixLength))) ≤
        ∑' coordinate : ℕ, (1 / 2 : ℝ) ^ (coordinate + prefixLength) :=
      ((summable_nat_add_iff prefixLength).mpr hsummable).tsum_le_tsum
        (fun _ ↦ min_le_left _ _)
        ((summable_nat_add_iff prefixLength).mpr summable_geometric_two)
    _ = 2 * (1 / 2 : ℝ) ^ prefixLength := by
      simp_rw [pow_add]
      rw [tsum_mul_right, tsum_geometric_two]

/-- Every coordinate discrepancy is controlled by the complete weighted
profile distance.  This is the coercive half of the metric construction: no
fixed pressure coordinate can move without paying its strictly positive
geometric weight in the global distance. -/
theorem exponentialProfileDistance_coordinateTerm_le
    {bound : ℝ} (left right : BoundedExponentialProfile bound)
    (coordinate : ℕ) :
    min ((1 / 2 : ℝ) ^ coordinate)
        (dist (left coordinate) (right coordinate)) ≤
      exponentialProfileDistance left right :=
  PiCountable.min_dist_le_dist_pi (F := fun _ : ℕ ↦ Set.Icc (-bound) bound)
    left right coordinate

/-- **Compactness of the countable exponential profile.**  Every sequence of
bounded profiles has one strictly increasing subsequence converging in the
product topology.  Product convergence is exactly coordinatewise convergence,
so the same subsequence works for every enumerated pressure coordinate. -/
theorem boundedExponentialProfile_compact_subsequence
    (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound) :
    ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit) :=
  CompactSpace.tendsto_subseq profiles

/-- Product convergence of bounded exponential profiles gives convergence of
every individual pressure coordinate along the same subsequence. -/
theorem boundedExponentialProfile_coordinatewise
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound} {subsequence : ℕ → ℕ}
    (hprofiles :
      Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit)) :
    ∀ coordinate : ℕ,
      Filter.Tendsto (fun n ↦ profiles (subsequence n) coordinate)
        Filter.atTop (nhds (limit coordinate)) :=
  fun coordinate ↦ (tendsto_pi_nhds.mp hprofiles) coordinate

theorem boundedExponentialProfile_common_coordinatewise_subsequence
    (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound) :
    ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        ∀ coordinate : ℕ,
          Filter.Tendsto (fun n ↦ profiles (subsequence n) coordinate)
            Filter.atTop (nhds (limit coordinate)) := by
  obtain ⟨limit, subsequence, hmono, hprofiles⟩ :=
    boundedExponentialProfile_compact_subsequence bound profiles
  exact ⟨limit, subsequence, hmono,
    boundedExponentialProfile_coordinatewise hprofiles⟩

/-- Standard convergence in the bundled right-profile metric is equivalent to
simultaneous convergence of every enumerated pressure coordinate.  This is
immediate from `PiCountable.metricSpace` carrying the product uniformity; the
former hand-rolled Tannery argument and its coercive converse are gone. -/
theorem exponentialProfilePoint_tendsto_iff_coordinatewise
    {bound : ℝ} {profiles : ℕ → ExponentialProfilePoint bound}
    {limit : ExponentialProfilePoint bound} :
    Filter.Tendsto profiles Filter.atTop (nhds limit) ↔
      ∀ coordinate : ℕ,
        Filter.Tendsto (fun n ↦ profiles n coordinate)
          Filter.atTop (nhds (limit coordinate)) :=
  tendsto_pi_nhds

/-- **Exact sequential characterization of the right-profile metric.**
Weighted-distance convergence is equivalent to simultaneous convergence of
all enumerated prior/replica/tilt pressure coordinates. -/
theorem exponentialProfileDistance_tendsto_zero_iff_coordinatewise
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound} :
    Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
        Filter.atTop (nhds 0) ↔
      ∀ coordinate : ℕ,
        Filter.Tendsto (fun n ↦ profiles n coordinate)
          Filter.atTop (nhds (limit coordinate)) :=
  (tendsto_iff_dist_tendsto_zero
      (f := fun n ↦ show ExponentialProfilePoint bound from profiles n)
      (a := show ExponentialProfilePoint bound from limit)).symm.trans
    exponentialProfilePoint_tendsto_iff_coordinatewise

theorem exponentialProfileDistance_tendsto_zero_of_coordinatewise
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound}
    (hcoordinate : ∀ coordinate : ℕ,
      Filter.Tendsto (fun n ↦ profiles n coordinate)
        Filter.atTop (nhds (limit coordinate))) :
    Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
      Filter.atTop (nhds 0) :=
  exponentialProfileDistance_tendsto_zero_iff_coordinatewise.mpr hcoordinate

theorem exponentialProfileDistance_coordinatewise_of_tendsto_zero
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound}
    (hdistance :
      Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
        Filter.atTop (nhds 0)) :
    ∀ coordinate : ℕ,
      Filter.Tendsto (fun n ↦ profiles n coordinate)
        Filter.atTop (nhds (limit coordinate)) :=
  exponentialProfileDistance_tendsto_zero_iff_coordinatewise.mp hdistance

/-- **Sequential compactness in the explicit distance.**  Every bounded
profile sequence has one common subsequence whose weighted exponential-profile
distance to a limiting profile tends to zero. -/
theorem boundedExponentialProfile_compact_subsequence_in_distance
    (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound) :
    ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        Filter.Tendsto
          (fun n ↦ exponentialProfileDistance (profiles (subsequence n)) limit)
          Filter.atTop (nhds 0) := by
  obtain ⟨limit, subsequence, hmono, hcoordinate⟩ :=
    boundedExponentialProfile_common_coordinatewise_subsequence bound profiles
  exact ⟨limit, subsequence, hmono,
    exponentialProfileDistance_tendsto_zero_of_coordinatewise hcoordinate⟩

/-- The bounded explicit right-profile metric space is compact in Mathlib's
ordinary topological sense, not only sequentially compact in a bespoke
statement. -/
instance exponentialProfilePointCompactSpace (bound : ℝ) :
    CompactSpace (ExponentialProfilePoint bound) :=
  Pi.compactSpace

/-- Every sequence in the bundled explicit metric has a conventionally
convergent subsequence. -/
theorem exponentialProfilePoint_isSeqCompact_univ (bound : ℝ) :
    IsSeqCompact (Set.univ : Set (ExponentialProfilePoint bound)) :=
  isCompact_univ.isSeqCompact

end ExponentialProfileCompactness

section MatchedBayesBoundary

/-- Primitive finite singular-value data sufficient for the standard
nuclear-norm/rank inequality.  The active set contains every nonzero singular
value, its cardinality is bounded by `rank`, and every singular value is at
most the operator bound.  No nuclear inequality is included as a field. -/
structure FiniteLowRankSingularSpectrum
    (Coordinate : Type*) [Fintype Coordinate] where
  singularValue : Coordinate → ℝ
  active : Finset Coordinate
  rank : ℕ
  operatorBound : ℝ
  operatorBound_nonnegative : 0 ≤ operatorBound
  singularValue_nonnegative : ∀ coordinate, 0 ≤ singularValue coordinate
  singularValue_le_operatorBound : ∀ coordinate,
    singularValue coordinate ≤ operatorBound
  inactive_zero : ∀ coordinate ∉ active, singularValue coordinate = 0
  active_card_le_rank : active.card ≤ rank

/-- The zero spectrum is a concrete inhabitant of the low-rank certificate
type; its support, rank, and operator bound all vanish.

Stated at an arbitrary finite coordinate type rather than at `PUnit`, because
what it is for is `finiteLowRankSingularSpectrum_nonempty` just below: every
result in this section is universally quantified over
`FiniteLowRankSingularSpectrum Coordinate`, and a universally quantified
statement about an uninhabited type is true for reasons that have nothing to do
with singular values. Pinning the witness to a one-point coordinate space would
have established non-vacuity at one dimension only, which is the dimension none
of the asymptotic results are about. -/
noncomputable def zeroFiniteLowRankSingularSpectrum
    (Coordinate : Type*) [Fintype Coordinate] :
    FiniteLowRankSingularSpectrum Coordinate where
  singularValue := fun _coordinate ↦ 0
  active := ∅
  rank := 0
  operatorBound := 0
  operatorBound_nonnegative := le_rfl
  singularValue_nonnegative := by simp
  singularValue_le_operatorBound := by simp
  inactive_zero := by simp
  active_card_le_rank := by simp

/-- **The low-rank certificate type is inhabited at every finite dimension**, so
the inequalities proved for it below are not vacuously true. -/
instance finiteLowRankSingularSpectrum_nonempty
    (Coordinate : Type*) [Fintype Coordinate] :
    Nonempty (FiniteLowRankSingularSpectrum Coordinate) :=
  ⟨zeroFiniteLowRankSingularSpectrum Coordinate⟩

/-- Raw nuclear distance represented by the sum of the certified singular
values. -/
noncomputable def FiniteLowRankSingularSpectrum.rawNuclearDistance
    {Coordinate : Type*} [Fintype Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate) : ℝ :=
  ∑ coordinate, spectrum.singularValue coordinate

/-- Dimension-normalized nuclear distance. -/
noncomputable def FiniteLowRankSingularSpectrum.normalizedNuclearDistance
    {Coordinate : Type*} [Fintype Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate) : ℝ :=
  spectrum.rawNuclearDistance / Fintype.card Coordinate

/-- Dimension-normalized rank. -/
noncomputable def FiniteLowRankSingularSpectrum.rankFraction
    {Coordinate : Type*} [Fintype Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate) : ℝ :=
  spectrum.rank / Fintype.card Coordinate

/-- The primitive support and operator-bound facts imply the raw inequality
`nuclear ≤ operatorBound * rank`. -/
theorem FiniteLowRankSingularSpectrum.rawNuclearDistance_le_rank_mul_operatorBound
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate) :
    spectrum.rawNuclearDistance ≤ spectrum.operatorBound * spectrum.rank := by
  rw [FiniteLowRankSingularSpectrum.rawNuclearDistance]
  calc
    (∑ coordinate, spectrum.singularValue coordinate) =
        ∑ coordinate ∈ spectrum.active, spectrum.singularValue coordinate := by
      symm
      apply Finset.sum_subset spectrum.active.subset_univ
      intro coordinate _hcoordinate hinactive
      exact spectrum.inactive_zero coordinate hinactive
    _ ≤ ∑ _coordinate ∈ spectrum.active, spectrum.operatorBound := by
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      exact spectrum.singularValue_le_operatorBound coordinate
    _ = spectrum.active.card * spectrum.operatorBound := by simp
    _ ≤ spectrum.rank * spectrum.operatorBound := by
      exact mul_le_mul_of_nonneg_right
        (mod_cast spectrum.active_card_le_rank) spectrum.operatorBound_nonnegative
    _ = spectrum.operatorBound * spectrum.rank := by ring

/-- After division by a positive dimension, the standard normalized inequality
is exactly `normalizedNuclearDistance ≤ operatorBound * rankFraction`. -/
theorem FiniteLowRankSingularSpectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate)
    (hdimension : 0 < Fintype.card Coordinate) :
    spectrum.normalizedNuclearDistance ≤
      spectrum.operatorBound * spectrum.rankFraction := by
  have hdimensionReal : (0 : ℝ) < Fintype.card Coordinate := by exact_mod_cast hdimension
  rw [FiniteLowRankSingularSpectrum.normalizedNuclearDistance,
    FiniteLowRankSingularSpectrum.rankFraction]
  calc
    spectrum.rawNuclearDistance / Fintype.card Coordinate ≤
        (spectrum.operatorBound * spectrum.rank) / Fintype.card Coordinate :=
      div_le_div_of_nonneg_right
        spectrum.rawNuclearDistance_le_rank_mul_operatorBound hdimensionReal.le
    _ = spectrum.operatorBound *
        (spectrum.rank / Fintype.card Coordinate) := by ring

/-- The concrete singular-value spectrum of a rank-one perturbation on the
`p+1`-dimensional outlier coordinate space. -/
noncomputable def finiteRankOneSingularSpectrum
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    FiniteLowRankSingularSpectrum (FiniteOutlierCoordinate population) where
  singularValue
    | none => spikeStrength
    | some _coordinate => 0
  active := {none}
  rank := 1
  operatorBound := spikeStrength
  operatorBound_nonnegative := hspike
  singularValue_nonnegative := by
    intro coordinate
    cases coordinate <;> simp_all
  singularValue_le_operatorBound := by
    intro coordinate
    cases coordinate <;> simp_all
  inactive_zero := by
    intro coordinate hinactive
    cases coordinate with
    | none => simp at hinactive
    | some coordinate => rfl
  active_card_le_rank := by simp

/-- The rank-one spectrum has raw nuclear distance equal to its spike
strength. -/
theorem finiteRankOneSingularSpectrum_rawNuclearDistance
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    (finiteRankOneSingularSpectrum population spikeStrength hspike).rawNuclearDistance =
      spikeStrength := by
  simp [FiniteLowRankSingularSpectrum.rawNuclearDistance,
    finiteRankOneSingularSpectrum, FiniteOutlierCoordinate]

/-- **The nuclear/rank inequality is attained, so nothing in it can be
tightened.** `rawNuclearDistance_le_rank_mul_operatorBound` holds for every
certificate; the rank-one spike turns it into an equality, which is what rules
out a strictly better constant, a strictly smaller power of the rank, or an
additive slack. An inequality with no attaining model is compatible with a
sharper law that the corpus would then be understating. -/
theorem finiteRankOneSingularSpectrum_rawNuclearDistance_eq_bound
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    (finiteRankOneSingularSpectrum population spikeStrength hspike).rawNuclearDistance =
      (finiteRankOneSingularSpectrum population spikeStrength hspike).operatorBound *
        (finiteRankOneSingularSpectrum population spikeStrength hspike).rank := by
  rw [finiteRankOneSingularSpectrum_rawNuclearDistance]
  simp [finiteRankOneSingularSpectrum]

/-- Its normalized nuclear distance is exactly `spikeStrength/(p+1)`. -/
theorem finiteRankOneSingularSpectrum_normalizedNuclearDistance
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    (finiteRankOneSingularSpectrum population spikeStrength hspike).normalizedNuclearDistance =
      spikeStrength / (population + 1 : ℕ) := by
  rw [FiniteLowRankSingularSpectrum.normalizedNuclearDistance,
    finiteRankOneSingularSpectrum_rawNuclearDistance]
  simp [FiniteOutlierCoordinate]

/-- Its normalized rank is exactly `1/(p+1)`. -/
theorem finiteRankOneSingularSpectrum_rankFraction
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    (finiteRankOneSingularSpectrum population spikeStrength hspike).rankFraction =
      1 / (population + 1 : ℕ) := by
  simp [FiniteLowRankSingularSpectrum.rankFraction,
    finiteRankOneSingularSpectrum, FiniteOutlierCoordinate]

/-- The normalized rank of the concrete rank-one spectrum vanishes as
dimension grows. -/
theorem finiteRankOneSingularSpectrum_rankFraction_tendsto_zero
    (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    Filter.Tendsto
      (fun population ↦
        (finiteRankOneSingularSpectrum population spikeStrength hspike).rankFraction)
      Filter.atTop (nhds 0) := by
  have hdenominator : Filter.Tendsto
      (fun population : ℕ ↦ ((population + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1) using 1
  have hinverse := hdenominator.inv_tendsto_atTop
  simpa only [finiteRankOneSingularSpectrum_rankFraction, one_div] using hinverse

/-- The exact model-side data needed to derive the matched scalar-channel
nuclear Lipschitz estimate.  `informationPath` interpolates between two channel
covariances, `tracePairing / 2` is the matrix I--MMSE directional derivative,
and `posteriorCovarianceTraceBound` is the covariance-order plus trace-duality
estimate.  Keeping these as named fields exposes the genuinely probabilistic
premises instead of assuming their final consequence. -/
structure MatchedInformationPathCertificate where
  informationPath : ℝ → ℝ
  tracePairing : ℝ → ℝ
  variance : ℝ
  nuclearDistance : ℝ
  variance_nonnegative : 0 ≤ variance
  nuclearDistance_nonnegative : 0 ≤ nuclearDistance
  immseDerivative : ∀ interpolation ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt informationPath (tracePairing interpolation / 2)
      (Set.Icc (0 : ℝ) 1) interpolation
  posteriorCovarianceTraceBound : ∀ interpolation ∈ Set.Ico (0 : ℝ) 1,
    |tracePairing interpolation| ≤ variance * nuclearDistance

/-- The constant zero path is a concrete matched-information certificate.  It
anchors the abstract certificate API in an actual model with zero variance and
zero covariance displacement. -/
noncomputable def zeroMatchedInformationPathCertificate :
    MatchedInformationPathCertificate where
  informationPath := fun _interpolation ↦ 0
  tracePairing := fun _interpolation ↦ 0
  variance := 0
  nuclearDistance := 0
  variance_nonnegative := le_rfl
  nuclearDistance_nonnegative := le_rfl
  immseDerivative := by
    intro interpolation _hinterpolation
    simpa using (hasDerivAt_const interpolation (0 : ℝ)).hasDerivWithinAt
  posteriorCovarianceTraceBound := by simp

/-- **The matched-information certificate type is inhabited**, so every bound
below is a bound on something. The premises are four nontrivial fields --- a
derivative identity holding on all of `[0,1]` and a trace bound holding on
`[0,1)` --- and a structure whose fields cannot be simultaneously satisfied
would make `matchedInformationPath_nuclear_bound` and everything downstream of
it true by having no models. -/
instance : Nonempty MatchedInformationPathCertificate :=
  ⟨zeroMatchedInformationPathCertificate⟩

/-- **The certificate that runs at the maximum rate the trace bound allows.**
The information path is linear with slope `variance · nuclearDistance / 2`, and
the trace pairing sits at the boundary of `posteriorCovarianceTraceBound`
throughout.

`zeroMatchedInformationPathCertificate` is the degenerate member of this family,
at `variance = nuclearDistance = 0`; this is the family it is degenerate in.
Its purpose is `saturatingMatchedInformationPathCertificate_attains_bound`. -/
noncomputable def saturatingMatchedInformationPathCertificate
    (variance nuclearDistance : ℝ) (hvariance : 0 ≤ variance)
    (hnuclear : 0 ≤ nuclearDistance) : MatchedInformationPathCertificate where
  informationPath := fun interpolation ↦
    variance * nuclearDistance / 2 * interpolation
  tracePairing := fun _interpolation ↦ variance * nuclearDistance
  variance := variance
  nuclearDistance := nuclearDistance
  variance_nonnegative := hvariance
  nuclearDistance_nonnegative := hnuclear
  immseDerivative := by
    intro interpolation _hinterpolation
    have hderivative :
        HasDerivAt (fun t : ℝ ↦ variance * nuclearDistance / 2 * t)
          (variance * nuclearDistance / 2) interpolation := by
      simpa using (hasDerivAt_id interpolation).const_mul
        (variance * nuclearDistance / 2)
    exact hderivative.hasDerivWithinAt
  posteriorCovarianceTraceBound := by
    intro _interpolation _hinterpolation
    exact le_of_eq (abs_of_nonneg (mul_nonneg hvariance hnuclear))

/-- **The pathwise nuclear estimate is attained, so the factor `1/2` is
optimal.** `matchedInformationPath_nuclear_bound` says the information change
along the covariance segment is at most `variance/2 · nuclearDistance`; this
exhibits, at every admissible pair of values, a certificate that changes by
exactly that much. No smaller multiplier than `1/2` is available, so the `1/2`
is the I--MMSE factor of one half and not a slack constant carried through the
calculus. -/
theorem saturatingMatchedInformationPathCertificate_attains_bound
    (variance nuclearDistance : ℝ) (hvariance : 0 ≤ variance)
    (hnuclear : 0 ≤ nuclearDistance) :
    |(saturatingMatchedInformationPathCertificate variance nuclearDistance
        hvariance hnuclear).informationPath 1 -
      (saturatingMatchedInformationPathCertificate variance nuclearDistance
        hvariance hnuclear).informationPath 0| =
      (saturatingMatchedInformationPathCertificate variance nuclearDistance
        hvariance hnuclear).variance / 2 *
        (saturatingMatchedInformationPathCertificate variance nuclearDistance
          hvariance hnuclear).nuclearDistance := by
  have hnonneg : 0 ≤ variance * nuclearDistance / 2 :=
    div_nonneg (mul_nonneg hvariance hnuclear) (by norm_num)
  simp only [saturatingMatchedInformationPathCertificate, mul_one, mul_zero,
    sub_zero]
  rw [abs_of_nonneg hnonneg]
  ring

/-- **Matrix-path derivation of the nuclear estimate.**  The I--MMSE
directional derivative and posterior-covariance trace bound imply that the
matched information change along the covariance segment is at most
`variance / 2` times nuclear distance. -/
theorem matchedInformationPath_nuclear_bound
    (certificate : MatchedInformationPathCertificate) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      certificate.variance / 2 * certificate.nuclearDistance := by
  have hderivative : ∀ interpolation ∈ Set.Ico (0 : ℝ) 1,
      ‖certificate.tracePairing interpolation / 2‖ ≤
        certificate.variance / 2 * certificate.nuclearDistance := by
    intro interpolation hinterpolation
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |certificate.tracePairing interpolation| / 2 ≤
          (certificate.variance * certificate.nuclearDistance) / 2 :=
        div_le_div_of_nonneg_right
          (certificate.posteriorCovarianceTraceBound interpolation hinterpolation)
          (by norm_num)
      _ = certificate.variance / 2 * certificate.nuclearDistance := by ring
  have hpath := norm_image_sub_le_of_norm_deriv_le_segment_01'
    certificate.immseDerivative hderivative
  simpa only [Real.norm_eq_abs] using hpath

/-- Combining the pathwise nuclear estimate with
`nuclearDistance ≤ operatorBound * rankFraction` gives the normalized low-rank
bound used in the matched-Bayes obstruction. -/
theorem matchedInformationPath_lowRank_bound
    (certificate : MatchedInformationPathCertificate)
    (operatorBound rankFraction : ℝ)
    (hnuclearRank : certificate.nuclearDistance ≤ operatorBound * rankFraction) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      certificate.variance * operatorBound / 2 * rankFraction := by
  calc
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
        certificate.variance / 2 * certificate.nuclearDistance :=
      matchedInformationPath_nuclear_bound certificate
    _ ≤ certificate.variance / 2 * (operatorBound * rankFraction) :=
      mul_le_mul_of_nonneg_left hnuclearRank
        (div_nonneg certificate.variance_nonnegative (by norm_num))
    _ = certificate.variance * operatorBound / 2 * rankFraction := by ring

/-- A uniform upper bound on prior variance is enough for the low-rank
estimate.  Exact equality of variances across a model sequence is unnecessary.
The nonnegativity needed to compare coefficients follows from the certified
nuclear-distance inequality itself. -/
theorem matchedInformationPath_lowRank_bound_of_varianceBound
    (certificate : MatchedInformationPathCertificate)
    (varianceBound operatorBound rankFraction : ℝ)
    (hvarianceBound : certificate.variance ≤ varianceBound)
    (hnuclearRank : certificate.nuclearDistance ≤ operatorBound * rankFraction) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      varianceBound * operatorBound / 2 * rankFraction := by
  have hproduct : 0 ≤ operatorBound * rankFraction :=
    certificate.nuclearDistance_nonnegative.trans hnuclearRank
  calc
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
        certificate.variance * operatorBound / 2 * rankFraction :=
      matchedInformationPath_lowRank_bound certificate operatorBound rankFraction
        hnuclearRank
    _ = certificate.variance / 2 * (operatorBound * rankFraction) := by ring
    _ ≤ varianceBound / 2 * (operatorBound * rankFraction) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hvarianceBound (by norm_num)) hproduct
    _ = varianceBound * operatorBound / 2 * rankFraction := by ring

/-- **I--MMSE low-rank bound derived from singular-value data.**  Once the
path's normalized nuclear distance is identified with the sum of its certified
singular values divided by dimension, the support/rank theorem above supplies
the required nuclear inequality automatically. -/
theorem matchedInformationPath_lowRank_bound_of_singularSpectrum
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : MatchedInformationPathCertificate)
    (spectrum : FiniteLowRankSingularSpectrum Coordinate)
    (hdimension : 0 < Fintype.card Coordinate)
    (hnuclear : certificate.nuclearDistance =
      spectrum.normalizedNuclearDistance) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      certificate.variance * spectrum.operatorBound / 2 * spectrum.rankFraction := by
  apply matchedInformationPath_lowRank_bound certificate spectrum.operatorBound
    spectrum.rankFraction
  rw [hnuclear]
  exact spectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction hdimension

/-- A uniform prior-variance ceiling gives the corresponding singular-spectrum
bound with `varianceBound` replacing the path's exact variance. -/
theorem matchedInformationPath_lowRank_bound_of_singularSpectrum_of_varianceBound
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : MatchedInformationPathCertificate)
    (spectrum : FiniteLowRankSingularSpectrum Coordinate)
    (varianceBound : ℝ) (hvarianceBound : certificate.variance ≤ varianceBound)
    (hdimension : 0 < Fintype.card Coordinate)
    (hnuclear : certificate.nuclearDistance =
      spectrum.normalizedNuclearDistance) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      varianceBound * spectrum.operatorBound / 2 * spectrum.rankFraction := by
  apply matchedInformationPath_lowRank_bound_of_varianceBound certificate
    varianceBound spectrum.operatorBound spectrum.rankFraction hvarianceBound
  rw [hnuclear]
  exact spectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction hdimension

/-- The asymptotic zero-gap conclusion shared by low-rank path certificates. -/
def MatchedInformationPathGapTendsToZero
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → MatchedInformationPathCertificate) : Prop :=
  Filter.Tendsto
    (fun index ↦ (certificate index).informationPath 1 -
      (certificate index).informationPath 0)
    regime (nhds 0)

/-- A family of certified matched-information paths with vanishing rank
fraction has vanishing information-density gap whenever its prior variances
are uniformly bounded.  Thus the asymptotic theorem needs no exact common
variance. -/
theorem matchedInformationPath_lowRank_tendsto_zero_of_varianceBound
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → MatchedInformationPathCertificate)
    (varianceBound operatorBound : ℝ) (rankFraction : Index → ℝ)
    (hvarianceBound : ∀ index, (certificate index).variance ≤ varianceBound)
    (hrankVanishing : Filter.Tendsto rankFraction regime (nhds 0))
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) :
    MatchedInformationPathGapTendsToZero regime certificate := by
  have hbound : Filter.Tendsto
      (fun index ↦ varianceBound * operatorBound / 2 * rankFraction index)
      regime (nhds 0) := by
    simpa using hrankVanishing.const_mul (varianceBound * operatorBound / 2)
  have habs : Filter.Tendsto
      (fun index ↦ |(certificate index).informationPath 1 -
        (certificate index).informationPath 0|)
      regime (nhds 0) := by
    apply squeeze_zero
    · intro index
      exact abs_nonneg _
    · intro index
      exact matchedInformationPath_lowRank_bound_of_varianceBound
        (certificate index) varianceBound operatorBound (rankFraction index)
        (hvarianceBound index) (hnuclearRank index)
    · exact hbound
  apply (tendsto_zero_iff_abs_tendsto_zero
    (fun index ↦ (certificate index).informationPath 1 -
      (certificate index).informationPath 0)).mpr
  simpa [Function.comp_def] using habs

/-- **Concrete bounded rank-one matched-Bayes invisibility.**  For the
`p+1`-dimensional rank-one singular spectrum, bounded prior variance and exact
identification of the normalized nuclear distance imply that the certified
information-density gap vanishes.  The nuclear/rank estimate is derived above,
not supplied by the caller. -/
theorem matchedInformationPath_rankOne_tendsto_zero_of_varianceBound
    (certificate : ℕ → MatchedInformationPathCertificate)
    (varianceBound spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength)
    (hvarianceBound : ∀ population,
      (certificate population).variance ≤ varianceBound)
    (hnuclear : ∀ population,
      (certificate population).nuclearDistance =
        (finiteRankOneSingularSpectrum population spikeStrength hspike).normalizedNuclearDistance) :
    Filter.Tendsto
      (fun population ↦ (certificate population).informationPath 1 -
        (certificate population).informationPath 0)
      Filter.atTop (nhds 0) := by
  apply matchedInformationPath_lowRank_tendsto_zero_of_varianceBound Filter.atTop
    certificate varianceBound spikeStrength
    (fun population ↦
      (finiteRankOneSingularSpectrum population spikeStrength hspike).rankFraction)
    hvarianceBound
    (finiteRankOneSingularSpectrum_rankFraction_tendsto_zero spikeStrength hspike)
  intro population
  rw [hnuclear population]
  exact
    FiniteLowRankSingularSpectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction
      (finiteRankOneSingularSpectrum population spikeStrength hspike) (by simp)

/-- The earlier common-variance formulation is a specialization of the
uniform-variance theorem, rather than a separate proof path. -/
theorem matchedInformationPath_lowRank_tendsto_zero
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → MatchedInformationPathCertificate)
    (operatorBound : ℝ) (rankFraction : Index → ℝ)
    (hvariance : ∃ variance : ℝ, ∀ index, (certificate index).variance = variance)
    (hrankVanishing : Filter.Tendsto rankFraction regime (nhds 0))
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) :
    MatchedInformationPathGapTendsToZero regime certificate := by
  obtain ⟨variance, hvariance⟩ := hvariance
  exact matchedInformationPath_lowRank_tendsto_zero_of_varianceBound regime
    certificate variance operatorBound rankFraction
    (fun index ↦ (hvariance index).le) hrankVanishing hnuclearRank

/-- The exact Wishart Frobenius second-moment identity plus operator-norm trace
bounds gives the dimension-scale second-moment estimate. -/
theorem wishartFrobeniusSecondMoment_le_dimensionScale
    (dimension sampleSize operatorBound covarianceTrace covarianceTraceSq
      frobeniusSecondMoment : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hoperator : 0 ≤ operatorBound)
    (htrace : |covarianceTrace| ≤ dimension * operatorBound)
    (htraceSq : covarianceTraceSq ≤ dimension * operatorBound ^ 2)
    (hmoment : frobeniusSecondMoment =
      (covarianceTrace ^ 2 + covarianceTraceSq) / sampleSize) :
    frobeniusSecondMoment ≤
      operatorBound ^ 2 * dimension * (dimension + 1) / sampleSize := by
  have hdimensionOperator : 0 ≤ dimension * operatorBound :=
    mul_nonneg hdimension.le hoperator
  have hproduct : 0 ≤
      (dimension * operatorBound - |covarianceTrace|) *
        (|covarianceTrace| + dimension * operatorBound) :=
    mul_nonneg (sub_nonneg.mpr htrace)
      (add_nonneg (abs_nonneg _) hdimensionOperator)
  have htracePower : covarianceTrace ^ 2 ≤
      (dimension * operatorBound) ^ 2 := by
    nlinarith [hproduct, sq_abs covarianceTrace]
  rw [hmoment]
  apply (div_le_div_iff_of_pos_right hsampleSize).mpr
  calc
    covarianceTrace ^ 2 + covarianceTraceSq ≤
        (dimension * operatorBound) ^ 2 +
          dimension * operatorBound ^ 2 :=
      add_le_add htracePower htraceSq
    _ = operatorBound ^ 2 * dimension * (dimension + 1) := by ring

/-- Taking square roots converts the Wishart second-moment estimate into the
Frobenius-error scale used by the nuclear comparison. -/
theorem wishartFrobeniusError_le_dimensionScale
    (dimension sampleSize operatorBound frobeniusSecondMoment
      frobeniusError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hoperator : 0 ≤ operatorBound)
    (hfrobenius : frobeniusError ≤ Real.sqrt frobeniusSecondMoment)
    (hsecondMoment : frobeniusSecondMoment ≤
      operatorBound ^ 2 * dimension * (dimension + 1) / sampleSize) :
    frobeniusError ≤ operatorBound *
      Real.sqrt (dimension * ((dimension + 1) / sampleSize)) := by
  have hratio : 0 ≤ dimension * ((dimension + 1) / sampleSize) := by positivity
  calc
    frobeniusError ≤ Real.sqrt frobeniusSecondMoment := hfrobenius
    _ ≤ Real.sqrt
        (operatorBound ^ 2 * dimension * (dimension + 1) / sampleSize) :=
      Real.sqrt_le_sqrt hsecondMoment
    _ = Real.sqrt (operatorBound ^ 2 *
        (dimension * ((dimension + 1) / sampleSize))) := by
      congr 1
      ring
    _ = Real.sqrt (dimension * ((dimension + 1) / sampleSize)) *
        Real.sqrt (operatorBound ^ 2) := by
      rw [mul_comm, Real.sqrt_mul hratio]
    _ = operatorBound *
        Real.sqrt (dimension * ((dimension + 1) / sampleSize)) := by
      rw [Real.sqrt_sq hoperator]
      ring

/-- **Deterministic Wishart nuclear-error ledger.**  Combining
`nuclearError ≤ sqrt dimension * frobeniusError` with the standard Wishart
Frobenius scale gives the normalized nuclear scale
`operatorBound * dimension * sqrt ((dimension + 1) / sampleSize)`. -/
theorem wishartNuclearError_le_dimensionScale
    (dimension sampleSize operatorBound nuclearError frobeniusError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hnuclear : nuclearError ≤ Real.sqrt dimension * frobeniusError)
    (hfrobenius : frobeniusError ≤ operatorBound *
      Real.sqrt (dimension * ((dimension + 1) / sampleSize))) :
    nuclearError ≤ operatorBound * dimension *
      Real.sqrt ((dimension + 1) / sampleSize) := by
  have hratio : 0 ≤ (dimension + 1) / sampleSize := by positivity
  have hsqrtIdentity : Real.sqrt dimension *
      Real.sqrt (dimension * ((dimension + 1) / sampleSize)) =
        dimension * Real.sqrt ((dimension + 1) / sampleSize) := by
    rw [show Real.sqrt (dimension * ((dimension + 1) / sampleSize)) =
        Real.sqrt ((dimension + 1) / sampleSize) * Real.sqrt dimension by
      rw [mul_comm, Real.sqrt_mul hratio]]
    calc
      Real.sqrt dimension *
          (Real.sqrt ((dimension + 1) / sampleSize) * Real.sqrt dimension) =
          (Real.sqrt dimension * Real.sqrt dimension) *
            Real.sqrt ((dimension + 1) / sampleSize) := by ring
      _ = dimension * Real.sqrt ((dimension + 1) / sampleSize) := by
        rw [Real.mul_self_sqrt hdimension.le]
  calc
    nuclearError ≤ Real.sqrt dimension * frobeniusError := hnuclear
    _ ≤ Real.sqrt dimension * (operatorBound *
        Real.sqrt (dimension * ((dimension + 1) / sampleSize))) :=
      mul_le_mul_of_nonneg_left hfrobenius (Real.sqrt_nonneg _)
    _ = operatorBound * dimension *
        Real.sqrt ((dimension + 1) / sampleSize) := by
      calc
        Real.sqrt dimension *
            (operatorBound *
              Real.sqrt (dimension * ((dimension + 1) / sampleSize))) =
            operatorBound *
              (Real.sqrt dimension *
                Real.sqrt (dimension * ((dimension + 1) / sampleSize))) := by ring
        _ = _ := by rw [hsqrtIdentity]; ring

/-- **Explicit matched random-design comparison rate.**  The normalized
information-path nuclear estimate and the Wishart nuclear scale imply error at
most `signal * variance * operatorBound / 2 * sqrt ((p+1)/n)`. -/
theorem matchedInformationError_le_wishartScale
    (dimension sampleSize signal variance operatorBound : ℝ)
    (informationError nuclearError : ℝ)
    (hdimension : 0 < dimension) (hsignal : 0 ≤ signal)
    (hvariance : 0 ≤ variance)
    (hinformation : |informationError| ≤
      signal * variance / (2 * dimension) * nuclearError)
    (hnuclear : nuclearError ≤ operatorBound * dimension *
      Real.sqrt ((dimension + 1) / sampleSize)) :
    |informationError| ≤ signal * variance * operatorBound / 2 *
      Real.sqrt ((dimension + 1) / sampleSize) := by
  have hcoefficient : 0 ≤ signal * variance / (2 * dimension) := by positivity
  calc
    |informationError| ≤ signal * variance / (2 * dimension) * nuclearError :=
      hinformation
    _ ≤ signal * variance / (2 * dimension) *
        (operatorBound * dimension *
          Real.sqrt ((dimension + 1) / sampleSize)) :=
      mul_le_mul_of_nonneg_left hnuclear hcoefficient
    _ = signal * variance * operatorBound / 2 *
        Real.sqrt ((dimension + 1) / sampleSize) := by
      field_simp

/-- The full deterministic comparison chain in one theorem: matrix
I--MMSE/nuclear sensitivity, nuclear-to-Frobenius control, and the Wishart
Frobenius scale imply the explicit normalized information error. -/
theorem matchedInformationError_le_of_wishartFrobenius
    (dimension sampleSize signal variance operatorBound : ℝ)
    (informationError nuclearError frobeniusError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hsignal : 0 ≤ signal) (hvariance : 0 ≤ variance)
    (hinformation : |informationError| ≤
      signal * variance / (2 * dimension) * nuclearError)
    (hnuclear : nuclearError ≤ Real.sqrt dimension * frobeniusError)
    (hfrobenius : frobeniusError ≤ operatorBound *
      Real.sqrt (dimension * ((dimension + 1) / sampleSize))) :
    |informationError| ≤ signal * variance * operatorBound / 2 *
      Real.sqrt ((dimension + 1) / sampleSize) := by
  have hnuclearScale := wishartNuclearError_le_dimensionScale
    dimension sampleSize operatorBound nuclearError frobeniusError
    hdimension hsampleSize hnuclear hfrobenius
  exact matchedInformationError_le_wishartScale
    dimension sampleSize signal variance operatorBound informationError nuclearError
    hdimension hsignal hvariance hinformation hnuclearScale

/-- **Complete Wishart-to-information comparison theorem.**  Starting from
the exact Wishart second-moment identity and elementary trace bounds, this
derives the normalized matched-information error in one chain. -/
theorem matchedInformationError_le_of_wishartMomentIdentity
    (dimension sampleSize signal variance operatorBound covarianceTrace
      covarianceTraceSq frobeniusSecondMoment frobeniusError nuclearError
      informationError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hsignal : 0 ≤ signal) (hvariance : 0 ≤ variance)
    (hoperator : 0 ≤ operatorBound)
    (htrace : |covarianceTrace| ≤ dimension * operatorBound)
    (htraceSq : covarianceTraceSq ≤ dimension * operatorBound ^ 2)
    (hmoment : frobeniusSecondMoment =
      (covarianceTrace ^ 2 + covarianceTraceSq) / sampleSize)
    (hfrobenius : frobeniusError ≤ Real.sqrt frobeniusSecondMoment)
    (hnuclear : nuclearError ≤ Real.sqrt dimension * frobeniusError)
    (hinformation : |informationError| ≤
      signal * variance / (2 * dimension) * nuclearError) :
    |informationError| ≤ signal * variance * operatorBound / 2 *
      Real.sqrt ((dimension + 1) / sampleSize) := by
  have hsecondMoment := wishartFrobeniusSecondMoment_le_dimensionScale
    dimension sampleSize operatorBound covarianceTrace covarianceTraceSq
    frobeniusSecondMoment hdimension hsampleSize hoperator htrace htraceSq hmoment
  have hfrobeniusScale := wishartFrobeniusError_le_dimensionScale
    dimension sampleSize operatorBound frobeniusSecondMoment frobeniusError
    hdimension hsampleSize hoperator hfrobenius hsecondMoment
  exact matchedInformationError_le_of_wishartFrobenius
    dimension sampleSize signal variance operatorBound informationError nuclearError
    frobeniusError hdimension hsampleSize hsignal hvariance hinformation
    hnuclear hfrobeniusScale

/-- The explicit Wishart comparison scale itself vanishes with the adjusted
dimension/sample ratio.  This analytic fact is shared by information-error
convergence and by the two-design separation theorem. -/
theorem wishartSqrtComparisonError_tendsto_zero
    {Index : Type*} (regime : Filter Index)
    (adjustedRatio : Index → ℝ) (constant : ℝ)
    (hratio : Filter.Tendsto adjustedRatio regime (nhds 0)) :
    Filter.Tendsto (fun index ↦ constant * Real.sqrt (adjustedRatio index))
      regime (nhds 0) := by
  have hsqrt : Filter.Tendsto
      (fun index ↦ Real.sqrt (adjustedRatio index)) regime (nhds 0) := by
    simpa using hratio.sqrt
  simpa using hsqrt.const_mul constant

/-- A uniform Wishart-scale information bound vanishes whenever the adjusted
dimension/sample ratio tends to zero. -/
theorem matchedInformationError_tendsto_zero_of_wishartRatio
    {Index : Type*} (regime : Filter Index)
    (informationError adjustedRatio : Index → ℝ) (constant : ℝ)
    (hratio : Filter.Tendsto adjustedRatio regime (nhds 0))
    (herror : ∀ index,
      |informationError index| ≤ constant * Real.sqrt (adjustedRatio index)) :
    Filter.Tendsto informationError regime (nhds 0) := by
  have hbound := wishartSqrtComparisonError_tendsto_zero
    regime adjustedRatio constant hratio
  have habs : Filter.Tendsto (fun index ↦ |informationError index|)
      regime (nhds 0) :=
    squeeze_zero (fun index ↦ abs_nonneg _) herror hbound
  apply (tendsto_zero_iff_abs_tendsto_zero informationError).mpr
  simpa [Function.comp_def] using habs

/-- **Random-design reduction, as the sharp asymmetric error ledger.**  If the
left and right random-design information densities have errors `εₗ` and `εᵣ`,
the scalar gap `Δ` loses at most their sum. -/
theorem randomDesign_gap_of_scalarGap_asymmetric
    (scalarLeft scalarRight randomLeft randomRight leftError rightError delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ leftError)
    (hright : |randomRight - scalarRight| ≤ rightError)
    (hgap : scalarRight - scalarLeft = delta) :
    delta - (leftError + rightError) ≤ randomRight - randomLeft := by
  have hlowerLeft : randomLeft ≤ scalarLeft + leftError := by
    have := le_trans (le_abs_self (randomLeft - scalarLeft)) hleft
    linarith
  have hlowerRight : scalarRight - rightError ≤ randomRight := by
    have := le_trans (neg_le_abs (randomRight - scalarRight)) hright
    linarith
  linarith

/-- Equal comparison errors specialize the asymmetric ledger to the familiar
loss `2ε`. -/
theorem randomDesign_gap_of_scalarGap
    (scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ epsilon)
    (hright : |randomRight - scalarRight| ≤ epsilon)
    (hgap : scalarRight - scalarLeft = delta) :
    delta - 2 * epsilon ≤ randomRight - randomLeft := by
  simpa only [two_mul] using
    randomDesign_gap_of_scalarGap_asymmetric scalarLeft scalarRight randomLeft randomRight
      epsilon epsilon delta hleft hright hgap

/-- A scalar gap larger than the sum of the two comparison errors forces a
strict random-design gap. -/
theorem randomDesign_separates_of_scalarGap_asymmetric
    (scalarLeft scalarRight randomLeft randomRight leftError rightError delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ leftError)
    (hright : |randomRight - scalarRight| ≤ rightError)
    (hgap : scalarRight - scalarLeft = delta)
    (hpositive : leftError + rightError < delta) :
    randomLeft < randomRight := by
  have hbound := randomDesign_gap_of_scalarGap_asymmetric scalarLeft scalarRight
    randomLeft randomRight leftError rightError delta hleft hright hgap
  linarith

/-- In particular a scalar matched-channel gap larger than twice the comparison error forces a
random-design gap. -/
theorem randomDesign_separates_of_scalarGap
    (scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ epsilon)
    (hright : |randomRight - scalarRight| ≤ epsilon)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 2 * epsilon < delta) :
    randomLeft < randomRight :=
  randomDesign_separates_of_scalarGap_asymmetric scalarLeft scalarRight
    randomLeft randomRight epsilon epsilon delta hleft hright hgap (by
      simpa only [two_mul] using hpositive)

/-- **Finite large-aspect-ratio reduction.**  If both random-design channels
are within `constant / sqrt aspectRatio` of their scalar counterparts, the
scalar gap survives whenever it exceeds twice that explicit error. -/
theorem randomDesign_separates_of_scalarGap_of_inverseSqrtAspect
    (scalarLeft scalarRight randomLeft randomRight : ℝ)
    (aspectRatio constant delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ constant / Real.sqrt aspectRatio)
    (hright : |randomRight - scalarRight| ≤ constant / Real.sqrt aspectRatio)
    (hgap : scalarRight - scalarLeft = delta)
    (hthreshold : 2 * (constant / Real.sqrt aspectRatio) < delta) :
    randomLeft < randomRight :=
  randomDesign_separates_of_scalarGap scalarLeft scalarRight randomLeft randomRight
    (constant / Real.sqrt aspectRatio) delta hleft hright hgap hthreshold

/-- **A positive scalar matched-channel gap survives eventually when the two
possibly different comparison errors both vanish.**  This is the asymptotic
completion of the sharp asymmetric ledger.

The model-specific work is exactly the convergence of the two error functions;
no additional uniformity or hidden constant is assumed here. -/
theorem randomDesign_eventually_separates_of_scalarGap_asymmetric
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta : ℝ)
    (randomLeft randomRight leftError rightError : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤ leftError index)
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤ rightError index)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (hleftVanishing : Filter.Tendsto leftError regime (nhds 0))
    (hrightVanishing : Filter.Tendsto rightError regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index := by
  have hsum : Filter.Tendsto (fun index ↦ leftError index + rightError index)
      regime (nhds 0) := by
    simpa using hleftVanishing.add hrightVanishing
  have hbelow : ∀ᶠ index in regime, leftError index + rightError index < delta :=
    hsum.eventually_lt_const hpositive
  filter_upwards [hbelow] with index hthreshold
  exact randomDesign_separates_of_scalarGap_asymmetric
    scalarLeft scalarRight (randomLeft index) (randomRight index)
    (leftError index) (rightError index) delta (hleft index) (hright index)
    hgap hthreshold

/-- The common-error asymptotic theorem is the equal-error specialization of
the asymmetric result. -/
theorem randomDesign_eventually_separates_of_scalarGap
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta : ℝ)
    (randomLeft randomRight comparisonError : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤ comparisonError index)
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤ comparisonError index)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (herrorVanishing : Filter.Tendsto comparisonError regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_asymmetric regime
    scalarLeft scalarRight delta randomLeft randomRight comparisonError comparisonError
    hleft hright hgap hpositive herrorVanishing herrorVanishing

/-- Reciprocation identifies the large-aspect filter exactly with approach to
zero from the positive side.  This is the precise bridge between the two
large-sample parameterizations used below; no positivity hypothesis is hidden,
because it is carried by the one-sided neighborhood `𝓝[>] 0`. -/
theorem aspectAtTop_iff_inverseTendstoNhdsGTZero
    {Index : Type*} (regime : Filter Index) (aspectRatio : Index → ℝ) :
    Filter.Tendsto aspectRatio regime Filter.atTop ↔
      Filter.Tendsto (fun index ↦ (aspectRatio index)⁻¹) regime (𝓝[>] 0) := by
  constructor
  · intro haspect
    exact tendsto_inv_atTop_nhdsGT_zero.comp haspect
  · intro hinverse
    have hreciprocal := hinverse.inv_tendsto_nhdsGT_zero
    convert hreciprocal using 1
    funext index
    simp

/-- In particular, a diverging aspect ratio has a reciprocal converging to
zero in the ordinary two-sided topology. -/
theorem inverseAspect_tendsto_zero
    {Index : Type*} (regime : Filter Index) (aspectRatio : Index → ℝ)
    (haspect : Filter.Tendsto aspectRatio regime Filter.atTop) :
    Filter.Tendsto (fun index ↦ (aspectRatio index)⁻¹) regime (nhds 0) :=
  haspect.inv_tendsto_atTop

/-- The inverse-square-root and square-root-of-reciprocal error formulas are
identical, including at zero and for negative inputs under Lean's totalized
real square root. -/
theorem div_sqrt_eq_mul_sqrt_inv (constant aspectRatio : ℝ) :
    constant / Real.sqrt aspectRatio =
      constant * Real.sqrt (aspectRatio⁻¹) := by
  rw [Real.sqrt_inv, div_eq_mul_inv]

/-- **Sharp two-design Wishart reduction.**  The two channels may have
different constants and different adjusted dimension/sample ratios.  If both
Wishart scales vanish, every fixed positive scalar gap eventually transfers. -/
theorem randomDesign_eventually_separates_of_scalarGap_of_asymmetricWishartRatios
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta leftConstant rightConstant : ℝ)
    (leftRatio rightRatio randomLeft randomRight : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤
        leftConstant * Real.sqrt (leftRatio index))
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤
        rightConstant * Real.sqrt (rightRatio index))
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (hleftRatio : Filter.Tendsto leftRatio regime (nhds 0))
    (hrightRatio : Filter.Tendsto rightRatio regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_asymmetric regime
    scalarLeft scalarRight delta randomLeft randomRight
    (fun index ↦ leftConstant * Real.sqrt (leftRatio index))
    (fun index ↦ rightConstant * Real.sqrt (rightRatio index))
    hleft hright hgap hpositive
    (wishartSqrtComparisonError_tendsto_zero regime leftRatio leftConstant hleftRatio)
    (wishartSqrtComparisonError_tendsto_zero regime rightRatio rightConstant hrightRatio)

/-- **Common-ratio Wishart reduction.**  This is the equal-constant,
equal-ratio specialization of the sharp two-design theorem. -/
theorem randomDesign_eventually_separates_of_scalarGap_of_wishartRatio
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta constant : ℝ)
    (adjustedRatio randomLeft randomRight : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤
        constant * Real.sqrt (adjustedRatio index))
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤
        constant * Real.sqrt (adjustedRatio index))
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (hratio : Filter.Tendsto adjustedRatio regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_of_asymmetricWishartRatios regime
    scalarLeft scalarRight delta constant constant adjustedRatio adjustedRatio
    randomLeft randomRight hleft hright hgap hpositive hratio hratio

/-- **Concrete large-aspect-ratio asymptotic reduction.**  This applies the
Wishart-ratio theorem above after the reciprocal reparameterization
`adjustedRatio = aspectRatio⁻¹`.  Thus the two APIs have one proof path rather
than independent asymptotic arguments. -/
theorem randomDesign_eventually_separates_of_scalarGap_of_aspectAtTop
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta constant : ℝ)
    (aspectRatio randomLeft randomRight : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤ constant / Real.sqrt (aspectRatio index))
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤ constant / Real.sqrt (aspectRatio index))
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (haspectRatio : Filter.Tendsto aspectRatio regime Filter.atTop) :
    ∀ᶠ index in regime, randomLeft index < randomRight index := by
  apply randomDesign_eventually_separates_of_scalarGap_of_wishartRatio regime
    scalarLeft scalarRight delta constant
    (fun index ↦ (aspectRatio index)⁻¹) randomLeft randomRight
  · intro index
    simpa only [div_sqrt_eq_mul_sqrt_inv] using hleft index
  · intro index
    simpa only [div_sqrt_eq_mul_sqrt_inv] using hright index
  · exact hgap
  · exact hpositive
  · exact inverseAspect_tendsto_zero regime aspectRatio haspectRatio

/-- **Low-rank perturbations cannot solve the matched scalar problem once the
nuclear estimate is available.**  The path-certificate theorem above derives
that estimate from matrix I--MMSE and posterior-covariance trace control; this
scalar corollary then turns rank fraction `ε` into error `constant * ε`. -/
theorem matchedDensity_lowRank_bound_of_nuclearEstimate
    (densityGap constant rankFraction epsilon : ℝ)
    (hconstant : 0 ≤ constant) (hrank : rankFraction ≤ epsilon)
    (hnuclear : |densityGap| ≤ constant * rankFraction) :
    |densityGap| ≤ constant * epsilon := by
  exact hnuclear.trans (mul_le_mul_of_nonneg_left hrank hconstant)

/-- **Sublinear-rank perturbations are asymptotically invisible to matched
information-density under the matrix I-MMSE/nuclear estimate.**  This is the
sequence theorem asserted by the low-rank boundary argument: once the rank
fraction tends to zero, the absolute information-density gap is squeezed to
zero by the same fixed nuclear-norm constant.

The final nuclear estimate may either be supplied directly or obtained from
`MatchedInformationPathCertificate`; the asymptotic passage from it to
invisibility is proved here. -/
theorem matchedDensity_lowRank_tendsto_zero_of_nuclearEstimate
    (densityGap rankFraction : ℕ → ℝ) (constant : ℝ)
    (hrankVanishing : Filter.Tendsto rankFraction Filter.atTop (nhds 0))
    (hnuclear : ∀ index,
      |densityGap index| ≤ constant * rankFraction index) :
    Filter.Tendsto densityGap Filter.atTop (nhds 0) := by
  have hbound :
      Filter.Tendsto (fun index ↦ constant * rankFraction index)
        Filter.atTop (nhds 0) := by
    have hconstant : Filter.Tendsto (fun _index : ℕ ↦ constant)
        Filter.atTop (nhds constant) := tendsto_const_nhds
    simpa using hconstant.mul hrankVanishing
  have habs :
      Filter.Tendsto (fun index ↦ |densityGap index|)
        Filter.atTop (nhds 0) :=
    squeeze_zero
      (fun index ↦ abs_nonneg (densityGap index))
      hnuclear hbound
  apply (tendsto_zero_iff_abs_tendsto_zero densityGap).mpr
  simpa [Function.comp_def] using habs

/-- **Finite extensive-rank certificate.**  Under the matrix
I--MMSE/nuclear estimate, a matched information-density gap of magnitude at
least `delta > 0` forces rank fraction at least `delta / constant`. -/
theorem matchedDensity_positiveGap_forces_rankFraction
    (densityGap constant rankFraction delta : ℝ)
    (hconstant : 0 < constant) (hdelta : 0 < delta)
    (hgap : delta ≤ |densityGap|)
    (hnuclear : |densityGap| ≤ constant * rankFraction) :
    0 < rankFraction ∧ delta / constant ≤ rankFraction := by
  have hlower : delta / constant ≤ rankFraction :=
    (div_le_iff₀ hconstant).mpr (by
      calc
        delta ≤ constant * rankFraction := hgap.trans hnuclear
        _ = rankFraction * constant := mul_comm _ _)
  exact ⟨(div_pos hdelta hconstant).trans_le hlower, hlower⟩

/-- A persistent positive matched-density gap forces an eventual uniform
lower bound on the perturbation rank fraction. -/
theorem matchedDensity_eventualGap_forces_eventualRankFraction
    {Index : Type*} (regime : Filter Index)
    (densityGap rankFraction : Index → ℝ) (constant delta : ℝ)
    (hconstant : 0 < constant) (hdelta : 0 < delta)
    (hgap : ∀ᶠ index in regime, delta ≤ |densityGap index|)
    (hnuclear : ∀ index,
      |densityGap index| ≤ constant * rankFraction index) :
    ∀ᶠ index in regime, delta / constant ≤ rankFraction index := by
  filter_upwards [hgap] with index hindex
  exact (matchedDensity_positiveGap_forces_rankFraction
    (densityGap index) constant (rankFraction index) delta
    hconstant hdelta hindex (hnuclear index)).2

/-- Consequently a persistent order-one matched-density separation is
incompatible with a rank fraction tending to zero.  This is the quantitative
extensive-rank obstruction required of any negative matched-Bayes witness. -/
theorem matchedDensity_eventualGap_not_sublinearRank
    {Index : Type*} (regime : Filter Index) [regime.NeBot]
    (densityGap rankFraction : Index → ℝ) (constant delta : ℝ)
    (hconstant : 0 < constant) (hdelta : 0 < delta)
    (hgap : ∀ᶠ index in regime, delta ≤ |densityGap index|)
    (hnuclear : ∀ index,
      |densityGap index| ≤ constant * rankFraction index) :
    ¬ Filter.Tendsto rankFraction regime (nhds 0) := by
  have hrankLower := matchedDensity_eventualGap_forces_eventualRankFraction
    regime densityGap rankFraction constant delta hconstant hdelta hgap hnuclear
  intro hrankZero
  have hthreshold : 0 < delta / constant := div_pos hdelta hconstant
  have hrankUpper : ∀ᶠ index in regime,
      rankFraction index < delta / constant :=
    hrankZero.eventually_lt_const hthreshold
  obtain ⟨index, hlower, hupper⟩ := (hrankLower.and hrankUpper).exists
  exact (not_lt_of_ge hlower) hupper

/-- **Certified finite extensive-rank obstruction.**  A positive information
gap along an I--MMSE path, a uniform variance bound, and a nuclear-to-rank
comparison force an explicit positive rank fraction.  No final information
Lipschitz inequality is accepted as an assumption. -/
theorem matchedInformationPath_positiveGap_forces_rankFraction_of_varianceBound
    (certificate : MatchedInformationPathCertificate)
    (varianceBound operatorBound rankFraction delta : ℝ)
    (hvarianceBound : certificate.variance ≤ varianceBound)
    (hvariancePositive : 0 < varianceBound) (hoperator : 0 < operatorBound)
    (hdelta : 0 < delta)
    (hgap : delta ≤
      |certificate.informationPath 1 - certificate.informationPath 0|)
    (hnuclearRank : certificate.nuclearDistance ≤ operatorBound * rankFraction) :
    0 < rankFraction ∧
      delta / (varianceBound * operatorBound / 2) ≤ rankFraction := by
  apply matchedDensity_positiveGap_forces_rankFraction
    (certificate.informationPath 1 - certificate.informationPath 0)
    (varianceBound * operatorBound / 2) rankFraction delta
  · positivity
  · exact hdelta
  · exact hgap
  · exact matchedInformationPath_lowRank_bound_of_varianceBound certificate
      varianceBound operatorBound rankFraction hvarianceBound hnuclearRank

/-- **Certified asymptotic extensive-rank obstruction.**  If a family of
I--MMSE paths has uniformly bounded positive variance scale and a persistent
order-one information gap, its perturbation rank fraction is eventually
bounded below by the exact finite constant and cannot tend to zero. -/
theorem matchedInformationPath_persistentGap_requires_extensiveRank
    {Index : Type*} (regime : Filter Index) [regime.NeBot]
    (certificate : Index → MatchedInformationPathCertificate)
    (varianceBound operatorBound delta : ℝ) (rankFraction : Index → ℝ)
    (hvariancePositive : 0 < varianceBound) (hoperator : 0 < operatorBound)
    (hdelta : 0 < delta)
    (hvarianceBound : ∀ index, (certificate index).variance ≤ varianceBound)
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index)
    (hgap : ∀ᶠ index in regime, delta ≤
      |(certificate index).informationPath 1 -
        (certificate index).informationPath 0|) :
    (∀ᶠ index in regime,
      delta / (varianceBound * operatorBound / 2) ≤ rankFraction index) ∧
      ¬ Filter.Tendsto rankFraction regime (nhds 0) := by
  let densityGap := fun index ↦
    (certificate index).informationPath 1 - (certificate index).informationPath 0
  let constant := varianceBound * operatorBound / 2
  have hconstant : 0 < constant := by
    dsimp only [constant]
    positivity
  have hinformation : ∀ index,
      |densityGap index| ≤ constant * rankFraction index := by
    intro index
    exact matchedInformationPath_lowRank_bound_of_varianceBound
      (certificate index) varianceBound operatorBound (rankFraction index)
      (hvarianceBound index) (hnuclearRank index)
  exact ⟨matchedDensity_eventualGap_forces_eventualRankFraction regime
      densityGap rankFraction constant delta hconstant hdelta hgap hinformation,
    matchedDensity_eventualGap_not_sublinearRank regime densityGap rankFraction
      constant delta hconstant hdelta hgap hinformation⟩

end MatchedBayesBoundary

end TrafficInvariantSeparation

end Calibrator
