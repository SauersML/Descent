/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Logic.Equiv.Fintype
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Sequences
import Mathlib.Tactic
import Calibrator.ObservationalCeiling

namespace Calibrator

namespace TrafficInvariantSeparation

/-!
# Hardness by invariant separation, and the sub-critical traffic window

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

* `rankOneGraphSum_le_inv` -- the arithmetic behind traffic-invisibility of a
  rank-one spike. For a connected test graph in which every vertex has even
  degree, the number of edges is at least the number of vertices, and the
  normalised graph sum is then bounded by `1/p`. The graph-theoretic input
  (`|E| ≥ |V|` for such graphs) is taken as a hypothesis here and the arithmetic
  consequence is proved.

* `cw_rate_lower_bound`, `cw_rate_upper_bound`, and
  `cwVariationalPressureGap_eq_zero_iff` -- Pinsker's inequality and a
  complementary logarithmic upper bound prove the exact critical point for the
  SUPREMAL variational pressure itself: below it the gap vanishes identically,
  and above it an explicit interior magnetisation makes the supremum positive.

* `fixedTraffic_invisible_logRuntime_visible` -- every fixed diagonal traffic
  coordinate loses a block of mass `4⁻ᵏ`, while `k` power iterations amplify its
  normalized squared output back to one.

* `invariantPolynomial_graphSum_factorization` and `truncatedTraffic_hardness`
  -- an explicit permutation extending the occupied-label bijection proves
  coefficient constancy on equality-pattern graphs; equality of a truncated
  traffic profile then transfers the complete Bayes gap to the degree-limited
  class.

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

* `randomDesign_gap_of_scalarGap` and
  `randomDesign_eventually_separates_of_scalarGap` -- the matched random-design
  question reduces to its scalar Gaussian counterpart with a sharp two-error
  ledger, and every positive scalar gap eventually survives whenever that
  comparison error vanishes.

* `matchedDensity_lowRank_tendsto_zero_of_nuclearEstimate` -- the conditional
  nuclear estimate implies the full asymptotic statement: a vanishing rank
  fraction forces the matched information-density gap to vanish.

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
nothing here asserts the missing LDP/Varadhan identification of the finite
pressure with the variational pressure. The rank-one construction cannot decide matched Bayes: a
perturbation of rank `o(p)` moves the exponential pressure by order one and the
matched mutual-information density by `o(1)`, so a negative witness there needs
EXTENSIVE rank. That contrast -- one perturbation, four procedure classes, two
of which see it and two of which do not -- is the reason the invariant hierarchy
is procedure-dependent rather than a single chain.
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

/-- Every fixed connected graph coordinate of the balanced positive rank-one spike vanishes. -/
theorem balancedRankOneTrafficCoordinate_tendsto_zero
    (hasOddDegree : Bool) (vertices edges : ℕ) (hev : vertices ≤ edges) :
    Filter.Tendsto
      (fun p : ℕ ↦ balancedRankOneTrafficCoordinate hasOddDegree (p + 1) vertices edges)
      Filter.atTop (nhds 0) := by
  cases hasOddDegree <;>
    simp [balancedRankOneTrafficCoordinate, balancedRankOneGraphSum_tendsto_zero vertices edges hev]

/-! ### Positive-cone and ground-state certificates -/

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

/-- The quantity whose supremum over `m` is the overlap-pressure gap.

    Empirical status: NOT AN EMPIRICAL CLAIM. -/
noncomputable def cwObjective (tlam m : ℝ) : ℝ :=
  tlam / 2 * m ^ 2 - cwRate m

/-- Pinsker gap for the balanced Bernoulli pair. -/
noncomputable def cwPinskerGap (m : ℝ) : ℝ :=
  cwRate m - m ^ 2 / 2

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem cwPinskerGap_at_reference_point :
    cwPinskerGap 0 = 0 := by
  norm_num [cwPinskerGap, cwRate]


/-- Derivative of the Pinsker gap on the open magnetisation interval. -/
noncomputable def cwPinskerGapDerivative (m : ℝ) : ℝ :=
  (Real.log (1 + m) - Real.log (1 - m)) / 2 - m

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem cwPinskerGapDerivative_at_reference_point :
    cwPinskerGapDerivative 0 = 0 := by
  norm_num [cwPinskerGapDerivative]


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

/-- Normalized squared output of the diagonal power iteration: the exceptional mass `4⁻ᵏ` is
amplified by `4ᵗ`. -/
noncomputable def mesoscopicGFOMEnergy (iteration runtime : ℕ) : ℝ :=
  (4 : ℝ) ^ runtime * (1 / 4 : ℝ) ^ iteration

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

/-- The complete fixed-coordinate/logarithmic-runtime separation in one statement. -/
theorem fixedTraffic_invisible_logRuntime_visible :
    (∀ edges : ℕ,
      Filter.Tendsto (fun iteration ↦ diagonalTrafficCorrection 1 edges iteration)
        Filter.atTop (nhds 0)) ∧
      ∀ iteration : ℕ, mesoscopicGFOMEnergy iteration iteration = 1 :=
  ⟨diagonalTrafficCorrection_tendsto_zero 1, mesoscopicGFOMEnergy_logRuntime⟩

end MesoscopicAmplification

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

/-- A scalar risk that has access only to traffic coordinates with at most `D` edges. -/
structure TruncatedTrafficRisk (D : ℕ) where
  coefficient : Fin (D + 1) → ℝ

/-- Evaluation of a truncated-traffic risk functional.

Convention: `D` is polynomial/edge degree, not the population-genetic
linkage-disequilibrium coefficient traditionally also denoted `D`. -/
noncomputable def TruncatedTrafficRisk.evaluate
    {D : ℕ} (risk : TruncatedTrafficRisk D) (traffic : Fin (D + 1) → ℝ) : ℝ :=
  ∑ graph, risk.coefficient graph * traffic graph

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

/-- A bounded countable exponential/LD profile.  Coordinate `j` packages one
choice of prior, replica number, and rational tilt from the fixed countable
dense family. -/
abbrev BoundedExponentialProfile (bound : ℝ) :=
  ℕ → Set.Icc (-bound) bound

/-- One coordinate of the explicit exponential-profile distance, capped at
one exactly as in the right-convergence definition. -/
noncomputable def cappedProfileDifference (left right : ℝ) : ℝ :=
  min 1 |left - right|

/-- The explicit weighted distance on the countable exponential/LD profile.
Lean indices start at zero, so the weights are `2⁻ʲ`; their sum is two.  This
is the same convention as equation (8.2) up to its harmless index origin.

Convention: the index is the enumeration position of a prior/replica/tilt
coordinate, not a biological locus. -/
noncomputable def exponentialProfileDistance
    {bound : ℝ} (left right : BoundedExponentialProfile bound) : ℝ :=
  ∑' coordinate : ℕ,
    (1 / 2 : ℝ) ^ coordinate *
      cappedProfileDifference (left coordinate) (right coordinate)

theorem cappedProfileDifference_nonneg (left right : ℝ) :
    0 ≤ cappedProfileDifference left right := by
  unfold cappedProfileDifference
  exact le_min zero_le_one (abs_nonneg _)

theorem cappedProfileDifference_le_one (left right : ℝ) :
    cappedProfileDifference left right ≤ 1 := by
  exact min_le_left _ _

theorem cappedProfileDifference_eq_zero_iff (left right : ℝ) :
    cappedProfileDifference left right = 0 ↔ left = right := by
  constructor
  · intro hzero
    have habs : |left - right| = 0 := by
      by_contra hne
      have hpositive : 0 < |left - right| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      have : 0 < cappedProfileDifference left right := by
        unfold cappedProfileDifference
        exact lt_min zero_lt_one hpositive
      linarith
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · rintro rfl
    simp [cappedProfileDifference]

theorem cappedProfileDifference_comm (left right : ℝ) :
    cappedProfileDifference left right = cappedProfileDifference right left := by
  simp [cappedProfileDifference, abs_sub_comm]

/-- Capping an absolute difference at one preserves the triangle inequality. -/
theorem cappedProfileDifference_triangle (left middle right : ℝ) :
    cappedProfileDifference left right ≤
      cappedProfileDifference left middle + cappedProfileDifference middle right := by
  have habs : |left - right| ≤ |left - middle| + |middle - right| := by
    calc
      |left - right| = |(left - middle) + (middle - right)| := by congr 1; ring
      _ ≤ |left - middle| + |middle - right| := abs_add_le _ _
  by_cases hleft : 1 ≤ |left - middle|
  · have hone : cappedProfileDifference left middle = 1 := by
      simp [cappedProfileDifference, min_eq_left hleft]
    rw [hone]
    have hnonneg := cappedProfileDifference_nonneg middle right
    exact (cappedProfileDifference_le_one left right).trans (by linarith)
  by_cases hright : 1 ≤ |middle - right|
  · have hone : cappedProfileDifference middle right = 1 := by
      simp [cappedProfileDifference, min_eq_left hright]
    rw [hone]
    have hnonneg := cappedProfileDifference_nonneg left middle
    exact (cappedProfileDifference_le_one left right).trans (by linarith)
  · have hleftEq : cappedProfileDifference left middle = |left - middle| := by
      unfold cappedProfileDifference
      rw [min_eq_right (le_of_not_ge hleft)]
    have hrightEq : cappedProfileDifference middle right = |middle - right| := by
      unfold cappedProfileDifference
      rw [min_eq_right (le_of_not_ge hright)]
    rw [hleftEq, hrightEq]
    exact (min_le_right (1 : ℝ) |left - right|).trans habs

/-- The coordinate series defining the profile distance is summable. -/
theorem exponentialProfileDistance_summable
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    Summable (fun coordinate : ℕ ↦
      (1 / 2 : ℝ) ^ coordinate *
        cappedProfileDifference (left coordinate) (right coordinate)) := by
  refine Summable.of_nonneg_of_le (fun coordinate ↦ ?_) (fun coordinate ↦ ?_)
    summable_geometric_two
  · exact mul_nonneg (by positivity) (cappedProfileDifference_nonneg _ _)
  · exact mul_le_of_le_one_right (by positivity) (cappedProfileDifference_le_one _ _)

theorem exponentialProfileDistance_nonneg
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    0 ≤ exponentialProfileDistance left right := by
  unfold exponentialProfileDistance
  exact tsum_nonneg fun _ ↦ mul_nonneg (by positivity) (cappedProfileDifference_nonneg _ _)

@[simp] theorem exponentialProfileDistance_self
    {bound : ℝ} (profile : BoundedExponentialProfile bound) :
    exponentialProfileDistance profile profile = 0 := by
  simp [exponentialProfileDistance, cappedProfileDifference]

theorem exponentialProfileDistance_comm
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right = exponentialProfileDistance right left := by
  apply tsum_congr
  intro coordinate
  rw [cappedProfileDifference_comm]

theorem exponentialProfileDistance_triangle
    {bound : ℝ} (left middle right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right ≤
      exponentialProfileDistance left middle + exponentialProfileDistance middle right := by
  let leftTerm := fun coordinate : ℕ ↦
    (1 / 2 : ℝ) ^ coordinate *
      cappedProfileDifference (left coordinate) (middle coordinate)
  let rightTerm := fun coordinate : ℕ ↦
    (1 / 2 : ℝ) ^ coordinate *
      cappedProfileDifference (middle coordinate) (right coordinate)
  have hpointwise : ∀ coordinate : ℕ,
      (1 / 2 : ℝ) ^ coordinate *
          cappedProfileDifference (left coordinate) (right coordinate) ≤
        leftTerm coordinate + rightTerm coordinate := by
    intro coordinate
    dsimp [leftTerm, rightTerm]
    calc
      (1 / 2 : ℝ) ^ coordinate *
          cappedProfileDifference (left coordinate) (right coordinate) ≤
        (1 / 2 : ℝ) ^ coordinate *
          (cappedProfileDifference (left coordinate) (middle coordinate) +
            cappedProfileDifference (middle coordinate) (right coordinate)) :=
        mul_le_mul_of_nonneg_left
          (cappedProfileDifference_triangle _ _ _)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) coordinate)
      _ = (1 / 2 : ℝ) ^ coordinate *
          cappedProfileDifference (left coordinate) (middle coordinate) +
        (1 / 2 : ℝ) ^ coordinate *
          cappedProfileDifference (middle coordinate) (right coordinate) := by ring
  calc
    exponentialProfileDistance left right ≤
        ∑' coordinate : ℕ, (leftTerm coordinate + rightTerm coordinate) :=
      (exponentialProfileDistance_summable left right).tsum_le_tsum hpointwise
        ((exponentialProfileDistance_summable left middle).add
          (exponentialProfileDistance_summable middle right))
    _ = exponentialProfileDistance left middle + exponentialProfileDistance middle right :=
      (exponentialProfileDistance_summable left middle).tsum_add
        (exponentialProfileDistance_summable middle right)

theorem exponentialProfileDistance_eq_zero_iff
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right = 0 ↔ left = right := by
  constructor
  · intro hzero
    funext coordinate
    apply Subtype.ext
    apply (cappedProfileDifference_eq_zero_iff _ _).mp
    have htermNonneg : 0 ≤ (1 / 2 : ℝ) ^ coordinate *
        cappedProfileDifference (left coordinate) (right coordinate) :=
      mul_nonneg (by positivity) (cappedProfileDifference_nonneg _ _)
    have htermLe : (1 / 2 : ℝ) ^ coordinate *
          cappedProfileDifference (left coordinate) (right coordinate) ≤
        exponentialProfileDistance left right := by
      exact (exponentialProfileDistance_summable left right).le_tsum coordinate
        (fun index _ ↦ mul_nonneg (by positivity) (cappedProfileDifference_nonneg _ _))
    have htermZero : (1 / 2 : ℝ) ^ coordinate *
        cappedProfileDifference (left coordinate) (right coordinate) = 0 := by
      rw [hzero] at htermLe
      linarith
    exact (mul_eq_zero.mp htermZero).resolve_left (by positivity)
  · rintro rfl
    exact exponentialProfileDistance_self left

/-- The explicit right-profile metric has uniform diameter at most two.  The
constant is exact for the zero-based weights `2⁻ʲ`: their total mass is two,
and every capped coordinate discrepancy is at most one. -/
theorem exponentialProfileDistance_le_two
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right ≤ 2 := by
  calc
    exponentialProfileDistance left right ≤ ∑' coordinate : ℕ, (1 / 2 : ℝ) ^ coordinate :=
      (exponentialProfileDistance_summable left right).tsum_le_tsum
        (fun coordinate ↦ mul_le_of_le_one_right (by positivity)
          (cappedProfileDifference_le_one _ _))
        summable_geometric_two
    _ = 2 := by
      rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      norm_num

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
  let term := fun coordinate : ℕ ↦
    (1 / 2 : ℝ) ^ coordinate *
      cappedProfileDifference (left coordinate) (right coordinate)
  have hsummable : Summable term := exponentialProfileDistance_summable left right
  have hprefixSum : ∑ coordinate ∈ Finset.range prefixLength, term coordinate = 0 := by
    apply Finset.sum_eq_zero
    intro coordinate hcoordinate
    have heq := hprefix coordinate (Finset.mem_range.mp hcoordinate)
    simp [term, heq, cappedProfileDifference]
  have hsplit := hsummable.sum_add_tsum_nat_add prefixLength
  rw [hprefixSum, zero_add] at hsplit
  change (∑' coordinate : ℕ, term coordinate) ≤
    2 * (1 / 2 : ℝ) ^ prefixLength
  rw [← hsplit]
  calc
    (∑' coordinate : ℕ, term (coordinate + prefixLength)) ≤
        ∑' coordinate : ℕ, (1 / 2 : ℝ) ^ (coordinate + prefixLength) := by
      apply ((summable_nat_add_iff prefixLength).mpr hsummable).tsum_le_tsum
      · intro coordinate
        exact mul_le_of_le_one_right (by positivity)
          (cappedProfileDifference_le_one _ _)
      · exact (summable_nat_add_iff prefixLength).mpr summable_geometric_two
    _ = 2 * (1 / 2 : ℝ) ^ prefixLength := by
      simp_rw [pow_add]
      rw [tsum_mul_right,
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      norm_num

/-- Every coordinate discrepancy is controlled by the complete weighted
profile distance.  This is the coercive half of the metric construction: no
fixed pressure coordinate can move without paying its strictly positive
geometric weight in the global distance. -/
theorem exponentialProfileDistance_coordinateTerm_le
    {bound : ℝ} (left right : BoundedExponentialProfile bound)
    (coordinate : ℕ) :
    (1 / 2 : ℝ) ^ coordinate *
        cappedProfileDifference (left coordinate) (right coordinate) ≤
      exponentialProfileDistance left right := by
  exact (exponentialProfileDistance_summable left right).le_tsum coordinate
    (fun index _ ↦ mul_nonneg (by positivity) (cappedProfileDifference_nonneg _ _))

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
    (hprofiles : Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit))
    (coordinate : ℕ) :
    Filter.Tendsto (fun n ↦ profiles (subsequence n) coordinate)
      Filter.atTop (nhds (limit coordinate)) := by
  exact (continuous_apply coordinate).continuousAt.tendsto.comp hprofiles

/-- **Diagonal compactness in the form used by right convergence.**  There is
one common subsequence along which every enumerated pressure coordinate has a
limit; the subsequence is not allowed to depend on the coordinate. -/
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

/-- The capped coordinate discrepancy is continuous in its first argument. -/
theorem continuous_cappedProfileDifference_left (right : ℝ) :
    Continuous (fun left : ℝ ↦ cappedProfileDifference left right) := by
  unfold cappedProfileDifference
  exact continuous_const.min ((continuous_id.sub continuous_const).abs)

/-- Coordinatewise convergence implies convergence in the explicit weighted
profile distance.  Tannery's theorem justifies exchanging the profile limit
with the infinite weighted sum; the geometric weights dominate every capped
coordinate term uniformly. -/
theorem exponentialProfileDistance_tendsto_zero_of_coordinatewise
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound}
    (hcoordinate : ∀ coordinate : ℕ,
      Filter.Tendsto (fun n ↦ profiles n coordinate)
        Filter.atTop (nhds (limit coordinate))) :
    Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
      Filter.atTop (nhds 0) := by
  have hterm : ∀ coordinate : ℕ,
      Filter.Tendsto
        (fun n ↦ (1 / 2 : ℝ) ^ coordinate *
          cappedProfileDifference (profiles n coordinate) (limit coordinate))
        Filter.atTop (nhds 0) := by
    intro coordinate
    have hvalue : Filter.Tendsto
        (fun n ↦ (profiles n coordinate : ℝ)) Filter.atTop
        (nhds (limit coordinate : ℝ)) :=
      continuous_subtype_val.continuousAt.tendsto.comp (hcoordinate coordinate)
    have hcapped : Filter.Tendsto
        (fun n ↦ cappedProfileDifference (profiles n coordinate) (limit coordinate))
        Filter.atTop (nhds 0) := by
      convert (continuous_cappedProfileDifference_left (limit coordinate)).continuousAt.tendsto.comp
        hvalue using 1
      simp [cappedProfileDifference]
    simpa using (tendsto_const_nhds.mul hcapped)
  have hbound : ∀ᶠ n in Filter.atTop, ∀ coordinate : ℕ,
      ‖(1 / 2 : ℝ) ^ coordinate *
        cappedProfileDifference (profiles n coordinate) (limit coordinate)‖ ≤
          (1 / 2 : ℝ) ^ coordinate := by
    exact Filter.Eventually.of_forall fun n coordinate ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact mul_le_of_le_one_right (by positivity)
          (cappedProfileDifference_le_one _ _)
      · exact mul_nonneg (by positivity) (cappedProfileDifference_nonneg _ _)
  have htendsto := tendsto_tsum_of_dominated_convergence
    (f := fun n coordinate ↦ (1 / 2 : ℝ) ^ coordinate *
      cappedProfileDifference (profiles n coordinate) (limit coordinate))
    (g := fun _coordinate : ℕ ↦ (0 : ℝ))
    (bound := fun coordinate : ℕ ↦ (1 / 2 : ℝ) ^ coordinate)
    summable_geometric_two hterm hbound
  simpa [exponentialProfileDistance] using htendsto

/-- Convergence in the explicit weighted profile distance forces convergence
of every enumerated pressure coordinate.  Together with
`exponentialProfileDistance_tendsto_zero_of_coordinatewise`, this proves that
the concrete right-profile distance carries exactly the intended sequential
product topology, rather than merely being a separating formula on it. -/
theorem exponentialProfileDistance_coordinatewise_of_tendsto_zero
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound}
    (hdistance :
      Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
        Filter.atTop (nhds 0)) :
    ∀ coordinate : ℕ,
      Filter.Tendsto (fun n ↦ profiles n coordinate)
        Filter.atTop (nhds (limit coordinate)) := by
  intro coordinate
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let weight : ℝ := (1 / 2 : ℝ) ^ coordinate
  have hweight : 0 < weight := by
    dsimp [weight]
    positivity
  have hcutoff : 0 < min epsilon 1 := lt_min hepsilon zero_lt_one
  have hthreshold : 0 < weight * min epsilon 1 := mul_pos hweight hcutoff
  have heventually := (Metric.tendsto_nhds.mp hdistance
    (weight * min epsilon 1) hthreshold)
  filter_upwards [heventually] with n hn
  have hdistanceNonneg :
      0 ≤ exponentialProfileDistance (profiles n) limit :=
    exponentialProfileDistance_nonneg _ _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hdistanceNonneg] at hn
  have hterm := exponentialProfileDistance_coordinateTerm_le
    (profiles n) limit coordinate
  change weight * cappedProfileDifference (profiles n coordinate) (limit coordinate) ≤
    exponentialProfileDistance (profiles n) limit at hterm
  have hcapped :
      cappedProfileDifference (profiles n coordinate) (limit coordinate) <
        min epsilon 1 := by
    exact (mul_lt_mul_iff_right₀ hweight).mp (hterm.trans_lt hn)
  have hcappedOne :
      cappedProfileDifference (profiles n coordinate) (limit coordinate) < 1 :=
    hcapped.trans_le (min_le_right _ _)
  have habsLe :
      |(profiles n coordinate : ℝ) - (limit coordinate : ℝ)| ≤ 1 := by
    by_contra hnot
    have hone : 1 ≤
        |(profiles n coordinate : ℝ) - (limit coordinate : ℝ)| :=
      le_of_not_ge hnot
    have : cappedProfileDifference (profiles n coordinate) (limit coordinate) = 1 := by
      exact min_eq_left hone
    linarith
  have hcappedEq :
      cappedProfileDifference (profiles n coordinate) (limit coordinate) =
        |(profiles n coordinate : ℝ) - (limit coordinate : ℝ)| := by
    exact min_eq_right habsLe
  have habs :
      |(profiles n coordinate : ℝ) - (limit coordinate : ℝ)| < epsilon := by
    rw [← hcappedEq]
    exact hcapped.trans_le (min_le_left _ _)
  simpa [Real.dist_eq] using habs

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
          Filter.atTop (nhds (limit coordinate)) := by
  constructor
  · exact exponentialProfileDistance_coordinatewise_of_tendsto_zero
  · exact exponentialProfileDistance_tendsto_zero_of_coordinatewise

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

end ExponentialProfileCompactness

section MatchedBayesBoundary

/-- **Random-design reduction, as a sharp error ledger.**  If each random-design information
density is within `ε` of its scalar matched-channel counterpart, a scalar gap `Δ` survives with
loss at most `2ε`. -/
theorem randomDesign_gap_of_scalarGap
    (scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ epsilon)
    (hright : |randomRight - scalarRight| ≤ epsilon)
    (hgap : scalarRight - scalarLeft = delta) :
    delta - 2 * epsilon ≤ randomRight - randomLeft := by
  have hlowerLeft : randomLeft ≤ scalarLeft + epsilon := by
    have := le_trans (le_abs_self (randomLeft - scalarLeft)) hleft
    linarith
  have hlowerRight : scalarRight - epsilon ≤ randomRight := by
    have := le_trans (neg_le_abs (randomRight - scalarRight)) hright
    linarith
  linarith

/-- In particular a scalar matched-channel gap larger than twice the comparison error forces a
random-design gap. -/
theorem randomDesign_separates_of_scalarGap
    (scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ epsilon)
    (hright : |randomRight - scalarRight| ≤ epsilon)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 2 * epsilon < delta) :
    randomLeft < randomRight := by
  have hbound := randomDesign_gap_of_scalarGap scalarLeft scalarRight randomLeft randomRight
    epsilon delta hleft hright hgap
  linarith

/-- **A positive scalar matched-channel gap survives eventually along every
regime in which the random-design comparison error vanishes.**  This is the
asymptotic completion of the two-error ledger: it makes “all sufficiently large
aspect ratios” precise without hard-coding a particular error formula.

The model-specific work is exactly the convergence of `comparisonError`; no
additional uniformity or hidden constant is assumed here. -/
theorem randomDesign_eventually_separates_of_scalarGap
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta : ℝ)
    (randomLeft randomRight comparisonError : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤ comparisonError index)
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤ comparisonError index)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (herrorVanishing :
      Filter.Tendsto comparisonError regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index := by
  have htwice :
      Filter.Tendsto (fun index ↦ 2 * comparisonError index) regime (nhds 0) := by
    simpa using herrorVanishing.const_mul 2
  have hbelow : ∀ᶠ index in regime, 2 * comparisonError index < delta :=
    htwice.eventually_lt_const hpositive
  filter_upwards [hbelow] with index hthreshold
  exact randomDesign_separates_of_scalarGap
    scalarLeft scalarRight (randomLeft index) (randomRight index)
    (comparisonError index) delta (hleft index) (hright index) hgap hthreshold

/-- **Low-rank perturbations cannot solve the matched scalar problem, conditional only on the
matrix I-MMSE/nuclear-norm estimate.**  Once that estimate bounds the information-density change
by `constant * rank/p`, an `ε` rank fraction gives an `constant * ε` change. -/
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

The matrix I-MMSE inequality remains an explicit model-side premise; the
asymptotic passage from that estimate to invisibility is proved here. -/
theorem matchedDensity_lowRank_tendsto_zero_of_nuclearEstimate
    (densityGap rankFraction : ℕ → ℝ) (constant : ℝ)
    (hrankVanishing : Filter.Tendsto rankFraction Filter.atTop (nhds 0))
    (hnuclear : ∀ index,
      |densityGap index| ≤ constant * rankFraction index) :
    Filter.Tendsto densityGap Filter.atTop (nhds 0) := by
  have hbound :
      Filter.Tendsto (fun index ↦ constant * rankFraction index)
        Filter.atTop (nhds 0) := by
    simpa using hrankVanishing.const_mul constant
  have habs :
      Filter.Tendsto (fun index ↦ |densityGap index|)
        Filter.atTop (nhds 0) :=
    squeeze_zero
      (fun index ↦ abs_nonneg (densityGap index))
      hnuclear hbound
  apply (tendsto_zero_iff_abs_tendsto_zero densityGap).mpr
  simpa [Function.comp_def] using habs

end MatchedBayesBoundary

end TrafficInvariantSeparation

end Calibrator
