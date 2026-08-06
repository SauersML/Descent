/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.CutCount
import Descent.Coalescent.Encoding
import Descent.Coalescent.StepLaw
import Descent.Coalescent.PaintboxFrequency
import Descent.Coalescent.Mutation
import Descent.Meta.Informal
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# What the coalescent group proves, and what it does not

This group formalises Kingman (1982), *The coalescent* (**K-C**) and *On the genealogy of
large populations* (**K-G**).  It does not formalise all of them.  This file is the record
of the difference, in the corpus rather than in a commit message, because an unrecorded gap
reads as a covered one.

## Settled, and where

* The rate ladder `d_k = k(k-1)/2` is a CARDINALITY of the state space, not a formula:
  `StateSpace.card_covers_eq_deathRate`.  K-C (1.6).
* The Wright-Fisher mechanism is explicit and the one-generation rates are counted off it
  within `(d_k/N)²/2`: `WrightFisher.coalescenceProb_le`, `.le_coalescenceProb`.  K-G (2.9).
* `hetRecurrence`, which the corpus previously posited, is that mechanism's pair-survival
  probability: `WrightFisher.hetRecurrence_eq_pairDistinct`.
* The jump chain is a Markov kernel on `𝓔ₙ` whose values are equivalence relations:
  `Kernel.jumpKernel`, `Process.jumpStep_apply_eq_jumpProb`.  K-C (2.2).
* Covers are merges from below and cuts from above: `StateSpace.covers_iff_exists_merge`,
  `Split.covers_iff_exists_splitBy`.
* Restriction is consistent, so sub-samples are coalescents: `Restriction.restrict_restrict`.
  K-G (7.2).
* Transit time, entrance boundary, absorption factor: `Rates`.  K-G (5.7)-(5.13), K-C p.239.
* Ewens (3.8) normalises at `n = 2, 3`: `Mutation.ewensProb_two_total`, `.ewensProb_three_total`.

## The mechanism layer, added after the two papers were covered

The group's first pass proved statements of the form *given this formula, these consequences
follow*.  Seven modules now supply the layer under that -- *this formula follows from this
explicitly defined stochastic mechanism* -- and they are listed together because the point is
the layer, not the seven results.

* `Coalescent.Pedigree` writes down the sentence K-G section 2 defines the subject with: an
  explicit sequence of parent maps, an explicit sample, and `ℛ_s` as the kernel of "who is
  your ancestor `s` generations back".  K-G (2.5), (2.6), (2.7) and the restriction
  consistency of (7.1) then hold PATHWISE, for every pedigree, with no distributional
  hypothesis -- they were never facts about a law.  Randomness enters at exactly one place,
  which pedigree, and `WrightFisher.parentAssignment` is one answer to that.
* `Coalescent.FamilySize` removes the last modelling assumption from the rate.  For an
  arbitrary pedigree map, `Σ_j ν_j = N` (K-G (2.1)) is a theorem about functions rather than
  a constraint on a distribution, the sibling count is `Σ_j ν_j(ν_j - 1)`, and dividing by the
  ordered pairs gives K-G p.35's `Var(ν₁)/(N-1)`.  Its Wright-Fisher instance reproduces the
  `1/N` that `WrightFisher` counts off the uniform parent law by a route that never mentions
  uniformity, and `sameParentCount_id` is the sharp form of what the rate measures: a
  population where every individual has exactly one child has coalescence probability zero at
  any size.  Drift is fertility variance, not finiteness.
* `Coalescent.BranchLength` derives the total length of the tree from the same ladder that
  gives its height, and gets the opposite behaviour: `E(L_n) = 2 a_{n-1}` diverges while
  `E(T_n) = 2 - 2/n` is capped.  `height_bounded_length_unbounded` states the pair.
* `Coalescent.SegregatingSites` puts K-G p.34's Poisson mutation on that tree and reads off
  Watterson's `E(S_n) = θ a_{n-1}`, the unbiasedness of `θ_W`, `E(π) = θ`, and a mean-zero
  Tajima numerator.  Each is a consequence of the branch-length sum, not a separate posit.
* `Coalescent.SiteFrequencySpectrum` adds Fu (1995)'s `E(ξ_i) = θ/i`, ASSERTED because its
  Pólya-urn count is missing, and subjects it to the check the corpus can make: the classes
  sum to the derived tree length.  Two consequences that are derived: the spectrum's shape
  carries no information about `θ`, and singletons are a `1/a_{n-1}` share.
* `Coalescent.VariableSize` removes the constant-size assumption in the standard way
  (Griffiths and Tavaré 1994): a varying size is the same coalescent on the clock
  `τ(t) = ∫₀ᵗ ds/λ(s)`, because every rate in the ladder is divided by the same `λ(t)`
  (`deathRate_mul_deriv_timeChange`).  The exponential history's `τ` is computed and its
  defining ODE `τ' = 1/λ` proved through `deriv`, and the demographic content is one
  inequality, `e^u ≥ 1 + u`: growth speeds the clock, so an expanding population's lineages
  coalesce sooner than a constant one's at every time, uniformly.
* `Coalescent.Duality` supplies the only forward-time statement in the group, and the reason
  any of this describes an allele frequency: `½x(1-x)·(xⁿ)'' = d_n(x^{n-1} - xⁿ)`.  The
  Wright-Fisher diffusion's generator applied to `xⁿ` in `x` IS the coalescent's block-count
  generator applied in `n`, so the forward and backward descriptions are one calculation, and
  the moment hierarchy closes because lineages only merge.

## The classical results the two papers do not contain

Five more modules cover results every coalescent course teaches and neither 1982 paper
states.  Each is anchored to something the corpus already derives, so none of them is a new
constant:

* `Coalescent.AlleleCount` divides out the seating weights `Ewens` had computed and never
  normalised: the `(n+1)`-st sample member opens a new allelic class with probability
  `θ/(θ+n)`, the configuration cancelling between numerator and denominator.  Hence
  `E(K_n) = Σ_{i<n} θ/(θ+i)` (Ewens 1972).  Two bridges: at `θ = 1` this IS `BranchLength`'s
  harmonic number, reached from the mutation side; at `n = 2` it is `2 - 1/(1+θ)`, whose
  `1/(1+θ)` is the identity-by-descent probability `Mutation.tendsto_identityByDescent` proves
  by a geometric sum over coalescence times.
* `Coalescent.ComingDownFromInfinity` supplies the rate the entrance boundary lacked.  The
  descent equation `n' = -n²/2` is verified through `deriv` and its solution `n(t) = 2/t`
  tested against `Rates.tsum_one_div_deathRate_tail`: at the exact mean entrance time
  `2/(k-1)` the curve reads `k - 1`, displaced by exactly the one lineage that `n²` versus
  `n(n-1)` drops.
* `Coalescent.Fixation` answers the forward model's other classical question.  The neutral
  generator kills affine functions, so `u(x) = x`; with a selective drift it kills Kimura's
  `(1-e^{-αx})/(1-e^{-α})`, and the cancellation is exhibited as algebra with both derivatives
  computed.  `selectedFixation_half_gt_half` is the substantive consequence: selection biases
  fixation at every strength, with no threshold.
* `Coalescent.TransitVariance` states what the bounded mean does not say.  `Var(T_n) ≥ 1` for
  every `n` while `E(T_n) < 2`, so `E(T_n)²/4 < Var(T_n)`: the tree height never concentrates,
  at any sample size.  More individuals resolve one tree better; they do not average anything,
  which is why inference runs across loci.
* `Coalescent.GeneTreeDiscordance` derives the incomplete-lineage-sorting probability
  `(2/3)e^{-T}` (Hudson 1983; Pamilo and Nei 1988) from two things the corpus already has: the
  `d_2` exponential survival through the internal branch, and `1 - jumpProb 3`, which is the
  uniform jump chain on the three covers of a three-block state rather than an assumed
  symmetry.  `discordance_gt_half_iff` is the anomaly zone: below `log(4/3)` the modal gene
  tree is one of the two WRONG ones, so a majority vote across loci converges to the wrong
  species tree as the number of loci grows.

## The six gaps this group recorded, and what closed them

An earlier revision of this file listed six areas of coalescent theory the group did not
have.  All six now have modules; what remains in each is a single named theorem rather than
an area, and the difference is worth recording because "absent" and "absent except for one
step" are different states.

* **Fu's Pólya urn** -- CLOSED.  `Coalescent.FuUrn` derives `E(L_i) = 2/i`.  K-C (2.3) times
  the number of set partitions with given class sizes leaves the ordered size vector uniform
  on compositions, so a block subtends `i` leaves with probability `C(n-i-1,k-2)/C(n-1,k-1)`;
  clearing both binomials leaves `Σ_{b≤m} C(a+b,a) = C(a+m+1,a+1)`, the hockey stick, after
  which the factorials cancel to `1/i`.  `SiteFrequencySpectrum`'s `ASSERTED` marker is
  discharged.
* **Second moments of the spectrum** -- CLOSED, both sides.  `Coalescent.SpectrumMoments`
  proves `Var(S_n) = θ a_{n-1} + θ² b_{n-1}` by the law of total variance, with `Var(L_n) = 4
  b_{n-1}` from the squared segment lengths and `b` bounded while `a` diverges,
  so Watterson's estimator is consistent at rate `1/log n`; `Coalescent.HoldingSecondMoment`
  removes the last quoted constant by integrating K-C (1.7)'s density twice (`Γ(3) = 2!`).
  `Coalescent.PairwiseTimes` and `Coalescent.TajimaVariance` then close `Var(π)`.  Restriction
  consistency puts two pairs sharing a lineage in a three-sample and two disjoint pairs in a
  four-sample; enumerating topologies gives `Cov(T,T') = 1/3` and `E(S) = 1` for the first,
  `2/9` and `2/3` for the second, and the counts `n(n-1)(n-2)/2` and `n(n-1)(n-2)(n-3)/8`
  assemble them into Tajima (1989)'s
  `(n+1)/(3(n-1)) θ + 2(n²+n+3)/(9n(n-1)) θ²` exactly.  The `n²+n+3` that looks arbitrary in
  the published formula is `9 + 6(n-2) + (n-2)(n-3)`: one term per pair class.

  Worth recording because the corpus caught it: an earlier pass asserted that DISJOINT pairs
  never share tree, which is true of the pairing that respects the cherries and false of the
  other two.  It would have made the `θ` coefficient vanish like `2/n` instead of tending to
  `1/3`.  The enumeration found it.
* **Möhle's lemma** -- CLOSED as K-G (2.14), the semigroup limit.
  `Coalescent.Convergence` proves the entrywise limit `p_N(k)^N → e^{-d_k}` for every `k`;
  `Coalescent.SemigroupLimit` proves the operator statement in the generality Kingman states
  it -- for any complete normed algebra, any `Q`, and any contractions `P_N` within `C/N²` of
  `exp(N⁻¹Q)`, the `N`-th powers converge to `exp Q`.  `Generator`'s contraction estimate does
  the accumulation and `exp(N⁻¹Q)^N = exp Q` is exact, so there is no continuity argument at
  all: the whole limit lives at `t = 1`, which is what "`N` generations are one coalescent
  unit" means.  `Coalescent.PairChainLimit` then instantiates it for the case the group is built on,
  and
  does so without ever exponentiating a matrix.  The two-state generator satisfies `Q² = -Q`
  -- that IS a `Q`-matrix on two states -- and from that one identity every power of `1 + aQ`
  has a closed form, so the comparison family `1 + (1-e^{-1/N})Q` is a semigroup by algebra
  rather than by exponentiation.  That is why `tendsto_pow_of_close` was stated with the
  comparison family left open.  The conclusion is
  `(1 + N⁻¹Q)^N → 1 + (1 - e^{-1})Q`, whose coefficient is the chance two lineages have met
  in one coalescent unit -- the operator statement of what
  `Convergence.tendsto_pairDistinct_pow` counts off the parent law.  `Coalescent.ExpRemainder` then
  removes the ANALYTIC obstacle to the many-state case, which
  was a gap in Mathlib rather than in genealogy: `‖exp x - 1 - x‖ ≤ e^{‖x‖} - 1 - ‖x‖` in any
  Banach algebra, hence `≤ ‖x‖²` on the unit ball, proved by peeling two terms off the
  exponential series and comparing it with itself.  Mathlib had that bound only for `ℝ` and
  `ℂ`.  `Coalescent.BlockCountMatrix` then counts the row.  The classical route is the occupancy
  distribution -- Stirling numbers times a falling factorial -- and the corpus has no Stirling
  numbers and does not need them: a generation dropping two lineages has two DISTINCT colliding
  pairs (`exists_two_collisions`, whose proof is that a single repeated pair leaves `f`
  injective off one point), each prescribed pair of pairs has at most `N^{k-2}` witnesses
  (`card_two_collisions_le'`, five overlap cases), and a union bound over the `≤ k⁴` quadruples
  gives `twoDropProb_le`: the chance of dropping two or more is at most `k⁴/N²`.  With
  `WrightFisher.coalescenceProb_le` on the diagonal, that is every entry of the row to the
  order K-G (2.11) asks for.  `Coalescent.BlockMatrixLimit` assembles them: the entries become a
  `Matrix` in the row-sum
  norm (K-G (2.12)'s norm, scoped in Mathlib as `Matrix.Norms.Operator`), each row is a
  probability distribution so the operator is a contraction, and `row_diff_bound` puts the row
  within `(d_k/N)² + 2k⁴/N²` of `1 + N⁻¹Q` -- the diagonal from `WrightFisher`'s sandwich, the
  tail from `twoDropProb_le`, and the subdiagonal by subtraction since the row sums to one.
  That is K-G (2.11) for the block-count chain.  `tendsto_blockOperator_pow` then CLOSES the
  many-state case outright: `P_N^N -> exp Q`, K-G (2.14) for the whole block-count chain, with
  every hypothesis a theorem rather than an assumption.  The last one to fall was `‖exp(tQ)‖
  ≤ 1`, obtained by uniformisation -- `blockGenerator_eq_smul` factors `Q = d_n(S - 1)` through
  the stochastic `S = 1 + Q/d_n`, and `SemigroupLimit.norm_exp_smul_sub_one_le_one` turns that
  into a contraction semigroup in any Banach algebra.  That in turn needed `‖exp x‖ ≤ e^{‖x‖}`,
  which Mathlib does not state; `ExpRemainder.norm_exp_le_exp_norm` is the second gap this
  group has had to close there.  `Coalescent.MohleLemma` then closes the other shape a
  transition operator comes in.  `mohle_limit`: if `P_N = A + N⁻¹B + O(N⁻²)` with `A` a
  PROJECTION rather than the identity -- diploidy, strong selfing, subdivision with fast
  internal migration -- then `P_N^N → A·exp(ABA)`.  The `ABA` is derived, not posited, and the
  reason is one line: `(1 - A)P_N = (1 - A)(P_N - A)`, because `A - A² = 0`.  Whatever the
  fast dynamics does outside the projection's range it does immediately and once, so only the
  part of `B` carrying the range back to itself can accumulate over `N` generations.  Kingman
  is `A = 1`, where `ABA = B` and this degenerates to K-G (2.14): the projection is trivial
  exactly when nothing happens on the fast scale.
* **The lookdown construction** -- CLOSED for what it is for, with its clocks.
  `Coalescent.Lookdown` proves the level structure's consistency pathwise: below the cut
  restriction commutes with looking down, at or above it the operation is invisible.  That is
  why all `n` coalescents fit on one space without a projective limit.
  `Coalescent.LookdownClocks` supplies the driving clocks from `CompetingRates`: the covers of
  `Δ` are the `C(n,2)` pairs of levels, `C(n,2)` unit-rate clocks survive to `t` with probability
  `e^{-d_n t}`, and the density of "this pair at this time" factorises with the
  same first factor for every pair -- minimum exponential at rate `d_n`, argmin uniform.
  The path-level law is NOT re-derived for levels, and deliberately: at `Δ` the covers ARE the
  pairs (`NeutralMutation.card_covers_delta`), so `Law.coalescentLaw` transported along that
  bijection is the lookdown's path law, and writing it out would be a second name for one
  object -- the failure mode this corpus exists to prevent.  The item is closed by declining
  to duplicate, not by an absence.
* **Spatial coalescents** -- CLOSED at the mechanism, and the walk's criterion counted.
  `Coalescent.PolyaCriterion` counts the returning paths -- `4^n` step-sets, `C(2n,n)` of them
  balanced, so `P(S_{2n}=0) = C(2n,n)/4^n` -- and proves the series diverges, which is Pólya's
  criterion in one dimension.  A return IS a coalescence by `SpatialCoalescent`'s iff, so the
  dependency is now one implication (the renewal identity turning divergence into almost-sure
  return) rather than the whole question.  Below, the mechanism.  `Coalescent.SpatialCoalescent`
  proves
  the voter-model duality `c_t = c₀ ∘ A_t` by induction, presents the dual AS a pedigree so
  that `Pedigree`'s structure theorems transfer unchanged, and reduces pairwise coalescence to
  a hitting time via `walk_sub`.  STILL ABSENT: recurrence of the difference walk, hence
  whether spatial lineages coalesce at all in a given dimension -- a theorem about random
  walks, not about genealogy.

Everything above compiles against the pinned Mathlib.  The build found eight defects in this
batch that re-reading had not, of which the instructive ones were `deriv_pow` having a
`DifferentiableAt` hypothesis and a shape nothing like the one written from memory, and two
hypotheses in `ComingDownFromInfinity` that were never used -- `2/(2/x) = x` holds at `x = 0`
too, because division by zero is zero.

## The process, finally

`Coalescent.TrajectoryLaw` builds the jump chain as a measure on INFINITE trajectories, via
Mathlib's Ionescu-Tulcea theorem.  Until it, every "almost surely" in this subject was
unavailable to the corpus: `Kernel` had one step, `Trajectory` had finite lists, `Law` had a
finite path coupled to a clock, and none of them could quantify over time.

`Program` had scoped Ionescu-Tulcea before and concluded it "avoids Kolmogorov's topological
hypotheses and not the missing simplex measure".  That verdict was right about the PAINTBOX,
whose kernel needs `𝒫_k` on the simplex, and wrong about the JUMP CHAIN at finite `n`, whose
kernel is `Kernel.jumpKernel` and needs no simplex at all.  The distinction had not been
drawn; drawing it is what unblocked this.

`Coalescent.EntranceLaw` then builds the clock -- an infinite product of `HoldingTime`'s
holding-time laws, one per level -- and takes the step the corpus had been unable to take:
Tonelli exchanges the sum and the integral, each coordinate's mean is `γ_k⁻¹`, and a
nonnegative series with summable means is finite almost everywhere.  So

  **a coalescent satisfying Schweinsberg's condition comes down from infinity in finite time,
  almost surely** (`ae_totalDescentTime_lt_top`), and Kingman's does
  (`kingman_ae_comesDownFromInfinity`).

That is the forward direction of the equivalence, and the statement K-C (2.8) and K-G (6.1)
rely on when they start the death process from infinity -- which the corpus previously had
only in expectation.  `Coalescent.LaplaceTransform` and `Coalescent.TransitTransform` then supply
the instrument
the converse runs on, and a headline of the paper the corpus lacked: the clock's transform is
`d/(d+θ)`, and independence of the coordinates -- `iIndepFun_infinitePi`, which is K-C
(1.12)'s premise proved of the construction rather than assumed -- makes the transit time's
transform their product,

  `E(e^{-θ Σ τ}) = ∏ d_r/(d_r + θ)`,     K-G (5.9),

from which K-G reads off the density `Rates.transitDensityTerm` sums.  `Coalescent.ThreeSeries` then
closes the converse and with it the equivalence.  At `θ = 1`
the product is `∏(1 - (γ_k+1)⁻¹) ≤ exp(-Σ(γ_k+1)⁻¹)`, which vanishes when the reciprocals
diverge; the clock is almost surely positive, so the truncated transforms decrease; monotone
convergence carries the vanishing inside the integral, and a nonnegative function with zero
integral is zero almost everywhere.  A vanishing `e^{-S}` is an infinite `S`.  So

  **the descent time is almost surely finite exactly when `Σ γ_k⁻¹` converges**
  (`ae_descent_dichotomy`),

with Kingman on one side and the star coalescent on the other, both proved.  `DecreaseRate` then
separates the two rates the multiple-merger case confuses.
`Lambda.totalRate` is the rate of LEAVING a level, `decreaseRate` is Schweinsberg's expected
rate of DECREASE, and `totalRate_le_decreaseRate` is the correction in one line: every merger
destroys at least one block, so `λ_b ≤ γ_b`.  Hence
`comesDownFromInfinity_of_summable_totalRate`: the corpus's level-by-level condition
`Σ λ_b⁻¹ < ∞` implies Schweinsberg's `Σ γ_b⁻¹ < ∞` and not conversely, so what
`ThreeSeries` proves is coming down under a STRICTLY STRONGER hypothesis.  The gap is exactly
the levels a multiple merger skips: a jump from `b` to `b-k+1` pays one sojourn where the
level sum charges `k-1`.  With only pairwise mergers the two rates coincide
(`decreaseRate_eq_totalRate_of_binary`), and Kingman is that case (`kingman_rates_eq`), which
is why everything else in this group is exact rather than approximate.  STILL ABSENT:
Schweinsberg's theorem proper, that the weaker condition suffices, which is a comparison
argument on the process rather than a sum over levels -- NOW CLOSED by
`Coalescent.SchweinsbergBound`, whose `meanTime_le_sum` proves `h(b) ≤ Σ_{j=2}^b γ_j⁻¹` by
strong induction on the mean-time recursion, the step being an exact cancellation: the sojourn
a multiple merger does not pay is paid by the levels it skips, since `Σ_k (k-1) p_{b,k} =
γ_b/λ_b`.  What it assumes is the recursion itself, that `p` is a distribution, and that `γ` is
non-decreasing; and Pólya's renewal identity -- NOW REDUCED by
`Coalescent.RenewalCriterion`, which proves the whole deduction from the identity to certain
return with no probability in it: summing `uₙ = Σ f_k u_{n-k}` over `n ≤ N` and exchanging the
order gives `U_N ≤ u₀ + q·U_N`, so a first-return mass `q < 1` bounds the partial sums and
forces summability, and `not_summable_returnProb` therefore forces `q = 1`.  What remains is
the identity itself, which
needs a walk on `ℤ` with its strong Markov property.

## Beyond Kingman

The two 1982 papers are not the whole of coalescent theory, and the group no longer stops
there.  `Coalescent.Lambda` places Kingman inside Pitman's family (*Coalescents with multiple
collisions*, Ann. Probab. 27, 1999; independently Sagitov, J. Appl. Prob. 36, 1999): any `k`
of `b` blocks merge at rate `∫ x^{k-2}(1-x)^{b-k} Λ(dx)`, and Kingman is the `Λ = δ₀` fibre
(`lambdaRate_dirac_zero`).  Pitman's consistency condition
`λ_{b,k} = λ_{b+1,k} + λ_{b+1,k+1}` is what makes the family a family, and the integral form
satisfies it (`lambdaRate_consistent`).  A consequence worth its own name: consistency FORCES
the pair rate to be sample-size independent, so K-C (1.3)'s `1` is not a modelling choice
(`eq_kingmanRate`).

`Coalescent.MultiMerge` gives the state space the moves that family needs -- `mergeSet` folds
any set of blocks onto one, and `blocks_mergeSet` says `|S|` blocks become one -- with
`StateSpace.merge` recovered as the two-element case.  So `𝓔ₙ` now carries multiple-merger
coalescents as well as Kingman's, and `Descent.Blindness.MultipleMergerBlindness`, which had
the rates but no state space, has one.

`Coalescent.Xi` goes one further, to Schweinsberg's simultaneous multiple mergers
(Electron. J. Probab. 5, 2000), and finds the general shape of a coalescent move on the way:
every merger is an IDEMPOTENT MAP on blocks, and the block count afterwards is `|range f|`
(`blocks_mergeIdem`).  `merge` and `mergeSet` are then literally instances.

`Coalescent.Recombination` adds Hudson's ancestral recombination graph (Theor. Popul. Biol.
23, 1983) at the level of its competing rates, with the pairwise `1/(1+ρ)`.
`Coalescent.Structured` adds Notohara's structured coalescent (J. Math. Biol. 29, 1990) and
Strobeck's invariance: within-deme coalescence time is `2` whatever the migration rate, so
`F_ST = 1/(1+2M)` has to be built from the DIFFERENCE of the two times.

Kingman's coalescent is now simultaneously the `Λ = δ₀` fibre, the identity-map fibre, and
the `ρ = 0` fibre -- three generalisations, each recovering the base development exactly.

`Coalescent.SeedBank` adds dormancy (Blath, González Casanova, Kurt and Spanò, J. Appl.
Prob. 50, 2013) and puts it beside `Structured` for the contrast: migration leaves the
coalescence time at the panmictic value, dormancy strictly inflates it, and the reason is
that migration moves a lineage somewhere it can still coalesce while dormancy moves it
somewhere it cannot.  `Coalescent.Selection` adds the ancestral selection graph of Krone and
Neuhauser (Theor. Popul. Biol. 51, 1997) at the same rate level, with the fact that makes
Kingman's model robust: coalescence is quadratic in the lineage count and branching is
linear, so their ratio `σ/(k-1)` vanishes as the sample grows.

`Coalescent.Beta` closes the other end of Pitman's family: the Beta-coalescents
`Λ = Beta(2-α, α)` of Schweinsberg (Stoch. Proc. Appl. 106, 2003), whose consistency is a
two-line identity about the Beta function itself, `B(a,b) = B(a+1,b) + B(a,b+1)`.  Read at
the rates that identity IS Pitman's condition.  At `α = 1` it gives the Bolthausen-Sznitman
rates `(k-2)!(b-k)!/(b-1)!`, which `Descent.Blindness.MultipleMergerBlindness` already
studies through its own chart -- that file asks which statistics can see `Λ`, and this one
says why the family it is looking at is a family.

`Coalescent.XiRates` supplies the language Schweinsberg's rates are indexed by: a merger's
SHAPE, the multiset of merging group sizes.  The block count a shape costs is `Σ(kᵢ - 1)`,
and the three families are nested by a condition on shapes rather than by three definitions
-- Kingman's shapes are `{2}`, `Λ`'s are the singletons `{k}`, `Ξ`'s are the rest.

Still absent, and not claimed: the measure `Ξ` on the infinite simplex and the integral
assigning a rate to each shape -- that needs an infinite-dimensional measure the corpus does
not have, and `XiRates` provides only the index set it would be a function on.  Likewise the
forward resolution of the ASG that decides which parent was real, which is a different
process rather than a harder case of this one.

## What Mathlib does and does not have, checked

The open items below are open because of missing foundations, and twice this session I
asserted that without looking.  Both times I was wrong -- once about an algebraic identity
the compiler then broke, once about `Coalescent.Uniqueness`, which turned out to be
available.  So the claims are now grepped rather than remembered, against the pinned
revision:

* **de Finetti / exchangeable measures**: absent.  No `deFinetti`, `DeFinetti` or
  `Exchangeable` anywhere in Mathlib.  Item 3's converse has no foundation to sit on.
* **Reverse martingale convergence**: absent, and it is worth naming the missing theorem
  exactly rather than the missing area.  `Probability/Martingale/Convergence.lean` HAS
  Lévy's UPWARD theorem -- `Integrable.tendsto_ae_condExp`, `E[g | 𝓕ₙ] → E[g | 𝓕_∞]` along an
  INCREASING filtration -- together with the upcrossing estimates and
  `Submartingale.ae_tendsto_limitProcess` behind it.  What is absent is Lévy's DOWNWARD
  theorem: convergence of `E[g | 𝓖ₙ]` along a DECREASING filtration to `E[g | ⋂ₙ 𝓖ₙ]`.  That
  is precisely the statement K-C's Theorem 2 uses (he cites Doob VII.4.25), and it is the
  single Mathlib lemma that would unblock the paintbox representation.  A reader wanting to
  finish item 3 should start there, not with de Finetti.

  One shortcut is worth ruling out before anyone spends a day on it.  `Filtration` is
  parameterised by an arbitrary `Preorder`, and Mathlib does instantiate it at an order dual
  elsewhere (`cylinderEventsCompl : Filtration (Finset α)ᵒᵈ`), so a decreasing filtration is
  expressible as `Filtration ℕᵒᵈ`.  But the convergence results are not: every theorem in
  `Martingale/Convergence.lean` fixes `ℱ : Filtration ℕ m0` and argues along `atTop` with upcrossing
  counts, and the downward theorem is not that argument dualised -- it turns on a
  reversed martingale being automatically uniformly integrable, which the forward proof never
  needs.  It is a separate development, not an instantiation.
* **Kolmogorov extension, general form**: absent.  `ProjectiveFamilyContent` and
  `ClosedCompactCylinders` exist and name it as their goal, but the existence theorem for a
  general consistent family is not there.  `IsProjectiveLimit.unique` IS, which is what
  `Uniqueness` used.
* **Ionescu-Tulcea**: PRESENT, in `Probability/Kernel/IonescuTulcea/Traj.lean` -- it builds a
  measure on infinite trajectories from a sequence of kernels without Kolmogorov's
  topological hypotheses.  This entry previously called it "the most promising unexplored
  route" to Theorem 3.  Scoping it properly retracts that.  Ionescu-Tulcea needs the kernels,
  and the kernel from `ℛ_k` to `ℛ_{k+1}` is a SPLITTING kernel whose probabilities are K-C
  (3.19)'s Dirichlet structure -- that is, the paintbox measure `𝒫_k` on the simplex.  So it
  avoids Kolmogorov's topological hypotheses and not the missing simplex measure: the same
  obstacle, one layer down.  Recorded because an optimistic claim in a ledger is worse than
  none, and this one was mine.

## Verification status

Every module in this group compiles against the pinned Mathlib
(`lake build Descent.Coalescent.*`, 58 modules, 3370 jobs, clean).  That is worth recording because
it was not true for most of this group's life, and because of what the first build found.

Six defects had been caught by re-reading, over many passes.  The first ten minutes of
compilation found more than that, including the only one that was mathematically wrong
rather than syntactically wrong:

* **A factor of two in `JumpChain.jumpCoeff_recursion`.**  The claim was
  `jumpCoeff n k · (n-k+1) / d_k = jumpCoeff n (k-1)`; the left side is TWICE the right.
  It had been checked by hand twice and described in its own docstring as "the arithmetic
  half of Kingman's displayed calculation".  The corrected form is multiplicative and
  avoids dividing by `d_k` at all.
* `WrightFisher`'s Bonferroni lemmas assumed `a_i ≤ 1` for every `i`, which is false for
  `i/N` once `i > N`.  The bound is only needed on `range k`, and that is now what they ask.
* Three `import`s that do not exist, written from memory.
* A missing `MeasurableSpace` instance underneath every measure in `Law`.
* `subst` eliminating the wrong variable, in three different files.
* `ring` on a normed ring, which is not commutative.

The lesson the group records is not that the mathematics was wrong -- almost all of it was
right -- but that the one place it was wrong was invisible to every amount of careful
reading, and visible to the kernel immediately.

## The five hard items, and where each stands

**1. The split count.**  SETTLED, `CutCount.card_covers_below`:
`#{ξ ; ξ ≺ η} = Σ_c (2^{λ_c - 1} - 1)`.  The route was to stop dividing by two.
`Split.splitBy_compl` shows each cut is named twice; `CutSets` breaks the tie with each
class's representative so a cut set names each state once; counting cut sets is then
counting subsets.  `sum_choose_interior_eq_two_mul_cutCount` below checks the total against
Kingman's `Σ_ν ½C(λ,ν)`.

**2. Ewens normalisation for general `n`.**  SETTLED, `Ewens.sum_ewensWeight`:
`Σ_{ξ ∈ 𝓔ₙ} θ^{|ξ|-1} ∏(λ_a - 1)! = (θ+1)⋯(θ+n-1)`, by the Chinese restaurant.  `Extend`
gives the fibre of restriction as `Option (Quotient ξ)`; seating multiplies the weight by
`θ` or by `λ_c`; `sum_classSize` turns the class sum into `n`.

**3. K-C Theorem 2, the paintbox representation.**  HALF SETTLED.  That a paintbox HAS
asymptotic frequencies, and that they are its own parameters, is
`PaintboxFrequency.tendsto_colourFrequency` -- K-C (3.8) by the strong law.  `Paintbox`
also proves the construction permutation-equivariant, which is the exchangeability that
needs no probability.  OPEN: the converse, that every exchangeable random equivalence
relation is a paintbox mixture.  K-C proves it by reversed martingale convergence (Doob
VII.4.25) and nothing in this corpus is close to it.

**4. K-C Theorem 1, independence of the jump chain and the death process.**  ONE STEP
SETTLED.  `CompetingRates`: unit rate on each cover makes the survivals multiply to
`e^{-d_k t}` (`prod_survival_covers`), and the joint density of "cover `η` at time `t`"
factorises as `(1/d_k) · d_k e^{-d_k t}` (`jointDensity_factors`), the same first factor for
every cover.  A density that splits is independence.  `Trajectory.chainLaw_head_blocks` adds
the structural reason it can hold at all: after `k` jumps the block count is `n - k` on every
trajectory, so the death process learns nothing from it.  The induction over steps is
`CompetingRates.pathDensity_factors`: the path's density is a product of one-step densities,
and a product of factorised terms factorises, so the whole path's density splits into a
trajectory factor and a clock factor.  For ONE step the passage from a factorised
density to independent random objects is `StepLaw`: `stepLaw_prod` is independence as a
statement about measures rather than densities, and the density it corresponds to is the one
competing clocks produce, so the arranged product is the right one.  For the WHOLE path the same
passage is
`Law.coalescentLaw_prod`, which is independence in measure for the coupled trajectory and
clock.  So the constructive direction is complete: densities factorise, one step factorises
in measure, the whole path factorises in measure.  OPEN, and now the only thing open in this
item: the CONVERSE, that an arbitrary `n`-coalescent -- one given by its rates rather than
built as a product -- factorises with independent factors.  That is Theorem 1 proper, and it
needs the general theory of jump chains for continuous-time Markov chains, which Mathlib does
not have.

**5. K-G section 6 and K-C Theorem 3, the constructions.**  FINITE `n` SETTLED.
`Trajectory.chainLaw` is a law on whole trajectories, with K-C (1.13) as
`chainLaw_support_chain'` and `chainLaw_head_eq_top`; `Path` turns a trajectory and holds
into `R_t = ℛ_{D(n,t)}` with `|R_t| = D(n,t)` (K-G (6.6)) and the death process pinned down
pathwise (`blockCountAt_eq`, K-C (2.6)); `Law` couples them; `HoldingTime` supplies K-C
(1.7)'s clock and proves both its integrals, so `E(T_n) = 2 - 2/n` runs from the density.
`Infinite` proves `𝓔` is the projective limit of the `𝓔ₙ` as a set, so specifying a process
by its restrictions is well posed.  `Encoding` supplies the measurable structure K-C
section 3 gets from viewing `𝓔` inside `2^{ℕ×ℕ}`: the embedding is injective, the σ-algebra
is the pullback, and every `ρ_n` is measurable -- so "the finite-dimensional distributions of
a process on `𝓔`" is now a well-formed phrase.  OPEN: the extension of a consistent family of
MEASURES to `n = ∞`, Theorem 3's Kakutani-Nelson step.  It is open for a stated reason -- a
theorem about measures -- rather than for want of a space to state it in.

Nothing above is asserted where it is open.  Where a result depends on an open item, the
dependence is a written hypothesis.

## Open, and why -- as objects rather than as this prose

EVERY "OPEN" AND "STILL ABSENT" ABOVE IS ALSO AN OBJECT BELOW.  The prose stays, because it
carries the argument and the objects carry only the claim, but the prose alone had the
failure mode this whole file is written against: it could not be counted, could not be
cited, and could not become false.  `Descent.Meta.Informal`'s `informal_lemma` and
`informal_definition` record each open item with a stable tag and the fully qualified names
it WAITS ON, add no constant to the environment, and let `#informal_report` answer the
question the prose cannot -- which of these has acquired all of its prerequisites since it
was written.

The dependency chains matter more here than anywhere else in the corpus, because this
group's open items are not independent.  Pólya's renewal identity waits on a strong Markov
property for a walk on `ℤ`; spatial coalescence waits on the renewal identity; Theorem 2
waits on Lévy's DOWNWARD martingale theorem and on nothing else, which is the single most
useful sentence in this section and was, until now, a sentence.  A reader who wants to know
what to work on next reads the chain, not the paragraphs.

Three retractions in this file also become objects.  Two are the Ionescu-Tulcea entry's own
corrections of earlier optimistic claims, and one is a mathematical error the enumeration
caught.  All three are recorded with `withdrawn`, which is the command form for a retracted
instruction that named no declaration -- which is most of them.

## Main results

- `sum_choose_interior_add_two`: `Σ_{ν=1}^{λ-1} C(λ,ν) = 2^λ - 2`.
- `two_mul_cutCount_add_two`: so the cuts of a `λ`-class number `2^{λ-1} - 1`, which is the
  `½` in `½ C(λ, ν)` summed.
-/

namespace Coalescent

open Finset

/-! ### The open items, as objects

Each carries the tag it will be cited by, and the names it waits on.  A dep that is already
a constant is closed; one that is not is either an object below or a piece of mathematics
nobody has written.  Nothing here adds a declaration, so no result in this group can rest
on any of it. -/

/-- **Lévy's DOWNWARD martingale convergence theorem**, the single Mathlib lemma that
unblocks the paintbox representation.

`Probability/Martingale/Convergence.lean` has Lévy's UPWARD theorem,
`Integrable.tendsto_ae_condExp`, along an INCREASING filtration, together with the
upcrossing estimates behind it.  What is absent is convergence of `E[g | 𝒢ₙ]` along a
DECREASING filtration to `E[g | ⋂ₙ 𝒢ₙ]`, which is what K-C's Theorem 2 uses (he cites Doob
VII.4.25).

The shortcut is ruled out and the ruling-out is the content.  `Filtration` is parameterised
by an arbitrary `Preorder` and Mathlib does instantiate it at an order dual, so a decreasing
filtration is expressible as `Filtration ℕᵒᵈ`.  The convergence results are not: every
theorem there fixes `Filtration ℕ` and argues along `atTop` with upcrossing counts, and the
downward theorem turns on a reversed martingale being automatically uniformly integrable,
which the forward proof never needs.  It is a separate development, not an instantiation.

It waits on nothing in this corpus. -/
informal_lemma "coalescent-levy-downward"
  Descent.Coalescent.tendsto_condExp_of_antitone
  []

/-- **K-C Theorem 2, the converse: every exchangeable random equivalence relation is a
paintbox mixture.**

The forward half is done.  `tendsto_colourFrequency` is K-C (3.8) by the strong law -- a
paintbox HAS asymptotic frequencies and they are its own parameters -- and
`paintboxRel_perm` is the permutation equivariance, which is the exchangeability that needs
no probability.

The converse is what is open, and it has exactly one prerequisite: the downward martingale
theorem above.  Not de Finetti, which is also absent from Mathlib and is the wrong place to
start; K-C proves this by reversed martingale convergence directly. -/
informal_lemma "coalescent-KC-thm2-paintbox-converse"
  Descent.Coalescent.exchangeable_isPaintboxMixture
  [Descent.Coalescent.tendsto_colourFrequency,
   Descent.Coalescent.paintboxRel_perm,
   Descent.Coalescent.tendsto_condExp_of_antitone]

/-- **The jump chain of a general continuous-time Markov chain.**

The constructive direction of K-C Theorem 1 is complete: densities factorise
(`pathDensity_factors`), one step factorises in measure (`stepLaw_prod`), and the whole
path factorises in measure (`coalescentLaw_prod`).  All three are about a process BUILT as
a product.

Theorem 1 proper is the converse, about a process given by its RATES, and it needs the
general theory this definition names: the embedded jump chain of a continuous-time Markov
chain, and the holding times it is independent of.  Mathlib has no such construction, and
this is the object the converse below is a statement about. -/
informal_definition "coalescent-jump-chain-of-markov-chain"
  Descent.Coalescent.jumpChainOfMarkovChain
  [Descent.Coalescent.jumpKernel]

/-- **K-C Theorem 1, the converse: an `n`-coalescent given by its rates factorises with
independent factors.**

`chainLaw_head_blocks` is the structural reason it can hold at all -- after `k` jumps the
block count is `n - k` on every trajectory, so the death process learns nothing from the
chain -- and it is proved.  What is missing is not a coalescent fact but a Markov-chain
fact, which is why this waits on the jump-chain construction and not on anything in this
group. -/
informal_lemma "coalescent-KC-thm1-independence-converse"
  Descent.Coalescent.coalescent_factorises_of_rates
  [Descent.Coalescent.coalescentLaw_prod,
   Descent.Coalescent.stepLaw_prod,
   Descent.Coalescent.chainLaw_head_blocks,
   Descent.Coalescent.jumpChainOfMarkovChain]

/-- **The projective limit of a consistent family of measures on `𝓔ₙ`.**

`Infinite` proves `𝓔` is the projective limit of the `𝓔ₙ` AS A SET, and `Encoding` supplies
the measurable structure by embedding `𝓔` in `2^{ℕ×ℕ}`: the embedding is injective, the
σ-algebra is the pullback, and every `ρₙ` is measurable.  So "the finite-dimensional
distributions of a process on `𝓔`" is a well-formed phrase and the space is there.

What is absent is the extension theorem itself.  Mathlib has `ProjectiveFamilyContent` and
`ClosedCompactCylinders`, which name this as their goal, and `IsProjectiveLimit.unique`,
which is what `Uniqueness` used -- but not the existence theorem for a general consistent
family. -/
informal_definition "coalescent-projective-limit-measure"
  Descent.Coalescent.projectiveLimitMeasure
  [Descent.Coalescent.encode_injective]

/-- **K-C Theorem 3 and K-G section 6: the construction at `n = ∞`.**

Finite `n` is settled -- `chainLaw` is a law on whole trajectories, `Path` turns a
trajectory and holds into `R_t` with the death process pinned down pathwise, `Law` couples
them.  Open is the Kakutani-Nelson step, the extension of a consistent family of MEASURES
to `n = ∞`, and it is open for a stated reason: a theorem about measures, not the want of a
space to state it in. -/
informal_lemma "coalescent-KC-thm3-kakutani-nelson"
  Descent.Coalescent.extend_consistent_coalescent_measures
  [Descent.Coalescent.chainLaw,
   Descent.Coalescent.encode_injective,
   Descent.Coalescent.projectiveLimitMeasure]

/-- **The strong Markov property of a random walk on `ℤ`.**

Absent from the corpus, and the reason the renewal identity below is not simply proved.  It
waits on nothing here. -/
informal_lemma "coalescent-strong-markov-walk"
  Descent.Coalescent.strongMarkov_of_randomWalk
  []

/-- **Pólya's renewal identity, `uₙ = Σ_k f_k u_{n-k}`.**

`RenewalCriterion` proves the whole deduction FROM the identity with no probability in it:
summing over `n ≤ N` and exchanging the order gives `U_N ≤ u₀ + q·U_N`, so a first-return
mass `q < 1` bounds the partial sums and forces summability, and `not_summable_returnProb`
therefore forces `q = 1`.  `PolyaCriterion` supplies the divergence by counting returning
paths.

What remains is the identity itself -- that the walk restarts at a first return -- which is
the strong Markov property above and nothing else. -/
informal_lemma "coalescent-polya-renewal-identity"
  Descent.Coalescent.renewalIdentity
  [Descent.Coalescent.returnProb,
   Descent.Coalescent.sum_le_of_renewal,
   Descent.Coalescent.not_summable_returnProb,
   Descent.Coalescent.strongMarkov_of_randomWalk]

/-- **Recurrence of the difference walk, hence whether spatial lineages coalesce at all.**

`SpatialCoalescent` proves the voter-model duality by induction, presents the dual AS a
pedigree so that `Pedigree`'s structure theorems transfer unchanged, and reduces pairwise
coalescence to a hitting time via `walk_sub`.  A return IS a coalescence by that iff, so
what is left is a theorem about random walks and not about genealogy: almost-sure return in
one dimension, which is the renewal identity applied to the divergence
`PolyaCriterion` already proves. -/
informal_lemma "coalescent-spatial-difference-walk-recurrence"
  Descent.Coalescent.recurrent_differenceWalk
  [Descent.Coalescent.walk_sub,
   Descent.Coalescent.not_summable_returnProb,
   Descent.Coalescent.renewalIdentity]

/-- **A measure on the infinite simplex.**

Needed for `Ξ`, and absent: the corpus has no infinite-dimensional measure at all.  This is
also the obstacle one layer under Ionescu-Tulcea for the paintbox kernel, which is the
correction the `withdrawn` note below records. -/
informal_definition "coalescent-infinite-simplex-measure"
  Descent.Coalescent.infiniteSimplexMeasure
  []

/-- **Schweinsberg's `Ξ`: the measure on the infinite simplex, and the integral assigning a
rate to each merger shape.**

`XiRates` supplies the index set such a function would be defined on -- a merger's SHAPE,
the multiset of merging group sizes, with `shapeDrop` the block count it costs -- and `Xi`
supplies the state-space move, every merger being an idempotent map on blocks.  What is
absent is the measure, and with it the integral.  `XiRates` provides only the index set,
which the file says and this records. -/
informal_definition "coalescent-xi-measure"
  Descent.Coalescent.xiRateOfShape
  [Descent.Coalescent.shapeDrop,
   Descent.Coalescent.blocks_mergeIdem,
   Descent.Coalescent.infiniteSimplexMeasure]

/-- **The forward resolution of the ancestral selection graph.**

`Selection` adds Krone and Neuhauser's ASG at the rate level, with the fact that makes
Kingman's model robust: coalescence is quadratic in the lineage count and branching linear,
so their ratio vanishes as the sample grows.  What is absent is the forward step deciding
which parent was real, and it is absent for a reason worth keeping separate from the
others -- it is a DIFFERENT PROCESS, not a harder case of this one. -/
informal_lemma "coalescent-asg-forward-resolution"
  Descent.Coalescent.asg_forward_resolution
  []

/-! ### Three retractions

Written with `withdrawn` rather than as prose because a retracted claim that cannot be
listed is a retracted claim the next reader re-derives.  None of the three named a
declaration, which is why they are commands and not attributes. -/

withdrawn "coalescent-ionescu-tulcea-most-promising"
  "an earlier revision of the Mathlib entry called Ionescu-Tulcea 'the most \
   promising unexplored route' to K-C Theorem 3. Scoping it retracts that: \
   Ionescu-Tulcea needs the kernels, and the kernel from R_k to R_{k+1} is a \
   splitting kernel whose probabilities are K-C (3.19)'s Dirichlet structure, \
   which is the paintbox measure on the simplex. It avoids Kolmogorov's \
   topological hypotheses and not the missing simplex measure -- the same \
   obstacle, one layer down. Recorded because an optimistic claim in a ledger \
   is worse than none."

withdrawn "coalescent-ionescu-tulcea-jump-chain-scope"
  "the verdict that Ionescu-Tulcea 'avoids Kolmogorov's topological hypotheses \
   and not the missing simplex measure' was right about the PAINTBOX, whose \
   kernel needs the simplex measure, and wrong about the JUMP CHAIN at finite \
   n, whose kernel is Kernel.jumpKernel and needs no simplex at all. The \
   distinction had not been drawn; drawing it is what unblocked \
   Coalescent.TrajectoryLaw."

withdrawn "coalescent-disjoint-pairs-never-share-tree"
  "an earlier pass asserted that DISJOINT pairs never share tree. That is true \
   of the pairing that respects the cherries and false of the other two, and it \
   would have made Tajima's theta coefficient vanish like 2/n instead of \
   tending to 1/3. The enumeration in TajimaVariance found it; re-reading had \
   not."

/-- The interior binomial coefficients of row `λ` sum to `2^λ - 2`.  Stated additively to
keep it clear of truncated subtraction. -/
theorem sum_choose_interior_add_two {lam : ℕ} (h : 1 ≤ lam) :
    (∑ nu ∈ Finset.Ico 1 lam, lam.choose nu) + 2 = 2 ^ lam := by
  have hfull : ∑ nu ∈ Finset.range (lam + 1), lam.choose nu = 2 ^ lam :=
    Nat.sum_range_choose lam
  have hsplit : ∑ nu ∈ Finset.range (lam + 1), lam.choose nu
      = lam.choose 0 + ∑ nu ∈ Finset.Ico 1 (lam + 1), lam.choose nu := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  have htop : ∑ nu ∈ Finset.Ico 1 (lam + 1), lam.choose nu
      = (∑ nu ∈ Finset.Ico 1 lam, lam.choose nu) + lam.choose lam :=
    Finset.sum_Ico_succ_top h _
  rw [hsplit, htop, Nat.choose_zero_right, Nat.choose_self] at hfull
  omega

/-- The number of ways to cut a class of size `λ` into two nonempty pieces: `2^{λ-1} - 1`.
Each cut is named twice by the piece sizes -- once as `ν` and once as `λ - ν` -- which is
exactly Kingman's factor `½`, and `Split.splitBy_eq_iff` is the statement that those two
names give the same state. -/
theorem two_mul_cutCount_add_two {lam : ℕ} (h : 1 ≤ lam) :
    2 * (2 ^ (lam - 1) - 1) + 2 = 2 ^ lam := by
  obtain ⟨m, rfl⟩ : ∃ m, lam = m + 1 := ⟨lam - 1, by omega⟩
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by
    rw [pow_succ]
    ring
  simp only [Nat.add_sub_cancel]
  omega

/-- **The two counts agree.**  Summing `½ C(λ, ν)` over the interior of row `λ` gives the
number of cuts of a `λ`-class.  This is the arithmetic half of open item 1: it says the
weight Kingman writes is the right weight, given that cuts and refining states correspond.
The correspondence itself is the half that is missing. -/
theorem sum_choose_interior_eq_two_mul_cutCount {lam : ℕ} (h : 1 ≤ lam) :
    ∑ nu ∈ Finset.Ico 1 lam, lam.choose nu = 2 * (2 ^ (lam - 1) - 1) := by
  have h1 := sum_choose_interior_add_two h
  have h2 := two_mul_cutCount_add_two h
  omega

/-- A class of size two has exactly one cut: into two singletons. -/
theorem cutCount_two : 2 ^ (2 - 1) - 1 = 1 := by norm_num

/-- A class of size three has three cuts, one for each element left alone. -/
theorem cutCount_three : 2 ^ (3 - 1) - 1 = 3 := by norm_num

end Coalescent

end Descent
