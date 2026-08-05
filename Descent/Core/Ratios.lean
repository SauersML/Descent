/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Core: the shared arithmetic kernels

**This module is depth 0. It imports Mathlib and nothing from this corpus, and it must
stay that way.** Everything here exists to be imported by files that would otherwise
write the same map out for the third time under a fourth name.

## Why this file and not a theorem

The corpus previously related its repeated maps with identity theorems collected in
`Foundations/Conventions`. That file sits near the TOP of the import graph: it imports
twenty-two modules and is imported by three. An identity stated above the things it
relates can only *describe* their agreement. Nothing below it can depend on the
agreement, so a divergence between two spellings is caught only if someone re-runs the
census. The root file already carries the rule this module applies:

> When two places must agree, make one of them call the other; a note explaining why
> they must agree is not a mechanism.

So the maps live here, at the bottom, and the named biological quantities *call* them.
A change to `proportionalReduction` now reaches every referent by construction, and the
identity theorems that used to state the agreement become `rfl`.

## What a kernel is, and what it is not

A kernel here is a SHAPE, not a quantity. `proportionalReduction a b = 1 - a/b` is not
`F_ST`, is not `R²`, and is not PC-correction efficacy. It is the construction all three
instantiate: a residual measured against a baseline.

## Empirical status

**Kernels carry no biological claim, and therefore no empirical status.** They cannot be
falsified, because they assert nothing about a population. What can be falsified is a
named quantity that claims a kernel computes it -- and those names are defined in the
subsystem modules, each keeping its own docstring, its own regime, and its own ledger
record. No DECLARATION in this file may acquire an `Empirical status:` line.

The heading above is what makes that policy visible to a machine. It is a module-level
declaration, and `validation/code/check.py`'s `identifications` guard and
`validation/empirical/simcov/inventory.py` both read it and apply it to every declaration
here that states none of its own -- which is all of them, by the rule in the paragraph
above. Before the heading existed the policy was stated in prose, both guards read it as
seven declarations owing a measurement, and the coverage scan additionally parsed the
words `Empirical status:` out of the sentence forbidding them and reported the two
characters after it as a verdict outside the closed vocabulary. A file was penalised for
saying clearly that it has no status.

**Do not fold named referents into their kernel.** Four names for `(1 - r)^t` is not
four copies of one thing: `admixtureLDDecay` carries a measured `+0.24%` to `+0.37%`
one-sided bias against finite-population retention and a theorem proving that sign,
which a bare primitive has nowhere to put. The rule is WRAP, never REPLACE. A wrapper
keeps the name, the docstring, and the measurement, and gains the dependency.

## Reference evaluations

Many declarations in this corpus carry a `_at_reference_point` theorem: the body evaluated
at a fixed argument, stated as an equality to a number. They exist because an inequality,
a monotonicity or an invariance leaves a whole family of bodies satisfying it, and a value
does not -- a definition that had quietly acquired a wrong coefficient would still satisfy
every bound written about it. Pinning one value excludes that family.

The explanation lives here rather than being restated on each of the 149 theorems that
used to carry it verbatim. Those docstrings now point at this paragraph.

## Junk values

Every kernel with a division inherits Lean's `x / 0 = 0`, so each has an argument at
which it returns a number that is not the value of the quantity being modelled. Those
points are named as theorems here rather than left for each of the seventeen call sites
to discover, and the naming convention `_is_junk` matches the rest of the corpus.
-/

namespace Descent.Core

/-! ### The bare binary operations

These four look content-free, and as bodies they are. They earn their place as the
things the census kept finding: `a / b` appears under seventeen names in the corpus and
`a * b` under thirteen. Routing those names through a kernel does not make them one
quantity -- it makes the SHAPE checkable, so a name that quietly grows a coefficient
stops being a wrapper and has to say so.
-/

/-- Ratio, `a / b`. The shape behind heritability fractions, portability ratios, cost
effectiveness, and every other "this per that" in the corpus. -/
noncomputable def ratio (a b : ℝ) : ℝ := a / b

/-- **ratio at a zero denominator, named.** Lean returns `0`, which reads as "none of
`a` per unit `b`" -- an answer, produced by a case where the question has none.
Consumers must require `b ≠ 0`. -/
theorem ratio_zero_denominator_is_junk (a : ℝ) : ratio a 0 = 0 := by
  unfold ratio; simp

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ratio_at_reference_point : ratio (1 / 2) (1 / 2) = 1 := by
  norm_num [ratio]

/-- Product, `a * b`. The shape behind tagged effects, attenuations, retentions, and
every other "scaled by" in the corpus. -/
noncomputable def product (a b : ℝ) : ℝ := a * b

/-- Reference evaluation. -/
theorem product_at_reference_point : product (1 / 2) (1 / 2) = 1 / 4 := by
  norm_num [product]

/-- Difference, `a - b`. The shape behind gaps, increments, penalties and biases. -/
noncomputable def difference (a b : ℝ) : ℝ := a - b

/-- Reference evaluation. -/
theorem difference_at_reference_point : difference (1 / 2) (1 / 4) = 1 / 4 := by
  norm_num [difference]

/-- Sum, `a + b`. The shape behind variance decompositions and additive liabilities. -/
noncomputable def sum (a b : ℝ) : ℝ := a + b

/-- Reference evaluation. -/
theorem sum_at_reference_point : sum (1 / 2) (1 / 4) = 3 / 4 := by
  norm_num [sum]

/-! ### Composite shapes

These carry structure a reader can get wrong, which is why relating them matters more
than relating `a / b`. Each is stated once and instantiated by name elsewhere.
-/

/-- Proportional reduction, `1 - a / b`: a residual measured against a baseline.

Instantiated by `F_ST` from a heterozygosity ratio, `F_ST` from coalescence times, `R²`
from a mean squared error, and PC-correction efficacy. Those are four quantities and not
one -- the first divides a heterozygosity by an ancestral heterozygosity, the second an
expected within-population coalescence time by a between-population one, the third an
error by an outcome variance, the fourth a corrected ancestry axis by an uncorrected
one. Nothing lets a value of one be substituted for another. What they share is the
construction, and sharing it is not a coincidence. -/
noncomputable def proportionalReduction (a b : ℝ) : ℝ := 1 - a / b

/-- **proportionalReduction at a zero baseline, named.** Lean returns `1`: "the residual
is entirely accounted for", which is the strongest claim the quantity can make, returned
for the case where there is no baseline to account against. Consumers must require
`b ≠ 0`. -/
theorem proportionalReduction_zero_baseline_is_junk (a : ℝ) :
    proportionalReduction a 0 = 1 := by
  unfold proportionalReduction; simp

/-- Reference evaluation. -/
theorem proportionalReduction_at_reference_point :
    proportionalReduction (1 / 2) 1 = 1 / 2 := by
  norm_num [proportionalReduction]

/-- Share, `a / (a + b)`: one part against the whole it belongs to.

Distinct from `ratio` and not a special case of it worth eliding: the denominator
CONTAINS the numerator, so the value is confined to the unit interval whenever both
parts are non-negative, and `share_mem_unit` below is the statement `ratio` cannot make.
Instantiated by the signal fraction of a variance, the shared-LD equilibrium, and the
heritability captured at a sample size. -/
noncomputable def share (a b : ℝ) : ℝ := a / (a + b)

/-- **share where both parts vanish, named.** With no whole there is no share. Lean
returns `0`, reporting "none of it", for the case that has no parts at all. Consumers
must require `a + b ≠ 0`. -/
theorem share_zero_total_is_junk : share 0 0 = 0 := by
  unfold share; norm_num

/-- **What `share` has and `ratio` does not.** A non-negative part against a positive
total lands in `[0, 1]`. This is the reason the two kernels are separate: `ratio` admits
no such bound, so a quantity that needs one must say through its body which kernel it
instantiates. -/
theorem share_mem_unit (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    0 ≤ share a b ∧ share a b ≤ 1 := by
  unfold share
  constructor
  · exact div_nonneg ha (le_of_lt hab)
  · rw [div_le_one hab]; linarith

/-- Reference evaluation. -/
theorem share_at_reference_point : share (1 / 2) (1 / 2) = 1 / 2 := by
  norm_num [share]

/-- Saturation, `x / (1 + x)`: a scaled rate read as a fraction.

This is `share x 1` and is kept separate because the "one" is not a second part -- it is
the unit the rate is scaled against. Instantiated by `F_ST` from a scaled coalescence
time `τ/(1+τ)`, by the mutation-drift floor `θ/(1+θ)`, and by shared LD from a scaled
migration rate. That these are one map is the fact behind the corpus convention that
every `F_ST` written in `τ/(1+τ)` coordinates is a HUDSON `F_ST`. -/
noncomputable def saturation (x : ℝ) : ℝ := x / (1 + x)

/-- **saturation at `x = -1`, named.** The denominator vanishes and Lean returns `0`,
reporting no differentiation for a scaled rate that has none of the meaning the argument
name carries. Consumers must require `1 + x ≠ 0`; every intended argument is
non-negative, where the guard cannot bite. -/
theorem saturation_at_neg_one_is_junk : saturation (-1) = 0 := by
  unfold saturation; norm_num

/-- **Saturation is a share of the unit-augmented total.** The bridge that keeps the two
kernels from drifting: if either body changes, this fails. -/
theorem saturation_eq_share (x : ℝ) : saturation x = share x 1 := by
  unfold saturation share
  rw [add_comm x 1]

/-- **Saturation lands in the unit interval on non-negative rates**, which is what makes
it usable as an `F_ST` coordinate. -/
theorem saturation_mem_unit (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ saturation x ∧ saturation x ≤ 1 := by
  rw [saturation_eq_share]
  exact share_mem_unit x 1 hx zero_le_one (by linarith)

/-- Reference evaluation. -/
theorem saturation_at_reference_point : saturation 1 = 1 / 2 := by
  norm_num [saturation]

/-- Odds-like ratio, `a / (a + 2 b)`: a part against itself plus twice a second part.

The factor of two is a PLOIDY factor wherever this map appears in the corpus, and it is
the whole content of the kernel -- `share` with the second part doubled is a different
number, and reading one for the other is exactly the Nei/Hudson confusion the corpus has
already recorded paying two to four fold for. Instantiated by `Q_ST` (between-population
additive variance against between plus twice within) and by `F_ST` from a coalescence
time in the same coordinates, which is why the two can be compared at all. -/
noncomputable def oddsLike (a b : ℝ) : ℝ := a / (a + 2 * b)

/-- **oddsLike where the total vanishes, named.** Consumers must require
`a + 2 * b ≠ 0`. -/
theorem oddsLike_zero_total_is_junk : oddsLike 0 0 = 0 := by
  unfold oddsLike; norm_num

/-- **The doubling is not a convention.** At `a = b = 1` the odds-like ratio is `1/3`
while the plain share is `1/2`. Stated as a value rather than left implicit, because a
one-sided bound or a monotonicity would be satisfied by both. -/
theorem oddsLike_ne_share : oddsLike 1 1 ≠ share 1 1 := by
  unfold oddsLike share; norm_num

/-- Reference evaluation. -/
theorem oddsLike_at_reference_point : oddsLike 1 1 = 1 / 3 := by
  norm_num [oddsLike]

/-- Convex combination, `α x + (1 - α) y`.

Instantiated by admixed allele frequencies, spike-and-slab effect variances,
ancestry-specific effects, and average phase interactions. -/
noncomputable def convexCombination (α x y : ℝ) : ℝ := α * x + (1 - α) * y

/-- **The endpoints, which fix the argument order.** `α` weights the FIRST value.
Getting this backwards is a real error and not a convention -- an admixed frequency at
`α = 0.2` is a different number from one at `α = 0.8` -- so the orientation is pinned
here rather than left to each call site's argument names. -/
theorem convexCombination_at_endpoints (x y : ℝ) :
    convexCombination 1 x y = x ∧ convexCombination 0 x y = y := by
  constructor <;> (unfold convexCombination; ring)

/-- Reference evaluation. -/
theorem convexCombination_at_reference_point :
    convexCombination (1 / 2) 1 0 = 1 / 2 := by
  norm_num [convexCombination]

/-- Geometric decay, `(1 - r)^t`.

Instantiated by per-generation LD decay, recombination survival to the MRCA, and
admixture LD decay. The last of those is MEASURED against finite-population retention
and carries a proved one-sided bias, which is the standing reason those three names are
not collapsed into this one. -/
noncomputable def geometricDecay (r : ℝ) (t : ℕ) : ℝ := (1 - r) ^ t

/-- **Decay at time zero is no decay**, whatever the rate. -/
theorem geometricDecay_at_zero (r : ℝ) : geometricDecay r 0 = 1 := by
  unfold geometricDecay; norm_num

/-- **The step law**: one more generation multiplies by `1 - r`. This is what makes the
name "decay" rather than "an exponent", and it is the property every referent needs. -/
theorem geometricDecay_succ (r : ℝ) (t : ℕ) :
    geometricDecay r (t + 1) = (1 - r) * geometricDecay r t := by
  unfold geometricDecay; ring

/-- Reference evaluation. -/
theorem geometricDecay_at_reference_point : geometricDecay (1 / 2) 2 = 1 / 4 := by
  norm_num [geometricDecay]

/-- Retained fraction, `(1 - loss) · total`: what survives a proportional loss.

Instantiated by the ascertainment-loss survivor, the neutral portability ratio, and
present-day PGS variance. -/
noncomputable def retainedFraction (loss total : ℝ) : ℝ := (1 - loss) * total

/-- Reference evaluation. -/
theorem retainedFraction_at_reference_point :
    retainedFraction (1 / 2) (1 / 2) = 1 / 4 := by
  norm_num [retainedFraction]

/-- Complement, `1 - x`: the fraction that did not survive, given the fraction that did.

Instantiated by `F_ST` from a drift retention factor, the covariance retention factor
from `F_ST`, and the loss from a retention. -/
noncomputable def complement (x : ℝ) : ℝ := 1 - x

/-- **Complement is an involution.** The property the name claims, stated so that a body
that stops satisfying it stops compiling. -/
theorem complement_involutive (x : ℝ) : complement (complement x) = x := by
  unfold complement; ring

/-- Reference evaluation. -/
theorem complement_at_reference_point : complement (1 / 4) = 3 / 4 := by
  norm_num [complement]

/-- Midpoint, `(a + b) / 2`: the unweighted average of two values.

This is `convexCombination (1/2)`, and the bridge below says so. Instantiated by the
mean allele frequency across two populations and by the effective symmetric migration
rate. -/
noncomputable def midpoint (a b : ℝ) : ℝ := (a + b) / 2

/-- **The midpoint is the balanced convex combination.** -/
theorem midpoint_eq_convexCombination (a b : ℝ) :
    midpoint a b = convexCombination (1 / 2) a b := by
  unfold midpoint convexCombination; ring

/-- Reference evaluation. -/
theorem midpoint_at_reference_point : midpoint 1 0 = 1 / 2 := by
  norm_num [midpoint]

/-- Complementary composition, `1 - (1 - a)(1 - b)`: two proportional reductions applied
in series, read as a single reduction.

This is Wright's hierarchical composition law when `a` and `b` are `F_ST` values at two
levels of subdivision, and it is the same map as the composition of branch-wise
differentiation along a two-branch genealogy. Those two facts being one map is a real
population-genetic identity and not an arithmetic coincidence. -/
noncomputable def complementaryComposition (a b : ℝ) : ℝ := 1 - (1 - a) * (1 - b)

/-- **Composition is symmetric**: the order in which two levels of subdivision are
applied does not change the total. -/
theorem complementaryComposition_comm (a b : ℝ) :
    complementaryComposition a b = complementaryComposition b a := by
  unfold complementaryComposition; ring

/-- **A level with no differentiation contributes nothing.** -/
theorem complementaryComposition_zero (a : ℝ) :
    complementaryComposition a 0 = a := by
  unfold complementaryComposition; ring

/-- **Composition is NOT addition**, which is the reason to write it out. At
`a = b = 1/2` the composed value is `3/4` and the sum is `1`. -/
theorem complementaryComposition_ne_sum :
    complementaryComposition (1 / 2) (1 / 2) ≠ sum (1 / 2) (1 / 2) := by
  unfold complementaryComposition sum; norm_num

/-- Reference evaluation. -/
theorem complementaryComposition_at_reference_point :
    complementaryComposition (1 / 2) (1 / 2) = 3 / 4 := by
  norm_num [complementaryComposition]

/-- Scaled squared difference, `(a - b)² / 4`: the between-group variance of two
equally-sized groups with means `a` and `b`.

The four is `2²` from the half-weighting on each group and is not free. -/
noncomputable def halfDiffSq (a b : ℝ) : ℝ := (a - b) ^ 2 / 4

/-- **Symmetric, and zero exactly when the groups agree.** -/
theorem halfDiffSq_eq_zero_iff (a b : ℝ) : halfDiffSq a b = 0 ↔ a = b := by
  unfold halfDiffSq
  constructor
  · intro h
    have h2 : (a - b) ^ 2 = 0 := by linarith
    have h3 : a - b = 0 := by
      exact sq_eq_zero_iff.mp h2
    linarith
  · rintro rfl; ring

/-- Reference evaluation. -/
theorem halfDiffSq_at_reference_point : halfDiffSq 1 0 = 1 / 4 := by
  norm_num [halfDiffSq]

/-- Survival-weighted mix, `(1 - c)² · (1/(2N) + (1 - 1/(2N)) · x)`.

Two lineages both escape an event of per-lineage probability `c` -- hence the square -- and
what they carry forward is a convex mix of a freshly generated `1/(2N)` and the retained
`x`. Instantiated by the drift step for linkage disequilibrium and by the
identity-by-descent recurrence, which are the same map: LD decay under drift IS the IBD
recurrence, with `c` reading as recombination in one and as mutation in the other. The
corpus had the two bodies written out separately in two modules with nothing relating
them. -/
noncomputable def survivalWeightedMix (N c x : ℝ) : ℝ :=
  (1 - c) ^ 2 * (1 / (2 * N) + (1 - 1 / (2 * N)) * x)

/-- **survivalWeightedMix at an empty population, named.** At `N = 0` the freshly generated
term is junk-zero and the retained term keeps its full weight, so an empty population is
reported as generating nothing new while losing nothing either. Consumers must require
`N ≠ 0`. -/
theorem survivalWeightedMix_empty_is_junk (c x : ℝ) :
    survivalWeightedMix 0 c x = (1 - c) ^ 2 * x := by
  unfold survivalWeightedMix; simp

/-- **No survival, nothing carried.** At `c = 1` the step returns zero whatever the state
was: if neither lineage survives the event, no information about the previous generation
reaches the next. -/
@[simp] theorem survivalWeightedMix_full_loss (N x : ℝ) :
    survivalWeightedMix N 1 x = 0 := by
  unfold survivalWeightedMix; ring

/-- **The mix is convex in the retained value**, so the step is monotone: a larger state in
carries a larger state out. -/
theorem survivalWeightedMix_mono (N c x y : ℝ) (hN : 1 / (2 * N) ≤ 1) (hxy : x ≤ y) :
    survivalWeightedMix N c x ≤ survivalWeightedMix N c y := by
  unfold survivalWeightedMix
  have h1 : 0 ≤ 1 - 1 / (2 * N) := by linarith
  have h2 : (1 - 1 / (2 * N)) * x ≤ (1 - 1 / (2 * N)) * y :=
    mul_le_mul_of_nonneg_left hxy h1
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

/-- Reference evaluation. -/
theorem survivalWeightedMix_at_reference_point :
    survivalWeightedMix 1 0 0 = 1 / 2 := by
  norm_num [survivalWeightedMix]

/-! ### Discrete shapes

Two indicator maps and one overlap profile, each written out in more than one module
before this. They are not `ℝ`-arithmetic in the sense of the kernels above, but they are
the same kind of object: a shape several named quantities instantiate. -/

/-- Kronecker delta, `1` when the arguments agree and `0` otherwise.

Instantiated by a persistence transition, a context-match quality, and a stay kernel --
three names in two modules for "did the state stay the same". -/
noncomputable def kronecker {α : Type*} [DecidableEq α] (x y : α) : ℝ :=
  if x = y then 1 else 0

/-- **The delta is one exactly on the diagonal.** -/
@[simp] theorem kronecker_self {α : Type*} [DecidableEq α] (x : α) :
    kronecker x x = 1 := by
  unfold kronecker; simp

/-- **And zero off it.** -/
theorem kronecker_of_ne {α : Type*} [DecidableEq α] {x y : α} (h : x ≠ y) :
    kronecker x y = 0 := by
  unfold kronecker; simp [h]

/-- **The delta is symmetric**, which is the property that makes it a transition kernel
of a reversible chain rather than an arbitrary indicator. -/
theorem kronecker_comm {α : Type*} [DecidableEq α] (x y : α) :
    kronecker x y = kronecker y x := by
  unfold kronecker
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- The complementary indicator, `0` on the diagonal and `1` off it: a switching
transition, a sequence distance, a swap kernel. -/
noncomputable def antiKronecker {α : Type*} [DecidableEq α] (x y : α) : ℝ :=
  if x = y then 0 else 1

/-- **The two indicators are complementary**, which is what makes a pair of them a
probability distribution over "stayed" and "switched" rather than two unrelated
functions. -/
theorem kronecker_add_antiKronecker {α : Type*} [DecidableEq α] (x y : α) :
    kronecker x y + antiKronecker x y = 1 := by
  unfold kronecker antiKronecker
  by_cases h : x = y <;> simp [h]

/-- **The delta unfolds on sight.**

Marked `simp` deliberately. `DynamicsContrast.contextMatchQuality` used to write this body
out rather than delegate, and its docstring gave the reason: the witness proofs below
evaluate the definition by `simp`, and a delegation stops them one unfolding short. That
was a correct objection to delegating WITHOUT this lemma. With it, a wrapper evaluates
exactly as an inlined body does, and the objection is answered rather than overruled. -/
@[simp] theorem kronecker_eq {α : Type*} [DecidableEq α] (x y : α) :
    kronecker x y = if x = y then 1 else 0 := rfl

/-- **The complementary indicator unfolds likewise**, for the same reason. -/
@[simp] theorem antiKronecker_eq {α : Type*} [DecidableEq α] (x y : α) :
    antiKronecker x y = if x = y then 0 else 1 := rfl

/-- Overlap profile, `x(1 - qx) / (1 - qx(1 - x))`.

The overlap-gap order parameter of a superposed landscape, written out under two names in
two modules that do not import each other. Not an arithmetic shape anyone would arrive at
twice by accident -- two copies of this body is a copied derivation. -/
noncomputable def overlapProfile (q x : ℝ) : ℝ :=
  x * (1 - q * x) / (1 - q * x * (1 - x))

/-- **At zero coupling the profile is the identity.** With `q = 0` there is no overlap
gap and the order parameter is just the mass. -/
@[simp] theorem overlapProfile_at_zero (x : ℝ) : overlapProfile 0 x = x := by
  unfold overlapProfile; simp

/-! ### Three more shapes the census kept finding

Each was written out in two modules that do not import each other. None is deep; what
makes them worth naming is that a second copy of a body is a copied derivation, and a
copied derivation drifts. -/

/-- Scaled square, `a² / b`. A moment permeability and an importance-weight effective
sample size are the same map: a squared total against a sum of squares. -/
noncomputable def scaledSquare (a b : ℝ) : ℝ := a ^ 2 / b

/-- **scaledSquare at a zero divisor, named.** Consumers must require `b ≠ 0`. -/
theorem scaledSquare_zero_divisor_is_junk (a : ℝ) : scaledSquare a 0 = 0 := by
  unfold scaledSquare; simp

/-- Ratio against a product, `a / (b · c)`. The events required for a recalibration and a
tag `r²` are the same map. -/
noncomputable def ratioOfProduct (a b c : ℝ) : ℝ := a / (b * c)

/-- **ratioOfProduct where either factor vanishes, named.** -/
theorem ratioOfProduct_zero_factor_is_junk (a c : ℝ) : ratioOfProduct a 0 c = 0 := by
  unfold ratioOfProduct; simp

/-- Squared ratio against a product, `a² / (b · c)`. The `R²` shape: a squared covariance
against a product of variances. Distinct from `scaledSquare` because the denominator is a
PRODUCT of two quantities that must both be positive, which is what confines the value to
the unit interval under Cauchy--Schwarz. -/
noncomputable def squaredShare (a b c : ℝ) : ℝ := a ^ 2 / (b * c)

/-- **What `squaredShare` has and `scaledSquare` does not.** Under Cauchy--Schwarz on the
two factors the value is at most one -- the bound that makes this an `R²` and not merely
a quotient. -/
theorem squaredShare_le_one (a b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 ≤ b * c) : squaredShare a b c ≤ 1 := by
  unfold squaredShare
  rw [div_le_one (mul_pos hb hc)]
  exact h

/-- Affine step, `a + b · c`. A kinship inflation and a linear norm of reaction are the
same map: a baseline displaced by a scaled increment. -/
noncomputable def affineStep (a b c : ℝ) : ℝ := a + b * c

/-- **At a zero increment the affine step is its baseline**, which is the property that
makes `a` the baseline rather than one term among three. -/
@[simp] theorem affineStep_at_zero (a b : ℝ) : affineStep a b 0 = a := by
  unfold affineStep; ring

end Descent.Core
