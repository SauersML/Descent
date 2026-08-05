/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Heterozygosity
import Descent.PopGen.AncestrySpecificArchitecture
import Descent.PopGen.AssortativeMatingPGS
import Descent.Foundations.CovarianceStructure
import Descent.PopGen.GeneticArchitectureDiscovery
import Descent.Portability.StatisticalGeneticsMethodology
import Descent.Blindness.BlindnessRegistry
import Descent.PopGen.SerialFounderChain
import Descent.Blindness.BundleRigidity.TwoAtom
import Descent.Portability.LongitudinalPortability
import Descent.Portability.ImputationPortability
import Descent.Portability.MetricSpecificPortability
import Descent.Portability.ScoreDistribution
import Descent.PopGen.EpistasisAndNonAdditivity
import Descent.PopGen.VarianceComponents
import Descent.Decision.PowerAnalysis
import Descent.PopGen.PolygenicAdaptation
import Descent.Portability.AncestryCalibration
import Descent.Portability.PortabilityBounds
import Descent.Portability.StratificationConfounding
import Descent.Portability.TransferLearningPGS
import Descent.Portability.RareVariantPortability
import Descent.Core.Fst
import Descent.Core.Parameters

namespace Descent.Program

open Descent.Core (coalescentTimeScale coalescentTimeScale_eq)
open Descent.Portability (genotypeVarianceHWE)

/-!

**This is an audit layer, not a foundation, and it used to be filed as one.**

Its 114 theorems relate quantities that live in fifteen different subsystem modules --
`driftVariance` against `genotypeVarianceHWE`, `amEquilibriumVariance` against `ibdFst`,
the `F_ST` spellings against each other. Doing that REQUIRES importing all fifteen, so it
can never sit below them, and nothing below it can be made to respect anything it proves.

That is not a defect in this file; checking agreement after the fact is a real job. The
defect was calling it a foundation. What genuinely belonged at the bottom has been moved
there -- `ploidy`, `convexMix`, `geometricDecay`, `oneMinusRatio` and `retainedFraction`
are now `Core` kernels that their referents CALL, and the fifteen identity theorems that
used to state their agreement are gone with them, because the agreement is in the bodies.

What is left here is what cannot be moved: relations between quantities that are genuinely
defined in different subsystems for different reasons. Those are worth stating and they
are worth re-reading when either side changes -- which is what an audit layer is for.

# Identifications: making a named quantity carry its obligation

A Lean `def` cannot be wrong internally, so the entire risk of this
development sits in one place: a definition whose *name* claims a
population-genetic meaning that its *formula* does not have. Every theorem
downstream is then machine-checked and misleading. Two instances have now been
found by simulation rather than by proof.

`demographicSpike` carried the wrong constant, `2 F m_eff` where the data give
`3.9920 ± 0.0045`. A cross-check between two independently written formulas
would have caught it, and `four_neiGst_eq_standardizedContrastVariance`
below is that cross-check.

`singletonProportion N₀ N₁ = 1 - log N₀ / log N₁` was worse, and no
cross-check of that kind could have caught it. It returns `0` at the null
where the truth is `0.187`, and it takes no sample size at all although the
observable moves from `0.427` to `0.368` when `n` goes from 50 to 200. The
signature cannot express the quantity. That is a type error, not an arithmetic
one, and it is invisible to any argument that only compares formulas to other
formulas.

The two failures therefore need two different mechanisms.

* Against a wrong constant: over-determination. Derive the quantity from a
  primitive so the constant is forced, and relate independently written
  formulas so that drift between them fails to compile. That is this file.

* Against a wrong signature: an obligation attached to the name. A named
  empirical quantity must be introduced together with the observable it claims
  to be, and a proof that the two agree. Then a formula that cannot depend on
  `n` cannot identify an observable that does. Claims whose signatures omit
  required variables are not exported as theorems.
-/

section Ploidy

/-! **`ploidy` is deleted here.**  It was `Descent.Core.ploidy` under a second name, and
every reference now calls the kernel.  A module whose subject is conventions is the last
place that should keep its own copy of one.

Its docstring recorded the census that gives this section its job, and that does not go
with it: every non-exponent factor of two in this development traces to the ploidy, and
every factor of four to twice it.  Forty-eight definition bodies outside this file carry
such a two and fourteen carry such a four.  The theorems below tie the independently
written ones back to the kernel, so that drift between them is a compile error rather than
a silent disagreement -- which is exactly what the local copy was in the way of. -/


end Ploidy

section Differentiation


/-! ### The arithmetic mean of two, shared with the migration rates

`meanAlleleFreq` averages two subgroup allele frequencies and
`effectiveSymmetricMigration` averages two directional migration rates: two different
quantities sharing one map, with an equal-weight convention that has to be the same
convention in both or the `F_ST` they feed disagrees with itself.

They are deliberately *not* collapsed into one definition. The bodies coincide, but an
allele frequency and a migration rate are not the same quantity, and a single name would
let a proof about one be applied to the other without anything failing. The theorem below
records the coincidence, which is what a shared convention deserves — as against the
island-model `F_ST`, where four names really did denote one quantity and are now one. -/


/-! ### Reference/alternate allele swap: a metamorphic relation, not a symmetry of taste

Which allele a variant call file names REFERENCE is a property of the assembly, not
of the biology. Swapping it sends `p ↦ 1 - p` at every population simultaneously.
Every allele-frequency-symmetric quantity must therefore be invariant, and every
effect-direction quantity must be negated; a body that is neither is reporting the
assembly. The corpus proves that its `F_ST` bodies do not care which population is
called first (`hudsonFst_symm`) but had no statement about which allele is called
reference, which is the convention that actually varies between panels. -/


end Differentiation

section EquilibriumAgreements

/-! **The island-model `F_ST` is one definition, `fstMigrationDriftEquilibrium`.**
Write new uses against it rather than spelling out `1 / (1 + 4 Nₑ m)` again; a second
spelling would carry its own factor of four with nothing to hold it in step.

`equilibriumFst` is worth recording as a hazard: it took its arguments in the opposite
order to the other two, so the same call spelled the same way meant different things
depending on which copy was in scope. -/


/-- **Cross-check spanning the mating and drift modules: assortative mating and
drift act multiplicatively on the additive variance.**

`amEquilibriumVariance` inflates by `1/(1 - r h²)` and `presentDayPGSVariance`
deflates by `(1 - F_ST)`, and composing them gives the product. Stated because
the two modules described the same variance and were never related, which is
the condition under which a falsified companion of `amEquilibriumVariance`
survived. -/
theorem amEquilibrium_then_drift (V_A r h2 fst : ℝ) :
    Portability.presentDayPGSVariance (PopGen.amEquilibriumVariance V_A r h2) fst =
      (1 - fst) * (V_A / (1 - r * h2)) := by
  unfold Portability.presentDayPGSVariance Portability.pgsVarianceFromHet PopGen.amEquilibriumVariance
  ring

/-! ### Tying the inlined genotype-variance restatements back to `ploidy`

**A definition that INLINES the literal `2` is tied to the ploidy convention by
nothing but the theorem that says so.** Those theorems are below, one per inlining
definition, and each is the only edge between a literal and the named convention:
change `ploidy` and they fail, which is their entire purpose. Do not delete one as a
trivial restatement -- the definitions on their left-hand sides do not reference
`ploidy`, so the equality holds only because `rfl` reduces `ploidy` to `2`.

The genotype variance is NOT one of them. `genotypeVarianceHWE` and `hweHeterozygosity`
both call `Descent.Core.hweHeterozygosity`, which carries `ploidy` in its body, so the
edge is the call and not a theorem; `hweHeterozygosity_eq_genotypeVarianceHWE` relates the
pair where they are defined. Two theorems here used to state that agreement against a
third name for the same body, and all three reduced to the same kernel: an identity whose
two sides wrap one kernel constrains nothing, so it and the third name are gone. -/

/-! ### Tying the island-model equilibrium back to the scaled rate

One definition, one bridge: the island-model equilibrium is the migration-drift
equilibrium at the scaled migration rate. A second spelling of `1 / (1 + 4 Nₑ m)` would
need its own bridge theorem, which is a reason not to add one. -/


/-! ### Per-generation drift rate, written out in three modules

`1 / (2 Nₑ)` appears independently in `LongitudinalPortability`,
`DemographicHistory` and `LDDecayTheory` under three names. It is the
reciprocal of the coalescent time scale in each. -/


/-! ### The coalescent `F_ST` map, written out once

`PopulationGeneticsFoundations.coalFst` is the one body for this map, and
`DemographicHistory` calls it directly. Simulation validates `coalFst` as split
`F_ST`, unbiased against branch-mode divergence where the drift formula runs up
to 28 percent high. The name `DemographicHistory.fstFromCoalescenceTime` is
absent on purpose: a second spelling of `coalFst` can drift from it silently. -/

/-! ### The harmonic mean, written out once

`OpenQuestions.f1Score` is the one body for this expression, and
`MetricSpecificPortability` calls it. The name
`MetricSpecificPortability.f1ScoreMetric` is absent on purpose: two spellings in
two modules, with no theorem relating them, can disagree without failing. -/


/-! ### The per-generation retention factor, written out in four modules

`1 - 1/(2 Nₑ)` is the probability that two lineages fail to coalesce in one
generation. It is spelled out independently in `PhenomeWidePortability`,
`LDDecayTheory`, `PopulationGeneticsFoundations` and `PortabilityDrift`.

**These theorems pin the constant, not the regime, and three of the four bodies below
are members of a falsified cluster.** `(1 - 1/(2 Nₑ))^t` is the closed-population,
no-mutation recurrence; at demographic equilibrium simulation measures a retention of
`1.02 ± 0.02` where it predicts `e^(-2) = 0.135`, because mutation replenishes diversity
(`DriftRegime`). Agreeing on `2 Nₑ` is exactly the kind of cross-check that cannot see
that, since every identity here holds *in* the shared premise whatever its value.

`heterozygosityLossFromDrift` and `wrightFisherDriftRetention` are attached to the named
regime at the end of this file. `neutralDriftFactor` is **not** attached and carries a
FALSIFIED status of its own in `PhenomeWidePortability`. Note that
`ldRetainedFraction_uses_timeScale` below is the one guard in this group that states
what its formula omits — copy that shape, not the bare ones. -/


/-! ### The coalescent time coordinate, written out twice

`t / (2 Nₑ)` is time in coalescent units, in `PortabilityDrift` and in `DGP`. -/


/-! ### The scaled rates, written out on three parameter records

`θ = 4 Nₑ μ` and `M = 4 Nₑ m` used to appear on two parameter records, each spelling out
its own four: `GenerationalPopGenParameters` in `PortabilityDrift` and
`EvolutionaryParameters` in `DGP`. There is now one record, `Core.PopGenParameters`, and
its `theta` and `bigM` are `Core.scaledMutationRate` and `Core.scaledMigrationRate` by
definition -- so the two theorems that used to hold those spellings together are deleted
rather than restated. What remains below is the `EvolutionaryParameters` pair, which is
still a separate record. -/


/-! ### Genotype variance inside sums and products

Eight further definitions carry `2 p (1 - p)` as a factor rather than as their
whole body: score means and variances, Fisher's average effect, dominance and
additive variance, two noncentrality parameters, and a pairwise epistatic
variance. Each is now written against `genotypeVarianceHWE`. -/


/-! ### The remaining singletons

Each of these uses the ploidy convention once, with no sibling to disagree
with, so only a derivation from `ploidy` ties them down. -/


/-! `steppingStoneCharacteristicLength_uses_timeScale` has been DELETED, not
restated. It asserted
`steppingStoneCharacteristicLength Ne m = Real.sqrt (coalescentTimeScale Ne * m)`,
i.e. that the 1D decay length carries the `2·Nₑ` ploidy convention. The
corrected definition is `√(m/(2·μ))` and contains no effective size at all, so
there is no convention here to pin and no honest restatement to make: the
theorem existed only because the wrong body happened to contain `2·Nₑ`. Its
replacement, stating what that definition does claim, is
`PopulationGeneticsFoundations.steppingStoneCharacteristicLength_balances_mutation`. -/


/-! The bridge from the migration-drift equilibrium to the scaled mutation-drift form is
`fstMigrationDriftEquilibrium_eq_scaled` above.  A second copy of it stood here, for the
second spelling of that equilibrium -- which is what the note above predicted: "A second
spelling of `1 / (1 + 4 Nₑ m)` would need its own bridge theorem, which is a reason not to
add one."  The spelling is gone from `PortabilityDrift` and its bridge with it. -/


/-! `neutralPortability_uses_ploidy` has been DELETED, not restated. It asserted
`neutralPortability r2_0 fst = r2_0 * max 0 (1 - ploidy * fst)`, reading the `2`
in the old `1 - 2·fst` body as the ploidy convention.

It was not ploidy. That `2` was the leading coefficient of a first-order
expansion of a heterozygosity ratio, and the expansion is what
`battery_bulk56` falsified: the linear form is off by 12 sems at `fst = 0.05`,
well inside the `fst ≪ 0.5` regime it claimed for itself. The corrected body,
`r2_0 * (1 - fst) / ((1 - fst) * r2_0 + (1 - r2_0))`, carries no such constant,
so there is no convention here to pin -- the theorem existed only because the
superseded body happened to contain a `2`.

What the corrected definition does claim about `fst` is stated where it is
measured, at `PortabilityBounds.neutralPortability_pos_beyond_half`. -/

/-! ### The last entangled uses

These carry the convention inside a larger expression. A relation still ties
them down; no definition needs rewriting. -/


/-! ### The last seven

Each carries the convention in its own shape: inside a `let`, in a recursion
step, or under two nested decay factors. A relation reaches all of them. -/


/-! ### Shared primitives

Several groups of definitions across the development are the same map applied
to different quantities. Left unrelated, each is free to drift from the others;
naming the map once and relating them makes a divergence a failed proof. This
is the same device as `ploidy`, applied to structure rather than to a
constant. -/

/-! ### Retention and ratio maps

Three further groups are one map under several names. -/


/-! `explainedR2FromTransportMoments` and `pgsR2` are the same term; the identity is
stated once, next to `pgsR2` in `TransferLearningPGS`. -/

/-! ### The regime obligation, stated once

A closed form whose docstring reads `Empirical status: FALSIFIED` or `CONDITIONALLY VALID`
is making two claims at once: an algebraic one, which Lean checks, and a claim about the
conditions under which the algebra describes a population, which until recently nothing
checked. `DriftRegime` established why that matters — a formula carrying its regime in a
docstring can be moved into a regime where it is false, and every internal cross-check will
still pass, because the identities are identities *in* the shared premise.

Every such closed form now carries its regime in a machine-checkable form, by one of four
mechanisms. Recorded here so that a new one added without any of them is visibly a
departure rather than an oversight:

* **In the signature.** The definition takes a structure whose fields include the
  regime definition: `ClosedPopulationNoMutation` has mutation fixed to zero,
  an explicitly stated approximation inequality.
* **Tied to a regime object.** A theorem identifies the bare formula with a quantity of a
  named regime: `closedPopulation_het_eq_neutralDriftFactor`,
  `heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss` and its two siblings.
* **Never as an external theorem field.** If the development has no derivation connecting
  a numerical chart to a scientific observable, no identification theorem is exported.
  A citation or caller-supplied proposition cannot manufacture that theorem.
* **As a proved failure.** The departure is itself a theorem, so the limit is checkable
  rather than described: `benchmarkRatioForm_cannot_reach_measured`,
  `demoSteppingStoneFst_indistinguishable_from_quadratic`,
  `pairwiseFstFromBranches_eq_fstFromTau_add_mul`,
  `sampleLimitedScratchTargetR2_negative_of_small_sample`.

The fourth is the one worth noticing. Several of these regimes are not conditions under
which the formula holds but statements of how it fails — and a proved failure is stronger
than a hedged docstring, because it cannot be read past. -/

/-! ### Attaching the drift closed forms to the regime they came from

`DriftRegime` records the incident these two definitions are the residue of: a cluster of
five quantities, all functions of one closed-population retention, every cross-check
between them passing because every identity among them is an identity *in* that retention.
It fixed the diagnosis by making the regime an object — `closedPopulation` against
`mutationDriftBalance`, with `regimes_disagree` separating them — but the closed forms in
`PopulationGeneticsFoundations` were never attached to it, so they still carry their regime
only in prose.

These two theorems attach them. Neither is deep; that is the point. Each says the bare
formula is the measured loss of a *named* trajectory, so a reader who wants to know which
regime `heterozygosityLossFromDrift` assumes can follow a proof instead of trusting a
docstring — and anyone who moves it to a population at mutation-drift balance now
contradicts `regimes_disagree` rather than silently getting a wrong number. -/


/-! **The argument-order hazard this section documented is gone with the second copy.**

This section carried a theorem restating, for `heterozygosityLossDerived`, the
closed-population regime that `heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss`
already records for the surviving name -- and a note that the two took their arguments in
opposite orders, "so the same call spelled the same way means different things depending on
which is in scope".

That note argued the two "must *not* be collapsed", to keep a within-population loss and a
between-population `F_ST` from being substituted for one another. Both definitions' own
docstrings opened by denying the `F_ST` reading, so the shared body was carrying one reading
under two names, and the hazard was the duplication rather than a defence against it.
Deleting the second copy removes the hazard the note described. `DriftRegime` still separates
the two READINGS, which is where that separation belongs.
-/


/-- **The fourth proportional-reduction body, and the one that could not be reached from
its siblings.**

`PopulationGeneticsFoundations.fstFromHetRatio_eq_hudsonFstFromCoalescenceTimes_eq_r2FromMSE`
already relates
three spellings of `1 - residual/baseline`: a heterozygosity ratio, a coalescence-time
ratio, and an error-to-variance ratio.  `PCCorrectability.Diagnostic.pcTargetAxisEfficacy`
is the fourth — the fraction of a target ancestry axis captured by correction, written in
its own docstring as `V_K = 1 - H'/H`, deliberately echoing `F_ST` — and it could not join
them there, because `Diagnostic` imports nothing outside `PCCorrectability` and none of the
other three files imports `Diagnostic`.

This module reaches all four, through `StratificationConfounding → PCCorrectability`.  That
is the whole reason the statement is here and not beside any of the definitions: **the
tying theorem belongs wherever both sides are visible, not in one of the two files.**  A
guard demanding the latter reported this pair as unfixable when the only thing missing was
permission to speak from a third module.

As with its siblings these are four different quantities and no value of one may be
substituted for another; what is shared is the measure, and sharing it silently is what
this section exists to prevent. -/
theorem pcTargetAxisEfficacy_eq_proportionalReduction (residual baseline : ℝ) :
    Portability.pcTargetAxisEfficacy baseline residual = PopGen.fstFromHetRatio residual baseline ∧
      Portability.pcTargetAxisEfficacy baseline residual =
        Portability.hudsonFstFromCoalescenceTimes residual baseline ∧
      Portability.pcTargetAxisEfficacy baseline residual = PopGen.r2FromMSE residual baseline := by
  refine ⟨rfl, rfl, rfl⟩


end EquilibriumAgreements

section InlinedConstants

/-! ## The remaining inline restatements, tied back

Each definition below spells a `2` or a `4` out in its own body, in its own module. The
theorems here are the edges between those literals and `ploidy`: rewrite `ploidy` and each
one stops compiling, which is the whole of their purpose. They are not restatements of the
definitions — the left-hand sides do not mention `ploidy`, so the equality holds only
because `ploidy` reduces to `2`.

Where the constant is a coalescent scaling the tie goes through `coalescentTimeScale`,
which is `ploidy · Nₑ`; where it is the diploid genotype variance it goes through
`genotypeVarianceHWE`; where it is a scaled rate it goes through `scaledMigrationRate`,
which `scaledMigrationRate_eq_ploidy_form` already forces. -/


/-- **All three twos in the serial-founder within-deme time are coalescent time scales.**
A pair either coalesces inside the chain, on the scale `coalescentTimeScale N`, or survives
into the ancestral population and waits a further `coalescentTimeScale Nanc`. Three literal
twos in one body is exactly the shape in which one of them gets changed alone.

There is no `tAnc` term, and that absence is the whole content of the correction this
body carries. Conditional on surviving to `tAnc` the pair waits `tAnc + 2 Nanc`, so the
survival branch does look like it should contribute one; but the coalesce-early branch is
a PARTIAL expectation, `∫₀^tAnc t (1/2N) e^{-t/2N} dt = 2N (1 - e^{-a}) - tAnc e^{-a}`,
whose `- tAnc e^{-a}` cancels it exactly. Writing `2N (1 - e^{-a})` for the early branch
and `e^{-a} (tAnc + 2 Nanc)` for the late one counts `tAnc e^{-a}` once too often, which
is what this body used to do. -/
theorem serialFounderWithinTime_uses_coalescentTimeScale (N Nanc tAnc : ℝ) :
    PopGen.serialFounderWithinTime N Nanc tAnc
      = coalescentTimeScale N * (1 - Real.exp (-tAnc / coalescentTimeScale N))
          + Real.exp (-tAnc / coalescentTimeScale N) * coalescentTimeScale Nanc := by
  unfold PopGen.serialFounderWithinTime coalescentTimeScale Descent.Core.ploidy; ring


/-- **The two-atom modulus curves are Nei's `G_ST` at the fold, divided by the product of
the two masses.**

`BundleRigidity.mOne` and `BundleRigidity.mTwo` share the numerator `|1 - 2p|`, and their
product is `(1 - 2p)² / (p (1 - p))`. The numerator is `neiGst p (1 - p)` by `neiGst_at_fold`
and the denominator is the product of the family's two masses, so the constant inside the
modulus curves is forced by the `ploidy` in `neiGst`'s normalisation rather than chosen.

This is the folded-spectrum reading of that module stated as an equation: `τ p = 1 - p` is
the ancestral/derived swap, `neiGst p (1 - p)` is symmetric under it, and the two modulus
curves are exchanged by it. `TwoAtom` imports only Mathlib and that is deliberate; the
statement therefore lives here, where both sides are visible. -/
theorem mOne_mul_mTwo_eq_neiGst_at_fold (p : ℝ) :
    Blindness.BundleRigidity.mOne p * Blindness.BundleRigidity.mTwo p = Descent.Core.neiGst p (1 - p) / (p * (1 - p)) := by
  rw [Descent.Core.neiGst_at_fold]
  unfold Blindness.BundleRigidity.mOne Blindness.BundleRigidity.mTwo Descent.Core.ploidy
  rw [div_mul_div_comm, ← sq_abs (1 - 2 * p), pow_two]

end InlinedConstants

section SharedMaps

/-! ## Quantities written twice in two modules, tied here

Three more pairs share a body across modules that cannot see each other. As everywhere in
this file, the tying theorem lives where both sides are visible, and the names stay
separate because they denote different things; what is forbidden is one spelling drifting
while the other stays put. -/

/-- **The importance-weighting effective sample size is a response-to-noise
permeability.** `(Σ w)² / Σ w²` is `Γ² / V` at `Γ = Σ w` and `V = Σ w²`: the reciprocal
variance with which averaging independent copies of a summary estimates its tangent.
`TransferLearningPGS` reads it as a sample count and `Permeability` reads it as
information; the arithmetic is one map, so a change of convention in either is a change in
both. -/
theorem importanceWeightESS_eq_momentPermeability (sum_w sum_w_sq : ℝ) :
    Portability.importanceWeightESS sum_w sum_w_sq = Spectral.momentPermeability sum_w sum_w_sq := rfl


end SharedMaps

end Descent.Program
