/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Descent.Program

/-!
# The conventions this development fixes, and where each one is now enforced

**This module has no theorems and imports nothing. That is the finding it records.**

It used to have a hundred and fifteen theorems and twenty-five imports, reaching from
`Core` to the top of `Portability`, `PopGen` and `Blindness`, and it sat at depth 22.
Every one of those theorems tied a quantity in one module to a convention named in another.
The file's own docstring called that an audit layer rather than a foundation, and argued
that an audit layer must sit above everything it audits: a tying theorem belongs wherever
both of its sides are visible, and the only module that could see fifteen subsystems at
once was this one.

That argument is correct and it was answering the wrong question. A theorem needs both
sides visible; it does not need them visible FROM THE TOP. Almost every "cross-module"
identity here had one side in a subsystem and the other in a convention -- `ploidy`,
`coalescentTimeScale`, `scaledMigrationRate`, `hweHeterozygosity`, `retainedFraction` --
and a convention is not a subsystem. Once the conventions were moved down into `Core`,
where every module already reaches them, "both sides visible" stopped selecting for the
top of the graph and started selecting for the module that declares the definition. Which
is where the theorems went.

## Where the theorems are now

Ninety-one declarations left this file. They were not deleted wholesale and they were not
kept wholesale; each was placed at the lowest module that can state it.

* **Kernels, to `Core`.** `neiGst`, `hudsonFst`, `meanAlleleFreq` and
  `betweenSubgroupVariance` were DEFINED here, at depth 22, out of `ploidy`, `midpoint` and
  `halfDiffSq` and nothing else. They are in `Core/Fst.lean` at depth 2, beside
  `hudsonFromTau` and `hudsonOfNei`, which are the same two estimators as one-field types.
  With them went the witnesses that Nei and Hudson are two functions rather than two
  spellings -- `neiGst_ne_hudsonFst`, `neiGst_ne_hudsonFst_at_mean_half` and
  `no_constant_scales_neiGst_to_hudsonFst` -- the conversion `hudsonFst_eq_of_neiGst`, both
  allele-swap invariances, and `neiGst_at_fold`. `ploidy_at_reference_point` is in
  `Core/Scaling.lean`; `scaledMutationRate_eq_ploidy_form` and its migration twin are in
  `Core/Fst.lean` beside the `_eq` forms of the same two constants.

* **Convention edges, to the module that owns the left-hand side.** Sixty-two theorems of
  the shape `x_uses_ploidy`, `x_uses_timeScale`, `x_uses_hwe` and `x_eq_scaled` are the only
  thing tying a literal `2` or `4` in one definition's body to the named convention.
  Rewrite `ploidy` and each of them stops compiling, which is their entire purpose, and
  that purpose is served from the file the definition is in. They are now in
  `LDDecayTheory`, `DemographicHistory`, `MigrationDriftFoundations`, `PortabilityDrift`
  and twenty-odd others.

* **Genuine cross-subsystem compositions, to `Program/Consequences.lean`.** Three theorems
  need two modules that do not import each other and are not related by a convention:
  `pcTargetAxisEfficacy_eq_proportionalReduction`, which reaches four spellings of
  `1 - residual/baseline` across `PCCorrectability`, `PopulationGeneticsFoundations` and
  `PortabilityDrift`; `importanceWeightESS_eq_momentPermeability`, which reads one
  arithmetic as a sample count in `TransferLearningPGS` and as information in `Spectral`;
  and `mOne_mul_mTwo_eq_neiGst_at_fold`, whose left side is in `BundleRigidity.TwoAtom`,
  a module that imports only Mathlib on purpose. `Consequences` is the corpus's declared
  home for exactly this shape -- "each theorem below needs results from at least two
  modules that do not import each other" -- and it is where they belong.

* **Two deletions, for cause.** `fstFromDrift_uses_coalescentTimeScale` and
  `heterozygosityLossFromDrift_uses_timeScale` were one statement about one body with one
  proof, under two names, differing in the order of two universally quantified binders.
  This file had accumulated one restatement per READING of a body rather than one per fact,
  and two readings of one body are not two edges. The survivor is in `WrightFStatistics`.

Three moves required an import that did not exist, and each is recorded where it was made:
`PCCorrectability/Threshold.lean` gained `Core.Fst` for the two spike specializations,
`SerialFounderChain.lean` gained `Core.Scaling` for the convention its own body writes out,
and `PortabilityDrift/PresentDayMetrics.lean` gained `PopGen.AssortativeMatingPGS` so that
`amEquilibrium_then_drift` could be stated at depth 9 rather than depth 22.

# Identifications: making a named quantity carry its obligation

This is the part of the file that is not a report on a refactor. It is standing policy, it
is cited from `StandardizedGenotypeMoments`, `DriftRegime`, `ObservationalCeiling`,
`LatentMechanismCollapse` and `Recombination`, and none of it depends on any theorem being
in this module.

A Lean `def` cannot be wrong internally, so the entire risk of this development sits in one
place: a definition whose *name* claims a population-genetic meaning that its *formula*
does not have. Every theorem downstream is then machine-checked and misleading. Two
instances have been found by simulation rather than by proof.

`demographicSpike` carried the wrong constant, `2 F m_eff` where the data give
`3.9920 ± 0.0045`. A cross-check between two independently written formulas would have
caught it, and `Core.four_neiGst_eq_standardizedContrastVariance` is that cross-check.

`singletonProportion N₀ N₁ = 1 - log N₀ / log N₁` was worse, and no cross-check of that kind
could have caught it. It returns `0` at the null where the truth is `0.187`, and it takes no
sample size at all although the observable moves from `0.427` to `0.368` when `n` goes from
50 to 200. The signature cannot express the quantity. That is a type error, not an
arithmetic one, and it is invisible to any argument that only compares formulas to other
formulas.

The two failures therefore need two different mechanisms.

* Against a wrong constant: over-determination. Derive the quantity from a primitive so the
  constant is forced, and relate independently written formulas so that drift between them
  fails to compile. That is what the sixty-two convention edges do, from the modules they
  now live in.

* Against a wrong signature: an obligation attached to the name. A named empirical quantity
  must be introduced together with the observable it claims to be, and a proof that the two
  agree. Then a formula that cannot depend on `n` cannot identify an observable that does.
  Claims whose signatures omit required variables are not exported as theorems.

## The ploidy census, which is what gives the convention edges their job

Every non-exponent factor of two in this development traces to the ploidy, and every factor
of four to twice it. Forty-eight definition bodies carry such a two and fourteen carry such
a four. `Core.ploidy` is the one site; a body that writes the literal instead is held to it
by a theorem in that body's own module, so that drift is a compile error rather than a
silent disagreement.

## The reference/alternate allele swap is a metamorphic relation, not a symmetry of taste

Which allele a variant call file names REFERENCE is a property of the assembly, not of the
biology. Swapping it sends `p ↦ 1 - p` at every population simultaneously. Every
allele-frequency-symmetric quantity must therefore be invariant, and every effect-direction
quantity must be negated; a body that is neither is reporting the assembly. That the `F_ST`
bodies do not care which population is called first is `Core.hudsonFst_symm`; that they do
not care which allele is called reference -- the convention that actually varies between
panels -- is `Core.neiGst_allele_swap` and `Core.hudsonFst_allele_swap`.

## One quantity, one definition, one bridge

Standing rules, each of which was learned from a collision:

* The island-model `F_ST` is `fstMigrationDriftEquilibrium`. Write new uses against it
  rather than spelling out `1 / (1 + 4 Nₑ m)` again; a second spelling carries its own
  factor of four with nothing to hold it in step, and needs its own bridge theorem, which
  is a reason not to add one. `equilibriumFst` is worth recording as a hazard: it took its
  arguments in the opposite order to the other two, so the same call spelled the same way
  meant different things depending on which copy was in scope.
* The coalescent `F_ST` map is `coalFst`, called directly by `DemographicHistory`. The name
  `fstFromCoalescenceTime` is absent on purpose.
* The harmonic mean is `OpenQuestions.f1Score`, called by `MetricSpecificPortability`. The
  name `f1ScoreMetric` is absent on purpose.
* `meanAlleleFreq` and `effectiveSymmetricMigration` are deliberately NOT collapsed. The
  bodies coincide, but an allele frequency and a migration rate are not the same quantity,
  and a single name would let a proof about one be applied to the other without anything
  failing. `effectiveSymmetricMigration_eq_meanAlleleFreq_map` records the coincidence,
  which is what a shared convention deserves -- as against the island-model `F_ST`, where
  four names really did denote one quantity and are now one.
* The genotype variance needs no such edge. `genotypeVarianceHWE` and `hweHeterozygosity`
  both CALL `Core.hweHeterozygosity`, which carries `ploidy` in its body, so the edge is the
  call. An identity whose two sides wrap one kernel constrains nothing.

## Two theorems were deleted rather than restated, and the reasons are anti-regression notes

`steppingStoneCharacteristicLength_uses_timeScale` asserted
`steppingStoneCharacteristicLength Ne m = Real.sqrt (coalescentTimeScale Ne * m)`, i.e. that
the 1D decay length carries the `2·Nₑ` convention. The corrected definition is `√(m/(2·μ))`
and contains no effective size at all, so there is no convention to pin: the theorem existed
only because the wrong body happened to contain `2·Nₑ`. What that definition does claim is
`PopulationGeneticsFoundations.steppingStoneCharacteristicLength_balances_mutation`.

`neutralPortability_uses_ploidy` asserted
`neutralPortability r2_0 fst = r2_0 * max 0 (1 - ploidy * fst)`, reading the `2` in the old
`1 - 2·fst` body as ploidy. It was not ploidy. That `2` was the leading coefficient of a
first-order expansion of a heterozygosity ratio, and the expansion is what `battery_bulk56`
falsified: the linear form is off by 12 sems at `fst = 0.05`, well inside the `fst ≪ 0.5`
regime it claimed for itself. The corrected body carries no such constant. What it does
claim about `fst` is at `PortabilityBounds.neutralPortability_pos_beyond_half`.

Both are recorded because a `2` in a body is not evidence of a convention, and a theorem
that pins one is not evidence that the body is right. Three of the four members of the
per-generation retention group -- `1 - 1/(2 Nₑ)`, spelled out in `PhenomeWidePortability`,
`LDDecayTheory`, `PopulationGeneticsFoundations` and `PortabilityDrift` -- belong to a
falsified cluster: at demographic equilibrium simulation measures a retention of
`1.02 ± 0.02` where the closed-population form predicts `e^(-2) = 0.135`, because mutation
replenishes diversity. Agreeing on `2 Nₑ` is exactly the kind of cross-check that cannot see
that, since every identity in the group holds *in* the shared premise whatever its value.
`ldRetainedFraction_uses_timeScale` is the one guard in that group that states what its
formula omits; copy that shape, not the bare ones.

# The regime obligation, stated once

A closed form whose docstring reads `Empirical status: FALSIFIED` or `CONDITIONALLY VALID`
is making two claims at once: an algebraic one, which Lean checks, and a claim about the
conditions under which the algebra describes a population, which until recently nothing
checked. `DriftRegime` established why that matters -- a formula carrying its regime in a
docstring can be moved into a regime where it is false, and every internal cross-check will
still pass, because the identities are identities *in* the shared premise.

Every such closed form now carries its regime in a machine-checkable form, by one of four
mechanisms. Recorded here so that a new one added without any of them is visibly a
departure rather than an oversight:

* **In the signature.** The definition takes a structure whose fields include the regime
  definition: `ClosedPopulationNoMutation` has mutation fixed to zero, an explicitly stated
  approximation inequality.
* **Tied to a regime object.** A theorem identifies the bare formula with a quantity of a
  named regime: `closedPopulation_het_eq_neutralDriftFactor`,
  `heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss` and its siblings. Those two
  are in `PhenomeWidePortability` and `BlindnessRegistry` now, next to the regime object and
  the retention they are about.
* **Never as an external theorem field.** If the development has no derivation connecting a
  numerical chart to a scientific observable, no identification theorem is exported. A
  citation or caller-supplied proposition cannot manufacture that theorem.
* **As a proved failure.** The departure is itself a theorem, so the limit is checkable
  rather than described: `benchmarkRatioForm_cannot_reach_measured`,
  `demoSteppingStoneFst_indistinguishable_from_quadratic`,
  `pairwiseFstFromBranches_eq_fstFromTau_add_mul`,
  `sampleLimitedScratchTargetR2_negative_of_small_sample`.

The fourth is the one worth noticing. Several of these regimes are not conditions under
which the formula holds but statements of how it fails -- and a proved failure is stronger
than a hedged docstring, because it cannot be read past.

# What this file is a standing argument against

A reconciliation module is a report, and a report at the top of an import graph has a
property nothing below it can be made to respect: it can prove that two definitions agree
and neither definition is obliged to keep agreeing, because neither can see the proof. The
right end state for a reconciliation module is that there is nothing left to reconcile from
the top -- the conventions are kernels the subsystems call, and the edges to the literals
that remain are stated where the literals are.

That end state is this file with no theorems in it. If theorems start accumulating here
again, the question to ask about each is not "can this module see both sides" -- it always
can, that is what it is for -- but "is one of the two sides a convention, and if so, why is
that convention not in `Core`".
-/

end Descent.Program
