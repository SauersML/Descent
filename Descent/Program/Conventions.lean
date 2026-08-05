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


/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ploidy_at_reference_point :
    Descent.Core.ploidy = 2 := by
  norm_num [Descent.Core.ploidy]


/-- **Cross-check: the scaled mutation rate in `PopulationGeneticsFoundations`
is twice the coalescent time scale times the mutation rate**, rather than an
independently chosen `4`. -/
theorem scaledMutationRate_eq_ploidy_form (Ne mu : ℝ) :
    Descent.Core.scaledMutationRate Ne mu = 2 * Descent.Core.ploidy * Ne * mu := by
  unfold Descent.Core.scaledMutationRate Descent.Core.ploidy Descent.Core.scaledMutationRate Descent.Core.ploidy; ring

/-- **Cross-check: the scaled migration rate in `PortabilityDrift` uses the
same convention.** These two were written in different files, each spelling
out its own `4`. -/
theorem scaledMigrationRate_eq_ploidy_form (Ne m : ℝ) :
    Descent.Core.scaledMigrationRate Ne m = 2 * Descent.Core.ploidy * Ne * m := by
  unfold Descent.Core.scaledMigrationRate Descent.Core.ploidy Descent.Core.scaledMigrationRate Descent.Core.ploidy; ring

/-- **Cross-check: `heterozygosityLossFromDrift` uses the coalescent time scale**, so the
`2 Nₑ` inside it is the same `ploidy · Nₑ` and not a separate choice.

The name of this theorem calls that body "the drift `F_ST`", and `DriftRegime` names
precisely that reading as the defect: a within-population heterozygosity loss and a
between-population variance ratio are different quantities, and the shared body is what
let one be substituted for the other. What is pinned here is the constant. The regime is
pinned separately, by
`heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss` at the end of this file. -/
theorem fstFromDrift_uses_coalescentTimeScale (t : ℕ) (Ne : ℝ) :
    PopGen.heterozygosityLossFromDrift t Ne = 1 - (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold PopGen.heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay; rw [coalescentTimeScale_eq]

/-- **Cross-check: the within-deme coalescence time carries the same two.**
`PortabilityDrift.twoDemeIMEquilibriumETss` is `2` in units of `Nₑ`
generations, and that two is the ploidy: `E[T_within] = ploidy · Nₑ`
generations is `coalescentTimeScale`, which is `2 Nₑ`. Writing the constant
without saying so left a bare numeral in an equilibrium; this theorem says
which two it is. -/
theorem twoDemeIMEquilibriumETss_eq_ploidy (M : ℝ) :
    Portability.twoDemeIMEquilibriumETss M = Descent.Core.ploidy := by
  unfold Portability.twoDemeIMEquilibriumETss Descent.Core.ploidy; ring

/-- **The two in the recessive drift parameter is the ploidy.**

`RareVariantPortability.recessiveMutationSelectionDriftParameter` is
`2 Nₑ √(μ s)`, and that two is the number of gene copies per individual: a
population of `Nₑ` diploids carries `ploidy · Nₑ` gene copies, drift acts at rate
`1 / (ploidy · Nₑ)`, and the parameter is the selective force `√(μ s)` measured
against it. Written inline the two was a bare numeral in a quantity whose whole
job is to say when drift wins, and a haploid reading of the same formula would
be off by exactly this factor. -/
theorem recessiveMutationSelectionDriftParameter_uses_ploidy (Ne mu s : ℝ) :
    Portability.recessiveMutationSelectionDriftParameter Ne mu s
      = Descent.Core.ploidy * Ne * Real.sqrt (mu * s) := by
  unfold Portability.recessiveMutationSelectionDriftParameter Descent.Core.ploidy; ring

/-- **The four in the dominant drift parameter is the corpus's own rate scaling.**

`RareVariantPortability.mutationSelectionDriftParameter` is `4 Nₑ h s`, and the
`4 Nₑ` is not an independent convention: it is `scaledMutationRate`, the same
`4 Nₑ ·` normalisation the corpus already applies to a mutation rate to get `θ`
and to a migration rate to get `4 Nₑ m`, applied here to the heterozygous
selection load `h s`. This is deliberately NOT stated as a multiple of `ploidy`.
Only one of the two factors in `4 = 2 · 2` is a gene-copy count; the other comes
from the diffusion limit, and tying it to `ploidy` would record a claim about
genetics that this parameter does not make. -/
theorem mutationSelectionDriftParameter_eq_scaledMutationRate (Ne s h : ℝ) :
    Portability.mutationSelectionDriftParameter Ne s h = Descent.Core.scaledMutationRate Ne (h * s) := by
  unfold Portability.mutationSelectionDriftParameter Descent.Core.scaledMutationRate Descent.Core.ploidy; ring

/-- **The two in the allele-frequency retention ratio is the ploidy, twice, and
that is why the ratio does not depend on it.**

`PortabilityDrift.tagAlleleFreqRetentionAt` is `2p_t(1 - p_t) / (2p_0(1 - p_0))`,
and both twos are the same gene-copy count that `genotypeVarianceHWE` carries:
the body is a ratio of Hardy-Weinberg genotype variances at two times. Stating
it that way is not decoration. A bare `2` in a numerator and a bare `2` in a
denominator can be two DIFFERENT conventions written the same way -- a
heterozygosity over a genotype variance, say -- and the ratio would then be off
by a factor while looking symmetric. Once both are `genotypeVarianceHWE` the
cancellation is forced, and the retention is a pure ratio that a haploid corpus
would compute identically. -/
theorem tagAlleleFreqRetentionAt_eq_genotypeVarianceHWE_ratio {p q : ℕ}
    (m : Portability.CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) :
    Portability.tagAlleleFreqRetentionAt m t i =
      genotypeVarianceHWE (Portability.tagAlleleFreqTargetAt m t i) /
        genotypeVarianceHWE (m.tagAlleleFreqSource i) := by
  unfold Portability.tagAlleleFreqRetentionAt genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

/-- **The same two, at the causal variants.** `causalAlleleFreqRetentionAt` is
the identical ratio on the causal side, and it is tied here separately rather
than by appeal to the tag version: two definitions with the same shape in one
file are exactly the pair a single fix leaves half-repaired. -/
theorem causalAlleleFreqRetentionAt_eq_genotypeVarianceHWE_ratio {p q : ℕ}
    (m : Portability.CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) :
    Portability.causalAlleleFreqRetentionAt m t j =
      genotypeVarianceHWE (Portability.causalAlleleFreqTargetAt m t j) /
        genotypeVarianceHWE (m.causalAlleleFreqSource j) := by
  unfold Portability.causalAlleleFreqRetentionAt genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

/-- **The three twos in the deme-corrected flow step are three different twos,
and only one of them is the ploidy.**

`DGP.fstDemeCorrectedFlowStep` is `F + (1 - F)/(2 Nₑ) - 2(2 mig + mu) F`, and
the constants are:

* `2 Nₑ` -- the GENE-COPY COUNT, `coalescentTimeScale Nₑ = ploidy · Nₑ`. Drift
  makes a pair identical at rate one over the number of copies, so this two is
  the ploidy and is stated as such.
* the inner `2` on `mig` -- the DEME-COUNT correction, `islandDemeCorrection 2`.
  A pair of lineages switches between the same-deme and different-deme states at
  emigration plus immigration, which at `d` demes is `m · d/(d - 1)` and at two
  demes is `2 m`. It would be `3/2 m` at three demes; nothing about ploidy moves
  when it changes.
* the outer `2` on the whole flow term -- the PAIR of lineages, either of which
  can leave the identity class. A pair is two gene copies whatever the ploidy of
  the organism carrying them, so this one is left inline: tying it to `ploidy`
  would make a haploid corpus compute a different number for the same event, and
  it does not.

Distinguishing them is the point. All three are the numeral `2` in one line of
source, and the guard that counts convention restatements cannot tell them
apart. -/
theorem fstDemeCorrectedFlowStep_constants_named (p : PopGen.EvolutionaryParameters)
    (F : ℝ) :
    PopGen.fstDemeCorrectedFlowStep p F =
      F + (1 - F) / coalescentTimeScale p.Ne
        - 2 * (Descent.Core.islandDemeCorrection 2 * p.mig + p.mu) * F := by
  unfold PopGen.fstDemeCorrectedFlowStep coalescentTimeScale Descent.Core.islandDemeCorrection
    Descent.Core.islandDemeCorrection Descent.Core.ratio Descent.Core.ploidy Descent.Core.ploidy
  norm_num

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


theorem effectiveSymmetricMigration_eq_meanAlleleFreq_map (m₁₂ m₂₁ : ℝ) :
    Portability.effectiveSymmetricMigration m₁₂ m₂₁ = Descent.Core.meanAlleleFreq m₁₂ m₂₁ := by
  unfold Portability.effectiveSymmetricMigration Descent.Core.meanAlleleFreq Descent.Core.midpoint; ring


/-- **Hudson's frequency form IS `1 - H_w/H_b`**, which is what puts it in the lattice.

`hudsonFst` is written `(p₁ - p₂)² / (p₁(1-p₂) + p₂(1-p₁))`, and nothing related that shape
to the heterozygosity-ratio reading the rest of the corpus states `F_ST` results in. It is
the same number: with `H_w = p₁(1-p₁) + p₂(1-p₂)` the mean within-subgroup heterozygosity
and `H_b = p₁(1-p₂) + p₂(1-p₁)` the between-subgroup one, `H_b - H_w = (p₁ - p₂)²` exactly,
so the squared frequency difference in the numerator is not a separate convention -- it is
the heterozygosity excess, already reduced.

This is the edge that was missing. `fstFromHetRatio` is `Core.proportionalReduction`, and
`slatkin_hetRatio_eq_coalescenceRatio` carries that to
`hudsonFstFromCoalescenceTimes`, so the chain now runs frequencies to heterozygosities to
coalescence times without leaving the Hudson convention -- which is the claim the corpus's
`τ/(1+τ)` results have been resting on.

    Empirical status: NOT AN EMPIRICAL CLAIM -- an algebraic identity between two
    spellings of one estimator. The measurement that matters is the one in `neiFst`'s
    docstring, where Hudson tracks the split law at 0.03 sems and Nei does not. -/
theorem hudsonFst_eq_fstFromHetRatio (p₁ p₂ : ℝ)
    (h : p₁ * (1 - p₂) + p₂ * (1 - p₁) ≠ 0) :
    Descent.Core.hudsonFst p₁ p₂
      = PopGen.fstFromHetRatio (p₁ * (1 - p₁) + p₂ * (1 - p₂))
          (p₁ * (1 - p₂) + p₂ * (1 - p₁)) := by
  unfold Descent.Core.hudsonFst PopGen.fstFromHetRatio Descent.Core.proportionalReduction
  field_simp
  ring


/-! ### Reference/alternate allele swap: a metamorphic relation, not a symmetry of taste

Which allele a variant call file names REFERENCE is a property of the assembly, not
of the biology. Swapping it sends `p ↦ 1 - p` at every population simultaneously.
Every allele-frequency-symmetric quantity must therefore be invariant, and every
effect-direction quantity must be negated; a body that is neither is reporting the
assembly. The corpus proves that its `F_ST` bodies do not care which population is
called first (`hudsonFst_symm`) but had no statement about which allele is called
reference, which is the convention that actually varies between panels. -/


/-- **Cross-check: the fair two-point variance in `ImitationRigidity` is the
between-subgroup variance.** Both are `(a - b)² / 4`: the variance of a
two-point law with equal weights. One is used as a nonconcentration witness for
a resolvent and the other as the numerator of `F_ST`, and neither file knew the
other existed. -/
theorem fairTwoPointVariance_eq_betweenSubgroupVariance (a b : ℝ) :
    Blindness.fairTwoPointVariance a b = Descent.Core.betweenSubgroupVariance a b := by
  unfold Blindness.fairTwoPointVariance Descent.Core.betweenSubgroupVariance Descent.Core.halfDiffSq; ring


/-- **Cross-check: the two spellings of Nei's `G_ST` in this corpus agree.**

What this proves is that two independently written spellings of NEI's `G_ST`
coincide. **Neither side is Hudson's estimator.** That one is `hudsonFst`, and
`neiGst_ne_hudsonFst` exhibits a point where it differs from both of these, so
do not read either name here as Hudson's. -/
theorem neiGstFromFrequencies_eq_neiGst (p₁ p₂ : ℝ)
    (h : Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂) ≠ 0) :
    PopGen.neiGstFromFrequencies p₁ p₂ = Descent.Core.neiGst p₁ p₂ := by
  rw [Descent.Core.neiGst_eq_varianceRatio p₁ p₂ h]
  change (p₁ - p₂) ^ 2 /
      (4 * Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂)) =
    ((p₁ - p₂) ^ 2 / 4) /
      (Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂))
  field_simp [h]


end Differentiation

section EquilibriumAgreements

/-! **The island-model `F_ST` is one definition, `fstMigrationDriftEquilibrium`.**
Write new uses against it rather than spelling out `1 / (1 + 4 Nₑ m)` again; a second
spelling would carry its own factor of four with nothing to hold it in step.

`equilibriumFst` is worth recording as a hazard: it took its arguments in the opposite
order to the other two, so the same call spelled the same way meant different things
depending on which copy was in scope. -/

/-- **Cross-check: the two assortative-mating inflation claims agree only at
full heritability.**

`StratificationConfounding` carried `amInflationFactor r = 1/(1 - r)` and
`AssortativeMatingPGS` carries `amEquilibriumVariance V_A r h² = V_A/(1 - r h²)`
for the same quantity, and no theorem related them. Forward simulation with the spousal correlation
measured rather than assumed puts the second within
-5% to +1% and the first between +3% and +82% high, so the first is deleted.
This theorem records why the disagreement was invisible: the two coincide
exactly when `h² = 1`, which is the only case anyone would have checked by
inspection, and diverge with `h²` everywhere else. Assortative mating is a
forward-time phenomenon, so no coalescent simulation could have separated
them. -/
theorem amEquilibriumVariance_at_full_heritability (V_A r : ℝ) :
    PopGen.amEquilibriumVariance V_A r 1 = V_A / (1 - r) := by
  unfold PopGen.amEquilibriumVariance
  ring_nf

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

theorem fstMigrationDriftEquilibrium_eq_scaled (Ne m : ℝ) :
    Portability.fstMigrationDriftEquilibrium Ne m =
      PopGen.fstMutationDriftEquilibrium (Descent.Core.scaledMigrationRate Ne m) := by
  unfold Portability.fstMigrationDriftEquilibrium PopGen.fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  rw [scaledMigrationRate_eq_ploidy_form]; unfold Descent.Core.ploidy; ring_nf

/-! ### Per-generation drift rate, written out in three modules

`1 / (2 Nₑ)` appears independently in `LongitudinalPortability`,
`DemographicHistory` and `LDDecayTheory` under three names. It is the
reciprocal of the coalescent time scale in each. -/

theorem driftLDCreationRate_eq_inv_timeScale (Ne : ℝ) :
    PopGen.driftLDCreationRate Ne = 1 / coalescentTimeScale Ne := by
  unfold PopGen.driftLDCreationRate PopGen.driftRatePerGen PopGen.alleleFreqDivergenceRate
  rw [coalescentTimeScale_eq]

theorem driftRatePerGen_eq_inv_timeScale (Ne : ℝ) :
    PopGen.driftRatePerGen Ne = 1 / coalescentTimeScale Ne := by
  unfold PopGen.driftRatePerGen PopGen.alleleFreqDivergenceRate
  rw [coalescentTimeScale_eq]

/-- **Cross-check: the `2 Nₑ` inside `coalFst` is the coalescent time scale.**
`coalFst t Ne = t / (t + 2 Nₑ)` is `t / (t + E[T_within])`, and `E[T_within]`
is `ploidy · Nₑ` generations. Writing the two inline left the constant free;
this states which two it is. -/
theorem coalFst_uses_coalescentTimeScale (t Ne : ℝ) :
    PopGen.coalFst t Ne = t / (t + coalescentTimeScale Ne) := by
  unfold PopGen.coalFst Descent.Core.oddsLike; rw [coalescentTimeScale_eq]

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

/-- Wright's compounding identity: one minus the product of retentions. It is
written once for the two branches of a split and once for the two levels of
the `F`-statistic hierarchy. -/
theorem pairwiseFstFromBranches_eq_wrightFIT (a b : ℝ) :
    Portability.pairwiseFstFromBranches a b = PopGen.wrightFIT a b := by
  unfold Portability.pairwiseFstFromBranches PopGen.wrightFIT Descent.Core.complementaryComposition; ring_nf

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

theorem neutralDriftFactor_uses_timeScale (Ne : ℝ) (t : ℕ) :
    Portability.neutralDriftFactor Ne t = (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold Portability.neutralDriftFactor; rw [coalescentTimeScale_eq]

/-- **The drift channel enters through `2·Nₑ`, and drift is not the whole retention.**
The recombination factor `(1 - r)` is part of the retained fraction, so
`(1 - 1/coalescentTimeScale Ne)^t` alone is NOT this quantity -- it is the `r = 0`
slice. This theorem pins the `2·Nₑ` convention inside the full expression. -/
theorem ldRetainedFraction_uses_timeScale (r Ne : ℝ) (t : ℕ) :
    PopGen.ldRetainedFraction r Ne t
      = ((1 - r) * (1 - 1 / coalescentTimeScale Ne)) ^ t := by
  unfold PopGen.ldRetainedFraction PopGen.ldRetentionPerGen; rw [coalescentTimeScale_eq]

theorem heterozygosityLossFromDrift_uses_timeScale (Ne : ℝ) (t : ℕ) :
    PopGen.heterozygosityLossFromDrift t Ne = 1 - (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold PopGen.heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay; rw [coalescentTimeScale_eq]

theorem wrightFisherDriftRetention_uses_timeScale (N : ℕ) (t : ℕ) :
    Portability.wrightFisherDriftRetention N t
      = (1 - 1 / coalescentTimeScale (N : ℝ)) ^ t := by
  unfold Portability.wrightFisherDriftRetention; rw [coalescentTimeScale_eq]

/-! ### The coalescent time coordinate, written out twice

`t / (2 Nₑ)` is time in coalescent units, in `PortabilityDrift` and in `DGP`. -/

theorem coalescentTau_uses_timeScale (t Ne : ℝ) :
    Portability.coalescentTau t Ne = t / coalescentTimeScale Ne := by
  unfold Portability.coalescentTau; rw [coalescentTimeScale_eq]

/-! ### The scaled rates, written out on three parameter records

`θ = 4 Nₑ μ` and `M = 4 Nₑ m` used to appear on two parameter records, each spelling out
its own four: `GenerationalPopGenParameters` in `PortabilityDrift` and
`EvolutionaryParameters` in `DGP`. There is now one record, `Core.PopGenParameters`, and
its `theta` and `bigM` are `Core.scaledMutationRate` and `Core.scaledMigrationRate` by
definition -- so the two theorems that used to hold those spellings together are deleted
rather than restated. What remains below is the `EvolutionaryParameters` pair, which is
still a separate record. -/

theorem EvolutionaryParameters_theta_eq_ploidy_form (p : PopGen.EvolutionaryParameters) :
    PopGen.EvolutionaryParameters.theta p = 2 * Descent.Core.ploidy * p.Ne * p.mu := by
  unfold PopGen.EvolutionaryParameters.theta Descent.Core.ploidy Descent.Core.scaledMutationRate Descent.Core.ploidy; ring

theorem EvolutionaryParameters_bigM_eq_ploidy_form (p : PopGen.EvolutionaryParameters) :
    PopGen.EvolutionaryParameters.bigM p = 2 * Descent.Core.ploidy * p.Ne * p.mig := by
  unfold PopGen.EvolutionaryParameters.bigM Descent.Core.ploidy Descent.Core.scaledMigrationRate Descent.Core.ploidy; ring

/-- **The between-population variance of the mean breeding value is
`ploidy · F_ST · V_A`.**

Two independently drifting populations each contribute `F_ST V_A`, so the
variance of their difference carries the ploidy factor. Writing `2` here is
the same convention as everywhere else and is now tied to it. -/
theorem Var_Delta_Mu_eq_ploidy_form (V_A fst : ℝ) :
    Portability.Var_Delta_Mu V_A fst = Descent.Core.ploidy * fst * V_A := by
  unfold Portability.Var_Delta_Mu Descent.Core.ploidy; ring

/-- **The one-population PGS drift variance carries the same ploidy factor.**

`pgsDriftVariance_one_pop` is the single-population form of `Var_Delta_Mu`, and its `2` is
the same convention: `ploidy · F_ST · V_A`.  The two definitions are alpha-equivalent, and
this pair of theorems is what says so rather than leaving it to the reader. -/
theorem pgsDriftVariance_one_pop_eq_ploidy_form (V_A fst : ℝ) :
    PopGen.pgsDriftVariance_one_pop V_A fst = Descent.Core.ploidy * fst * V_A := by
  unfold PopGen.pgsDriftVariance_one_pop Portability.Var_Delta_Mu Descent.Core.ploidy
  ring

/-- The two drift-variance definitions are the same quantity. -/
theorem pgsDriftVariance_one_pop_eq_Var_Delta_Mu (V_A fst : ℝ) :
    PopGen.pgsDriftVariance_one_pop V_A fst = Portability.Var_Delta_Mu V_A fst := by
  rw [pgsDriftVariance_one_pop_eq_ploidy_form, Var_Delta_Mu_eq_ploidy_form]

/-! ### Genotype variance inside sums and products

Eight further definitions carry `2 p (1 - p)` as a factor rather than as their
whole body: score means and variances, Fisher's average effect, dominance and
additive variance, two noncentrality parameters, and a pairwise epistatic
variance. Each is now written against `genotypeVarianceHWE`. -/

theorem pgsVariance_uses_hwe {m : ℕ} (β p : Fin m → ℝ) :
    Portability.pgsVariance β p = ∑ i, β i ^ 2 * genotypeVarianceHWE (p i) := by
  unfold Portability.pgsVariance genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

theorem dominanceVariance_uses_hwe {m : ℕ} (p d : Fin m → ℝ) :
    PopGen.dominanceVariance p d = ∑ i, (genotypeVarianceHWE (p i) * d i) ^ 2 := by
  unfold PopGen.dominanceVariance genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

/-- **`additiveVariance` is a sum over loci and therefore assumes linkage equilibrium**;
this theorem pins its `2 p (1 - p)` to `ploidy` and says nothing about that assumption.

The qualifier is load-bearing. The per-locus sum drops the cross term
`Σ_{i≠j} 4 α_i α_j D_ij`, and the sign of the resulting error flips with the sign of the
effect product, so no constant repairs it: at `p = 1/2`, `D = 1/8`, `α = (1,1)` gives `1`
against a true `3/2`, while `α = (1,-1)` gives `1` against a true `1/2`. The
unconditional reading is FALSIFIED (`VarianceComponents.additiveVariance`). -/
theorem additiveVariance_uses_hwe {m : ℕ} (p α : Fin m → ℝ) :
    PopGen.additiveVariance p α = ∑ i, genotypeVarianceHWE (p i) * (α i) ^ 2 := by
  unfold PopGen.additiveVariance genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

theorem noncentralityParam_uses_hwe (n : ℕ) (beta p : ℝ) :
    Decision.noncentralityParam n beta p = n * beta ^ 2 * genotypeVarianceHWE p := by
  unfold Decision.noncentralityParam genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

theorem gwasNCP_uses_hwe (n : ℕ) (β p : ℝ) :
    PopGen.gwasNCP n β p = n * β ^ 2 * genotypeVarianceHWE p := by
  unfold PopGen.gwasNCP Portability.ncp Portability.effectiveFisherInformation Portability.fisherInformation genotypeVarianceHWE
    genotypeVarianceHWE Descent.Core.product Descent.Core.hweHeterozygosity Descent.Core.ploidy
  ring_nf

theorem effectiveFisherInformation_uses_hwe (n : ℕ) (p r2_ld : ℝ) :
    Portability.effectiveFisherInformation n p r2_ld = n * genotypeVarianceHWE p * r2_ld := by
  unfold Portability.effectiveFisherInformation Portability.fisherInformation genotypeVarianceHWE
    genotypeVarianceHWE Descent.Core.product Descent.Core.hweHeterozygosity Descent.Core.ploidy
  ring_nf

theorem epistaticVariancePairwise_uses_hwe (γ p₁ p₂ : ℝ) :
    Portability.epistaticVariancePairwise γ p₁ p₂ =
      γ ^ 2 * genotypeVarianceHWE p₁ * genotypeVarianceHWE p₂ := by
  unfold Portability.epistaticVariancePairwise genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

/-- The between-population drift variance of the score, carrying the same
ploidy factor as `Var_Delta_Mu`. -/
theorem expectedPGSDiffVariance_eq_ploidy_form (V_A fst : ℝ) :
    PopGen.expectedPGSDiffVariance V_A fst = Descent.Core.ploidy * Descent.Core.ploidy * fst * V_A := by
  unfold PopGen.expectedPGSDiffVariance Descent.Core.ploidy; ring

/-! ### The remaining singletons

Each of these uses the ploidy convention once, with no sibling to disagree
with, so only a derivation from `ploidy` ties them down. -/

/-- **Do not simplify this to `coalescentTimeScale Ne * log 2`.** That is the `r → 0`
limit and is false at every `r > 0`. The `2·Nₑ` convention appears inside the retention
whose logarithm sets the half-life, which is what this states. -/
theorem ldHalfLife_uses_timeScale (r Ne : ℝ) :
    PopGen.ldHalfLife r Ne
      = Real.log 2 / (-Real.log ((1 - r) * (1 - 1 / coalescentTimeScale Ne))) := by
  unfold PopGen.ldHalfLife PopGen.ldRetentionPerGen; rw [coalescentTimeScale_eq]

/-! `steppingStoneCharacteristicLength_uses_timeScale` has been DELETED, not
restated. It asserted
`steppingStoneCharacteristicLength Ne m = Real.sqrt (coalescentTimeScale Ne * m)`,
i.e. that the 1D decay length carries the `2·Nₑ` ploidy convention. The
corrected definition is `√(m/(2·μ))` and contains no effective size at all, so
there is no convention here to pin and no honest restatement to make: the
theorem existed only because the wrong body happened to contain `2·Nₑ`. Its
replacement, stating what that definition does claim, is
`PopulationGeneticsFoundations.steppingStoneCharacteristicLength_balances_mutation`. -/

theorem cumulativeDrift_uses_timeScale {T : ℕ} (Ne : Fin T → ℝ) :
    PopGen.cumulativeDrift Ne = ∑ i, 1 / coalescentTimeScale (Ne i) := by
  unfold PopGen.cumulativeDrift
  simp only [coalescentTimeScale_eq]

theorem ldRetentionPerGen_uses_timeScale (r Ne : ℝ) :
    PopGen.ldRetentionPerGen r Ne = (1 - r) * (1 - 1 / coalescentTimeScale Ne) := by
  unfold PopGen.ldRetentionPerGen; rw [coalescentTimeScale_eq]

theorem hetDecayFactor_uses_timeScale (Ne θ : ℝ) :
    PopGen.hetDecayFactor Ne θ
      = (1 - 1 / coalescentTimeScale Ne) * (1 - θ / coalescentTimeScale Ne) := by
  unfold PopGen.hetDecayFactor PopGen.hetDecayFromScaled; rw [coalescentTimeScale_eq]

/-- The differentiation transient's decay factor is on the same coalescent clock as the
heterozygosity one it extends: the migration channel divides by the timescale, not by a
free constant. -/
theorem fstTransientDecayFromScaled_uses_timeScale (Ne θ bigM : ℝ) :
    PopGen.fstTransientDecayFromScaled Ne θ bigM
      = PopGen.hetDecayFromScaled Ne θ * (1 - bigM / coalescentTimeScale Ne) := by
  unfold PopGen.fstTransientDecayFromScaled; rw [coalescentTimeScale_eq]

theorem asymmetricFst_eq_scaled (Ne m₁₂ m₂₁ : ℝ) :
    Portability.asymmetricFst Ne m₁₂ m₂₁
      = PopGen.fstMutationDriftEquilibrium (Descent.Core.scaledMigrationRate Ne (m₁₂ + m₂₁)) := by
  unfold Portability.asymmetricFst PopGen.fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  rw [scaledMigrationRate_eq_ploidy_form]; unfold Descent.Core.ploidy; ring_nf

/-! The bridge from the migration-drift equilibrium to the scaled mutation-drift form is
`fstMigrationDriftEquilibrium_eq_scaled` above.  A second copy of it stood here, for the
second spelling of that equilibrium -- which is what the note above predicted: "A second
spelling of `1 / (1 + 4 Nₑ m)` would need its own bridge theorem, which is a reason not to
add one."  The spelling is gone from `PortabilityDrift` and its bridge with it. -/

theorem fstMigrationMutationEquilibriumManyDemes_eq_scaled (Ne m μ : ℝ) :
    PopGen.fstMigrationMutationEquilibriumManyDemes Ne m μ
      = 1 / (1 + Descent.Core.scaledMigrationRate Ne m + Descent.Core.scaledMutationRate Ne μ) := by
  unfold PopGen.fstMigrationMutationEquilibriumManyDemes Descent.Core.fstFromFlow
  rw [scaledMigrationRate_eq_ploidy_form, scaledMutationRate_eq_ploidy_form]
  unfold Descent.Core.ploidy; ring_nf

/-- **The finite-deme island equilibrium carries the same two scaled rates.** Its
`4 Nₑ m` is `scaledMigrationRate` and its `4 Nₑ μ` is `scaledMutationRate`, exactly as in
the deme-blind limit form; the deme correction multiplies the migration rate and does not
touch either constant. Without this the `4` would be a third inlined ploidy convention. -/
theorem fstIslandEquilibriumFiniteDemes_eq_scaled (Ne m μ nDemes : ℝ) :
    PopGen.fstIslandEquilibriumFiniteDemes Ne m μ nDemes
      = 1 / (1 + Descent.Core.scaledMigrationRate Ne m * Descent.Core.islandDemeCorrection nDemes
              + Descent.Core.scaledMutationRate Ne μ) := by
  -- The bridge this used to go through, `fstIslandEquilibriumFiniteDemes_eq`, was
  -- deleted when the body was repointed at `Core.fstFromFlow`, which is `1/(1+x)`
  -- and needs no normalisation lemma of its own. What is left to say is that the
  -- two `4`s in the flow are the two scaled rates and not a third inlined ploidy
  -- convention, which is exactly what the two `_eq_ploidy_form` rewrites state.
  unfold PopGen.fstIslandEquilibriumFiniteDemes Descent.Core.fstFromFlow
  rw [scaledMigrationRate_eq_ploidy_form, scaledMutationRate_eq_ploidy_form]
  unfold Descent.Core.ploidy; ring_nf

theorem expectedFreqDiffSq_uses_hwe (fst p0 : ℝ) :
    PopGen.expectedFreqDiffSq fst p0 = fst * genotypeVarianceHWE p0 := by
  unfold PopGen.expectedFreqDiffSq genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

theorem pgsMean_uses_ploidy {m : ℕ} (β p : Fin m → ℝ) :
    Portability.pgsMean β p = ∑ i, β i * (Descent.Core.ploidy * p i) := by
  unfold Portability.pgsMean Descent.Core.ploidy; ring_nf

theorem fisherAverageEffect_uses_ploidy (a d p : ℝ) :
    PopGen.fisherAverageEffect a d p = a + d * (1 - Descent.Core.ploidy * p) := by
  unfold PopGen.fisherAverageEffect Descent.Core.ploidy; ring

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

theorem selectedDriftFactor_uses_timeScale (Ne : ℝ) (t : ℕ) (s_correction : ℝ) :
    Portability.selectedDriftFactor Ne t s_correction
      = (1 - 1 / coalescentTimeScale Ne + s_correction) ^ t := by
  unfold Portability.selectedDriftFactor; rw [coalescentTimeScale_eq]

theorem SplitMigrationModel_scaledMigration_eq_ploidy_form
    (m : Portability.SplitMigrationModel) :
    Descent.Core.scaledMigrationRate m.Ne m.mig = 2 * Descent.Core.ploidy * m.Ne * m.mig := by
  unfold Descent.Core.scaledMigrationRate Descent.Core.ploidy Descent.Core.scaledMigrationRate Descent.Core.ploidy; ring

theorem fstMigDriftNext_uses_timeScale (Ne m Fst : ℝ) :
    Portability.fstMigDriftNext Ne m Fst
      = (1 - 2 * m - 1 / coalescentTimeScale Ne) * Fst
        + 1 / coalescentTimeScale Ne := by
  unfold Portability.fstMigDriftNext; rw [coalescentTimeScale_eq]

theorem ibdFst_eq_ploidy_form (d N sigma_sq : ℝ) :
    PopGen.ibdFst d N sigma_sq = d / (2 * Descent.Core.ploidy * N * sigma_sq + d) := by
  unfold PopGen.ibdFst Descent.Core.ploidy; ring_nf

theorem EvolutionaryParameters_tau_uses_timeScale (p : PopGen.EvolutionaryParameters) :
    PopGen.EvolutionaryParameters.tau p = p.t_div / coalescentTimeScale p.Ne := by
  unfold PopGen.EvolutionaryParameters.tau; rw [coalescentTimeScale_eq]

/-- The factor of two in the shared-LD exponent is the PLOIDY: two lineages must
independently avoid recombination, so the per-meiosis survival `1 - r` is raised to
`ploidy · t_div` and not to `t_div`. The statement survived the body's correction from
`exp(-2·r·t_div)` to `(1-r)^(2·t_div)` with the exponential replaced by the exact survival,
which is the point of stating the convention separately from the functional form: the
convention is about the EXPONENT, and the correction was to the base. -/
theorem sharedLDRetention_uses_ploidy (p : PopGen.EvolutionaryParameters) :
    PopGen.sharedLDRetention p = (1 - p.recomb) ^ (Descent.Core.ploidy * p.t_div) := by
  unfold PopGen.sharedLDRetention Descent.Core.ploidy; ring_nf

theorem demoSteppingStoneFst_eq_scaled (d Ne m σ_sq : ℝ) :
    PopGen.demoSteppingStoneFst d Ne m σ_sq
      = d / (d + Descent.Core.scaledMigrationRate Ne m * σ_sq) := by
  unfold PopGen.demoSteppingStoneFst
  rw [scaledMigrationRate_eq_ploidy_form]; unfold Descent.Core.ploidy; ring_nf

/-! ### The last seven

Each carries the convention in its own shape: inside a `let`, in a recursion
step, or under two nested decay factors. A relation reaches all of them. -/

theorem tauAt_uses_timeScale (g : Descent.Core.PopGenParameters) (t : ℕ) :
    Descent.Core.PopGenParameters.tauAt g t
      = (t : ℝ) / coalescentTimeScale g.Ne := by
  unfold Descent.Core.PopGenParameters.tauAt; rw [coalescentTimeScale_eq]

/-- The divergence rate is the reciprocal of the coalescent timescale, and the scaled mutation
and migration rates do not appear. This theorem previously carried them in the denominator; the
body they came from was falsified at up to 1620 sems and the convention statement follows it. -/
theorem alleleFreqDivergenceRate_eq_scaled (Ne mu m_rate : ℝ) :
    PopGen.alleleFreqDivergenceRate Ne mu m_rate = 1 / coalescentTimeScale Ne := by
  unfold PopGen.alleleFreqDivergenceRate
  rw [coalescentTimeScale_eq]

theorem fstMutationDriftTransient_uses_timeScale (θ t Ne : ℝ) :
    PopGen.fstMutationDriftTransient θ t Ne
      = PopGen.fstMutationDriftEquilibrium θ *
          (1 - Real.exp (-(1 + θ) * t / coalescentTimeScale Ne)) := by
  unfold PopGen.fstMutationDriftTransient; rw [coalescentTimeScale_eq]

theorem MutationDriftModelAssumptions_fstTransient_uses_timeScale
    (m : Portability.MutationDriftModelAssumptions) :
    Portability.MutationDriftModelAssumptions.fstTransient m
      = m.fstEquilibrium *
          (1 - Real.exp (-(1 + m.theta) * m.t / coalescentTimeScale m.Ne)) := by
  unfold Portability.MutationDriftModelAssumptions.fstTransient
  rw [coalescentTimeScale_eq]

theorem hetMutationDriftRecurrence_step_uses_timeScale
    (Ne mu H₀ : ℝ) (t : ℕ) :
    PopGen.hetMutationDriftRecurrence Ne mu H₀ (t + 1)
      = (1 - 1 / coalescentTimeScale Ne) * PopGen.hetMutationDriftRecurrence Ne mu H₀ t
        + Descent.Core.ploidy * mu * (1 - PopGen.hetMutationDriftRecurrence Ne mu H₀ t) := by
  change
    (1 - 1 / (2 * Ne)) * PopGen.hetMutationDriftRecurrence Ne mu H₀ t +
        2 * mu * (1 - PopGen.hetMutationDriftRecurrence Ne mu H₀ t) = _
  rw [coalescentTimeScale_eq]
  unfold Descent.Core.ploidy
  rfl

/-- Equilibrium heterozygosity under mutation-drift balance, `θ/(1 + θ)`,
written out with its own four. This is the last inline restatement of the
ploidy convention in the development. -/
theorem hetMutationFloor_eq_scaled (Ne mu : ℝ) :
    Portability.hetMutationFloor Ne mu
      = Descent.Core.scaledMutationRate Ne mu / (1 + Descent.Core.scaledMutationRate Ne mu) := by
  unfold Portability.hetMutationFloor
  rw [scaledMutationRate_eq_ploidy_form]; unfold Descent.Core.ploidy; ring_nf

/-! ### Shared primitives

Several groups of definitions across the development are the same map applied
to different quantities. Left unrelated, each is free to drift from the others;
naming the map once and relating them makes a divergence a failed proof. This
is the same device as `ploidy`, applied to structure rather than to a
constant. -/

/-! ### Retention and ratio maps

Three further groups are one map under several names. -/

/-- **Present-day PGS variance is a retained fraction of the ancestral variance.**
`presentDayPGSVariance` is not a wrapper over the kernel -- it routes through
`pgsVarianceFromHet` -- so this is a real identity and not a restatement of a body. -/
theorem presentDayPGSVariance_eq_retainedFraction (V_A fst : ℝ) :
    Portability.presentDayPGSVariance V_A fst = Descent.Core.retainedFraction fst V_A := by
  unfold Portability.presentDayPGSVariance Portability.pgsVarianceFromHet Descent.Core.retainedFraction; ring

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

theorem heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss
    (t : ℕ) (Ne H₀ : ℝ) (hH : 0 < H₀) :
    PopGen.heterozygosityLossFromDrift t Ne = (PopGen.closedPopulation Ne H₀ hH).measuredLoss t := by
  rw [PopGen.measuredLoss_closedPopulation]
  unfold PopGen.heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  rfl

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

/-- **The Wright-Fisher loss is the same regime again**, at an integer effective size.

Third copy of the body, third reading of it. `DriftRegime` counted five members in the
cluster; this attaches the one that states the recurrence over `ℕ` generations, so that
all three now name the same trajectory rather than three formulas that happen to agree. -/
theorem wrightFisherHeterozygosityLoss_eq_closedPopulation_measuredLoss
    (N t : ℕ) (H₀ : ℝ) (hH : 0 < H₀) :
    Portability.wrightFisherHeterozygosityLoss N t
      = (PopGen.closedPopulation (N : ℝ) H₀ hH).measuredLoss t := by
  rw [PopGen.measuredLoss_closedPopulation]
  unfold Portability.wrightFisherHeterozygosityLoss Portability.wrightFisherDriftRetention
  rfl

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

/-- **Slatkin's identity**: `1 - H_w/H_b = 1 - E[T_w]/E[T_b]`.

The heterozygosity reading of `F_ST` and the coalescence-time reading are the same number
whenever the two RATIOS agree -- which is the content, and it is a premise here rather than
a theorem. Under the infinite-sites limit expected heterozygosity is proportional to
expected coalescence time, so the constant cancels in the ratio; away from that limit it
does not, and this statement correctly says nothing.

What the corpus gets from it is a lattice edge. `fstFromHetRatio` and
`hudsonFstFromCoalescenceTimes` are both `Core.proportionalReduction`, so at EQUAL
arguments they agree by `rfl` and that is what
`pcTargetAxisEfficacy_eq_proportionalReduction` above records. This says the harder thing:
at DIFFERENT arguments -- heterozygosities on one side, coalescence times on the other --
they still agree, provided the population genetics that relates those arguments holds. Both
are Hudson-convention readings, so the edge is inside one convention and needs no bridge.

    Empirical status: NOT AN EMPIRICAL CLAIM -- the algebra is `rw [h]`. The premise
    `H_w/H_b = E[T_w]/E[T_b]` is where all the biology is, and it is supplied by the
    caller, not established here. -/
theorem slatkin_hetRatio_eq_coalescenceRatio
    (Hw Hb ETw ETb : ℝ) (h : Hw / Hb = ETw / ETb) :
    PopGen.fstFromHetRatio Hw Hb = Portability.hudsonFstFromCoalescenceTimes ETw ETb := by
  unfold PopGen.fstFromHetRatio Portability.hudsonFstFromCoalescenceTimes
    Descent.Core.proportionalReduction
  rw [h]

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

/-- **The `2 p (1 - p)` in the effective sample size is the diploid genotype variance.**
`StatisticalGeneticsMethodology.effectiveSampleSizeFromSE` inverts `SE² · Var(dosage)`, and
`Var(dosage)` under Hardy-Weinberg proportions is `genotypeVarianceHWE`. Written inline the
two was free; here it is the ploidy, and an SE reported on a haploid dosage scale would
have to change this file rather than that definition. -/
theorem effectiveSampleSizeFromSE_uses_genotypeVarianceHWE (se p : ℝ) :
    Portability.effectiveSampleSizeFromSE se p = 1 / (se ^ 2 * genotypeVarianceHWE p) := by
  unfold Portability.effectiveSampleSizeFromSE genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

/-- **Both twos in the mutation-drift heterozygosity step are the ploidy.** The drift term
loses a fraction `1 / (ploidy · Nₑ)` per generation — the reciprocal coalescent time scale —
and the mutation term gains `ploidy · mu` because both copies at the locus are exposed. A
haploid recursion would carry neither. -/
theorem hetStepWithMutation_uses_coalescentTimeScale (Ne mu H : ℝ) :
    Portability.hetStepWithMutation Ne mu H
      = (1 - 1 / coalescentTimeScale Ne) * H + Descent.Core.ploidy * mu * (1 - H) := by
  unfold Portability.hetStepWithMutation Descent.Core.ploidy; rw [coalescentTimeScale_eq]

/-- **The closed-population retention is the coalescent retention over the horizon.** -/
theorem retention_uses_coalescentTimeScale (r : Portability.ClosedPopulationNoMutation) :
    r.retention = (1 - 1 / coalescentTimeScale r.Ne) ^ r.horizon := by
  unfold Portability.ClosedPopulationNoMutation.retention; rw [coalescentTimeScale_eq]

/-- **Both twos in the identity-flow step are the ploidy.** Identity is created at
`1 / (ploidy · Nₑ)` per generation, and destroyed at `ploidy · rate` because either of the
two lineages of a sampled pair can be hit by the homogenising force. That second two is
what makes the fixed point `1 / (1 + 4 Nₑ · rate)` rather than `1 / (1 + 2 Nₑ · rate)`, so
it is the one a reader most needs pinned. -/
theorem ibdFlowStep_uses_coalescentTimeScale (Ne rate F : ℝ) :
    Portability.ibdFlowStep Ne rate F
      = F + (1 - F) / coalescentTimeScale Ne - Descent.Core.ploidy * rate * F := by
  unfold Portability.ibdFlowStep Descent.Core.ploidy; rw [coalescentTimeScale_eq]

/-- **The multiplicative identity recurrence carries the same coalescent scale.** -/
theorem ibdRecurrenceStep_uses_coalescentTimeScale (Ne rate x : ℝ) :
    Portability.ibdRecurrenceStep Ne rate x
      = (1 - rate) ^ 2 * (1 / coalescentTimeScale Ne
          + (1 - 1 / coalescentTimeScale Ne) * x) := by
  unfold Portability.ibdRecurrenceStep Descent.Core.survivalWeightedMix; rw [coalescentTimeScale_eq]

/-- **The rest point of that recurrence carries it too**, in both of its constants: the
`2 Nₑ` is the coalescent time scale and the `2 - rate` is `ploidy - rate`, the two lineages
less the one disrupting event they share. -/
theorem ibdRecurrenceFixedPoint_uses_coalescentTimeScale (Ne rate : ℝ) :
    Portability.ibdRecurrenceFixedPoint Ne rate
      = (1 - rate) ^ 2
          / ((1 - rate) ^ 2 + coalescentTimeScale Ne * rate * (Descent.Core.ploidy - rate)) := by
  unfold Portability.ibdRecurrenceFixedPoint Descent.Core.ploidy; rw [coalescentTimeScale_eq]

/-- **Both denominators in the scaled heterozygosity decay are the coalescent time
scale**, so `θ / (2 Nₑ)` is `θ` measured in coalescent units and not a second convention. -/
theorem hetDecayFromScaled_uses_coalescentTimeScale (Ne θ : ℝ) :
    PopGen.hetDecayFromScaled Ne θ
      = (1 - 1 / coalescentTimeScale Ne) * (1 - θ / coalescentTimeScale Ne) := by
  unfold PopGen.hetDecayFromScaled; rw [coalescentTimeScale_eq]

/-- **The `F_ST` flow step is `ibdFlowStep` at the summed rate, with the same two twos.**
Migration and mutation enter through their sum, and the `ploidy` in front of that sum is
the same "either lineage" factor as in `ibdFlowStep`. -/
theorem fstDriftFlowStep_uses_coalescentTimeScale (p : PopGen.EvolutionaryParameters) (F : ℝ) :
    PopGen.fstDriftFlowStep p F
      = F + (1 - F) / coalescentTimeScale p.Ne - Descent.Core.ploidy * (p.mig + p.mu) * F := by
  unfold PopGen.fstDriftFlowStep Descent.Core.ploidy; rw [coalescentTimeScale_eq]

/-- **The deme-corrected flow step restates neither convention.** Its `2 Nₑ` is the same
`coalescentTimeScale` and its leading `2` on the rate sum is the same `ploidy` "either
lineage" factor as in `fstDriftFlowStep`. The only new constant is the `2` INSIDE the rate
sum, multiplying `mig` alone, and that one is not a ploidy convention at all: it is
`PopulationGeneticsFoundations.islandDemeCorrection` at two demes, the emigration rate plus
the immigration rate. Mutation carries no such factor, and this theorem is where that
asymmetry is visible as an asymmetry rather than as an inlined constant. -/
theorem fstDemeCorrectedFlowStep_uses_coalescentTimeScale (p : PopGen.EvolutionaryParameters) (F : ℝ) :
    PopGen.fstDemeCorrectedFlowStep p F
      = F + (1 - F) / coalescentTimeScale p.Ne
          - Descent.Core.ploidy * (Descent.Core.islandDemeCorrection 2 * p.mig + p.mu) * F := by
  unfold PopGen.fstDemeCorrectedFlowStep Descent.Core.ploidy Descent.Core.islandDemeCorrection Descent.Core.ploidy
    Descent.Core.islandDemeCorrection Descent.Core.ratio
  rw [coalescentTimeScale_eq]; norm_num

/-- **The `2 p` in Fisher's average effect is the expected diploid dosage.** The dominance
deviation is weighted by `1 - ploidy · p`, which is `q - p`, and `ploidy · p` is `E[X]` for
a dosage `X` on `0, 1, …, ploidy` in Hardy-Weinberg proportions. On a haploid scale the
weight is not this expression, so the constant is forced by the coding and belongs here. -/
theorem averageEffect_uses_ploidy (m : Blindness.OneLocusArchitecture) :
    m.averageEffect = m.a + m.d * (1 - Descent.Core.ploidy * m.p) := by
  unfold Blindness.OneLocusArchitecture.averageEffect Descent.Core.ploidy; ring

/-- **The two in the polygenic-adaptation shift is the ploidy.** The mean score is
`Σᵢ βᵢ · ploidy · pᵢ`, so its shift carries the same factor; the body writes the `2` as a
literal only because importing `Conventions` into `SelectionArchitecture` closes an import
cycle. This theorem is what stops that literal from drifting away from `ploidy`. -/
theorem polygenicAdaptationShift_uses_ploidy {m : ℕ} (β Δp : Fin m → ℝ) :
    PopGen.polygenicAdaptationShift β Δp = ∑ i, β i * Descent.Core.ploidy * Δp i := by
  unfold PopGen.polygenicAdaptationShift Descent.Core.ploidy
  simp

/-- **The four in the quadratic stepping-stone form is twice the ploidy**, the same
`4 Nₑ` scaling as every other migration-drift denominator in the corpus. Only the powers of
`m` and `σ²` distinguish this form from `demoSteppingStoneFst`; the constant does not. -/
theorem steppingStoneFstQuadratic_uses_ploidy (d Ne m σ_sq : ℝ) :
    PopGen.steppingStoneFstQuadratic d Ne m σ_sq
      = d / (d + 2 * Descent.Core.ploidy * Ne * σ_sq ^ 2 * m ^ 2) := by
  unfold PopGen.steppingStoneFstQuadratic Descent.Core.ploidy; ring

/-- **The two-locus drift step carries the coalescent time scale.** `driftLDStep` creates
identity at `1 / (ploidy · Nₑ)`, the same rate `driftLDCreationRate` names. -/
theorem driftLDStep_uses_coalescentTimeScale (Ne c Q : ℝ) :
    PopGen.driftLDStep Ne c Q
      = (1 - c) ^ 2 * (1 / coalescentTimeScale Ne
          + (1 - 1 / coalescentTimeScale Ne) * Q) := by
  unfold PopGen.driftLDStep Descent.Core.survivalWeightedMix; rw [coalescentTimeScale_eq]

/-- **Its slope in `Q` carries it too.** -/
theorem driftLDRetention_uses_coalescentTimeScale (Ne c : ℝ) :
    PopGen.driftLDRetention Ne c = (1 - c) ^ 2 * (1 - 1 / coalescentTimeScale Ne) := by
  unfold PopGen.driftLDRetention; rw [coalescentTimeScale_eq]

/-- **And so does its equilibrium**, which is a ratio of two expressions in that one
scale rather than an independently chosen constant. -/
theorem driftLDEquilibrium_uses_coalescentTimeScale (Ne c : ℝ) :
    PopGen.driftLDEquilibrium Ne c
      = (1 - c) ^ 2 * (1 / coalescentTimeScale Ne) / (1 - PopGen.driftLDRetention Ne c) := by
  unfold PopGen.driftLDEquilibrium; rw [coalescentTimeScale_eq]

/-- **The `ρ` of the Ohta-Kimura approximation is the coalescent-scaled recombination
rate**, `2 · ploidy · Nₑ · c`, the same scaling `scaledMutationRate` applies to `μ` and
`scaledMigrationRate` to `m`. The remaining `2`, `10` and `11` are coefficients of the
moment recursion and are deliberately left as literals: they are not conventions, and
tying them to `ploidy` would assert a derivation this corpus does not have. -/
theorem ohtaKimuraSigmaDSq_uses_ploidy (Ne c : ℝ) :
    PopGen.ohtaKimuraSigmaDSq Ne c
      = (10 + 2 * Descent.Core.ploidy * Ne * c)
          / ((2 + 2 * Descent.Core.ploidy * Ne * c) * (11 + 2 * Descent.Core.ploidy * Ne * c)) := by
  simp only [PopGen.ohtaKimuraSigmaDSq, Descent.Core.ploidy, Descent.Core.ploidy]
  ring

/-- **The finite-deme island `F_ST` is the identity fraction at the deme-corrected scaled
migration rate.** Its `4 Nₑ m` is `scaledMigrationRate`, which
`scaledMigrationRate_eq_ploidy_form` already forces to `2 · ploidy · Nₑ · m`; the deme
correction multiplies that rate and does not touch the constant. This is the second
consumer of the one bridge, so the finite-`d` form and its `d → ∞` limit cannot acquire
different conventions. -/
theorem islandFstFiniteDemes_eq_scaled (Ne m d : ℝ) :
    PopGen.islandFstFiniteDemes Ne m d
      = PopGen.fstMutationDriftEquilibrium (Descent.Core.scaledMigrationRate Ne m * Descent.Core.islandDemeCorrection d) := by
  unfold PopGen.islandFstFiniteDemes PopGen.fstMutationDriftEquilibrium Descent.Core.scaledMigrationRate Descent.Core.fstFromFlow
    Descent.Core.islandDemeCorrection Descent.Core.islandDemeCorrection Descent.Core.ratio Descent.Core.scaledMigrationRate Descent.Core.ploidy
  ring

/-- **The `2 μ` in the stepping-stone characteristic length counts the two lineages of a
sampled pair.** Mutation destroys the identity of a pair at rate `ploidy · μ`, so
`1 / (ploidy · μ)` is the time available to the diffusion and `L² = m σ² / (ploidy · μ)`
is the balance. Written inline the two read as arbitrary; it is the same two that
`coalescentTimeScale` puts in front of `Nₑ`. -/
theorem steppingStoneCharacteristicLength_uses_ploidy (m σ_sq μ : ℝ) :
    PopGen.steppingStoneCharacteristicLength m σ_sq μ = Real.sqrt (m * σ_sq / (Descent.Core.ploidy * μ)) := by
  unfold PopGen.steppingStoneCharacteristicLength Descent.Core.ploidy; ring

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

/-- **The `p (1 - p)` in the drift variance is half the diploid genotype variance.**
`AncestrySpecificArchitecture.driftVariance` is `p₀ (1 - p₀) · F_ST`, the ancestral
heterozygosity that has become between-population variance. Its heterozygosity factor is
`genotypeVarianceHWE` on the allele scale rather than the dosage scale, which is exactly
one `ploidy` apart, and writing it inline left that scale choice free. -/
theorem driftVariance_uses_genotypeVarianceHWE (p0 fst : ℝ) :
    PopGen.driftVariance p0 fst = genotypeVarianceHWE p0 * fst / Descent.Core.ploidy := by
  unfold PopGen.driftVariance genotypeVarianceHWE Descent.Core.ploidy Descent.Core.hweHeterozygosity Descent.Core.ploidy
  ring

/-- **The realised target PGS variance is a retained fraction, scaled by transport.**
`PortabilityDrift.realWorldPGSVariance` erodes the additive variance by `1 - F_ST` and then
by the transported correlation. The first factor is `Core.retainedFraction`, the same
`(1 - loss) · total` map as the ascertainment survivor and the neutral portability ratio.
Those two now CALL the kernel and so need no theorem here; this one does not, because it
routes through a transported correlation as well, which is why it survives the deletion of
its four siblings. -/
theorem realWorldPGSVariance_eq_retainedFraction (V_A fst rhoSq : ℝ) :
    Portability.realWorldPGSVariance V_A fst rhoSq = rhoSq * Descent.Core.retainedFraction fst V_A := by
  unfold Portability.realWorldPGSVariance Descent.Core.retainedFraction; ring

end SharedMaps

end Descent.Program
