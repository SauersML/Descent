/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.WrightFisher
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

/-!

**This is an audit layer, not a foundation, and it used to be filed as one.**

Its 114 theorems relate quantities that live in fifteen different subsystem modules --
`driftVariance` against `hweGenotypeVariance`, `amEquilibriumVariance` against `ibdFst`,
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

/-- Number of homologous copies per locus. Every non-exponent factor of two in
this development traces to this constant, and every factor of four to twice
it. Forty-eight definition bodies outside this file carry such a two and
fourteen carry such a four. The theorems in this file tie the independently
written ones back here, so that drift between them is a compile error rather
than a silent disagreement. -/
noncomputable def ploidy : ℝ := Descent.Core.ploidy

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ploidy_at_reference_point :
    ploidy  = 2 := by
  norm_num [ploidy, Descent.Core.ploidy]



/-- Genotype variance at a locus in Hardy-Weinberg proportions, for dosage
coded `0, 1, …, ploidy`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_core.py`,
    `test_hwe_variance`). Realised dosage variance over 400000 Hardy-Weinberg
    genotypes per cell: worst 0.88 sems over a prediction spanning 0.09500 to
    0.50000. This body also appears as `AncestrySpecificPower.genotypeVarianceHWE`
    and `hweHeterozygosity`; all three are measured against the same oracle. -/
noncomputable def hweGenotypeVariance (p : ℝ) : ℝ := Descent.Core.hweHeterozygosity p

/-- **The genotype variance peaks at even allele frequency and is exactly one half there.** With
diploid ploidy the value at `p = 1/2` is `2 · (1/2) · (1/2) = 1/2`. The vanishing at the two
fixed points is shared by every multiple of `p(1-p)`; the value at the interior maximum fixes the
ploidy factor, which is the only free constant in the formula. -/
theorem hweGenotypeVariance_at_half : hweGenotypeVariance (1 / 2) = 1 / 2 := by
  unfold hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy
  norm_num

/-- Coalescent time scale: time measured in units of `ploidy · Nₑ`
generations.

    Regime: a single panmictic diploid population; the scale is the MEAN
    PAIRWISE coalescence time, which is what makes it a time and not a rate.

    Empirical status: **VALIDATED** (`simcov/battery_bulk37.py`). Measured in
    BRANCH mode -- straight off the genealogies, with no mutation model, so no
    mutation-rate convention can leak in -- over 2 Mb with recombination so each
    replicate averages many independent trees. Across `Nₑ` = 500, 1000, 2000,
    5000 the worst cell is 1.08 sems at 2.4% relative.

    Power: the `4·Nₑ` reading is carried on the same cells and is FALSIFIED at
    46.96 sems (105% relative). The tenfold `Nₑ` sweep is what provides that
    separation.

    Control: Watterson's `E[S] = θ·∑_{i<n} 1/i` for the expected number of
    segregating sites, computed from tree sequences generated by the same
    demography -- an independent classical result that would break if the
    demography or the mutation placement were wrong. It passes at worst 1.27
    sems (15.33 measured against 14.19 predicted at `Nₑ = 500`, rising to 151.5
    against 141.9 at `Nₑ = 5000`).

    This run replaces `battery_bulk23.py`, which measured the same thing
    correctly but carried a control asserting that the coefficient of variation
    of the replicate means is 1. That holds for a single exponential `T₂`, not
    for a mean over the many genealogies recombination supplies, so that control
    failed and its `4·Nₑ` rejection was recorded VOID. A run whose control fails
    is rightly distrusted even where its headline comparison does not depend on
    it.

    This is the `2·Nₑ` in the corpus that is NOT the other one. The `4·Nₑ` that
    appears throughout -- in `scaledMutationRate`, `scaledMigrationRate`,
    `fstMutationDriftEquilibrium` -- is the scaling of a RATE, `θ = 4·Nₑ·μ` and
    `M = 4·Nₑ·m`, and shares only its shape with this. -/
noncomputable def coalescentTimeScale (Ne : ℝ) : ℝ := ploidy * Ne

@[simp] theorem coalescentTimeScale_eq (Ne : ℝ) :
    coalescentTimeScale Ne = 2 * Ne := by
  unfold coalescentTimeScale ploidy Descent.Core.ploidy; ring

/-- **The convention is the coalescent's own mean, not a second choice of `2`.**

`coalescentTimeScale` says that one coalescent time unit is `2·Nₑ` generations.  Until this
theorem existed that was a NUMBER SOMEONE WROTE DOWN, agreeing with the coalescent because
both had been got right, with nothing forcing them to move together.  What it converts is
the mean number of generations back to the common ancestor of two lineages, and the
mechanism supplies that mean: `Coalescent.tsum_pairDistinct_diploid`, the sum of the
Wright-Fisher pair-survival probabilities over all generations, which the geometric series
evaluates to `2·Nₑ`.

This is the corpus's first use of `Descent/Coalescent/` from outside it for a quantity
rather than a lemma: the 12,000-line derivation now decides a constant the applied layer
depends on, so a change to the mechanism reaches the convention instead of merely
disagreeing with it. -/
theorem coalescentTimeScale_eq_meanPairCoalescenceTime {Ne : ℕ} (hNe : 0 < Ne) :
    coalescentTimeScale (Ne : ℝ) = ∑' s : ℕ, Coalescent.pairDistinct (2 * Ne) s := by
  rw [Coalescent.tsum_pairDistinct_diploid hNe, coalescentTimeScale_eq]

/-- **Cross-check: the scaled mutation rate in `PopulationGeneticsFoundations`
is twice the coalescent time scale times the mutation rate**, rather than an
independently chosen `4`. -/
theorem scaledMutationRate_eq_ploidy_form (Ne mu : ℝ) :
    PopGen.scaledMutationRate Ne mu = 2 * ploidy * Ne * mu := by
  unfold PopGen.scaledMutationRate ploidy Descent.Core.scaledMutationRate Descent.Core.ploidy; ring

/-- **Cross-check: the scaled migration rate in `PortabilityDrift` uses the
same convention.** These two were written in different files, each spelling
out its own `4`. -/
theorem scaledMigrationRate_eq_ploidy_form (Ne m : ℝ) :
    PopGen.scaledMigrationRate Ne m = 2 * ploidy * Ne * m := by
  unfold PopGen.scaledMigrationRate ploidy Descent.Core.scaledMigrationRate Descent.Core.ploidy; ring

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
    Portability.twoDemeIMEquilibriumETss M = ploidy := by
  unfold Portability.twoDemeIMEquilibriumETss ploidy Descent.Core.ploidy; ring

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
      = ploidy * Ne * Real.sqrt (mu * s) := by
  unfold Portability.recessiveMutationSelectionDriftParameter ploidy Descent.Core.ploidy; ring

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
    Portability.mutationSelectionDriftParameter Ne s h = PopGen.scaledMutationRate Ne (h * s) := by
  unfold Portability.mutationSelectionDriftParameter PopGen.scaledMutationRate Descent.Core.scaledMutationRate Descent.Core.ploidy; ring

/-- **The two in the allele-frequency retention ratio is the ploidy, twice, and
that is why the ratio does not depend on it.**

`PortabilityDrift.tagAlleleFreqRetentionAt` is `2p_t(1 - p_t) / (2p_0(1 - p_0))`,
and both twos are the same gene-copy count that `hweGenotypeVariance` carries:
the body is a ratio of Hardy-Weinberg genotype variances at two times. Stating
it that way is not decoration. A bare `2` in a numerator and a bare `2` in a
denominator can be two DIFFERENT conventions written the same way -- a
heterozygosity over a genotype variance, say -- and the ratio would then be off
by a factor while looking symmetric. Once both are `hweGenotypeVariance` the
cancellation is forced, and the retention is a pure ratio that a haploid corpus
would compute identically. -/
theorem tagAlleleFreqRetentionAt_eq_hweGenotypeVariance_ratio {p q : ℕ}
    (m : Portability.CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) :
    Portability.tagAlleleFreqRetentionAt m t i =
      hweGenotypeVariance (Portability.tagAlleleFreqTargetAt m t i) /
        hweGenotypeVariance (m.tagAlleleFreqSource i) := by
  unfold Portability.tagAlleleFreqRetentionAt hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

/-- **The same two, at the causal variants.** `causalAlleleFreqRetentionAt` is
the identical ratio on the causal side, and it is tied here separately rather
than by appeal to the tag version: two definitions with the same shape in one
file are exactly the pair a single fix leaves half-repaired. -/
theorem causalAlleleFreqRetentionAt_eq_hweGenotypeVariance_ratio {p q : ℕ}
    (m : Portability.CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) :
    Portability.causalAlleleFreqRetentionAt m t j =
      hweGenotypeVariance (Portability.causalAlleleFreqTargetAt m t j) /
        hweGenotypeVariance (m.causalAlleleFreqSource j) := by
  unfold Portability.causalAlleleFreqRetentionAt hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

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
        - 2 * (PopGen.islandDemeCorrection 2 * p.mig + p.mu) * F := by
  unfold PopGen.fstDemeCorrectedFlowStep coalescentTimeScale PopGen.islandDemeCorrection
    Descent.Core.islandDemeCorrection Descent.Core.ratio ploidy Descent.Core.ploidy
  norm_num

end Ploidy

section Differentiation

/-- Mean allele frequency across two subgroups of equal weight.

    Empirical status: NOT AN EMPIRICAL CLAIM. This file exists to fix conventions, and the
    equal-weight arithmetic mean is one: `(p₁ + p₂)/2` DEFINES what "the mean frequency"
    denotes downstream rather than predicting anything a sample could refute. The empirical
    consequence of choosing equal weights over sample-size weights shows up in the `F_ST`
    that consumes it, and the note below records that `effectiveSymmetricMigration` must
    share this convention or the two disagree. -/
noncomputable def meanAlleleFreq (p₁ p₂ : ℝ) : ℝ :=
  Descent.Core.midpoint p₁ p₂

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

/-- **The mean allele frequency is unweighted, pinned.** The identity with the symmetric
migration map constrains the two definitions jointly. Taken alone: a fixed and an absent allele
average to one half, which fixes the two-population mean as the arithmetic midpoint. -/
theorem meanAlleleFreq_fixed_and_absent :
    meanAlleleFreq 0 1 = 1 / 2 := by
  unfold meanAlleleFreq Descent.Core.midpoint
  norm_num

theorem effectiveSymmetricMigration_eq_meanAlleleFreq_map (m₁₂ m₂₁ : ℝ) :
    Portability.effectiveSymmetricMigration m₁₂ m₂₁ = meanAlleleFreq m₁₂ m₂₁ := by
  unfold Portability.effectiveSymmetricMigration meanAlleleFreq Descent.Core.midpoint; ring

/-- **Nei's `G_ST`, explicitly distinguished from Hudson's `F_ST`.** One minus the ratio
of mean within-subgroup heterozygosity to TOTAL heterozygosity is the
definition of `G_ST`. Hudson's `F_ST`
divides by the BETWEEN-subgroup heterozygosity `p₁(1-p₂) + p₂(1-p₁)`, not by
the total-pool `2·p̄·(1-p̄)`. The two denominators differ by exactly
`(p₁-p₂)²/2`, so THE DENOMINATORS agree iff `p₁ = p₂`, and the two ESTIMATORS
agree iff `G_ST = 0` or `G_ST = 1` -- that is, only where the differentiation
is degenerate.

**They agree when `p₁ = p₂`, and NOT when `p̄ = 1/2`**; the second is a tempting
disjunct and it is false in both readings.
The denominators differ by `(p₁-p₂)²/2`, which does not vanish at `p̄ = 1/2`;
and by the corpus's own `hudsonFst_eq_of_neiGst`, Hudson `= 2G/(1+G)`,
which equals `G` only at `G = 0` or `G = 1`. So there is no interior
`p̄ = 1/2` slice on which the two coincide. Witness, on `p̄ = 1/2` exactly:
at `p₁ = 0.9, p₂ = 0.1` the Nei denominator is `1`, `G_ST = 0.64`, and Hudson
is `0.64/0.82 = 0.7805` -- a ratio of `1.22`. Nearer the middle it is worse:
`1.995` at `(0.525, 0.475)`, `1.923` at `(0.6, 0.4)`, `1.724` at `(0.7, 0.3)`.

The error is worth naming because it is cheap to half-check and wrong: at
`p̄ = 1/2` the Nei denominator `4·p̄·(1-p̄)` is exactly `1`, which feels like it
should settle the comparison and does not -- it makes `G_ST = (p₁-p₂)²`, while
Hudson still divides by `1 - 2p₁p₂`. A DENOMINATOR COINCIDENCE IS NOT AN
ESTIMATOR COINCIDENCE, and here there was not even a denominator coincidence.
The claim had propagated into three `checks.py` can-fail clauses and out of the
corpus into status reporting before anyone tested the slice it names.

    Derivation, since this is decidable without any simulation. With
    `d = p₁ - p₂` and `p̄ = (p₁+p₂)/2`,
    `H_T - H_S = 2p̄(1-p̄) - (p₁(1-p₁) + p₂(1-p₂)) = d²/2`, so this body is
    `d² / (4·p̄·(1-p̄))`, which is Nei's `G_ST` and is also exactly the body of
    `PopulationGeneticsFoundations.neiGstFromFrequencies` --
    `neiGstFromFrequencies_eq_neiGst` below proves the two agree, and what
    it actually proves is that both are Nei.
    Hudson's is `d² / (p₁ + p₂ - 2p₁p₂)`; `hudsonFst` states it and
    `hudsonFst_eq_of_neiGst` gives the exact conversion. At `p₁ = 0.2`,
    `p₂ = 0.6` this body gives `0.1667` where Hudson gives `0.2857`, the
    +71.4% the differential tier measured against an independent
    implementation.

    The old `hudsonFst` name on the Nei body was removed rather than retained as
    a compatibility alias: that alias would preserve the biological category
    error. The genuine Hudson body now owns `hudsonFst`. Read every `neiGst` in the
    *contrast-normalization* chain --
    including `four_neiGst_eq_standardizedContrastVariance` -- as Nei's `G_ST`.
    The algebra is unaffected: `4·G_ST` is the standardized allele-frequency
    contrast variance for THIS body. It is not the empirically calibrated BBP
    spike. That law uses genuine Hudson `F_ST` and is named `hudsonBbpSpike`
    below. At weak differentiation the latter is almost twice
    `neiContrastSpike`; silently exchanging them is therefore a biologically
    material error, not a harmless change of notation.

    **There is no exception at `p̄ = 1/2`. Do not add one.** The factor does not
    vanish there: measured ratios along that exact slice are `1.995`, `1.923`,
    `1.724`, `1.220` -- monotone in `|p₁ - p₂|` and never reaching `1`. The
    identity in this file settles it without any measurement:
    `hudsonFst_eq_of_neiGst` gives `Hudson = 2G/(1+G)`, which equals `G` only at
    `G = 0` or `G = 1`. `neiGst_ne_hudsonFst_at_mean_half` certifies it at
    `(9/10, 1/10)` -- `p̄ = 1/2` exactly, ratio `50/41` -- and exists to stop an
    "except at `p̄ = 1/2`" caveat being reintroduced.

    Note which witness does the work: `neiGst_ne_hudsonFst` sits at `p̄ = 2/5`,
    OUTSIDE that slice, and cannot refute a claim about it. A witness outside an
    exception never refutes the exception.

    **Numerical warning -- this body must not be evaluated as written.** It is
    `1` minus a ratio that tends to `1` as the two populations become similar,
    so its floating-point relative error is the machine epsilon divided by the
    answer. Between human populations `G_ST` is `O(10⁻³)` genome-wide and much
    smaller at an individual variant, which is exactly the regime that has no
    digits left. Measured float64 against a 60-digit reference over
    `p₂ = p₁ + δ` for `p₁ ∈ {0.01, 0.1, 0.3, 0.5}` and `δ` from `10⁻²` down to
    `10⁻¹⁴`, arguments rounded to float64 FIRST so input representation cannot
    be charged to the formula: **36 of 52 cells exceed 1e-6 relative error,
    worst 9.3·10¹¹** -- the returned `G_ST` is wrong by eleven orders of
    magnitude, and at `δ ≲ 10⁻⁸` it is pure rounding noise of either sign.

    `PopulationGeneticsFoundations.neiGstFromFrequencies` is the SAME quantity
    written as `(p₁-p₂)² / (4 p̄ (1-p̄))`, with the cancellation done by hand;
    `neiGstFromFrequencies_eq_neiGst` proves they are equal over `ℝ`. On the
    same 52 cells that body gives **0 over tolerance, worst 1.9·10⁻¹⁶**. The
    equality theorem is what makes the substitution safe and it is also what
    made the difference invisible: two provably equal bodies are not two equally
    usable programs. Evaluate `neiGstFromFrequencies`; read `neiGst` as the
    definition of what is being computed.

    Metamorphic relations this body satisfies, all exactly:
    population relabelling `(p₁, p₂) ↦ (p₂, p₁)`, invariant;
    reference/alternate allele swap `(p₁, p₂) ↦ (1-p₁, 1-p₂)`, invariant
    (`neiGst_allele_swap`); and `p₁ = p₂`, zero.

    Empirical status: CONVENTION PINNED (Nei's `G_ST`; the name was corrected with it). -/
noncomputable def neiGst (p₁ p₂ : ℝ) : ℝ :=
  (p₁ - p₂) ^ 2 /
    (ploidy ^ 2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))

/-- **The textbook spelling, kept as a theorem rather than as the body.**

`G_ST = 1 - H_S/H_T` is how the quantity is defined in the literature and it is
what the name means; it is not how it should be computed. As `p₁ → p₂` the ratio
tends to `1` and `G_ST` is whatever survives the
subtraction, so its float64 relative error is machine epsilon divided by the
answer. Measured float64 against a 60-digit reference over `p₂ = p₁ + δ` for
`p₁ ∈ {0.01, 0.1, 0.3, 0.5}` and `δ` from `10⁻²` to `10⁻¹⁴`, arguments rounded to
float64 first: **36 of 52 cells over 1e-6 relative error, worst 9.3·10¹¹** for
this form, against **0 of 52, worst 1.9·10⁻¹⁶** for the body above. Human `G_ST`
is `O(10⁻³)` genome-wide and smaller per variant, so the failing region was the
use case.

The hypothesis is the one point at which the two spellings genuinely differ --
see `neiGst_at_zero_mean_heterozygosity`. -/
theorem neiGst_eq_oneMinusRatio (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    neiGst p₁ p₂ =
      1 - (p₁ * (1 - p₁) + p₂ * (1 - p₂)) /
        (ploidy * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  have h1 : meanAlleleFreq p₁ p₂ ≠ 0 := left_ne_zero_of_mul h
  have h2 : (1 - meanAlleleFreq p₁ p₂) ≠ 0 := right_ne_zero_of_mul h
  unfold neiGst ploidy Descent.Core.ploidy
  field_simp
  unfold meanAlleleFreq Descent.Core.midpoint
  ring

/-- **Two identical monomorphic populations are not differentiated.**

Two populations fixed for the same allele could not be more alike, and the
statistic reports `0`. This is a real value, not a junk branch: the numerator
`(p₁ - p₂)²` vanishes with the denominator, so the cancellation-free body is
defined here by the same algebra that makes it stable elsewhere. Under the
`1 - H_S/H_T` spelling the ratio divides by zero, Mathlib returns `0`, and the
statistic reads `1` -- COMPLETE differentiation -- so that spelling requires
consumers to exclude the point. The stable spelling and the correct boundary are
the same spelling. -/
theorem neiGst_at_zero_mean_heterozygosity (p₁ p₂ : ℝ)
    (hzero : ploidy ^ 2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) = 0) :
    neiGst p₁ p₂ = 0 := by
  unfold neiGst
  rw [hzero, div_zero]


/-- **Hudson's `F_ST` for two subgroups, parametric limit** (Bhatia, Patterson,
Sankararaman & Price 2013, eq. 10, at infinite sample size):

  `F_ST = (p₁ - p₂)² / (p₁(1-p₂) + p₂(1-p₁))`

The denominator is the probability that two genes drawn from DIFFERENT
subgroups differ -- the between-subgroup heterozygosity -- which is what makes
this a ratio of averages and what distinguishes it from Nei's `G_ST`. Added
alongside `neiGst` rather than replacing it, because the corpus's arithmetic
is Nei's throughout and changing the arithmetic would silently move every
downstream number; what was missing was a name for the quantity the corpus kept
saying it meant.

    Empirical status: VALIDATED -- matches `validation/differential/refs.fst_hudson`, which
    is checked against scikit-allel. -/
noncomputable def hudsonFst (p₁ p₂ : ℝ) : ℝ :=
  (p₁ - p₂) ^ 2 / (p₁ * (1 - p₂) + p₂ * (1 - p₁))

/-- **hudsonFst where its denominator vanishes, named.** The guard `p₁ * (1 - p₂) + p₂ * (1 - p₁)`
is zero at `p₁ = 0`, `p₂ = 0`. Two populations both fixed for the reference allele have no
polymorphism to partition. Lean returns `0` there rather than the value the modelled quantity
takes, and no type error marks the point. Consumers must require `p₁ * (1 - p₂) + p₂ * (1 - p₁)
≠ 0`. -/
theorem hudsonFst_at_p0p0_is_junk :
    hudsonFst 0 0 = 0 := by
  unfold hudsonFst
  norm_num

/-- **Hudson's `F_ST` does not care which population is called first.** Both the squared
frequency difference and the denominator `p₁ + p₂ - 2p₁p₂` are symmetric, so the statistic is
too. A body that broke this would be measuring a directed quantity under a symmetric name. -/
theorem hudsonFst_symm (p₁ p₂ : ℝ) : hudsonFst p₁ p₂ = hudsonFst p₂ p₁ := by
  unfold hudsonFst; ring_nf

/-- Two populations at the same frequency are not differentiated. -/
theorem hudsonFst_self (p : ℝ) : hudsonFst p p = 0 := by
  unfold hudsonFst; simp

/-! ### Reference/alternate allele swap: a metamorphic relation, not a symmetry of taste

Which allele a variant call file names REFERENCE is a property of the assembly, not
of the biology. Swapping it sends `p ↦ 1 - p` at every population simultaneously.
Every allele-frequency-symmetric quantity must therefore be invariant, and every
effect-direction quantity must be negated; a body that is neither is reporting the
assembly. The corpus proves that its `F_ST` bodies do not care which population is
called first (`hudsonFst_symm`) but had no statement about which allele is called
reference, which is the convention that actually varies between panels. -/

/-- **Nei's `G_ST` is invariant under the reference/alternate allele swap.** Both the
within-population heterozygosity `p(1-p)` and the mean-frequency heterozygosity are
even about `p = 1/2`, so relabelling the alleles cannot move the statistic. -/
theorem neiGst_allele_swap (p₁ p₂ : ℝ) :
    neiGst (1 - p₁) (1 - p₂) = neiGst p₁ p₂ := by
  unfold neiGst meanAlleleFreq Descent.Core.midpoint
  have hnum : ((1 - p₁) - (1 - p₂)) ^ 2 = (p₁ - p₂) ^ 2 := by ring
  have hden : ploidy ^ 2 * ((1 - p₁ + (1 - p₂)) / 2) * (1 - (1 - p₁ + (1 - p₂)) / 2)
      = ploidy ^ 2 * ((p₁ + p₂) / 2) * (1 - (p₁ + p₂) / 2) := by ring
  rw [hnum, hden]

/-- **Hudson's `F_ST` is invariant under the reference/alternate allele swap.** The
numerator is a squared difference and the between-population denominator
`p₁(1-p₂) + p₂(1-p₁)` is the probability that two genes drawn from different demes
differ, which is a statement about disagreement and so cannot depend on the labels. -/
theorem hudsonFst_allele_swap (p₁ p₂ : ℝ) :
    hudsonFst (1 - p₁) (1 - p₂) = hudsonFst p₁ p₂ := by
  unfold hudsonFst
  have hnum : ((1 - p₁) - (1 - p₂)) ^ 2 = (p₁ - p₂) ^ 2 := by ring
  have hden : (1 - p₁) * (1 - (1 - p₂)) + (1 - p₂) * (1 - (1 - p₁))
      = p₁ * (1 - p₂) + p₂ * (1 - p₁) := by ring
  rw [hnum, hden]

/-- **Hardy-Weinberg genotype variance is invariant under the reference/alternate allele
swap.** Recoding dosage as `ploidy - dosage` is an affine map with slope `-1`, which
leaves any variance alone; a body carrying an odd power of `p` would not survive it. -/
theorem hweGenotypeVariance_allele_swap (p : ℝ) :
    hweGenotypeVariance (1 - p) = hweGenotypeVariance p := by
  unfold hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy
  ring

/-- **The exact conversion between the two conventions**, which is what turns
"they disagree by about 72% somewhere in this range" into a statement that
holds everywhere: `F_ST^Hudson = 2·G_ST / (1 + G_ST)`. Note it is not a
constant factor -- the discrepancy is 2× as `G_ST → 0` and vanishes as
`G_ST → 1` -- so no recalibration constant can absorb a convention mix-up.

WHAT IS AND IS NOT NEW HERE, stated so nobody reports the wrong half. THAT NEI
AND HUDSON DISAGREE IS TEXTBOOK: Bhatia, Patterson, Sankararaman & Price (2013)
is the standard reference, it is cited on `hudsonFst` above, and the
disagreement is not a finding of this corpus. What belongs to this development
is narrower and worth exactly what it is: the algebraic bridge between them
written down explicitly, MACHINE-CHECKED in Lean rather than asserted, and then
confirmed numerically against simulation to the last reported digit. A
well-known fact and a proved identity are different objects, and only the
second is ours.

    Empirical status: VALIDATED, and it is currently the cleanest
    theory-to-measurement match in this corpus. Inverting the identity to
    `G = H/(2 - H)` predicts the Nei estimate from the Hudson estimate on the
    same simulated data at **0.00% relative error across all eight cells**,
    while Hudson itself tracks the true `F_ST` (`0.0501` measured against
    `0.050` simulated). The identity is exact in practice as well as in Lean,
    which is the strongest form this kind of claim can take: a conversion that
    is proved and then found to hold to the last reported digit on data it was
    not fitted to.

    Power: across the eight frequency cells of
    `validation/empirical/differential/cluster/fam_fst_allel_crosscheck.py`
    (`(p₁, p₂)` from `(0.70, 0.75)` to `(0.10, 0.90)`) the predicted Nei
    estimate spans `0.0031` to `0.6400` and the Hudson estimate `0.0063` to
    `0.7805`, so the ratio between the conventions runs from `2.0` at the
    small-divergence end to `1.22` at the large one. A conversion off by any
    constant factor, and any conversion linear in `G`, separates on that
    design. -/
theorem hudsonFst_eq_of_neiGst (p₁ p₂ : ℝ)
    (hpos : 0 < p₁ * (1 - p₂) + p₂ * (1 - p₁))
    (hbar : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    hudsonFst p₁ p₂ = 2 * neiGst p₁ p₂ / (1 + neiGst p₁ p₂) := by
  have hne : p₁ * (1 - p₂) + p₂ * (1 - p₁) ≠ 0 := ne_of_gt hpos
  have hmean : meanAlleleFreq p₁ p₂ ≠ 0 := left_ne_zero_of_mul hbar
  have hcomp : 1 - meanAlleleFreq p₁ p₂ ≠ 0 := right_ne_zero_of_mul hbar
  have hD : 2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hmean) hcomp
  have hlink :
      (1 + neiGst p₁ p₂) *
          (2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) =
        p₁ * (1 - p₂) + p₂ * (1 - p₁) := by
    unfold neiGst ploidy Descent.Core.ploidy
    field_simp [hD]
    unfold meanAlleleFreq Descent.Core.midpoint
    ring
  have htwo :
      2 * neiGst p₁ p₂ =
        (p₁ - p₂) ^ 2 /
          (2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
    unfold neiGst ploidy Descent.Core.ploidy
    field_simp [hD]
  have hone :
      1 + neiGst p₁ p₂ =
        (p₁ * (1 - p₂) + p₂ * (1 - p₁)) /
          (2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) :=
    (eq_div_iff hD).2 hlink
  have hquot :
      (p₁ * (1 - p₂) + p₂ * (1 - p₁)) /
          (2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) ≠ 0 :=
    div_ne_zero hne hD
  unfold hudsonFst
  rw [htwo, hone]
  field_simp [hne, hD, hquot]

/-- **Witness that the two estimators are different functions**, not two
spellings of one. Without an exhibited point the conflation can be
reintroduced by anyone who reads the `neiGst` name and believes it. -/
theorem neiGst_ne_hudsonFst :
    neiGst (1/5) (3/5) ≠ hudsonFst (1/5) (3/5) := by
  unfold neiGst hudsonFst ploidy meanAlleleFreq Descent.Core.midpoint Descent.Core.ploidy
  norm_num

/-- **A witness ON the `p̄ = 1/2` slice**, where the estimators are sometimes
claimed to agree. They do not.

`p₁ = 9/10, p₂ = 1/10` has `p̄ = 1/2` exactly. `neiGst` (Nei's `G_ST`) is
`16/25` and `hudsonFst` is `(16/25)/(41/50)`, a ratio of `50/41 ≈ 1.22`.
The false claim is therefore refuted at a point, not merely argued against:
`p̄ = 1/2` makes the Nei denominator `1` and nothing more. Stated separately
from `neiGst_ne_hudsonFst` because that witness sits at `p̄ = 2/5` and
so cannot exclude the slice that was actually claimed. -/
theorem neiGst_ne_hudsonFst_at_mean_half :
    neiGst (9/10) (1/10) ≠ hudsonFst (9/10) (1/10) := by
  unfold neiGst hudsonFst ploidy meanAlleleFreq Descent.Core.midpoint Descent.Core.ploidy
  norm_num

/-- **NO FIXED FACTOR CONVERTS NEI'S `G_ST` INTO HUDSON'S `F_ST`.**

This closes the fork rather than documenting it. The two witnesses above exhibit
points where the estimators disagree, and `hudsonFst_eq_of_neiGst` gives the exact
map `Hudson = 2·G/(1 + G)`. Neither shuts the door this theorem shuts: a reader
who accepts that the two differ can still believe the difference is a calibration
constant to be divided out, and that belief is what a factor-of-two-to-four error
looks like from the inside.

There is no such constant, anywhere on the interior of the frequency range, and
the witnesses say why. The map `Hudson = 2G/(1 + G)` has slope `2` at `G = 0` and
slope `1` at `G = 1`, so the RATIO moves with the differentiation: at
`p₁ = 1/5, p₂ = 3/5` it is `12/7`, and at `p₁ = 9/10, p₂ = 1/10` it is `50/41`.

This is the machine-checked form of what `PopulationGeneticsFoundations.neiFst`
records in prose -- that the measured ratio runs `0.60, 0.60, 0.68, 0.82` across a
`τ` sweep, so no rescaling reconciles the two. A docstring paragraph can be read
past; a theorem cannot. After this, substituting one estimator for the other is
not a judgement call about tolerable error, it is a claim this file refutes.

    Empirical status: NOT AN EMPIRICAL CLAIM -- an arithmetic fact about two
    definitions, with both witnesses exhibited rather than sampled. -/
theorem no_constant_scales_neiGst_to_hudsonFst :
    ¬ ∃ c : ℝ, ∀ p₁ p₂ : ℝ, 0 < p₁ → p₁ < 1 → 0 < p₂ → p₂ < 1 →
      hudsonFst p₁ p₂ = c * neiGst p₁ p₂ := by
  rintro ⟨c, hc⟩
  have h₁ := hc (1/5) (3/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₂ := hc (9/10) (1/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold neiGst hudsonFst ploidy meanAlleleFreq Descent.Core.midpoint Descent.Core.ploidy at h₁ h₂
  norm_num at h₁ h₂
  linarith

/-- Between-subgroup allele-frequency variance for an equal-weight split. -/
noncomputable def betweenSubgroupVariance (p₁ p₂ : ℝ) : ℝ :=
  Descent.Core.halfDiffSq p₁ p₂

/-- **The between-subgroup variance's normalisation, pinned.** The identity with the fair
two-point variance constrains the two definitions jointly and leaves a shared wrong factor free.
Two subgroups at the extremes of the frequency range have between-group variance one quarter --
the variance of a fair coin -- not one. -/
theorem betweenSubgroupVariance_extremes :
    betweenSubgroupVariance 1 0 = 1 / 4 := by
  unfold betweenSubgroupVariance Descent.Core.halfDiffSq
  norm_num

/-- **Cross-check: the fair two-point variance in `ImitationRigidity` is the
between-subgroup variance.** Both are `(a - b)² / 4`: the variance of a
two-point law with equal weights. One is used as a nonconcentration witness for
a resolvent and the other as the numerator of `F_ST`, and neither file knew the
other existed. -/
theorem fairTwoPointVariance_eq_betweenSubgroupVariance (a b : ℝ) :
    Blindness.fairTwoPointVariance a b = betweenSubgroupVariance a b := by
  unfold Blindness.fairTwoPointVariance betweenSubgroupVariance Descent.Core.halfDiffSq; ring

/-- **Cross-check: the heterozygosity form and the variance form of `F_ST`
agree.** The corpus contained both shapes and never related them. -/
theorem neiGst_eq_varianceRatio (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    neiGst p₁ p₂ =
      betweenSubgroupVariance p₁ p₂ /
        (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  have h1 : meanAlleleFreq p₁ p₂ ≠ 0 := left_ne_zero_of_mul h
  have h2 : (1 - meanAlleleFreq p₁ p₂) ≠ 0 := right_ne_zero_of_mul h
  unfold neiGst betweenSubgroupVariance ploidy Descent.Core.halfDiffSq Descent.Core.ploidy
  field_simp
  ring

/-- **Cross-check: the two spellings of Nei's `G_ST` in this corpus agree.**

What this proves is that two independently written spellings of NEI's `G_ST`
coincide. **Neither side is Hudson's estimator.** That one is `hudsonFst`, and
`neiGst_ne_hudsonFst` exhibits a point where it differs from both of these, so
do not read either name here as Hudson's. -/
theorem neiGstFromFrequencies_eq_neiGst (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    PopGen.neiGstFromFrequencies p₁ p₂ = neiGst p₁ p₂ := by
  rw [neiGst_eq_varianceRatio p₁ p₂ h]
  change (p₁ - p₂) ^ 2 /
      (4 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) =
    ((p₁ - p₂) ^ 2 / 4) /
      (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))
  field_simp [h]

/-- **The allele-frequency contrast constant is forced, not chosen.**

Four times `neiGst` -- which is Nei's `G_ST`, see its docstring; the `4` is
derived for THAT quantity and is not an empirical constant for Hudson's
estimator -- is exactly the variance of the standardized allele-frequency
contrast. The BBP inversion that recovered `3.9920 ± 0.0045` used genuine
Hudson `F_ST`; it validates `hudsonBbpSpike`, not this identity. Keeping those
two facts separate is the point of the named specializations below. -/
theorem four_neiGst_eq_standardizedContrastVariance (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    4 * neiGst p₁ p₂ =
      (p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  rw [neiGst_eq_varianceRatio p₁ p₂ h]
  unfold betweenSubgroupVariance Descent.Core.halfDiffSq
  field_simp

/-- **The allele-frequency-contrast normalization.**

This is deliberately not called the BBP spike: its input is Nei's `G_ST`, and
its interpretation is the standardized allele-frequency contrast
variance times the subgroup load.

    Empirical status: CONVENTION PINNED as Nei's `G_ST`, and no measurement bears on the
    constant here. The `4` in `demographicSpike` is DERIVED for this input --
    `four_neiGst_eq_standardizedContrastVariance` proves `4·G_ST` IS the standardized
    allele-frequency contrast variance, as algebra with no population in it -- so this
    specialization inherits an identity rather than an empirical calibration. The BBP
    inversion that recovered `3.9920 ± 0.0045` supplied genuine Hudson `F_ST` and therefore
    calibrates `hudsonBbpSpike`; because `Hudson = 2G/(1+G)` is nonlinear, that measurement
    does NOT transfer here, which is the whole reason the two specializations are named
    apart. -/
noncomputable def neiContrastSpike (n m p₁ p₂ : ℝ) : ℝ :=
  Portability.demographicSpike n (neiGst p₁ p₂) m

/-- **The empirically calibrated PC/BBP normalization.**

The `F` supplied to the validation experiment was the ratio-of-averages Hudson
estimator. This named specialization prevents that empirical law from being
silently reinterpreted as the different Nei functional.

    Empirical status: **VALIDATED**, and this specialization is the one the measurement was
    made on. Inverting the BBP eigenvalue law on simulated genotypes recovers the constant
    as `3.9920 ± 0.0045` against the derived `4`, with `F` measured as genuine Hudson
    `F_ST` on the same simulated data
    (`validation/empirical/differential/cluster/fam_im_coalescent_results.json`, which
    records `3.99240`). That is 1.8 sems from `4` and 442 sems from the `2` the constant
    might otherwise have been, so the run discriminates the constant rather than tolerating
    it.

    The competitor on the same cells is `neiContrastSpike`: supplying Nei's `G_ST` to the
    same body moves the answer by a factor approaching two at weak differentiation, so the
    measurement identifies the ESTIMATOR as well as the constant. -/
noncomputable def hudsonBbpSpike (n m p₁ p₂ : ℝ) : ℝ :=
  Portability.demographicSpike n (hudsonFst p₁ p₂) m

/-- **The Nei-normalized contrast spike has an exact observable form.** -/
theorem neiContrastSpike_eq_contrastVariance_mul_effectiveSize
    (n m p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    neiContrastSpike n m p₁ p₂ =
      ((p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))) *
        Portability.effectiveSubgroupSize n m := by
  unfold neiContrastSpike Portability.demographicSpike
  rw [← four_neiGst_eq_standardizedContrastVariance p₁ p₂ h]

/-- **The Hudson-calibrated spike expressed on the Nei scale.**

The exact conversion is nonlinear:
`4·Hudson = 8·G_ST/(1+G_ST)`. Thus the two named spike laws cannot be
reconciled by changing a global constant. In the weak-differentiation regime
the Hudson-calibrated level approaches twice the Nei contrast level. -/
theorem hudsonBbpSpike_eq_eight_neiGst_div_one_add_mul_effectiveSize
    (n m p₁ p₂ : ℝ)
    (hpos : 0 < p₁ * (1 - p₂) + p₂ * (1 - p₁))
    (hbar : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    hudsonBbpSpike n m p₁ p₂ =
      (8 * neiGst p₁ p₂ / (1 + neiGst p₁ p₂)) * Portability.effectiveSubgroupSize n m := by
  unfold hudsonBbpSpike Portability.demographicSpike
  rw [hudsonFst_eq_of_neiGst p₁ p₂ hpos hbar]
  ring

/-- **A regression witness preventing convention collapse.** At an interior,
mean-one-half frequency pair, the empirically Hudson-calibrated spike and the
exact Nei contrast spike are different. -/
theorem hudsonBbpSpike_ne_neiContrastSpike_at_mean_half :
    hudsonBbpSpike 4 2 (9/10) (1/10) ≠
      neiContrastSpike 4 2 (9/10) (1/10) := by
  unfold hudsonBbpSpike neiContrastSpike Portability.demographicSpike hudsonFst neiGst
    Portability.effectiveSubgroupSize ploidy meanAlleleFreq Descent.Core.midpoint Descent.Core.ploidy
  norm_num

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
for the same quantity, and no theorem related them. Forward simulation with the spousal correlation measured rather than assumed puts the second within
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

Prefer calling `hweGenotypeVariance` in new code, so no new edge is needed.

The two inlinings are `genotypeVarianceHWE` and `hweHeterozygosity`, both in
`AncestrySpecificPower` and related to each other there by
`hweHeterozygosity_eq_genotypeVarianceHWE`. The two theorems below tie that pair back to
`ploidy`, so the convention has exactly one place to change. -/

theorem genotypeVarianceHWE_eq_hwe (p : ℝ) :
    Portability.genotypeVarianceHWE p = hweGenotypeVariance p := by
  unfold Portability.genotypeVarianceHWE hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

theorem hweHeterozygosity_eq_hwe (p : ℝ) :
    Portability.hweHeterozygosity p = hweGenotypeVariance p := by
  unfold Portability.hweHeterozygosity hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

/-! ### Tying the island-model equilibrium back to the scaled rate

One definition, one bridge: the island-model equilibrium is the migration-drift
equilibrium at the scaled migration rate. A second spelling of `1 / (1 + 4 Nₑ m)` would
need its own bridge theorem, which is a reason not to add one. -/

theorem fstMigrationDriftEquilibrium_eq_scaled (Ne m : ℝ) :
    Portability.fstMigrationDriftEquilibrium Ne m =
      PopGen.fstMutationDriftEquilibrium (PopGen.scaledMigrationRate Ne m) := by
  unfold Portability.fstMigrationDriftEquilibrium PopGen.fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy Descent.Core.ploidy; ring_nf

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

`heterozygosityLossDerived` and `wrightFisherDriftRetention` are attached to the named
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

theorem heterozygosityLossDerived_uses_timeScale (Ne : ℝ) (t : ℕ) :
    PopGen.heterozygosityLossDerived Ne t = 1 - (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold PopGen.heterozygosityLossDerived Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay; rw [coalescentTimeScale_eq]

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
    PopGen.EvolutionaryParameters.theta p = 2 * ploidy * p.Ne * p.mu := by
  unfold PopGen.EvolutionaryParameters.theta ploidy PopGen.scaledMutationRate Descent.Core.scaledMutationRate Descent.Core.ploidy; ring

theorem EvolutionaryParameters_bigM_eq_ploidy_form (p : PopGen.EvolutionaryParameters) :
    PopGen.EvolutionaryParameters.bigM p = 2 * ploidy * p.Ne * p.mig := by
  unfold PopGen.EvolutionaryParameters.bigM ploidy PopGen.scaledMigrationRate Descent.Core.scaledMigrationRate Descent.Core.ploidy; ring

/-- **The between-population variance of the mean breeding value is
`ploidy · F_ST · V_A`.**

Two independently drifting populations each contribute `F_ST V_A`, so the
variance of their difference carries the ploidy factor. Writing `2` here is
the same convention as everywhere else and is now tied to it. -/
theorem Var_Delta_Mu_eq_ploidy_form (V_A fst : ℝ) :
    Portability.Var_Delta_Mu V_A fst = ploidy * fst * V_A := by
  unfold Portability.Var_Delta_Mu ploidy Descent.Core.ploidy; ring

/-- **The one-population PGS drift variance carries the same ploidy factor.**

`pgsDriftVariance_one_pop` is the single-population form of `Var_Delta_Mu`, and its `2` is
the same convention: `ploidy · F_ST · V_A`.  The two definitions are alpha-equivalent, and
this pair of theorems is what says so rather than leaving it to the reader. -/
theorem pgsDriftVariance_one_pop_eq_ploidy_form (V_A fst : ℝ) :
    PopGen.pgsDriftVariance_one_pop V_A fst = ploidy * fst * V_A := by
  unfold PopGen.pgsDriftVariance_one_pop Portability.Var_Delta_Mu ploidy Descent.Core.ploidy
  ring

/-- The two drift-variance definitions are the same quantity. -/
theorem pgsDriftVariance_one_pop_eq_Var_Delta_Mu (V_A fst : ℝ) :
    PopGen.pgsDriftVariance_one_pop V_A fst = Portability.Var_Delta_Mu V_A fst := by
  rw [pgsDriftVariance_one_pop_eq_ploidy_form, Var_Delta_Mu_eq_ploidy_form]

/-! ### Genotype variance inside sums and products

Eight further definitions carry `2 p (1 - p)` as a factor rather than as their
whole body: score means and variances, Fisher's average effect, dominance and
additive variance, two noncentrality parameters, and a pairwise epistatic
variance. Each is now written against `hweGenotypeVariance`. -/

theorem pgsVariance_uses_hwe {m : ℕ} (β p : Fin m → ℝ) :
    Portability.pgsVariance β p = ∑ i, β i ^ 2 * hweGenotypeVariance (p i) := by
  unfold Portability.pgsVariance hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

theorem dominanceVariance_uses_hwe {m : ℕ} (p d : Fin m → ℝ) :
    PopGen.dominanceVariance p d = ∑ i, (hweGenotypeVariance (p i) * d i) ^ 2 := by
  unfold PopGen.dominanceVariance hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

/-- **`additiveVariance` is a sum over loci and therefore assumes linkage equilibrium**;
this theorem pins its `2 p (1 - p)` to `ploidy` and says nothing about that assumption.

The qualifier is load-bearing. The per-locus sum drops the cross term
`Σ_{i≠j} 4 α_i α_j D_ij`, and the sign of the resulting error flips with the sign of the
effect product, so no constant repairs it: at `p = 1/2`, `D = 1/8`, `α = (1,1)` gives `1`
against a true `3/2`, while `α = (1,-1)` gives `1` against a true `1/2`. The
unconditional reading is FALSIFIED (`VarianceComponents.additiveVariance`). -/
theorem additiveVariance_uses_hwe {m : ℕ} (p α : Fin m → ℝ) :
    PopGen.additiveVariance p α = ∑ i, hweGenotypeVariance (p i) * (α i) ^ 2 := by
  unfold PopGen.additiveVariance hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

theorem noncentralityParam_uses_hwe (n : ℕ) (beta p : ℝ) :
    Decision.noncentralityParam n beta p = n * beta ^ 2 * hweGenotypeVariance p := by
  unfold Decision.noncentralityParam hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

theorem gwasNCP_uses_hwe (n : ℕ) (β p : ℝ) :
    PopGen.gwasNCP n β p = n * β ^ 2 * hweGenotypeVariance p := by
  unfold PopGen.gwasNCP Portability.ncp Portability.effectiveFisherInformation Portability.fisherInformation Portability.genotypeVarianceHWE
    hweGenotypeVariance Descent.Core.product Descent.Core.hweHeterozygosity Descent.Core.ploidy
  ring_nf

theorem effectiveFisherInformation_uses_hwe (n : ℕ) (p r2_ld : ℝ) :
    Portability.effectiveFisherInformation n p r2_ld = n * hweGenotypeVariance p * r2_ld := by
  unfold Portability.effectiveFisherInformation Portability.fisherInformation Portability.genotypeVarianceHWE
    hweGenotypeVariance Descent.Core.product Descent.Core.hweHeterozygosity Descent.Core.ploidy
  ring_nf

theorem epistaticVariancePairwise_uses_hwe (γ p₁ p₂ : ℝ) :
    Portability.epistaticVariancePairwise γ p₁ p₂ =
      γ ^ 2 * hweGenotypeVariance p₁ * hweGenotypeVariance p₂ := by
  unfold Portability.epistaticVariancePairwise hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

/-- The between-population drift variance of the score, carrying the same
ploidy factor as `Var_Delta_Mu`. -/
theorem expectedPGSDiffVariance_eq_ploidy_form (V_A fst : ℝ) :
    PopGen.expectedPGSDiffVariance V_A fst = ploidy * ploidy * fst * V_A := by
  unfold PopGen.expectedPGSDiffVariance ploidy Descent.Core.ploidy; ring

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
      = PopGen.fstMutationDriftEquilibrium (PopGen.scaledMigrationRate Ne (m₁₂ + m₂₁)) := by
  unfold Portability.asymmetricFst PopGen.fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy Descent.Core.ploidy; ring_nf

/-! The bridge from the migration-drift equilibrium to the scaled mutation-drift form is
`fstMigrationDriftEquilibrium_eq_scaled` above.  A second copy of it stood here, for the
second spelling of that equilibrium -- which is what the note above predicted: "A second
spelling of `1 / (1 + 4 Nₑ m)` would need its own bridge theorem, which is a reason not to
add one."  The spelling is gone from `PortabilityDrift` and its bridge with it. -/

theorem fstMigrationMutationEquilibriumManyDemes_eq_scaled (Ne m μ : ℝ) :
    PopGen.fstMigrationMutationEquilibriumManyDemes Ne m μ
      = 1 / (1 + PopGen.scaledMigrationRate Ne m + PopGen.scaledMutationRate Ne μ) := by
  unfold PopGen.fstMigrationMutationEquilibriumManyDemes Descent.Core.fstFromFlow
  rw [scaledMigrationRate_eq_ploidy_form, scaledMutationRate_eq_ploidy_form]
  unfold ploidy Descent.Core.ploidy; ring_nf

/-- **The finite-deme island equilibrium carries the same two scaled rates.** Its
`4 Nₑ m` is `scaledMigrationRate` and its `4 Nₑ μ` is `scaledMutationRate`, exactly as in
the deme-blind limit form; the deme correction multiplies the migration rate and does not
touch either constant. Without this the `4` would be a third inlined ploidy convention. -/
theorem fstIslandEquilibriumFiniteDemes_eq_scaled (Ne m μ nDemes : ℝ) :
    PopGen.fstIslandEquilibriumFiniteDemes Ne m μ nDemes
      = 1 / (1 + PopGen.scaledMigrationRate Ne m * PopGen.islandDemeCorrection nDemes
              + PopGen.scaledMutationRate Ne μ) := by
  unfold PopGen.fstIslandEquilibriumFiniteDemes Descent.Core.fstFromFlow
  rw [scaledMigrationRate_eq_ploidy_form, scaledMutationRate_eq_ploidy_form]
  unfold ploidy Descent.Core.ploidy; ring_nf

theorem expectedFreqDiffSq_uses_hwe (fst p0 : ℝ) :
    PopGen.expectedFreqDiffSq fst p0 = fst * hweGenotypeVariance p0 := by
  unfold PopGen.expectedFreqDiffSq hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

theorem pgsMean_uses_ploidy {m : ℕ} (β p : Fin m → ℝ) :
    Portability.pgsMean β p = ∑ i, β i * (ploidy * p i) := by
  unfold Portability.pgsMean ploidy Descent.Core.ploidy; ring_nf

theorem fisherAverageEffect_uses_ploidy (a d p : ℝ) :
    PopGen.fisherAverageEffect a d p = a + d * (1 - ploidy * p) := by
  unfold PopGen.fisherAverageEffect ploidy Descent.Core.ploidy; ring

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
    PopGen.scaledMigrationRate m.Ne m.mig = 2 * ploidy * m.Ne * m.mig := by
  unfold PopGen.scaledMigrationRate ploidy Descent.Core.scaledMigrationRate Descent.Core.ploidy; ring

theorem fstMigDriftNext_uses_timeScale (Ne m Fst : ℝ) :
    Portability.fstMigDriftNext Ne m Fst
      = (1 - 2 * m - 1 / coalescentTimeScale Ne) * Fst
        + 1 / coalescentTimeScale Ne := by
  unfold Portability.fstMigDriftNext; rw [coalescentTimeScale_eq]

theorem ibdFst_eq_ploidy_form (d N sigma_sq : ℝ) :
    PopGen.ibdFst d N sigma_sq = d / (2 * ploidy * N * sigma_sq + d) := by
  unfold PopGen.ibdFst ploidy Descent.Core.ploidy; ring_nf

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
    PopGen.sharedLDRetention p = (1 - p.recomb) ^ (ploidy * p.t_div) := by
  unfold PopGen.sharedLDRetention ploidy Descent.Core.ploidy; ring_nf

theorem demoSteppingStoneFst_eq_scaled (d Ne m σ_sq : ℝ) :
    PopGen.demoSteppingStoneFst d Ne m σ_sq
      = d / (d + PopGen.scaledMigrationRate Ne m * σ_sq) := by
  unfold PopGen.demoSteppingStoneFst
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy Descent.Core.ploidy; ring_nf

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
        + ploidy * mu * (1 - PopGen.hetMutationDriftRecurrence Ne mu H₀ t) := by
  change
    (1 - 1 / (2 * Ne)) * PopGen.hetMutationDriftRecurrence Ne mu H₀ t +
        2 * mu * (1 - PopGen.hetMutationDriftRecurrence Ne mu H₀ t) = _
  rw [coalescentTimeScale_eq]
  unfold ploidy Descent.Core.ploidy
  rfl

/-- Equilibrium heterozygosity under mutation-drift balance, `θ/(1 + θ)`,
written out with its own four. This is the last inline restatement of the
ploidy convention in the development. -/
theorem hetMutationFloor_eq_scaled (Ne mu : ℝ) :
    Portability.hetMutationFloor Ne mu
      = PopGen.scaledMutationRate Ne mu / (1 + PopGen.scaledMutationRate Ne mu) := by
  unfold Portability.hetMutationFloor
  rw [scaledMutationRate_eq_ploidy_form]; unfold ploidy Descent.Core.ploidy; ring_nf

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

/-- **The same body, read as a between-population `F_ST`.**

`heterozygosityLossDerived` and `heterozygosityLossFromDrift` share a body, and `DriftRegime` names
that
coincidence as the defect rather than a convenience: a within-population heterozygosity
loss and a between-population variance ratio are different quantities, and the shared body
is what let one be substituted for the other. They are deliberately *not* merged. This
theorem records that `heterozygosityLossDerived` inherits the closed-population regime through that
shared body — which is the fact a reader needs in order to see that its `F_ST` reading is
only available in the regime where the loss reading is.

Note the argument orders differ: `heterozygosityLossFromDrift` takes `(t, Ne)` and
`heterozygosityLossDerived` takes `(Ne, t)`, so the same call spelled the same way means different
things
depending on which is in scope. That is the hazard `equilibriumFst` carried before it was
collapsed, still live here because these two must *not* be collapsed. -/
theorem heterozygosityLossDerived_eq_closedPopulation_measuredLoss
    (t : ℕ) (Ne H₀ : ℝ) (hH : 0 < H₀) :
    PopGen.heterozygosityLossDerived Ne t = (PopGen.closedPopulation Ne H₀ hH).measuredLoss t := by
  rw [PopGen.measuredLoss_closedPopulation]
  unfold PopGen.heterozygosityLossDerived Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  rfl

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
`hweGenotypeVariance`; where it is a scaled rate it goes through `scaledMigrationRate`,
which `scaledMigrationRate_eq_ploidy_form` already forces. -/

/-- **The `2 p (1 - p)` in the effective sample size is the diploid genotype variance.**
`StatisticalGeneticsMethodology.effectiveSampleSizeFromSE` inverts `SE² · Var(dosage)`, and
`Var(dosage)` under Hardy-Weinberg proportions is `hweGenotypeVariance`. Written inline the
two was free; here it is the ploidy, and an SE reported on a haploid dosage scale would
have to change this file rather than that definition. -/
theorem effectiveSampleSizeFromSE_uses_hweGenotypeVariance (se p : ℝ) :
    Portability.effectiveSampleSizeFromSE se p = 1 / (se ^ 2 * hweGenotypeVariance p) := by
  unfold Portability.effectiveSampleSizeFromSE hweGenotypeVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

/-- **Both twos in the mutation-drift heterozygosity step are the ploidy.** The drift term
loses a fraction `1 / (ploidy · Nₑ)` per generation — the reciprocal coalescent time scale —
and the mutation term gains `ploidy · mu` because both copies at the locus are exposed. A
haploid recursion would carry neither. -/
theorem hetStepWithMutation_uses_coalescentTimeScale (Ne mu H : ℝ) :
    Portability.hetStepWithMutation Ne mu H
      = (1 - 1 / coalescentTimeScale Ne) * H + ploidy * mu * (1 - H) := by
  unfold Portability.hetStepWithMutation ploidy Descent.Core.ploidy; rw [coalescentTimeScale_eq]

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
      = F + (1 - F) / coalescentTimeScale Ne - ploidy * rate * F := by
  unfold Portability.ibdFlowStep ploidy Descent.Core.ploidy; rw [coalescentTimeScale_eq]

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
          / ((1 - rate) ^ 2 + coalescentTimeScale Ne * rate * (ploidy - rate)) := by
  unfold Portability.ibdRecurrenceFixedPoint ploidy Descent.Core.ploidy; rw [coalescentTimeScale_eq]

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
      = F + (1 - F) / coalescentTimeScale p.Ne - ploidy * (p.mig + p.mu) * F := by
  unfold PopGen.fstDriftFlowStep ploidy Descent.Core.ploidy; rw [coalescentTimeScale_eq]

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
          - ploidy * (PopGen.islandDemeCorrection 2 * p.mig + p.mu) * F := by
  unfold PopGen.fstDemeCorrectedFlowStep ploidy PopGen.islandDemeCorrection Descent.Core.ploidy
    Descent.Core.islandDemeCorrection Descent.Core.ratio
  rw [coalescentTimeScale_eq]; norm_num

/-- **The `2 p` in Fisher's average effect is the expected diploid dosage.** The dominance
deviation is weighted by `1 - ploidy · p`, which is `q - p`, and `ploidy · p` is `E[X]` for
a dosage `X` on `0, 1, …, ploidy` in Hardy-Weinberg proportions. On a haploid scale the
weight is not this expression, so the constant is forced by the coding and belongs here. -/
theorem averageEffect_uses_ploidy (m : Blindness.OneLocusArchitecture) :
    m.averageEffect = m.a + m.d * (1 - ploidy * m.p) := by
  unfold Blindness.OneLocusArchitecture.averageEffect ploidy Descent.Core.ploidy; ring

/-- **The two in the polygenic-adaptation shift is the ploidy.** The mean score is
`Σᵢ βᵢ · ploidy · pᵢ`, so its shift carries the same factor; the body writes the `2` as a
literal only because importing `Conventions` into `SelectionArchitecture` closes an import
cycle. This theorem is what stops that literal from drifting away from `ploidy`. -/
theorem polygenicAdaptationShift_uses_ploidy {m : ℕ} (β Δp : Fin m → ℝ) :
    PopGen.polygenicAdaptationShift β Δp = ∑ i, β i * ploidy * Δp i := by
  unfold PopGen.polygenicAdaptationShift ploidy Descent.Core.ploidy
  simp

/-- **The four in the quadratic stepping-stone form is twice the ploidy**, the same
`4 Nₑ` scaling as every other migration-drift denominator in the corpus. Only the powers of
`m` and `σ²` distinguish this form from `demoSteppingStoneFst`; the constant does not. -/
theorem steppingStoneFstQuadratic_uses_ploidy (d Ne m σ_sq : ℝ) :
    PopGen.steppingStoneFstQuadratic d Ne m σ_sq
      = d / (d + 2 * ploidy * Ne * σ_sq ^ 2 * m ^ 2) := by
  unfold PopGen.steppingStoneFstQuadratic ploidy Descent.Core.ploidy; ring

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
      = (10 + 2 * ploidy * Ne * c)
          / ((2 + 2 * ploidy * Ne * c) * (11 + 2 * ploidy * Ne * c)) := by
  simp only [PopGen.ohtaKimuraSigmaDSq, ploidy, Descent.Core.ploidy]
  ring

/-- **The finite-deme island `F_ST` is the identity fraction at the deme-corrected scaled
migration rate.** Its `4 Nₑ m` is `scaledMigrationRate`, which
`scaledMigrationRate_eq_ploidy_form` already forces to `2 · ploidy · Nₑ · m`; the deme
correction multiplies that rate and does not touch the constant. This is the second
consumer of the one bridge, so the finite-`d` form and its `d → ∞` limit cannot acquire
different conventions. -/
theorem islandFstFiniteDemes_eq_scaled (Ne m d : ℝ) :
    PopGen.islandFstFiniteDemes Ne m d
      = PopGen.fstMutationDriftEquilibrium (PopGen.scaledMigrationRate Ne m * PopGen.islandDemeCorrection d) := by
  unfold PopGen.islandFstFiniteDemes PopGen.fstMutationDriftEquilibrium PopGen.scaledMigrationRate Descent.Core.fstFromFlow
    PopGen.islandDemeCorrection Descent.Core.islandDemeCorrection Descent.Core.ratio Descent.Core.scaledMigrationRate Descent.Core.ploidy
  ring

/-- **The `2 μ` in the stepping-stone characteristic length counts the two lineages of a
sampled pair.** Mutation destroys the identity of a pair at rate `ploidy · μ`, so
`1 / (ploidy · μ)` is the time available to the diffusion and `L² = m σ² / (ploidy · μ)`
is the balance. Written inline the two read as arbitrary; it is the same two that
`coalescentTimeScale` puts in front of `Nₑ`. -/
theorem steppingStoneCharacteristicLength_uses_ploidy (m σ_sq μ : ℝ) :
    PopGen.steppingStoneCharacteristicLength m σ_sq μ = Real.sqrt (m * σ_sq / (ploidy * μ)) := by
  unfold PopGen.steppingStoneCharacteristicLength ploidy Descent.Core.ploidy; ring

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
  unfold PopGen.serialFounderWithinTime coalescentTimeScale ploidy Descent.Core.ploidy; ring

/-- **Nei's `G_ST` between a frequency and its fold is the squared contrast.** At
`p₂ = 1 - p` the mean frequency is `1/2`, the total heterozygosity `ploidy · p̄ (1 - p̄)`
is `1/2`, and `G_ST` collapses to `(1 - ploidy · p)²`. This is the only place the
denominator's `ploidy` is visible as a number, and it is what makes the next theorem an
identity rather than a proportionality. -/
theorem neiGst_at_fold (p : ℝ) : neiGst p (1 - p) = (1 - ploidy * p) ^ 2 := by
  unfold neiGst meanAlleleFreq ploidy Descent.Core.midpoint Descent.Core.ploidy; ring

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
    Blindness.BundleRigidity.mOne p * Blindness.BundleRigidity.mTwo p = neiGst p (1 - p) / (p * (1 - p)) := by
  rw [neiGst_at_fold]
  unfold Blindness.BundleRigidity.mOne Blindness.BundleRigidity.mTwo ploidy Descent.Core.ploidy
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
`hweGenotypeVariance` on the allele scale rather than the dosage scale, which is exactly
one `ploidy` apart, and writing it inline left that scale choice free. -/
theorem driftVariance_uses_hweGenotypeVariance (p0 fst : ℝ) :
    PopGen.driftVariance p0 fst = hweGenotypeVariance p0 * fst / ploidy := by
  unfold PopGen.driftVariance hweGenotypeVariance ploidy Descent.Core.hweHeterozygosity Descent.Core.ploidy
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
