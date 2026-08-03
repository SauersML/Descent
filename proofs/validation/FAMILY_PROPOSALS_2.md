# Family proposals, bucket 2

Classification only. No simulator was written, no Lean build was run, no number in
this document was measured. Every claim below about a definition is a claim about
the text of a `.lean` file in the working tree on 2026-08-03, cited by **file and
declaration name** — never by line number, because line numbers in this tree
moved measurably within the hour.

Read first, and not reproduced here:
`proofs/validation/empirical/COVERAGE_DENOMINATOR.md` (the census) and
`proofs/validation/empirical/differential/cluster/families.py` (what a family is).

---

## 0. Scope, and a scope defect

The brief named fourteen modules and asked for 266 definitions. Those fourteen
modules hold **230** `def`/`abbrev` declarations by source count:

| module (under `proofs/Calibrator/`) | defs |
|---|---:|
| TransferLearningPGS.lean | 52 |
| FoldedSpectrum.lean | 26 |
| PolygenicArchitecture.lean | 24 |
| ConditionalGain.lean | 22 |
| EnsembleChannel.lean | 17 |
| DirichletTransfer.lean | 13 |
| BayesianPGSTheory.lean | 13 |
| SelectionArchitecture.lean | 12 |
| ClinicalUtilityFairness.lean | 10 |
| UnifiedBiology.lean | 9 |
| PCCorrectability/Frequency.lean | 9 |
| GenerativePortabilityLaw.lean | 9 |
| PolygenicAdaptation.lean | 7 |
| HorizonCurve.lean | 7 |
| **subtotal** | **230** |

"the rest of that group" was not enumerable from the brief, so three thematically
adjacent modules were added and are **declared here rather than assumed**:
`GeneticArchitectureDiscovery.lean` (18), `PolygenicSpectroscopy.lean` (13),
`AncestrySpecificArchitecture.lean` (6). **Total classified: 267.**

**Ownership flags — do not act on these without the lead.**

* `PCCorrectability/ImitationCapacity.lean` (28 checkable defs, the fourth-largest
  module in the census) is the immediate sibling of `PCCorrectability/Frequency.lean`,
  which I *was* given. I did not classify it. Somebody should.
* The three modules I added may belong to a sibling agent. If so, drop §2's
  `ascertainment` / `pgs_transport_drift` / `site_frequency_spectrum` rows and the
  `hwe_dosage_kurtosis_information` family loses its `PolygenicSpectroscopy` half.

**A method check worth recording.** The checkable/non-checkable split below was
computed by hand from return types, using the corpus's own F1 rule. Where the
census published a per-module checkable count it agrees **exactly**:
EnsembleChannel 16, FoldedSpectrum 16, GeneticArchitectureDiscovery 16,
BayesianPGSTheory 13. That is the only evidence offered that this classification
is reproducible, and it is worth more than the prose.

---

## 1. The split across the three outcomes

| outcome | defs |
|---|---:|
| (a) joins an **existing** family | 67 |
| (b) belongs to a **new** family proposed here | 173 |
| (c) makes **no empirically checkable claim** | 27 |
| **total** | **267** |

Membership is many-to-many, as the census says it must be. The per-family counts
in §3 sum to more than 173 because several definitions are members of two
families; the 173 above is the *primary* assignment, one per definition, so that
the three outcomes partition the 267.

### Outcome (c), the 27, named by kind

**Propositions (17).** `TransferLearningPGS.AsymptoticallyZero`,
`TransferLearningPGS.AsymptoticallyConsistent`,
`FoldedSpectrum.InLinkageEquilibrium`, `FoldedSpectrum.HasFrequencyTie`,
`FoldedSpectrum.ReadsThroughFunctionals`, `FoldedSpectrum.HasScalarSummary`,
`FoldedSpectrum.IsLevelSetFunctional`, `FoldedSpectrum.ReversalEven`,
`FoldedSpectrum.ReversalOdd`, `FoldedSpectrum.Reversible`,
`ConditionalGain.FullSupport`, `ConditionalGain.CoversTuple`,
`ConditionalGain.ProductCovers`, `HorizonCurve.IsStationaryKernel`,
`GenerativePortabilityLaw.MarginalAmplitudeDeterminesHistoryDegradation`,
`GeneticArchitectureDiscovery.gwasDiscovered`,
`PolygenicSpectroscopy.hweLatticeCondition`.

**Index, permutation and type constructions (5).** `FoldedSpectrum.genotypeFlip3`
(the permutation `![2,1,0]` on `Fin 3`), `FoldedSpectrum.idReversal`,
`UnifiedBiology.BinaryBiologicalState` (`abbrev … := Fin 2`),
`PolygenicSpectroscopy.hardCallLatticeIndex` (`→ ℤ`),
`ConditionalGain.copyWitnessValue` is **not** here — it returns `Fin 2 → ℝ` and is
checkable.

**Sets and finsets (4).** `PolygenicArchitecture.boundedEffectCarrier`,
`PolygenicArchitecture.effects`,
`PCCorrectability.Frequency.FrequencyResolvedCohort.correctableClasses`,
`GeneticArchitectureDiscovery.lassoActiveLoci`.

**Structural witness, unadjudicated (1).**
`GenerativePortabilityLaw.marginalAmplitudeHistoryDegradationBlindness` — a
`ProbeBlindness` instance, the exact category the census parked as its 42 UNKNOWN.
Counted in (c) here and flagged as a human call.

**A caution about (c) that the corpus earned the hard way.** `families.py` records
that across two tiers and **thirty-one** attempts, nothing in this corpus has
survived an un-simulatability claim; every one lost to F3, the real-valued-consumer
test. So the 27 above are offered as *category errors of return type* only. None of
them is claimed to be beyond reach through composition, and four of them are almost
certainly reachable that way: `InLinkageEquilibrium`, `ReadsThroughFunctionals`,
`HasFrequencyTie` and `IsStationaryKernel` are all hypotheses of real-valued
theorems whose conclusions a simulator can evaluate on both sides.

---

## 2. Outcome (a): 67 definitions join families that already exist

This is the cheapest coverage in the bucket and it should be spent first. Nothing
here needs a new generative process; it needs a membership entry in
`families.py` and a re-run so the credit is earned rather than asserted.

**A structural finding first.** `families.py` already lists
`effectVarianceRecurrence`, `equilibriumEffectVariance`, `discoveryNCP`,
`noncentralityParam` and `expectedFreqDiffSq` as members — and every one of them
is declared **outside the seven-file slice**, in `SelectionArchitecture.lean`,
`GeneticArchitectureDiscovery.lean` and `AncestrySpecificArchitecture.lean`. The
existing families are therefore *already* out-of-slice families; the in-slice
coverage percentage has been counting the fraction of them that happens to land in
seven filenames. That is the census's point about the slice being a file list, made
concrete from the other direction.

| existing family | joining definitions | n |
|---|---|---:|
| `selection_regimes` | SelectionArchitecture: `equilibriumEffectVariance`, `effectVarianceRecurrence` (already declared members — this records where they *live*), `stabilizingSelectedArchitectureVariance`, `optimumOUVariance`, `fluctuatingSelectedArchitectureVariance`, `effectCorrelationStabilizing`, `fluctuatingEffectCorrelation`, `stabilizingNsFromObservedCorrelation`, `tauFromObservedEffectCorrelation`, `sigmaThetaFromObservedSelectedVariance`; PolygenicAdaptation: `effectCorrelationStabilizingDriftSelection`, `effectCorrelationFluctuating` | 12 |
| `linear_prediction_transport` | TransferLearningPGS: `targetLinearExcessRisk`, `exactAdaptationGain`, `coefficientGapSq`; GeneticArchitectureDiscovery: `borrowedTraitBCrossCov`, `traitBSpecificCrossCov`, `totalTraitBCrossCov`, `borrowedTraitBProjection`, `totalTraitBProjection`, `taggedScoreEstimationRisk`, `ctMissedTargetSignal`, `commonOnlyPortableModel`, `commonAndRarePortableModel` | 12 |
| `liability_threshold_metrics` | ClinicalUtilityFairness: `LiabilityThresholdModel.witness`, `liabilitySensitivity`, `liabilitySpecificity`, `sensFromR2`, `specFromR2`, `ppv`, `proportionCorrectlyClassified`, `numberNeededToScreen`, `populationAttributableFraction`, `netReclassificationImprovement` | 10 |
| `ascertainment` | GeneticArchitectureDiscovery: `discoveryNCP` (declared member; lives here), `multiTraitDiscoveryNCP`, `olsEffectEstimationVariance`, `expectedLinearEffectEstimate`, `perCausalLocusSignal`, `geneticCorrelation`, `multiTraitEffectiveSampleSize`; SelectionArchitecture: `gwasNCP`; BayesianPGSTheory: `multiAncestryEffectiveN` | 9 |
| `pgs_transport_drift` | PolygenicAdaptation: `pgsDriftVariance_one_pop`, `pgsDriftVarianceFromLoci`, `pgsDiffVariance_two_pop`, `expectedPGSDiffVariance`, `qst`; SelectionArchitecture: `polygenicAdaptationShift`; AncestrySpecificArchitecture: `driftVariance`, `twoPopDriftVariance` | 8 |
| `hwe_genotype_score` | FoldedSpectrum: `diploidStdev`, `diploidAtomValue`, `diploidAtomMass`, `diploidFamily`; PolygenicSpectroscopy: `standardizedSquare` | 5 |
| `portability_permeability_and_completion` | FoldedSpectrum: `diploidCovarianceMomentPermeability`, `diploidPanelCovarianceMomentPermeability`, `totalDiploidCovarianceMomentInformation` | 3 |
| `neutral_af_benchmark_transport` | AncestrySpecificArchitecture: `portabilityFromArchitecture` (a Lean theorem in that file already factors it through `covarianceRetention`); PolygenicArchitecture: `rgFstWeightedUpperBound` | 2 |
| `ensemble_portability_channel` | EnsembleChannel: `weightedBandEnsembleLoss`, `weightedBandPredictorLoss` | 2 |
| `identity_by_descent_recurrence` | AncestrySpecificArchitecture: `geneFlowFstStep` — `geneFlowFstStep_eq_ibdFlowStep` is proved `rfl`, so this is the same map under a second name | 1 |
| `site_frequency_spectrum` | AncestrySpecificArchitecture: `expectedFreqDiffSq` (declared member; lives here) | 1 |
| `estimator_moments` | ConditionalGain: `secondMoment` | 1 |
| `island_migration_fst` | TransferLearningPGS: `privateArchitectureTransferCeiling` (built on `sharedLDFromMigration`) | 1 |
| **total** | | **67** |

Two of these rows carry a **short-name collision hazard** of the kind
`families.py` documents as O5b. `expectedFreqDiffSq` and `discoveryNCP` each
resolve to more than one declaration in this corpus. Any membership entry for
them must be keyed on the **fully qualified** name, or the join will over-count in
the flattering direction, as it did when the headline moved from 295 to 316.

---

## 3. Outcome (b): eleven new families, ranked

Ranked by members covered × cheapness of the simulator × whether a live
disagreement or a suspicious definition sits inside. Every family states what a
simulator would MEASURE and WHAT WOULD FALSIFY IT. None is marked
unsimulatable-as-stated; §3.11 explains the one place that was close.

---

### 3.1 `temporal_arrow_and_order_erasure` — 31 members, 3 files. **Rank 1.**

**Generative process.** A stationary finite-state Markov chain (two or three
states) is observed twice: once as an *ordered* sequence, once as an unordered
bag. A payoff is evaluated at the pair (source state, target state) rather than at
the target state alone, and an orientation imbalance `θ` biases the forward
against the reverse traversal. The whole family is the comparison between what an
order-free statistic can see and what the ordered pair can.

**Members.** EnsembleChannel: `twoUnitArrow`, `binaryFirstAnnotation`,
`binarySecondAnnotation`, `binaryTransitionArrowStatistic`,
`binaryOrientationStatisticMean`, `binaryOrientationArrowVariance`,
`threeCycleFeatureA`, `threeCycleFeatureB`, `threeCycleForwardCrossMoment`,
`threeCycleCrossFeatureArrow`. UnifiedBiology: `onePointPerformance`,
`targetOnlyTransportPerformance`, `crossStatePerformance`, `binaryStateWeight`,
`persistentTransition`, `switchingTransition`, `targetAnnotation`,
`contextMatchQuality`. HorizonCurve: `uniformTwo`, `stayKernel`, `swapKernel`,
`agreement`, `regretCurve`, `horizonPolynomial`. GenerativePortabilityLaw:
`historyKernel`, `historySelfEnergy`, `historySpectralDistanceSq`,
`historyDegradation`, `historyMarginalAmplitude`, `independentHistory`,
`persistentHalfHistory`.

**Measure.** `E[arrow]` as a function of `θ`; the naive one-endpoint average
against the two-endpoint regret under the stay and swap kernels; the degradation
of the independent history against the persistent one at matched marginal
amplitude; the sample size at which each is resolved.

**Falsifier.** Every headline here is a *blindness* claim — "no order-free
statistic can see `θ`", "marginal amplitude does not determine degradation",
"the naive horizon curve is flat". A simulator that only confirms these is
worthless, so it must be run in both directions. (i) Simulate the two processes
with identical one-point marginals and run a battery of order-free statistics —
panel mean, panel variance, the empirical state histogram, a heterozygosity
summary — at increasing `n`. If **any** of them separates the two processes the
wall is false. (ii) Simultaneously, the arrow statistic must separate them at an
`n` well below where the order-free battery does, or the practical claim that
order carries otherwise-unavailable information has no operating regime. Both
directions must fire; a run producing only (i)'s null is not evidence.

**Why rank 1.** Largest member count in the bucket; the simulator is finite-state
arithmetic with no genotypes, no LD and no coalescent, so it is the cheapest
script anyone in this bucket will write; and it contains the bucket's most
striking defect (§4.1): **four byte-identical Kronecker deltas under four names
across three files.**

---

### 3.2 `shrinkage_transfer_mse` — 25 members, 3 files. **Rank 2.**

**Generative process.** A target effect (or effect vector) is estimated two ways:
from a source that sits at squared distance `gapSq` from the target optimum, and
from `n` target samples with per-sample noise `noiseVar`. The deployed estimator
is the convex combination; the process draws the truth, the source estimate and
the target sample, forms the combination, and measures MSE across replicates and
across the mixing weight.

**Members.** TransferLearningPGS: `sourceShrinkageMSE`,
`optimalSourceShrinkageWeight`, `optimalFineTuningMSE`,
`requiredTargetSamplesForOptimalFineTuningMSE`, `sampleLimitedScratchTargetR2`,
`usableScratchTargetR2`, `scratchVsFineTuningCriticalSampleSize`,
`scratchTargetR2`, `fineTunedTargetR2`, `deployedTransferTargetR2`,
`oracleTransportAdaptationGain`, `transportPenalty`. BayesianPGSTheory:
`jamesSteinMSE`, `optimalShrinkage`, `gaussianPosteriorShrinkage`,
`shrinkageFactor`, `posteriorPrecision`, `posteriorVariance`, `posteriorMean`,
`snpShrinkage`, `spikeAndSlabPriorVariance`, `misspecExcessRisk`,
`posteriorPredictiveVariance`, `BayesianLinearModel.witness`.
PolygenicArchitecture: `spikeAndSlabVariance`.

**Measure.** `MSE(λ)` over a `λ` grid and its empirical argmin; the sample size at
which the target-only estimator overtakes the transferred one; the excess risk of
a Gaussian-prior posterior mean applied to a spike-and-slab truth.

**Falsifier.** **The corpus carries two mirror conventions for one quadratic and
does not say they are mirrors.** `TransferLearningPGS.sourceShrinkageMSE` is
`gapSq·λ² + (noiseVar/n)(1-λ)²` and its optimum
`optimalSourceShrinkageWeight = (noiseVar/n)/(gapSq + noiseVar/n)` weights the
**source** by the **noise**. `BayesianPGSTheory.jamesSteinMSE` is
`λ²σ² + (1-λ)²β²` and its optimum `optimalShrinkage = β²/(σ² + β²)` weights the
**data** by the **signal**. These are the same algebra with `λ` naming opposite
things. Simulate one process with a genuinely biased source and locate the
empirical argmin: at matched parameters at most one file's downstream theorems can
be reading its own `λ` correctly, and the run says which. Second falsifier:
`misspecExcessRisk = π(1-π)σ²_β` is derived in its own docstring by summing
per-SNP over- and under-shrinkage *without* re-optimising; simulate a π-sparse
architecture and measure the actual excess of the Gaussian-prior posterior mean
over the spike-and-slab one. Third: `posteriorPredictiveVariance = residual +
estimation` assumes zero covariance between the two terms; a design where the
score and the residual are correlated must break it.

---

### 3.3 `architecture_effect_mass_portability` — 21 members, 1 file. **Rank 3.**

**Generative process.** An architecture of `q` causal SNPs carries source squared
effects drawn from a chosen distribution (infinitesimal, spike-and-slab, or
selection-shaped) and a per-SNP retention fraction into the target. Portability is
the retained fraction of squared-effect mass.

**Members.** PolygenicArchitecture: `expectedSquaredEffect`,
`effectivePolygenicity`, `effectivePolygenicityOfEffects`,
`SNPArchitecturePortabilityModel.witness`, `sourceEffectMass`,
`targetRetainedEffectMass`, `lostEffectMass`, `relativePortabilityLoss`,
`portabilityScore`, `predictedPortability`,
`uniformCatastrophicPortabilityScore`, `meanAbsoluteEffect`,
`weightedRetentionUpperBound`, `heritabilityEnrichment`,
`logCoveringAtExponent`, `architectureRadius`, `architectureMoment`,
`certificationGap`, `mixtureExperiment`, `finiteProblem`, `calculus`.

**Measure.** `M_eff = (Σβ²)²/Σβ⁴` under each effect distribution, against `q`;
retained mass fraction after drift; the enrichment ratio for a functional
category.

**Falsifier.** `effectivePolygenicity` is documented as "the effective number of
causal variants", and its own docstring already concedes that the two-free-reals
form cannot express `M_eff ≤ q`. Draw `q` effects and compute `M_eff/q`. Under an
exponential effect distribution the ratio is a *constant* independent of `q`;
under spike-and-slab it tracks the causal fraction. If `M_eff/q` is a fixed
function of the effect **distribution** and not of the architecture **size**, then
"effective number of causal variants" names a shape statistic and not a count, and
every downstream statement reading it as a count is scope-broken. Cheap — no
genotypes, no LD, one array of draws — and it settles a naming claim rather than
an arithmetic one. Second falsifier: `uniformCatastrophicPortabilityScore` is
`1 - |mismatched|/M` under *equal* effects; draw unequal effects and the surviving
mass fraction diverges from the surviving SNP fraction, by an amount that grows
with effect-size dispersion. The "more polygenic architectures are more robust"
theorem is stated on the equal-effect surface only.

---

### 3.4 `hwe_dosage_kurtosis_information` — 19 members, 2 files. **Rank 4.**

**Generative process.** Hardy-Weinberg genotypes at allele frequency `q`,
standardized to `x = (g - 2q)/√(2q(1-q))`. The family is the higher-moment
structure of `x`: its fourth moment, the variance of `x²`, the Mellin drift
`E[x² log x²]`, and the sampling cost these impose on a covariance-moment
estimator.

**Members.** FoldedSpectrum: `invHeterozygosity`. PolygenicSpectroscopy:
`standardizedFourthMoment`, `mellinDrift`, `hweMellinDrift`, `mellinJetVariance`,
`hweMellinJetVariance`, `maxSafeEpistaticOrder`, `latticeCriticalMaf`,
`hardCallLatticeSpan`, `hardCallObservables`, `hweCodingInvariants`. (The
per-locus atoms `diploidStdev`, `diploidAtomValue`, `diploidAtomMass`,
`diploidFamily`, `standardizedSquare` are filed under `hwe_genotype_score` in §2
and are members here too — this is the many-to-many case.)

**Measure.** `E[x⁴]` against `1/(2q(1-q))` across the frequency spectrum; the
`≈24.75×` covariance-estimation multiplier at `q = 0.01`; the `≈198×` replicate
multiplier; `E[x² log x²]` against `hweMellinDrift`.

**Falsifier.** The `24.75×` and `99×` design constants are exact in the corpus
under a **known-mean** estimator with **independent loci**. Re-estimate with the
mean taken from the same sample and with loci in LD: the finite-sample multiplier
must move. Sharper, and this is the real test — at `q = 0.01` with `n = 1000` the
expected count of minor homozygotes is `0.1`, so the *realised* fourth moment is
dominated by whether any minor homozygote was drawn at all. The asymptotic
multiplier and the realised one need not agree at any feasible `n`, and the corpus
quotes the constant with **no sample-size condition attached**. If the measured
multiplier at deployment-scale `n` differs from `4901/198` by more than
Monte-Carlo error, the design law needs an `n`-regime declaration of exactly the
kind the census's `selection_regimes` entry had to add for population size.

**Rank 4 because it may already be half-done.** `PolygenicSpectroscopy` docstrings
name `proofs/validation/empirical/condensation/check_condensation.py` and
`proofs/validation/empirical/safe_order/` as already evaluating `hweMellinDrift`
and `maxSafeEpistaticOrder` numerically, and `maxSafeEpistaticOrder` already
carries `Empirical status: FALSIFIED on the common-variant column … VALIDATED on
the rare-variant tail`. **Check those two directories before writing anything.**
If they cover the Mellin half, this family is a membership entry plus a re-run —
the cheapest coverage in §3 — and only the kurtosis/sampling-cost half needs new
code.

---

### 3.5 `conditional_gain_characteristic_function` — 18 members, 1 file. **Rank 5.**

**Generative process.** A finite multilocus law assigns a phase to each site; the
score is the sum of phases and the conditional gain is `-log|E e^{isS}|`, infinite
at exact cancellation. Draw from the law, form the empirical characteristic
function at swept `s`, and measure how the gain grows with the number of sites.

**Members.** ConditionalGain: `scorePhase`, `cosPart`, `sinPart`,
`characteristicAmplitude`, `conditionalGainFunctional`,
`balancedBinaryOppositePhaseLaw`, `biasedBinaryOppositePhaseLaw`,
`copiedBinaryJointExpectation`, `copiedBinaryConditionalProductExpectation`,
`FiniteBoundedDeviation.witness`, `copyWitnessFamily`, `modulusCopyCoupling`,
`copyWitnessValue`, `gainBounded`, `gainLog`, `gainPolynomialRow`, `gainLinear`,
`toFiberCoupling`.

**Measure.** `|φ(s)|` for the balanced and biased binary laws; `-log|φ_n(s)|` as
`n` grows, for each candidate dependence structure.

**Falsifier.** The four gain rows — bounded, `log n`, `n^β log n`, linear — are
asserted as a *landscape*, and the only theorems about them are that they are
eventually ordered, which is arithmetic about logarithms and powers and says
nothing about any process. The empirical claim is that some real dependence
structure realises each row. Simulate the candidates the docstrings themselves
name — a Pisot-collapsed lattice law, a heavy-tail ghost, an equicorrelated
copula, an independent law — and measure the growth rate. **If any row has no
realising process the landscape has an empty cell; if two named processes land in
the same row the landscape does not separate what it claims to separate.** Either
outcome is a finding. Second falsifier, already half-built in the file:
`copiedBinaryJointExpectation` is `1` and
`copiedBinaryConditionalProductExpectation` is `0`, and the accompanying theorem
refutes a conditional-product identity. That refutation is exact arithmetic on two
constants; a simulator should reproduce it by *sampling* the copied-dependence law,
which is the positive control that the sampler is drawing the law the constants
describe.

**Nearly unsimulatable, and why it isn't.** `gainBounded := fun _ ↦ 1`,
`gainLog := Real.log`, `gainLinear := id`. Three of the four rows have bodies with
no model content whatever. Under the corpus's own F3 rule they stay in anyway,
because the composition with a realising process is testable even though the row
alone is a renamed Mathlib function — and the burden that creates is precisely
that the simulator must **supply** the processes rather than plot the four curves.
A script that plots `1`, `log n`, `n^β log n` and `n` and observes that they are
ordered is the "simulator that can only agree" the brief warns about.

---

### 3.6 `shared_ld_kernel_transport` — 14 members, 1 file. **Rank 6.**

**Generative process.** Genotypes in two populations share one LD kernel `K`. A
score uses the source effect vector as weights; the target phenotype is generated
from the target effect vector. Both the score variance and the target genetic
variance are evaluated under `K`. The headline claim is the exact identity
`R²_target = rg_K² × h²_target`.

**Members.** TransferLearningPGS: `pgsPhenoCov`, `sharedLDGeneticVariance`,
`sharedLDHeritability`, `pgsR2`, `sourceTruthR2SharedLD`,
`transportedTargetR2SharedLD`, `ldEffectGeneticCorrelation`,
`effectGeneticCorrelation`, `standardizedDiagonalLD`, `additiveGeneticVariance`,
`additiveHeritability`, `sourceSelfR2DiagonalLD`, `transportedTargetR2DiagonalLD`,
`targetOracleR2DiagonalLD`.

**Measure.** Target `R²` measured on **independent** target individuals, against
`rg_K² × h²_target` evaluated on the same simulated kernel; and the diagonal-LD
specialization against the shared-LD general form.

**Falsifier.** The identity assumes **one** kernel shared by both populations —
and differing LD between populations is the whole portability problem. Simulate
`K_source ≠ K_target` and the identity must break; measure the break as a function
of `‖K_s − K_t‖_F`. **If it does not break, the shared-kernel hypothesis is doing
no work and the theorem is vacuous for portability**, which is a finding about the
file's flagship result. Second falsifier, and the one that connects to a defect
already on the record: `effectGeneticCorrelation` is a plain cosine similarity of
two effect vectors, with no allele frequencies and no LD anywhere in its body.
Under the free rescaling `g → cg`, `β → β/c` — raw dosages versus standardized
genotypes, under which the phenotype, the score and every measured moment are
unchanged — a genuine genetic correlation is invariant, while a cosine of the two
`β` vectors is **not**, once the two populations have different allele
frequencies and therefore different `c`. That is the identical failure mode
`linear_prediction_transport` already recorded and quantified for
`r2FromSourceWeights`, and the identical `c`-rescaling control settles it here.

---

### 3.7 `dirichlet_staleness_and_damping` — 13 members, 1 file. **Rank 7.**

**Generative process.** An environment relaxes at rate `λ`; a design is chosen
optimally at time `0` and deployed at time `τ`. Simulate a finite reversible chain
or an Ornstein-Uhlenbeck environment, choose the myopic optimum at `0`, evaluate
at `τ`, and measure the premium over an environment-blind design and over a
damped one.

**Members.** DirichletTransfer: `dirichletEfficiency`, `driftHorizon`,
`localizedTransferVariance`, `delocalizedTransferVariance`,
`sampleInverseInflation`, `valueMass`, `autocorrTime`, `stalePremium`,
`stalenessCrossover`, `dampedAdjustment`, `dampedPremium`, `myopiaPrice`,
`shrinkagePremium`.

**Measure.** The premium curve and its zero crossing; the argmax over the
shrinkage `α`; the decay in `k` of the delocalized transfer variance.

**Falsifier.** `stalenessCrossover = log 2 / λ` follows from
`stalePremium = (2e^{−λτ} − 1)V`, which assumes the stale design's value decays
*exactly* as the autocorrelation. Measure the premium curve in a simulated OU
environment: if the zero crossing is not at `log 2 / λ`, the functional form is
wrong. **Sharper, and this is the live disagreement inside the file:** run a
**multi-rate** environment with two modes at `λ₁ ≠ λ₂`. `autocorrTime = Σ wᵢ/λᵢ`
is defined for exactly that case, but `stalenessCrossover` takes a **single** `λ`
and no theorem in the file says which one. Measure the true crossover and compare
against `log 2 / λ` evaluated at (i) the slowest rate, (ii) the spectral gap,
(iii) the weighted harmonic mean `V/T`. **At most one can be right and the corpus
names none of them.** Positive control with an exact reference:
`sampleInverseInflation n m = n/(n−m−1)` is the inverse-Wishart mean inflation, so
drawing Wisharts checks the harness against a closed form nobody in this corpus
wrote.

---

### 3.8 `meta_learning_effect_averaging` — 12 members, 1 file. **Rank 8.**

**Generative process.** `k` source populations each carry an effect vector equal
to a shared center plus a population-specific deviation. The meta-learner averages
them (uniformly, or with affine weights) and is deployed against a target optimum.
Draw the deviations from a specified covariance, average over `k`, measure the
squared gap to the target.

**Members.** TransferLearningPGS: `coefficientGapSq`, `populationDeviationSum`,
`meanPopulationDeviation`, `metaLearnedSourceWeights`,
`centeredPopulationEffectDeviation`, `sourcePopulationMeanWeights`,
`metaLearnedTransferGapSq`, `weightedPopulationDeviation`,
`weightedMetaSourceWeights`, `weightedMetaTransferGapSq`, `uniformMetaWeight`,
`weightedPopulationEffectAverage`.

**Measure.** `gap(k)` against `k` for `k = 1 … 20`, at several deviation
correlations; the achieved gap of uniform weights against the best affine weights.

**Falsifier.** The `gap_shared + σ²/k` law needs the deviations to be **pairwise
orthogonal, of equal squared norm, and each orthogonal to the shared residual**.
Real ancestries are a tree, not a star: their deviations are correlated. Draw
deviations with pairwise correlation `ρ > 0` and the gap becomes
`gap_shared + σ²(1/k + (1−1/k)ρ)`, which **floors at `gap_shared + σ²ρ` and never
decays to the shared gap**. If the measured curve flattens at `ρ > 0` while the
corpus predicts continued `1/k` decay, then
`amortized_per_population_adaptation_cost_falls_with_task_count` — a named
headline theorem — is scoped to a star phylogeny, and that scope is declared
nowhere. Cheapest simulator in the entire bucket: pure linear algebra on random
vectors, no genotypes, no phenotypes, minutes to write.

---

### 3.9 `domain_adaptation_information_bound` — 9 members, 1 file. **Rank 9.**

**Generative process.** A jointly Gaussian source `(Y, φ(X))` with mutual
information `I_Y`, and a binary ancestry label `A` whose mutual information with
`φ(X)` is `I_A`. Draw the joint, measure the true source residual risk and the true
divergence between the two ancestry-conditional laws of `φ(X)`, and compare to the
corpus's certified envelope.

**Members.** TransferLearningPGS: `benDavidUpperBound`, `infoBottleneckObjective`,
`gaussianSourceResidualRisk`, `pinskerAncestryDivergenceCap`,
`infoCertifiedBenDavidUpperBound`, `importanceWeightESS`,
`pcaSignalLossPenalty`, `pcaBiasReduction`, `pcaNetTargetError`.

**Measure.** `exp(−2I)` against the measured `1 − R²`; `√(2I)` against the measured
total variation and `H`-divergence; the Kish ESS `(Σw)²/Σw²` against the measured
variance of a weighted mean.

**Falsifier.** (i) `gaussianSourceResidualRisk = exp(−2I)` holds for `I` in **nats**
with `Var(Y) = 1`; the corpus states neither the base nor the normalisation. Sweep
`I ∈ [0, 3]` — the identity is exact or it is off by `log 2`, and the run says
which. (ii) `pinskerAncestryDivergenceCap = √(2I)`: Pinsker in nats gives
`TV ≤ √(I/2)` and the binary-domain `H`-divergence is `2·TV`, so the constant is
right **only** under both those conventions simultaneously. Construct two
Gaussians at known KL and measure the divergence directly: if it ever exceeds
`√(2I)` the cap is false, and if it never comes within a factor of two the cap is
uninformative — a different result and equally worth reporting. (iii) The file
**deleted two theorems** (`iw_ess_decreases_with_divergence`,
`iw_positive_weight_variance_reduces_ess`) for asserting a monotone
ESS-versus-divergence relation over a formula that exists nowhere in the corpus,
and the claim survives in prose. Simulate importance weights from two Gaussians at
swept KL and measure the ESS: **the file itself says nobody has checked this**,
and the check is twenty lines.

---

### 3.10 `pc_correctability_information_budget` — 8 members, 1 file. **Rank 10.**

**Generative process.** A cohort of `N` individuals contains a subgroup of size
`n`, genotyped at `M_c` effectively independent markers in frequency class `c`
with differentiation `F_c`. Simulate two populations at swept `F_ST`, sample the
subgroup, build the class-by-class ancestry decomposition, and measure whether the
subgroup's ancestry axis is resolved above the sampling noise.

**Members.** PCCorrectability/Frequency: `FrequencyResolvedCohort.witness`,
`classMargin`, `classInformation`, `informationMatchedWeight`,
`totalInformation`, `weightedSignal`, `weightedNoise`, `weightedInformation`.

**Measure.** The realised margin against `classMargin`; the empirically optimal
class weighting against `informationMatchedWeight = M_c F_c`.

**Falsifier.** `weightedInformation = signal²/noise` with
`noise = Σ wᵢ²/Mᵢ` is a Cauchy-Schwarz ceiling attained at `wᵢ ∝ MᵢFᵢ`. That is
exact **only** if the per-class estimates are independent — and frequency classes
of the same genome are not, because they share the same individuals. Simulate with
shared individuals across classes and the achieved information must fall below the
ceiling; measure the shortfall against the class count. If it does not fall, the
independence assumption is doing no work and the ceiling is not a ceiling.

**Ranked low for a reason that is not about the family.**
`PCCorrectability/ImitationCapacity.lean` holds 28 checkable definitions on the
same structure and **is not in my brief and I do not know who owns it**. Anyone
writing this simulator will collide with whoever has that module. Settle
ownership first.

---

### 3.11 `folded_spectrum_identifiability` — 8 members, 1 file. **Rank 11.**

**Generative process.** A panel of `n` loci carries allele frequencies and
weights; each locus induces a law of `|x² − 1|` for the standardized dosage `x`,
and the panel's modulus law is the weighted mixture. Draw panels, compute the
modulus law, and ask whether two different panels give the same one.

**Members.** FoldedSpectrum: `Panel.reflect`, `Panel.fold`, `twoPointModulusLaw`,
`positiveThreshold`, `ScalarSecondMoments.witness`, `gamma`, `requiredCohorts`,
`recoveredVariance`.

**Measure.** The modulus law of a panel and of its reflection `q ↦ 1 − q` (must
agree exactly — the polarization/folded-spectrum positive control); the modulus
law of two panels matched in mean inverse heterozygosity but differing in its
variance; the degenerate law at `q = 1/2`.

**Falsifier.** `dispersion_escapes_low_moments` proves that two panels matched in
the **mean** of inverse heterozygosity differ in its **variance**, and
`portability_gap_not_attributable_to_spectrum` concludes that no estimator reading
through the matched functional can tell them apart. The empirical claim is about
**real** summary-statistic methods, and the file's own docstring says so: "It is
falsifiable by simulation: match the functional, simulate both spectra, and any
residual gap localizes the cause." Build the two panels the theorem constructs
(`![q₁,q₂]` against `![q₃,q₃]`), simulate genotypes for both under linkage
equilibrium, and run an actual LD-score-style heritability estimator on each. **If
the estimates differ beyond Monte-Carlo error, the estimator does not read through
inverse heterozygosity alone and the decomposition does not apply to it.** The
positive control that makes the null interpretable is the reflection: a panel and
its reflection must give bit-identical statistics, and if they do not the harness
is broken rather than the theory.

**Low-confidence memberships, declared.** `requiredCohorts` and
`recoveredVariance` sit in `FoldedSpectrum.lean` but their bodies belong to the
permeability/ensemble process, not to the modulus map. They are listed here only
because no other family in this bucket reaches them. Someone owning
`Permeability.lean` should take them.

---

## 4. Findings: definitions whose name claims more than their body does

The brief asked for these as findings rather than silent filings. Five, ordered by
how much they would mislead a reader.

### 4.1 Four byte-identical Kronecker deltas under four names in three files

`HorizonCurve.stayKernel`, `HorizonCurve.agreement`,
`UnifiedBiology.persistentTransition` and `UnifiedBiology.contextMatchQuality` all
have the body `if i = j then 1 else 0`, on the same two-element index type. Two of
them sit in the *same* file under different names. This is not concealed —
`UnifiedBiology`'s own docstring says "The two-context biological witness runs on
the horizon-curve kernels" — but four names for one function across a "temporal
kernel", a "design efficiency", a "biological transition" and a "readout quality"
makes four independent-looking results out of one. `EnsembleChannel`'s
`binaryFirstAnnotation`/`binarySecondAnnotation` and
`GenerativePortabilityLaw`'s `historyMarginalAmplitude` (which is the projection
`h ↦ h.amplitude`) extend the same pattern. This is the defect class the lead
flagged in `TransferLearningPGS`, occurring at family scale, and it is the main
reason §3.1 ranks first.

### 4.2 `PolygenicArchitecture.predictedPortability` is `portabilityScore`

`noncomputable def predictedPortability (model) : ℝ := model.portabilityScore` —
byte-identical body, different name, adjacent in the same file. The docstring
frames it as the file's *prediction surface*; it is a rename of the quantity two
declarations above it.

### 4.3 `SelectionArchitecture.stabilizingSelectedArchitectureVariance` is `equilibriumEffectVariance`

Same pattern: `:= equilibriumEffectVariance v_mutation s`, byte-identical, in the
same file. The name adds "stabilizing selection" and "architecture" to a body that
is `v_mutation / s`.

### 4.4 `TransferLearningPGS.weightedPopulationEffectAverage` is `weightedPopulationDeviation`

`:= weightedPopulationDeviation wSource weight` — byte-identical. It is called an
**average** but the body is a weighted **sum**; it is an average only when
`Σⱼ wⱼ = 1`, which is a hypothesis of the theorems that use it and is not a
condition on the definition. Feeding it weights that do not sum to one returns a
number the name says is an average of the inputs and that need not lie in their
convex hull.

### 4.5 `TransferLearningPGS.additiveGeneticVariance` is a squared Euclidean norm

`:= ∑ᵢ βᵢ²`. Additive genetic variance is `Σ 2p(1−p)β²`; no allele frequency
appears anywhere in the body. This one is **scoped**, not wrong: the surrounding
section says "standardized diagonal-LD model", under which `2p(1−p) = 1` by
construction. It is recorded because the name is used unqualified in
`additiveHeritability`, `sourceSelfR2DiagonalLD` and
`targetOracleR2DiagonalLD`, and a reader arriving at those from elsewhere gets no
signal that the standardization is load-bearing. The same is true of
`TransferLearningPGS.targetOracleR2DiagonalLD`, whose body is
`sourceSelfR2DiagonalLD β_target var_y` — legitimate (the target's self-`R²` *is*
its oracle ceiling) but a second name for one function.

### 4.6 Two conventions for one quadratic, in two files

Recorded in §3.2 and repeated here because it is the only item on this list that
can change a number rather than a reading:
`TransferLearningPGS.optimalSourceShrinkageWeight` and
`BayesianPGSTheory.optimalShrinkage` are the same closed form with `λ` naming
opposite things, and neither file mentions the other.

---

## 5. What I could not classify, and why

* **`PCCorrectability/ImitationCapacity.lean`, 28 checkable definitions.** Not in
  the brief; ownership unknown; adjacent to a module I was given. Not touched.
* **`GenerativePortabilityLaw.marginalAmplitudeHistoryDegradationBlindness`.** A
  `ProbeBlindness` instance. The census parked 42 of these as UNKNOWN pending a
  human call and said they cannot move the headline by more than 3 per cent. I
  have made no call on it either; it is counted in (c) and flagged.
* **Whether the three modules I added (`GeneticArchitectureDiscovery`,
  `PolygenicSpectroscopy`, `AncestrySpecificArchitecture`) are mine.** Declared in
  §0 rather than assumed. If they belong to a sibling, 37 of the 267 above are
  double work and should be struck.
* **Whether `PolygenicSpectroscopy` is already simulated.** Its docstrings name
  `proofs/validation/empirical/condensation/check_condensation.py` and
  `proofs/validation/empirical/safe_order/`, and `maxSafeEpistaticOrder` already
  carries a FALSIFIED/VALIDATED status. I could not verify what those scripts
  cover without running them, which this workstation may not do. §3.4 is written
  on the assumption that they may already discharge half of it.
