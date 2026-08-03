# Family proposals, bucket 2

Classification only. No simulator was written, no Lean build was run, no number in
this document was measured. Every claim below about a definition is a claim about
the text of a `.lean` file in the working tree on 2026-08-03, cited by **file and
declaration name** — never by line number, because line numbers in this tree
moved measurably within the hour.

Read first, and not reproduced here:
`proofs/validation/empirical/COVERAGE_DENOMINATOR.md` (the census) and
`proofs/validation/empirical/differential/cluster/families.py` (what a family is).

**How `families.py` was used here, and how it was not.** It supplied the *schema*
— what a family is, what a member list is, which families exist, which have a
simulator. **No population-genetics formula was taken from it.** Its cited
literature reference for the isolation-with-migration coalescent has since been
refuted by simulation at 1340 standard errors, so quoting its arithmetic would
propagate a known error. Where this document names a formula, the formula was read
from the Lean source.

---

## 0. Scope

**Exactly the 26 modules assigned, 266 definitions, all under `proofs/Calibrator/`.**

| module | defs | | module | defs |
|---|---:|---|---|---:|
| TransferLearningPGS | 52 | | EffectSizeSurgery | 6 |
| FoldedSpectrum | 26 | | ResonanceSpectrum | 5 |
| PolygenicArchitecture | 24 | | SelectionValidation | 4 |
| ConditionalGain | 22 | | GeneEnvironmentInterplay | 4 |
| EnsembleChannel | 17 | | SerialFounderChain | 4 |
| DirichletTransfer | 13 | | CountingInvariantInstances | 3 |
| BayesianPGSTheory | 13 | | BundleRigidity/Telescope | 3 |
| SelectionArchitecture | 12 | | HumanDemography | 2 |
| ClinicalUtilityFairness | 10 | | BundleRigidity/Realizability | 2 |
| UnifiedBiology | 9 | | PencilEnvironment | 1 |
| PCCorrectability/Frequency | 9 | | EquityAndImplementation | 1 |
| GenerativePortabilityLaw | 9 | | PCCorrectability/Unified | 1 |
| PolygenicAdaptation | 7 | | | |
| HorizonCurve | 7 | | **total** | **266** |

`GeneticArchitectureDiscovery`, `PolygenicSpectroscopy` and
`AncestrySpecificArchitecture` were provisionally classified in the previous
revision and have been **removed**: they are buckets 3, 1 and 4. Nothing below
depends on them. One consequence is recorded honestly in §3.12 — a family
proposed in that revision **no longer exists** once `PolygenicSpectroscopy` is
withdrawn, because half its members went with it.

`PCCorrectability/ImitationCapacity.lean` (28 checkable defs) is still unassigned
as far as I can tell, and is the immediate sibling of two modules I do hold.

**A method check.** The checkable/non-checkable split was computed by hand from
return types using the corpus's own F1 rule. Where the census published a
per-module checkable count it agrees **exactly**: EnsembleChannel 16,
FoldedSpectrum 16, BayesianPGSTheory 13, ConditionalGain within one. That is the
only evidence offered that this split is reproducible, and it is worth more than
the prose around it.

---

## 1. The split across the three outcomes

| outcome | defs |
|---|---:|
| (a) joins an **existing** family | 59 |
| (b) belongs to a **new** family proposed here | 181 |
| (c) makes **no empirically checkable claim** | 26 |
| **total** | **266** |

Membership is many-to-many, as the census says it must be. The 181 is the
*primary* assignment, one per definition, so the three outcomes partition the 266;
the per-family counts in §3 include shared members and therefore do not sum to it.

### Outcome (c), the 26

**Propositions (18).** `TransferLearningPGS.AsymptoticallyZero`,
`TransferLearningPGS.AsymptoticallyConsistent`,
`FoldedSpectrum.InLinkageEquilibrium`, `FoldedSpectrum.HasFrequencyTie`,
`FoldedSpectrum.ReadsThroughFunctionals`, `FoldedSpectrum.HasScalarSummary`,
`FoldedSpectrum.IsLevelSetFunctional`, `FoldedSpectrum.ReversalEven`,
`FoldedSpectrum.ReversalOdd`, `FoldedSpectrum.Reversible`,
`EnsembleChannel.IsOrderFreeStatistic`, `ConditionalGain.FullSupport`,
`ConditionalGain.CoversTuple`, `ConditionalGain.ProductCovers`,
`HorizonCurve.IsStationaryKernel`,
`GenerativePortabilityLaw.MarginalAmplitudeDeterminesHistoryDegradation`,
`EffectSizeSurgery.IsEvenSummary`, `EffectSizeSurgery.IsOddSummary`.
(`ResonanceSpectrum.PhasePanel.IsResonantAt` is also a `Prop` and is discussed
separately below.)

**Index, permutation and type constructions (3).** `FoldedSpectrum.genotypeFlip3`
(the permutation `![2,1,0]` on `Fin 3`), `FoldedSpectrum.idReversal`,
`UnifiedBiology.BinaryBiologicalState` (`abbrev … := Fin 2`).

**Sets and finsets (3).** `PolygenicArchitecture.boundedEffectCarrier`,
`PolygenicArchitecture.effects`,
`PCCorrectability.Frequency.FrequencyResolvedCohort.correctableClasses`.

**Structural witness, unadjudicated (1).**
`GenerativePortabilityLaw.marginalAmplitudeHistoryDegradationBlindness` — a
`ProbeBlindness` instance, the exact category the census parked as its 42 UNKNOWN.
Counted in (c) and flagged as a human call.

**The caution the corpus earned.** `families.py` records that across two tiers and
**thirty-one** attempts nothing in this corpus has survived an un-simulatability
claim; every one lost to F3, the real-valued-consumer test. The 26 above are
therefore offered as *category errors of return type only*. None is claimed to be
beyond reach through composition, and at least five plainly are not:
`InLinkageEquilibrium`, `ReadsThroughFunctionals`, `HasFrequencyTie`,
`IsStationaryKernel` and `IsResonantAt` are all hypotheses or level sets of
real-valued theorems whose conclusions a simulator can evaluate on both sides.
`IsResonantAt` is the sharpest case: §3.4 shows it is the zero set of a
real-valued function defined in a **different file**, which is precisely the F3
composition that killed thirty-one previous parkings.

---

## 2. Outcome (a): 59 definitions join families that already exist

Cheapest coverage in the bucket; spend it first. Nothing here needs a new
generative process, only a membership entry in `families.py` and a re-run so the
credit is earned rather than asserted.

**A structural finding.** `families.py` already lists `effectVarianceRecurrence`
and `equilibriumEffectVariance` as members of `selection_regimes`, and both are
declared **outside the seven-file slice**, in `SelectionArchitecture.lean` — a
module in this bucket. The existing families are therefore already out-of-slice
families, and the published in-slice coverage percentage has been counting the
fraction of them that happens to land in seven filenames. That is the census's
point about the slice being a file list, arrived at from the other direction.

| existing family | joining definitions | n |
|---|---|---:|
| `selection_regimes` | SelectionArchitecture: `equilibriumEffectVariance`, `effectVarianceRecurrence` (already declared members — this records where they *live*), `stabilizingSelectedArchitectureVariance`, `optimumOUVariance`, `fluctuatingSelectedArchitectureVariance`, `effectCorrelationStabilizing`, `fluctuatingEffectCorrelation`, `stabilizingNsFromObservedCorrelation`, `tauFromObservedEffectCorrelation`, `sigmaThetaFromObservedSelectedVariance`; PolygenicAdaptation: `effectCorrelationStabilizingDriftSelection`, `effectCorrelationFluctuating`; SelectionValidation: `SelectionValidationModel.witness`, `selectionSummaryLogLik`, `missedSelectedVariance`, `selectionModelLRT` | 16 |
| `liability_threshold_metrics` | ClinicalUtilityFairness: `LiabilityThresholdModel.witness`, `liabilitySensitivity`, `liabilitySpecificity`, `sensFromR2`, `specFromR2`, `ppv`, `proportionCorrectlyClassified`, `numberNeededToScreen`, `populationAttributableFraction`, `netReclassificationImprovement` | 10 |
| `pgs_transport_drift` | PolygenicAdaptation: `pgsDriftVariance_one_pop`, `pgsDriftVarianceFromLoci`, `pgsDiffVariance_two_pop`, `expectedPGSDiffVariance`, `qst`; SelectionArchitecture: `polygenicAdaptationShift`; HumanDemography: `neutralDriftR2Ratio`, `taggedDriftR2RatioCorrected` | 8 |
| `gxe_and_interaction` | GeneEnvironmentInterplay: `effectiveGeneticEffect`, `linearNormOfReaction`, `cohortShift`, `GxEDeployment.shift` | 4 |
| `split_fst` | SerialFounderChain: `serialFounderJoinTime`, `serialFounderWithinTime`, `serialFounderCeilingFst`, `SerialFounderChain.joinTime` | 4 |
| `hwe_genotype_score` | FoldedSpectrum: `diploidStdev`, `diploidAtomValue`, `diploidAtomMass`, `diploidFamily` | 4 |
| `portability_permeability_and_completion` | FoldedSpectrum: `invHeterozygosity`, `diploidCovarianceMomentPermeability`, `diploidPanelCovarianceMomentPermeability`, `totalDiploidCovarianceMomentInformation` | 4 |
| `linear_prediction_transport` | TransferLearningPGS: `targetLinearExcessRisk`, `exactAdaptationGain`, `coefficientGapSq` | 3 |
| `ascertainment` | SelectionArchitecture: `gwasNCP`; BayesianPGSTheory: `multiAncestryEffectiveN` | 2 |
| `ensemble_portability_channel` | EnsembleChannel: `weightedBandEnsembleLoss`, `weightedBandPredictorLoss` | 2 |
| `neutral_af_benchmark_transport` | PolygenicArchitecture: `rgFstWeightedUpperBound` | 1 |
| `estimator_moments` | ConditionalGain: `secondMoment` | 1 |
| `island_migration_fst` | TransferLearningPGS: `privateArchitectureTransferCeiling` (built on `sharedLDFromMigration`) | 1 |
| **total** | | **59** |

**Short-name collision hazard, O5b.** `total`, `imbalance`, `cosPart`, `sinPart`
and `witness` each resolve to more than one declaration in this corpus, and
`cosPart`/`sinPart` resolve to two declarations that are **byte-identical**
(§4.2). Every membership entry must key on the **fully qualified** name. A
collision adds spurious matches to the numerator and leaves the denominator
untouched, so it always flatters — which is how the headline moved from 295 to
316.

### 2a. Three rows that come with history, stated rather than glossed

**`HumanDemography` — a family member that already has a simulator
`families.py` does not know about.** `taggedDriftR2RatioCorrected` carries
`Empirical status: VALIDATED (proofs/validation/empirical/drift_diff/)`, and that
directory exists in this tree with `drift_sim.py` and four result files. Its
predecessor `taggedDriftR2Ratio` was **deleted today** after Wright-Fisher
simulation found it 15 % to 112 % high, always overstating portability. I verified
by grep that the dead identifier survives **only inside the deletion note's
prose**, never as a declaration, and it is **not** proposed as a member of
anything here. `neutralDriftR2Ratio` and `taggedDriftR2RatioCorrected` are both
built on `presentDayR2`, already a `pgs_transport_drift` member — so this is a
membership entry plus a re-run, and the re-run has already happened. Cheapest
genuine coverage in the bucket.

**`SerialFounderChain` — covered by an unreproducible file, which is not
covered.** All four members route to `split_fst` because
`serialFounderCeilingFst` is `τ / (T_within + τ)`, the same waiting-time ratio as
Hudson's `t/(t + 2Nₑ)`. But the file names
`proofs/validation/empirical/differential/cluster/fam_serial_founder.py` as its
instrument, and that is the family whose stored result **cannot be regenerated end
to end**, because its part B reads a study dataset no clone contains. The status
of these four is therefore **covered-by-an-unreproducible-file**, which is weaker
than covered and must not be entered in a coverage count as the latter. The
definition's own docstring is already careful in the same direction —
`serialFounderCeilingFst` records `MEASURED at one design point … Power is not
established: a single configuration cannot reject a wrong functional form, so this
is not recorded as VALIDATED`. That is the right strength; the coverage
bookkeeping should match it rather than round it up.

**`GeneEnvironmentInterplay` — a mechanism for the suspected mis-grouping of
`gxe_and_interaction`.** A sibling found `optimalSlopeFromVariance` is at least 1
while `optimalSlopeLinearNoise` is at most 1 — slopes in opposite directions,
possibly mis-grouped. My four definitions supply the mechanism.
`effectiveGeneticEffect = β_G + β_GxE·E_mean` and `linearNormOfReaction = a + b·E`
are **DGP-side**: the true genetic effect as a function of environment, before any
estimator exists. The two slopes the sibling compared are **estimator-side**:
recalibration slopes a fitted linear score is left with. `gxe_and_interaction`
holds both kinds in one member list, and **that alone is sufficient to produce two
"slopes" bounded on opposite sides of 1 without either being wrong** — a true
effect gradient is unbounded in either direction, while the attenuation factor of
a least-squares fit is bounded above by 1. The recommendation is therefore not to
delete the family but to **split it**: a `gxe_generative` arm (my four, plus the
corpus's `trueExpectation` structures) and a `gxe_recalibration_slope` arm (the
two slopes and their relatives), with the **composition** — feed the generative
arm's output into the estimator arm and check the slope lands where the estimator
arm says — as the test neither arm can perform alone. *Falsifier for the split:*
simulate the interactive DGP at `β_GxE ≠ 0`, fit the linear score, measure the OLS
slope. If it lands above 1 the estimator-side bound is wrong; if the DGP-side
gradient is bounded by 1 the generative-side reading is wrong; if both hold, the
two arms measure different things and the family was mis-grouped — the sibling's
suspicion confirmed by construction rather than by inspection.

Also in that file: `effectiveGeneticEffect` and `linearNormOfReaction` have
**byte-identical bodies**, `x + y·z` under two names, three sections apart (§4.6).

---

## 3. Outcome (b): eleven new families, ranked

Ranked by members covered × cheapness of the simulator × whether a live
disagreement or a suspicious definition sits inside. Every family states what a
simulator would MEASURE and WHAT WOULD FALSIFY IT. §3.4 explains the one place
that came close to unsimulatable-as-stated and why it is not.

---

### 3.1 `temporal_arrow_and_order_erasure` — 31 members, 4 files. **Rank 1.**

**Generative process.** A stationary finite-state Markov chain (two or three
states) is observed twice: once as an *ordered* sequence, once as an unordered
bag. A payoff is evaluated at the pair (source state, target state) rather than at
the target state alone, and an orientation imbalance `θ` biases the forward
against the reverse traversal.

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

**Measure.** `E[arrow]` against `θ`; the naive one-endpoint average against the
two-endpoint regret under the stay and swap kernels; the degradation of the
independent history against the persistent one at matched marginal amplitude; the
sample size at which each is resolved.

**Falsifier.** Every headline is a *blindness* claim — "no order-free statistic
can see `θ`", "marginal amplitude does not determine degradation", "the naive
horizon curve is flat". A simulator that only confirms these is worthless, so it
must run in both directions. (i) Simulate the two processes at identical one-point
marginals and run a battery of order-free statistics — panel mean, panel variance,
the empirical state histogram, a heterozygosity summary — at increasing `n`. If
**any** separates them the wall is false. (ii) The arrow statistic must separate
them at an `n` well below where the order-free battery does, or the practical
claim that order carries otherwise-unavailable information has no operating
regime. Both directions must fire; a run producing only (i)'s null is not
evidence.

**Why rank 1.** Largest member count; the simulator is finite-state arithmetic
with no genotypes, no LD and no coalescent, so it is the cheapest script anyone
will write; and it contains the bucket's most striking defect — **four
byte-identical Kronecker deltas under four names across three files** (§4.1).

---

### 3.2 `shrinkage_transfer_mse` — 26 members, 4 files. **Rank 2.**

**Generative process.** A target effect is estimated two ways: from a source at
squared distance `gapSq` from the target optimum, and from `n` target samples with
per-sample noise. The deployed estimator is the convex combination. Draw the
truth, the source estimate and the target sample, form the combination, measure
MSE across replicates and across the mixing weight.

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
PolygenicArchitecture: `spikeAndSlabVariance`. EquityAndImplementation:
`expectedR2FromN`.

**Measure.** `MSE(λ)` over a `λ` grid and its empirical argmin; the sample size at
which the target-only estimator overtakes the transferred one; the excess risk of
a Gaussian-prior posterior mean applied to a spike-and-slab truth.

**Falsifier.** **The corpus carries two mirror conventions for one quadratic and
does not say they are mirrors.** `TransferLearningPGS.sourceShrinkageMSE` is
`gapSq·λ² + (noiseVar/n)(1−λ)²`, whose optimum
`optimalSourceShrinkageWeight = (noiseVar/n)/(gapSq + noiseVar/n)` weights the
**source** by the **noise**. `BayesianPGSTheory.jamesSteinMSE` is
`λ²σ² + (1−λ)²β²`, whose optimum `optimalShrinkage = β²/(σ² + β²)` weights the
**data** by the **signal**. Same algebra, `λ` naming opposite things, neither file
citing the other. Simulate one process with a genuinely biased source and locate
the empirical argmin: at matched parameters at most one file's downstream theorems
read their own `λ` correctly, and the run says which. Second falsifier:
`misspecExcessRisk = π(1−π)σ²_β` is derived in its own docstring by summing
per-SNP over- and under-shrinkage **without re-optimising**; simulate a π-sparse
architecture and measure the actual excess of the Gaussian-prior posterior mean
over the spike-and-slab one. Third: `posteriorPredictiveVariance =
residual + estimation` assumes zero covariance between its two terms, and a design
where the score and residual are correlated must break it.

**New this revision.** `EquityAndImplementation.expectedR2FromN =
h²·(n h²/(n h² + M))` is the classical expected-`R²`-versus-`N` law, and its inner
factor is **the same body as `optimalShrinkage`** under `β² ↦ n h²`, `σ² ↦ M`. One
simulator settles both. A third file joining this family is what raises its rank.

---

### 3.3 `architecture_effect_mass_portability` — 21 members, 1 file. **Rank 3.**

**Generative process.** An architecture of `q` causal SNPs carries source squared
effects from a chosen distribution (infinitesimal, spike-and-slab, or
selection-shaped) and a per-SNP retention fraction into the target. Portability is
the retained fraction of squared-effect mass.

**Members.** PolygenicArchitecture: `expectedSquaredEffect`,
`effectivePolygenicity`, `effectivePolygenicityOfEffects`,
`SNPArchitecturePortabilityModel.witness`, `sourceEffectMass`,
`targetRetainedEffectMass`, `lostEffectMass`, `relativePortabilityLoss`,
`portabilityScore`, `predictedPortability`,
`uniformCatastrophicPortabilityScore`, `meanAbsoluteEffect`,
`weightedRetentionUpperBound`, `heritabilityEnrichment`, `logCoveringAtExponent`,
`architectureRadius`, `architectureMoment`, `certificationGap`,
`mixtureExperiment`, `finiteProblem`, `calculus`.

**Measure.** `M_eff = (Σβ²)²/Σβ⁴` under each effect distribution, against `q`;
retained mass fraction after drift; the enrichment ratio for a functional
category.

**Falsifier.** `effectivePolygenicity` is documented as "the effective number of
causal variants", and its own docstring already concedes the two-free-reals form
cannot express `M_eff ≤ q`. Draw `q` effects and compute `M_eff/q`. Under an
exponential effect distribution the ratio is a **constant independent of `q`**;
under spike-and-slab it tracks the causal fraction. If `M_eff/q` is a fixed
function of the effect **distribution** and not of the architecture **size**, then
"effective number of causal variants" names a shape statistic and not a count, and
every downstream statement reading it as a count is scope-broken. Cheap — one
array of draws, no genotypes — and it settles a naming claim rather than an
arithmetic one. Second falsifier: `uniformCatastrophicPortabilityScore` is
`1 − |mismatched|/M` under *equal* effects; draw unequal effects and the surviving
mass fraction diverges from the surviving SNP fraction by an amount growing with
effect-size dispersion, so the "more polygenic architectures are more robust"
theorem is stated on the equal-effect surface only.

---

### 3.4 `conditional_gain_and_resonance` — 22 members, 2 files. **Rank 4.**

**Generative process.** A finite multilocus law assigns a phase to each site; the
score is the sum of phases; the characteristic function `Ψ(s) = E e^{isS}` is
formed at swept `s`. The conditional gain is `−log|Ψ(s)|` and the resonance set is
`{s : |Ψ(s)|² = 1}`. Draw from the law, form the empirical characteristic
function, measure both.

**Members.** ConditionalGain: `scorePhase`, `cosPart`, `sinPart`,
`characteristicAmplitude`, `conditionalGainFunctional`,
`balancedBinaryOppositePhaseLaw`, `biasedBinaryOppositePhaseLaw`,
`copiedBinaryJointExpectation`, `copiedBinaryConditionalProductExpectation`,
`FiniteBoundedDeviation.witness`, `copyWitnessFamily`, `modulusCopyCoupling`,
`copyWitnessValue`, `gainBounded`, `gainLog`, `gainPolynomialRow`, `gainLinear`,
`toFiberCoupling`. ResonanceSpectrum: `PhasePanel.witness`, `PhasePanel.cosPart`,
`PhasePanel.sinPart`, `PhasePanel.intensity`.

**The merge is the finding, and it supplies a missing half.**
`ResonanceSpectrum.PhasePanel.cosPart` and `ConditionalGain.cosPart` are
byte-identical weighted cosine sums; `intensity` is `cosPart² + sinPart²` and
`characteristicAmplitude` is its square root. Therefore
`IsResonantAt s ⟺ intensity s = 1 ⟺ conditionalGainFunctional s = 0`: **the
resonance spectrum and the zero-conditional-gain set are one set under two names
in two files**, and neither file mentions the other.

**Measure.** `|Ψ(s)|` for the balanced and biased binary laws; the resonance set
for lattice versus generic phases; `−log|Ψ_n(s)|` as `n` grows, for each candidate
dependence structure.

**Falsifier.** The four gain rows — bounded, `log n`, `n^β log n`, linear — are
asserted as a *landscape*, and the only theorems about them are that they are
eventually ordered, which is arithmetic about logarithms and powers and says
nothing about any process. The empirical claim is that some dependence structure
realises each row. **The merge supplies the missing experiment:** the resonance
side names exactly the realising process the gain side needs. Phases on a lattice
(a Pisot set) give an infinite resonance set and therefore a bounded gain — the
`gainBounded` row; generic phases give resonance only at `s = 0` and a growing
gain. Simulate both, plus the heavy-tail and equicorrelated-copula laws the
docstrings name, and measure the growth rate. **If any row has no realising
process the landscape has an empty cell; if two named processes land in the same
row the landscape does not separate what it claims to separate.** Either is a
finding. Positive control, already half-built: `copiedBinaryJointExpectation` is
`1` and `copiedBinaryConditionalProductExpectation` is `0`, and an accompanying
theorem refutes a conditional-product identity on those two constants; the
simulator must reproduce that refutation by **sampling** the copied-dependence
law, which proves the sampler is drawing the law the constants describe.

**Nearly unsimulatable, and why it is not.** `gainBounded := fun _ ↦ 1`,
`gainLog := Real.log`, `gainLinear := id`. Three of the four rows have bodies with
no model content whatever. Under the corpus's own F3 rule they stay in, because
the composition with a realising process is testable even though the row alone is
a renamed Mathlib function — and the burden that creates is exactly that the
simulator must **supply** the processes. A script that plots `1`, `log n`,
`n^β log n` and `n` and observes they are ordered is the simulator-that-can-only-
agree the brief warns about.

---

### 3.5 `spectrum_and_effect_fiber_identifiability` — 14 members, 3 files. **Rank 5.**

**Generative process.** Two fiber decompositions read by the same machinery. On
the frequency side, a panel of `n` loci induces a law of `|x² − 1|` for the
standardized dosage, and reflection `q ↦ 1 − q` is a gauge. On the effect side, an
effect distribution factors into magnitude fibers each carrying mass at `+level`
and `−level`, and the surgery moves mass `δ` across the sign at fixed magnitude.

**Members.** FoldedSpectrum: `Panel.reflect`, `Panel.fold`, `twoPointModulusLaw`,
`positiveThreshold`, `ScalarSecondMoments.witness`, `gamma`, `requiredCohorts`,
`recoveredVariance`. EffectSizeSurgery: `Fiber.total`, `Fiber.imbalance`,
`Fiber.contribution`, `Fiber.transfer`. BundleRigidity/Realizability:
`outerAtom`, `innerAtom`.

**Why one family and not three.** `FoldedSpectrum` imports `EffectSizeSurgery`,
and its §7 "pair theorem" states both verdicts as **one statement**: the frequency
spectrum is recoverable from summary statistics and the effect-size architecture
is not. `outerAtom = √(1+w)` and `innerAtom = √(1−w)` are the `±√(1±v)` atoms of
the four-atom family whose classification `FoldedSpectrum` §1b corrects. Splitting
these apart would hide that they are one argument.

**Measure.** The modulus law of a panel and of its reflection (must agree exactly
— the folded-spectrum positive control); the modulus law of two panels matched in
mean inverse heterozygosity but differing in its variance; every even summary
(`E[β²]`, `E[β⁴]`, LD-score regression on squared `z`, method-of-moments
polygenicity) before and after the transfer; every odd summary before and after.

**Falsifier, and there are two because there are two fibers.** (i) *Frequency
side.* `dispersion_escapes_low_moments` proves two panels matched in the **mean**
of inverse heterozygosity differ in its **variance**, and the file concludes no
estimator reading through the matched functional can tell them apart. The
docstring invites the test outright: "It is falsifiable by simulation: match the
functional, simulate both spectra, and any residual gap localizes the cause."
Build the two panels the theorem constructs, simulate genotypes under linkage
equilibrium, and run an **actual** LD-score-style heritability estimator. If the
estimates differ beyond Monte-Carlo error, the estimator does not read through
inverse heterozygosity alone. (ii) *Effect side.* Apply `transfer` at fixed
magnitude and re-run the same estimators. An even-by-construction estimator is
even only in exact arithmetic — once a MAF filter or an ascertainment threshold is
applied it consults the sign — and if any of them moves beyond Monte-Carlo error
the fiber decomposition does not describe what real estimators see. Symmetrically,
an odd summary must move by **exactly** `2δ·level` per fiber
(`transfer_imbalance`); if it moves by less, the estimator is partially even and
the file's recommendation — do not answer a question about sign symmetry with a
statistic that is constant on the fibers the question is about — is weaker than
stated. The reflection gauge is the positive control that makes both nulls
interpretable: a panel and its reflection must give bit-identical statistics, and
if they do not the harness is broken rather than the theory.

**Low-confidence memberships, declared.** `requiredCohorts` and
`recoveredVariance` sit in `FoldedSpectrum.lean` but their bodies belong to the
permeability/ensemble process, not the modulus map. They are here only because no
other family in this bucket reaches them; whoever owns `Permeability.lean` should
take them.

---

### 3.6 `shared_ld_kernel_transport` — 14 members, 1 file. **Rank 6.**

**Generative process.** Genotypes in two populations share one LD kernel `K`. A
score uses the source effect vector as weights; the target phenotype comes from
the target effect vector; both the score variance and the target genetic variance
are evaluated under `K`. Headline claim: `R²_target = rg_K² × h²_target`.

**Members.** TransferLearningPGS: `pgsPhenoCov`, `sharedLDGeneticVariance`,
`sharedLDHeritability`, `pgsR2`, `sourceTruthR2SharedLD`,
`transportedTargetR2SharedLD`, `ldEffectGeneticCorrelation`,
`effectGeneticCorrelation`, `standardizedDiagonalLD`, `additiveGeneticVariance`,
`additiveHeritability`, `sourceSelfR2DiagonalLD`, `transportedTargetR2DiagonalLD`,
`targetOracleR2DiagonalLD`.

**Measure.** Target `R²` on **independent** target individuals against
`rg_K² × h²_target` evaluated on the same simulated kernel; the diagonal-LD
specialization against the shared-LD general form.

**Falsifier.** The identity assumes **one** kernel shared by both populations —
and differing LD between populations *is* the portability problem. Simulate
`K_source ≠ K_target`; the identity must break, and the break must scale with
`‖K_s − K_t‖_F`. **If it does not break, the shared-kernel hypothesis is doing no
work and the theorem is vacuous for portability**, which is a finding about the
file's flagship result. Second falsifier, connecting to a defect already on the
record: `effectGeneticCorrelation` is a plain cosine similarity of two effect
vectors, with no allele frequency and no LD anywhere in its body. Under the free
rescaling `g → cg`, `β → β/c` — raw dosages versus standardized genotypes, under
which the phenotype, the score and every measured moment are unchanged — a genuine
genetic correlation is invariant while a cosine of the two `β` vectors is **not**,
once the two populations have different frequencies and therefore different `c`.
That is the identical failure mode `linear_prediction_transport` already recorded
and quantified for `r2FromSourceWeights`, and the identical `c`-rescaling control
settles it here.

---

### 3.7 `dirichlet_staleness_and_damping` — 13 members, 1 file. **Rank 7.**

**Generative process.** An environment relaxes at rate `λ`; a design is chosen
optimally at time `0` and deployed at time `τ`. Simulate a finite reversible chain
or an Ornstein-Uhlenbeck environment, choose the myopic optimum at `0`, evaluate
at `τ`, and measure the premium over an environment-blind design and over a damped
one.

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
environment: if the zero crossing is not at `log 2 / λ` the functional form is
wrong. **Sharper, and this is the live disagreement inside the file:** run a
**multi-rate** environment with two modes at `λ₁ ≠ λ₂`. `autocorrTime = Σ wᵢ/λᵢ`
is defined for exactly that case, but `stalenessCrossover` takes a **single** `λ`
and no theorem says which. Measure the true crossover and compare against
`log 2 / λ` at (i) the slowest rate, (ii) the spectral gap, (iii) the weighted
harmonic mean `V/T`. **At most one can be right and the corpus names none.**
Positive control with an exact foreign reference:
`sampleInverseInflation n m = n/(n−m−1)` is the inverse-Wishart mean inflation, so
drawing Wisharts checks the harness against a closed form nobody in this corpus
wrote.

---

### 3.8 `meta_learning_effect_averaging` — 12 members, 1 file. **Rank 8.**

**Generative process.** `k` source populations each carry an effect vector equal
to a shared center plus a population-specific deviation. The meta-learner averages
them (uniformly or with affine weights) and is deployed against a target optimum.
Draw the deviations from a specified covariance, average over `k`, measure the
squared gap to the target.

**Members.** TransferLearningPGS: `coefficientGapSq`, `populationDeviationSum`,
`meanPopulationDeviation`, `metaLearnedSourceWeights`,
`centeredPopulationEffectDeviation`, `sourcePopulationMeanWeights`,
`metaLearnedTransferGapSq`, `weightedPopulationDeviation`,
`weightedMetaSourceWeights`, `weightedMetaTransferGapSq`, `uniformMetaWeight`,
`weightedPopulationEffectAverage`.

**Measure.** `gap(k)` against `k` for `k = 1 … 20` at several deviation
correlations; the achieved gap of uniform weights against the best affine weights.

**Falsifier.** The `gap_shared + σ²/k` law needs the deviations **pairwise
orthogonal, of equal squared norm, and each orthogonal to the shared residual**.
Real ancestries are a tree, not a star: their deviations are correlated. Draw
deviations with pairwise correlation `ρ > 0` and the gap becomes
`gap_shared + σ²(1/k + (1−1/k)ρ)`, which **floors at `gap_shared + σ²ρ` and never
decays to the shared gap**. If the measured curve flattens at `ρ > 0` while the
corpus predicts continued `1/k` decay, then
`amortized_per_population_adaptation_cost_falls_with_task_count` — a named
headline theorem — is scoped to a star phylogeny, and that scope is declared
nowhere. Cheapest simulator in the bucket: pure linear algebra on random vectors,
no genotypes, no phenotypes.

---

### 3.9 `domain_adaptation_information_bound` — 9 members, 1 file. **Rank 9.**

**Generative process.** A jointly Gaussian source `(Y, φ(X))` with mutual
information `I_Y`, and a binary ancestry label `A` whose mutual information with
`φ(X)` is `I_A`. Draw the joint, measure the true source residual risk and the true
divergence between the two ancestry-conditional laws of `φ(X)`, and compare to the
corpus's certified envelope.

**Members.** TransferLearningPGS: `benDavidUpperBound`, `infoBottleneckObjective`,
`gaussianSourceResidualRisk`, `pinskerAncestryDivergenceCap`,
`infoCertifiedBenDavidUpperBound`, `importanceWeightESS`, `pcaSignalLossPenalty`,
`pcaBiasReduction`, `pcaNetTargetError`.

**Measure.** `exp(−2I)` against the measured `1 − R²`; `√(2I)` against the measured
total variation and `H`-divergence; the Kish ESS `(Σw)²/Σw²` against the measured
variance of a weighted mean.

**Falsifier.** (i) `gaussianSourceResidualRisk = exp(−2I)` holds for `I` in
**nats** with `Var(Y) = 1`; the corpus states neither the base nor the
normalisation. Sweep `I ∈ [0, 3]` — the identity is exact or off by `log 2`, and
the run says which. (ii) `pinskerAncestryDivergenceCap = √(2I)`: Pinsker in nats
gives `TV ≤ √(I/2)` and the binary-domain `H`-divergence is `2·TV`, so the
constant is right **only** under both conventions simultaneously. Construct two
Gaussians at known KL and measure the divergence directly: if it ever exceeds
`√(2I)` the cap is false; if it never comes within a factor of two the cap is
uninformative — a different result and equally worth reporting. (iii) The file
**deleted two theorems** (`iw_ess_decreases_with_divergence`,
`iw_positive_weight_variance_reduces_ess`) for asserting a monotone
ESS-versus-divergence relation over a formula existing nowhere in the corpus, and
the claim survives in prose. Simulate importance weights from two Gaussians at
swept KL and measure the ESS: **the file itself says nobody has checked this**,
and the check is twenty lines.

---

### 3.10 `pc_correctability_information_budget` — 9 members, 2 files. **Rank 10.**

**Generative process.** A cohort of `N` individuals contains a subgroup of size
`n`, genotyped at `M_c` effectively independent markers in frequency class `c`
with differentiation `F_c`. Simulate two populations at swept `F_ST`, sample the
subgroup, build the class-by-class ancestry decomposition, and measure whether the
subgroup's ancestry axis is resolved above the sampling noise.

**Members.** PCCorrectability/Frequency: `FrequencyResolvedCohort.witness`,
`classMargin`, `classInformation`, `informationMatchedWeight`, `totalInformation`,
`weightedSignal`, `weightedNoise`, `weightedInformation`.
PCCorrectability/Unified: `modeledPCResidualSusceptibility`.

**Measure.** The realised margin against `classMargin`; the empirically optimal
class weighting against `informationMatchedWeight = M_c F_c`; residual
susceptibility above and below the spectral edge.

**Falsifier.** `weightedInformation = signal²/noise` with `noise = Σ wᵢ²/Mᵢ` is a
Cauchy-Schwarz ceiling attained at `wᵢ ∝ MᵢFᵢ`. That is exact **only** if the
per-class estimates are independent — and frequency classes of the same genome are
not, because they share the same individuals. Simulate with shared individuals
across classes: the achieved information must fall below the ceiling, and the
shortfall must grow with the class count. If it does not fall, the independence
assumption is doing no work and the ceiling is not a ceiling. Second falsifier,
supplied by the `Unified` member: `modeledPCResidualSusceptibility` is proved
equal to the **uncorrected** susceptibility below the spectral edge — a sharp,
cheap, two-sided prediction. Sweep the spike through the threshold: the measured
residual must sit exactly on the uncorrected value below it and depart above it. A
simulator whose spike grid stays on one side of the edge validates the definition
on a range where it is constant by construction, which is the can-fail failure
mode.

**Ranked low for a reason that is not about the family.**
`PCCorrectability/ImitationCapacity.lean` holds 28 checkable definitions on the
same structure and is, as far as I can tell, unassigned. Anyone writing this
simulator will collide with whoever eventually gets it. Settle ownership first.

---

### 3.11 `moment_blindness_and_word_telescoping` — 7 members, 3 files. **Rank 11.**

**Generative process.** Two spectra on the same number of markers whose low-order
moments agree to within `1/(n+1)` while an inverse-trace certificate differs by
exactly `n/(n+1)`; and the word-telescoping algebra — products of weights and
operators along a word, and the alternating sum satisfying the peeling recursion —
that makes the identifiability argument run.

**Members.** CountingInvariantInstances: `momentDist`, `momentInvariant`,
`meffApproxWitness`. BundleRigidity/Telescope: `prodWeight`, `prodOp`, `altSum`.
PencilEnvironment: `ababFinite`.

**Measure.** `momentDist` between the two spectra at each order `o`; the
certificate gap; the finite-`m` path expression `ababFinite` against a simulated
ensemble; the telescoping recursion against direct evaluation of the alternating
sum at word length 6–10.

**Partly already simulated — attribute before writing.** `ababFinite` carries its
own measured status in its docstring — forty-two ensembles matching at
`max|z| = 2.07`, the deterministic case reproducing `(2(m−1)+4(m−2))/m` exactly —
and `CountingInvariantInstances` names a script that "re-derives
`certificate gap = n/(n+1)` exactly and every order-2 moment gap within
`1/(n+1)`". Part of this family therefore needs a membership entry and a re-run,
not new code. Check that first.

**Falsifier.** The open half is the approximate-blindness witness.
`meffApproxWitness` claims the two spectra's moments agree to `1/(n+1)` while the
certificate differs by `n/(n+1)`. At `n = 3` those are `0.25` and `0.75` — not far
apart — and the existing script only re-derives the two algebraic bounds, which is
an instrument checking its own arithmetic rather than the world. The **empirical**
claim is that a real `m_eff` estimator consulting order-`o` moments cannot
separate the two spectra. Build both spectra, simulate genotypes at each, run an
actual effective-marker estimator, and measure the separation against `1/(n+1)`.
**If it separates them, order-`o` moment agreement is not what a real estimator
consults**, and the blindness witness witnesses something narrower than its name.
`prodWeight`, `prodOp` and `altSum` are the composition through which this is
testable: the telescoping identity is what licenses reading a finite-word peeling
result as a statement about a whole panel, and evaluating `altSum` numerically
against direct summation is the positive control that the recursion is the object
the theorems think it is.

---

### 3.12 A family withdrawn, and why

The previous revision proposed `hwe_dosage_kurtosis_information` — 19 members
across `FoldedSpectrum` and `PolygenicSpectroscopy`, ranked 4th. **It no longer
exists.** `PolygenicSpectroscopy` is bucket 1 and carried ten of the nineteen
members and the whole Mellin-drift half of the process. What remains —
`invHeterozygosity` and the three `diploid…Permeability` definitions — is not a
distinct generative process; it is the fourth moment of a Hardy-Weinberg dosage,
which `hwe_genotype_score` and `portability_permeability_and_completion` already
own. Those four are filed in §2 as existing-family members and no new family is
proposed for them.

Recorded rather than quietly dropped because it is the one place where the
corrected scope changed a **conclusion** and not just a count. It also leaves a
live cross-bucket note for bucket 1: `FoldedSpectrum.invHeterozygosity` and
`PolygenicSpectroscopy.HardyWeinbergModel.standardizedFourthMoment` are the same
quantity, `1/(2q(1−q))`, proved separately in two files as `diploid_fourth_moment`
and `standardizedFourthMoment_eq`. Whoever simulates either should know the other
exists.

---

## 4. Findings: definitions whose name claims more than their body does

Eight, ordered by how much they would mislead a reader.

### 4.1 Four byte-identical Kronecker deltas under four names in three files

`HorizonCurve.stayKernel`, `HorizonCurve.agreement`,
`UnifiedBiology.persistentTransition` and `UnifiedBiology.contextMatchQuality` all
have the body `if i = j then 1 else 0` on the same two-element index type — two of
them in the same file. This is not concealed; `UnifiedBiology`'s docstring says
"The two-context biological witness runs on the horizon-curve kernels". But four
names for one function, presented as a "temporal kernel", a "design efficiency", a
"biological transition" and a "readout quality", makes four independent-looking
results out of one. `GenerativePortabilityLaw.historyMarginalAmplitude` (the
projection `h ↦ h.amplitude`) extends the pattern.

### 4.2 `ResonanceSpectrum` and `ConditionalGain` define the same object twice

`PhasePanel.cosPart`/`PhasePanel.sinPart` and `ConditionalGain.cosPart`/`sinPart`
are byte-identical weighted trigonometric sums; `intensity` is the square of
`characteristicAmplitude`. It follows that `IsResonantAt` is the zero set of
`conditionalGainFunctional`. Neither file cites the other. Not merely cosmetic —
§3.4 turns it into the missing experiment for the gain landscape. It is also a
live O5b hazard, since `cosPart` and `sinPart` now resolve to two declarations
each.

### 4.3 Two conventions for one shrinkage quadratic, in two files

`TransferLearningPGS.optimalSourceShrinkageWeight` and
`BayesianPGSTheory.optimalShrinkage` are the same closed form with `λ` naming
opposite things, and neither mentions the other. The only item on this list that
can change a number rather than a reading. Detailed in §3.2.

### 4.4 `PolygenicArchitecture.predictedPortability` is `portabilityScore`

`:= model.portabilityScore` — byte-identical body, different name, adjacent in the
same file. The docstring frames it as the file's *prediction surface*; it is a
rename of the quantity two declarations above it.

### 4.5 `SelectionArchitecture.stabilizingSelectedArchitectureVariance` is `equilibriumEffectVariance`

`:= equilibriumEffectVariance v_mutation s`, byte-identical, same file. The name
adds "stabilizing selection" and "architecture" to a body that is
`v_mutation / s`.

### 4.6 `GeneEnvironmentInterplay.effectiveGeneticEffect` is `linearNormOfReaction`

Both are `x + y·z`, three sections apart in one file, one called an effective
genetic effect and the other a norm of reaction. Their **grouping** matters more
than the duplication — see §2a.

### 4.7 `TransferLearningPGS.weightedPopulationEffectAverage` is `weightedPopulationDeviation`

`:= weightedPopulationDeviation wSource weight` — byte-identical. Called an
**average**, but the body is a weighted **sum**; it is an average only when
`Σⱼ wⱼ = 1`, which is a hypothesis of the theorems that use it and not a condition
on the definition. Off that surface it returns a number the name says is an
average of its inputs and which need not lie in their convex hull.

### 4.8 `TransferLearningPGS.additiveGeneticVariance` is a squared Euclidean norm

`:= ∑ᵢ βᵢ²`. Additive genetic variance is `Σ 2p(1−p)β²`; no allele frequency
appears in the body. **Scoped, not wrong** — the surrounding section says
"standardized diagonal-LD model", under which `2p(1−p) = 1` by construction. It is
recorded because the name is used unqualified by `additiveHeritability`,
`sourceSelfR2DiagonalLD` and `targetOracleR2DiagonalLD`, and a reader arriving
from elsewhere gets no signal that the standardization is load-bearing. Same for
`targetOracleR2DiagonalLD`, whose body is `sourceSelfR2DiagonalLD β_target var_y`
— legitimate, since a target's self-`R²` *is* its oracle ceiling, but a second
name for one function.

---

## 5. What I could not classify, and why

* **`PCCorrectability/ImitationCapacity.lean`, 28 checkable definitions.** Not in
  any brief I have seen; sibling of two modules I hold; not touched.
* **`GenerativePortabilityLaw.marginalAmplitudeHistoryDegradationBlindness`.** A
  `ProbeBlindness` instance — the category the census parked as its 42 UNKNOWN,
  saying they cannot move the headline by more than 3 %. I make no call either; it
  is counted in (c) and flagged.
* **The true coverage status of `SerialFounderChain`.** Its four members route to
  `split_fst`, but its named instrument
  (`differential/cluster/fam_serial_founder.py`) belongs to the family whose
  stored result cannot be regenerated end to end. Recorded as
  **covered-by-an-unreproducible-file** rather than covered; I could not check
  further without running it, which this workstation may not do.
* **Whether `PencilEnvironment.ababFinite` and `CountingInvariantInstances`'s
  witnesses are already discharged.** Both docstrings describe measurements that
  appear to have been made. I could not verify what those runs cover. §3.11 is
  written on the assumption that they may already discharge part of it.
