# Family proposals, bucket 4

Classification only. No Lean build was run, no simulator was written, no simulation
was executed, no number below was produced by this session's measurement. Every
count is a source-level census of `proofs/Calibrator/` performed by reading and
grepping declarations; every declaration is cited by FILE and DECLARATION NAME,
never by line number.

**Drift warning, and it bit during this pass.** I read
`proofs/validation/empirical/COVERAGE_DENOMINATOR.md` at the start of this session.
By the end of it, `find proofs/validation -name '*.md'` returned nothing and
`git ls-files` agreed: that file and `proofs/validation/README.md` are no longer in
the tree. Another session moved or removed them mid-pass. The census below was taken
against `proofs/Calibrator/` on 2026-08-03 and is a count *at that state*; it is not
tied to a digest because I did not run the extraction that produces one.

---

## 1. What this bucket is

The lead named: `Permeability`, `EpistaticChaos`, `TransportIdentities`,
`StratificationConfounding`, `CondensationUnification`, `HaplotypeTheory`,
`Conventions`, `LongitudinalPortability`, `StatisticalGeneticsMethodology`,
`BundleRigidity`, `BundleRigidity.LinearSCM`, `ErgodicCovariancePencil`,
`JetBarrier`, `AncestrySpecificArchitecture`, "and the rest of that group", with
`FoldedSpectrum` named separately in the cautions.

I resolved "the rest of that group" as: the whole `BundleRigidity/` subdirectory
(twelve further modules, since `BundleRigidity.LinearSCM` was named explicitly and
the directory is one development), plus `FoldedSpectrum.lean`, plus
`EnsembleChannel.lean`.

**`EnsembleChannel.lean` is the ambiguous one and I am flagging it rather than
assuming.** It was not named in any bucket. I claimed it because its
`binaryOrientationArrowVariance`, `binaryOrientationStatisticMean` and three-cycle
features are the *other half* of a law whose Permeability half is unambiguously
mine — `Permeability.binaryOrientationArrowPermeability` is literally
`momentPermeability 1 (binaryOrientationArrowVariance θ)` — and splitting that law
across two agents would produce two half-families. If another agent has claimed
`EnsembleChannel`, family **F6** below is the only thing that has to move, and it
should move whole.

**Excluded as instructed:** the seven-file slice, and the modules led by
`PGSCalibrationTheory`, `TransferLearningPGS` and `Probability` and their groups.
Note that `EpistaticChaos.lean` imports `Calibrator.Probability` and
`Calibrator.ImitationRigidity`, and `FoldedSpectrum.lean` imports six other modules
including `ConditionalGain` and `SpectralDegradation`. I classified only
declarations *declared in* my modules; imports were read, never claimed.

## 2. The census

**318 definitions** (`def`/`abbrev`) across 26 files.

| outcome | count |
|---|---:|
| already a member of an existing family | 14 |
| (a) joins an EXISTING family — membership edit only | 45 |
| (b) belongs to a NEW family proposed below | 198 |
| (c) makes no empirically checkable claim (F1) | 61 |
| **total** | **318** |

Of the 318, **257 carry a real-valued claim** under families.py test F1 — they
denote a real, a vector or matrix of reals, or a structure whose fields are reals.
**14 of those 257 are already members of an existing family** (ten in
`portability_permeability_and_completion`, four in `ensemble_portability_channel`),
so **243 checkable definitions in this bucket have never been classified** — the 45
in (a) and the 198 in (b). That is the number this document exists to move.

### The 61 that are category errors, and the split inside them

**41 are Props, Sets, Finsets, index types or naturals.** A generative process
cannot produce a different value for them. Examples, not a list:
`EpistaticChaos.VariantDisjoint`, `EpistaticChaos.Tempered`,
`BundleRigidity.Separating`, `BundleRigidity.Covers`,
`BundleRigidity.Coverage.peelSet` and its four siblings (all `Set T`-valued),
`BundleRigidity.Operator.IsSymmetry`, `BundleRigidity.LinearSCM.IsSolution`,
`JetBarrier.IsLatticeLaw`, `JetBarrier.IsNonlatticeLaw`,
`FoldedSpectrum.HasScalarSummary`, `FoldedSpectrum.ReadsThroughFunctionals`,
`EnsembleChannel.IsOrderFreeStatistic`, `Permeability.firstTwoLags` (`ℕ`),
`CondensationUnification.ladderMomentOrder` (`ℕ`),
`EpistaticChaos.variantRecurrence` (`ℕ`),
`BundleRigidity.SingleModulus.plusSide` / `minusSide` (`Finset`).

**20 are constructors, not claims** — codings, designs, panels, permutations,
measures and fields: `EpistaticChaos.twoPoolDesign`,
`EpistaticChaos.geneBurdenDesign`, `EpistaticChaos.slidingWindowDesign`,
`EpistaticChaos.equilibriumDesign`, `EpistaticChaos.freeRecombinationStep`,
`EpistaticChaos.flipOrientation`, `EpistaticChaos.SymmetricCoding.scale`,
`EpistaticChaos.equalFrequencyGenotypeCoding`, `EpistaticChaos.genotypeFlip`,
`EpistaticChaos.flipLocus`, `EpistaticChaos.SymmetricCoding.witness`,
`CondensationUnification.GenotypeDesign.reModel`,
`ErgodicCovariancePencil.twoSlice`, `ErgodicCovariancePencil.coupledBinarySource`,
`ErgodicCovariancePencil.coordinatewiseMarginalPreserver` and its two witnesses,
`JetBarrier.logSqGaussianLaw`, `FoldedSpectrum.genotypeFlip3`,
`FoldedSpectrum.idReversal`.

**These 20 are counted in (c) by F1 but I am NOT parking them.** families.py's own
rule is explicit: a coercion, bundler or projection goes into the family of its
downstream consumer, because the COMPOSITION is testable even when the projection
alone is trivial, and that rule has a 31-for-31 record of destroying
un-simulatability claims. Every one of these 20 is a *parameter of a sampler* —
`twoPoolDesign` is the design the two-pool null is measured on;
`coupledBinarySource` is the four-state counterexample; `genotypeFlip3` is the
reflection whose invariance F3 below measures. Each is listed as a member of the
family that consumes it, and each would fall to F3 if anyone claimed otherwise.

**I do not mark any definition in this bucket unsimulatable-as-stated.** That is
itself the finding the lead asked for. Given the corpus's own standing record —
thirty-one attempts, thirty-one losses — a new un-simulatability claim should be
expected to lose before it is written, and I found nothing here strong enough to
be worth losing. The nearest candidate is `BundleRigidity.Operator.transfer` and
`coTransferₗ`, which are linear maps on `C(T, ℝ)` for an arbitrary compact `T`: a
sampler can only instantiate finite `T`, at which point they are matrices and the
statements are linear algebra. That is a limit on what a simulator *reaches*, not
a claim that no generative process bears on them, and I state it as the former.

---

## 3. (a) — 45 definitions that join an existing family

No new generative process. These are membership edits, and the simulators must be
re-run afterwards so the credit is earned rather than asserted.

### To `portability_permeability_and_completion` (simulator `cluster/fam_permeability.py`, FULL PROFILE PASSED) — 27

`Permeability.centeredSquareVarianceFromMoments`,
`covarianceScoreInformationFromMoments`, `momentPermeability`,
`totalCovarianceMomentInformation`, `replicatesForEqualPermeability`,
`diagonalCovarianceMomentPermeability`, `diagonalSquareNoisePrecision`,
`twoChannelMomentPrecision`, `twoChannelMomentResponse`,
`twoChannelMomentNoiseDet`, `twoChannelMomentNoisePrecision`,
`twoChannelConditionalMomentResponse`, `twoChannelConditionalMomentNoise`,
`informationPerUnitCost`, `twoChannelMomentInnovationInformation`,
`totalMultivariateGaussianInformation`, `twoChannelWhitenedDerivative`,
`totalGaussianInformation`, `covarianceTangentEstimatorVarianceFromMoments`,
`gaussianCovarianceTangentEstimatorVariance`, `lagSensitivityMatrix`,
`geometricLagCovarianceDerivative`; and from `FoldedSpectrum.lean`
`diploidCovarianceMomentPermeability`, `diploidPanelCovarianceMomentPermeability`,
`totalDiploidCovarianceMomentInformation`, `requiredCohorts`, `recoveredVariance`.

The five from `FoldedSpectrum` are the diploid instantiation of the same
covariance-moment channel — `diploidCovarianceMomentPermeability` is
`covarianceMomentPermeability` evaluated at the Hardy-Weinberg second and fourth
moments — plus the cohort-partition law. The permeability family's recorded run
already measured that law ("at fixed total budget N = 131072 the predicted and
measured optima coincide exactly at m = 2048 cohorts of n' = 64 loci"), and
`requiredCohorts` and `recoveredVariance` are the two definitions that law is
about. They are unassigned.

Every one is an internal piece of an arm `fam_permeability.py` already runs. The
C6 two-channel arm is reported as passing to machine precision, and its five
`twoChannelMoment*` definitions are not members; the C1 estimator-variance arm
passes, and `covarianceTangentEstimatorVarianceFromMoments` is not a member; the
fixed-budget cost arm fired both directions of the threshold, and
`informationPerUnitCost` is not a member. **This is the cheapest coverage in the
bucket by a wide margin: 22 definitions, zero new code.**

**One defect found while doing this.** The family's member list names
`covarianceScoreInformation_gaussian`. No such declaration exists in
`Permeability.lean`. The definition is `covarianceScoreInformationFromMoments` and
the *theorem* relating it to the Gaussian case carries the `_gaussian` suffix. A
membership entry that matches nothing is credited to nothing, so the family's
member count is one lower than it reads. Worth checking whether the coverage join
silently drops it or silently matches a theorem.

### To `ensemble_portability_channel` (simulator `cluster/fam_ensemble_channel.py`) — 5

`EnsembleChannel.twoUnitArrow`, `weightedBandEnsembleLoss`,
`weightedBandPredictorLoss`, and `FoldedSpectrum.ScalarSecondMoments.witness` and
`FoldedSpectrum.gamma`. The first is the arrow whose vacuity that family already
measured; the two band losses are the weighted generalisations of
`ensembleSquaredLoss` and `ensemblePredictorSquaredLoss`, which are members; and
`gamma k = S.moment 0 k` is the stationary autocovariance sequence that family's
Fejér channel is a functional of.

### To `fst_estimator_sampling` (simulator `cluster/fam_fst_estimators.py`, GREEN) — 6

`Conventions.neiGst`, `hudsonFst`, `meanAlleleFreq`, `betweenSubgroupVariance`,
`neiContrastSpike`, `hudsonBbpSpike`. These are the Nei/Hudson convention pair and
the two spike laws built on them. The family already simulates the two estimators'
sampling behaviour; `Conventions.lean` is out of the slice, so these six are
out-of-slice restatements the family reaches but does not claim.

### To `hwe_genotype_score` and `drift_retention` — 3

`Conventions.ploidy` and `hweGenotypeVariance` to `hwe_genotype_score`;
`Conventions.coalescentTimeScale` to `drift_retention`.

### The four hub primitives, and a coverage-accounting hazard — 4

`Conventions.convexMix`, `geometricDecay`, `oneMinusRatio`, `retainedFraction`.

Each is one map with several named referents in other files, tied by theorem.
`geometricDecay` alone has four referents across four files
(`LongitudinalPortability.ldDecayPerGeneration`,
`DGP.discreteRecombinationSurvival`, `PortabilityDrift.admixtureLDDecay`, and
itself), and `Conventions.lean` says in its own docstring that they must not be
folded into one because identical arithmetic is not identical meaning.

**The hazard.** A membership pass that assigns a hub to the family of any one
referent makes the coverage percentage rise without any new measurement, and the
other three referents stay unmeasured behind a name that now reads as covered. This
is the same failure mode families.py records as defect O5b — a loosened join
always flatters — in a form that fully-qualified names do not catch, because
`Conventions.geometricDecay` is a genuinely distinct declaration. **Recommendation:
assign each hub to the family of EVERY referent, or to none.** Assigning it to one
is the only wrong answer, and it is the answer a mechanical pass produces.

---

## 4. (b) — eleven new families, ranked

Ranked by members covered, simulator cheapness, and whether a live disagreement or
a suspicious definition sits inside.

---

### F1. `confounded_estimator_bias` — 34 members. **Rank 1.**

**Members.** All 24 of `StratificationConfounding.lean`
(`StratificationModel.witness`, `varTrue`, `varBias`, `TwoPopBiasModel.witness`,
`varBiasTarget`, `ColliderModel.inducedCov`, `β_selected`, `RGEModel.witness`,
`pred`, `RGEInflationModel.witness`, `r2_obs`, `SurvivorshipModel.witness`,
`pSurv`, `SurvivorshipAttenuationModel.witness`, `r2_surv`,
`pgsAttenuationFactor`, `AttenuationModel.witness`, `reliabilityRatio`,
`AttenuationModel.β_obs`, `TransportabilityModel.witness`, `r2_target`,
`MRInstrumentModel.witness`, `fStat`, `r2EstimatorVariance`) plus all 10 of
`StatisticalGeneticsMethodology.lean` (`incrementalR2`, `portabilityRatio`,
`effectiveSampleSizeFromSE`, `MetaAnalysisModel.witness`, `fixed_weights`,
`random_weights`, `fixed_se_sq`, `random_se_sq`, `LDSCModel.witness`,
`disjointWindowLimitVariance`).

**Generative process.** A linear phenotype model on a stratified population:
`Y = Σ βᵢ Gᵢ + Σ bᵢ Aᵢ + ε`, with allele frequencies differing along an ancestry
axis, so the genetic and confounding components are correlated by construction.
Then apply, one at a time and in composition, the seven distortions the module
names: collider selection on a function of `Y`, survivorship at rate `s`,
measurement error of variance `σ²_noise`, a gene-environment correlation channel,
a source-to-target effect shift `δ`, an instrument of strength `F`, and finite-`n`
estimation of `R²`.

**What a simulator MEASURES.** For each distortion: the closed form's predicted
bias against the bias actually observed in the fitted PGS. `varTrue`/`varBias`
against decomposed variance components; `ColliderModel.β_selected` against the OLS
slope re-fitted inside the selected sample; `pSurv` and `r2_surv` against
survivor-cohort `R²`; `reliabilityRatio` and `β_obs` against attenuation under
injected noise; `fStat` against the first-stage F; `r2EstimatorVariance` against
the Monte Carlo variance of the plug-in `R̂²` over the `(R², n)` grid.

**WHAT WOULD FALSIFY IT.** Each of the seven is a closed form for a bias the
sampler measures directly, so any of the seven differing from its measurement
falsifies that arm. Split controls: at zero confounding (`b ≡ 0`) every bias term
must be exactly zero and every `R²` must be unbiased, isolating the estimator from
the distortion; at zero selection pressure the collider covariance must be exactly
zero. Can-fail condition: the selection strength must be large enough that
`inducedCov` is a detectable share of the total covariance — at a selection
fraction of 0.99 every collider claim validates by construction.

**A LIVE DISAGREEMENT ALREADY SITS INSIDE.** `r2EstimatorVariance`'s own docstring
contains a seven-cell measured table, and then states, in the corpus's own words,
"Note this does not match the boundary asserted below. The Empirical status line
states `0.99-1.01 for n >= 1000`, but at `R² = 0.01` the ratio is 0.954 at
`n = 1000` and 0.985 at `n = 5000` — both outside that band, at sample sizes the
band claims to cover." The `Empirical status: VALIDATED (… 0.99-1.01 for n >= 1000)`
line directly beneath it is unchanged. The formula's regime is real and is in
`n·R²`, not `n`. **This family's first arm is to reproduce that table and force the
status line into the right variable.** It is a claim-versus-evidence conflict the
file has already documented against itself and not acted on.

**Cost.** Cheapest of the large families: pure linear-Gaussian sampling, no
coalescent, no genome. Vectorises trivially over replicates.

---

### F2. `bundle_spectrum_identifiability` — 49 checkable members. **Rank 2.**

This is one development across thirteen files and it should be one family; splitting
`BundleRigidity/` from `BundleRigidity.lean` would produce a family whose simulator
cannot reach the machinery its own theorems are proved with.

**Members.** `BundleRigidity.lean`: `BundleFamily.modulus`, `BundleFamily.massAt`,
`spectrumModulusLaw`, `Panel.addWeights`, `Panel.smulWeights`, `singleAtomFamily`,
`singleLocusPanel`, and the three Props `Covers`, `SinglyCoveredBy`, `Separating`
as the sampler's admissibility predicates.
`BundleRigidity/Coverage.lean`: `coverers`, `singleWindow`, `peelSet`, `peel`,
`core`. `BundleRigidity/CoverageInvariance.lean`: `chargedTuples`.
`BundleRigidity/SingleModulus.lean`: `SingleModulus.witness`, `plusSide`,
`minusSide`, `wPlus`, `wMinus`, `threeAtom`, `threeAtomWitness_threeFifths`,
`threeAtomAtOne`, `fourAtom`. `BundleRigidity/TwoAtom.lean`: `mOne`, `mTwo`,
`chain`. `BundleRigidity/Realizability.lean`: `outerAtom`, `innerAtom`.
`BundleRigidity/Operator.lean`: `modulusMap`, `coTransfer`, `coTransferₗ`,
`transfer`, `diracAt`, `pullback`, `evenPart`, `oddPart`, with `SameTransfer`,
`IsSymmetry`, `IsTauOdd`, `IsTauEven`, `IsInvariantFn` as predicates.
`BundleRigidity/Telescope.lean`: `prodWeight`, `prodOp`, `altSum`.
`BundleRigidity/Dichotomy.lean`: `weightRatio`, `defect`, `falsifierP`,
`falsifierQ`, `chi`, `bezout`. `BundleRigidity/Freshness.lean`: `dimSum`, `effDim`.
`BundleRigidity/DeploymentCeiling.lean`: `DeploymentModel.witness`, `sampleCost`.
`FoldedSpectrum.lean`: `diploidStdev`, `diploidAtomValue`, `diploidAtomMass`,
`diploidFamily`, `genotypeFlip3`, `Panel.reflect`, `Panel.fold`,
`HasFrequencyTie`, `invHeterozygosity`, `twoPointModulusLaw`, `positiveThreshold`,
`InLinkageEquilibrium`.

`Dichotomy`'s `falsifierP = ![3/10, 2/5]` and `falsifierQ = ![7/10, 3/5]` are
already a named numeric falsifying pair — a two-point measure pair on which the
dichotomy is claimed to separate. **A simulator gets that arm for free: evaluate
`weightRatio`, `chi`, `defect` and `bezout` on those two measures over word lists
of increasing length and check the claimed separation actually opens.** A named
falsifier that has never been evaluated is exactly what families.py's un-simulatable
machinery exists to catch.

`Operator`'s eight transfer definitions are reachable only at finite `T`, where they
are matrices; see §2. `DeploymentCeiling.sampleCost (C/η)^(2k)` grows as the `2k`
power and is the arm where a grid confined to small `k` validates everything.

**Generative process.** Draw a finite realized panel: `n` loci with minor allele
frequencies `qᵢ` and weights `wᵢ`. At each locus draw genotypes from the
Hardy-Weinberg masses `((1−q)², 2q(1−q), q²)`, standardize, and form
`U = X² − 1`. The panel's modulus law is the distribution of `|U|` across the
panel; `spectrumModulusLaw` is that law computed analytically as a mixture over
loci, which is exactly the linkage-equilibrium reading.

**What a simulator MEASURES.** (i) the sampled `|U|` histogram against
`spectrumModulusLaw`; (ii) the modulus law of a panel against that of
`Panel.reflect` (`q ↦ 1 − q`) — the polarization claim; (iii) whether inverting the
linear map recovers the weight vector of a `Separating` panel and fails on a panel
with `HasFrequencyTie`; (iv) `wPlus`/`wMinus`/`threeAtom`/`fourAtom` as the
explicit two-, three- and four-atom realizations, checked against the modulus
values they claim.

**WHAT WOULD FALSIFY IT.** A `Separating` panel whose spectrum is *not* recovered
by the inversion refutes `spectrum_determined_of_separating` on realized data. A
reflected panel whose modulus law measurably differs refutes the folding claim
(this arm should PASS — `aⱼ(1−q) = −a₂₋ⱼ(q)` is exact, so it is the positive
control, and if it fails the sampler is wrong, not the corpus). The arm that can
genuinely fail is (i) **run under linkage disequilibrium**: `spectrumModulusLaw`
is a mixture over independent loci, the file says so and carries
`InLinkageEquilibrium` as an explicit hypothesis, and the measured `|U|` histogram
of a panel with genotype-level LD at fixed frequencies is where the mixture reading
breaks. Can-fail condition: the frequency spectrum must include values near 0 and
1 where `invHeterozygosity` blows up; a spectrum confined to `q ∈ [0.2, 0.8]`
validates everything.

**Scope note, and it is not a defect.** `BundleRigidity.lean`'s header already
states that these are theorems about realized finite panels and that over a
continuous mixing measure single coverage never occurs and the argument does not
start. A simulator must therefore sample finite panels, and a simulator that
sampled a continuous spectrum would be testing something the corpus does not claim.

---

### F3. `haplotype_phase_and_local_ancestry` — 20 members. **Rank 3.**

**Members.** All 14 of `HaplotypeTheory.lean` (`expectedDistinctHaplotypes`,
`haplotypeHomozygosity`, `effectiveHaplotypeNumber`, `averagePhaseInteraction`,
`dosagePhaseMisspecificationError`, `haplotypePhasePredictionError`,
`dosageTransportBias`, `haplotypeTransportBias`, `haplotypeEffectVarianceOLS`,
`phaseAttenuation`, `ancestrySpecificEffect`, `globalAncestryAveragedEffect`,
`localAncestryMisspecification`, `expectedTractLength`) plus all 6 of
`AncestrySpecificArchitecture.lean` (`driftVariance`, `twoPopDriftVariance`,
`expectedFreqDiffSq`, `gwasHeritability`, `geneFlowFstStep`,
`portabilityFromArchitecture`).

**Generative process.** Two arms sharing one population. **Phase arm:** simulate
diploid haplotype pairs at `k` linked loci with a cis/trans interaction term, then
corrupt the phase call at switch-error rate `s` and refit. **Admixture arm:** a
single-pulse hybrid-isolation pedigree with explicit Poisson crossovers over `g`
generations at admixture fraction `α`, carrying ancestry-specific effect sizes.

**What a simulator MEASURES.** Distinct haplotype count against
`expectedDistinctHaplotypes(k, n)`; homozygosity and effective haplotype number;
the ratio of phased to dosage prediction `R²` against `phaseAttenuation(s)`; the
`R²` gain from local-ancestry deconvolution against
`localAncestryMisspecification`; realized ancestry tract lengths against
`expectedTractLength(g, α)`; and, on the drift side, the realized allele-frequency
divergence against `expectedFreqDiffSq(F_ST, p₀)`.

**WHAT WOULD FALSIFY IT.** `phaseAttenuation s = (1 − 2s)²` is the sharp one. It
and the plausible competitor `(1 − s)` agree at `s = 0` and are both zero-ish at the
endpoints; they differ by up to 25% near `s = 0.25`, so **the switch-error grid must
include `s ≈ 0.25` or the arm decides nothing.** At `s = 1/2` the attenuation must
be exactly 0 — phase is pure noise — and that is the split control isolating the
attenuation from the estimator.

**Built-in positive control, which is why this family is cheap to trust.**
`expectedTractLength`'s docstring records an already-completed falsification: the
competing form `1/(g·r_total)` moves 16-fold with map length while the truth is
asymptotically independent of it, and the body `1/(g(1−α))` matches to 0.1–7%
where censoring is small. A simulator that cannot reproduce that table is broken
before its new arms mean anything. **The simulator must reproduce the edge-censored
approach to `1/(g(1−α))` rather than assert it** — the recorded values rise
`0.1462 → 0.1728 → 0.1913` toward `0.20` as chromosome length grows, and a
simulator that lands on `0.20` at 1 Morgan is not simulating censoring.

---

### F4. `overlap_spectrum_null` — 17 checkable members plus 11 sampler constructors. **Rank 4.**

**Members.** From `EpistaticChaos.lean`: `configurationWeight`,
`interactionMonomial`, `magnitudeProfile`, `statistic`, `locusInfluence`,
`fourthCumulantFromMoments`, `circulantSpectrumA`, `circulantSpectrumB`,
`overlapMatrix`, `cycleDensity`, `palindromicCycleDensityA`,
`palindromicCycleDensityB`, `hweThirdCentralMoment`,
`HardyWeinbergModel.standardizedGenotype`, `HardyWeinbergModel.centeredSquare`,
`HardyWeinbergModel.signBias`, `HardyWeinbergModel.reflect`, plus the ten design
and coding constructors listed in §2 as sampler parameters (`twoPoolDesign`,
`geneBurdenDesign`, `slidingWindowDesign`, `equilibriumDesign`,
`freeRecombinationStep`, `flipOrientation`, `SymmetricCoding.witness`,
`SymmetricCoding.scale`, `equalFrequencyGenotypeCoding`, `flipLocus`), and
`CondensationUnification.GenotypeDesign.reModel`.

**Generative process.** Draw `n` independent Hardy-Weinberg loci at frequency `q`,
standardize, and form pool statistics `Tᵢ` over disjoint locus pools. Build the
overlapping quadratic design `f = Σ_{i≠j} A_ij Tᵢ Tⱼ` for the two 8×8 circulants
with palindromic offsets `(0,1,2,0,0,0,2,1)` and `(0,2,1,0,0,0,1,2)`, and
separately the two-pool statistic `T₁·T₂` and a variant-disjoint design.

**What a simulator MEASURES.** The fourth cumulant of `f` under each design; the
full sampled null histogram of design A against design B; `overlapMatrix` and
`cycleDensity` as trace power sums of the realized design; and the two-pool
statistic's fourth cumulant against 6, the disjoint design's against 0.

**WHAT WOULD FALSIFY IT.** The central claim of `EpistaticChaos`'s `OverlapSpectrum`
section is that the null is a *spectral* invariant and not a function of the
profile counts: the two circulants have the identical entry multiset
`{0,0,0,0,1,1,2,2}` in every row, identical row sum 6, identical
`variantRecurrence` profile — so every profile functional agrees — and different
eigenvalue multisets. **If the two designs' sampled nulls agree within Monte Carlo
error, the file's central witness is gone**, and with it
`CondensationUnification.recurrence_preserving_resampling_is_not_a_calibration`,
which takes the change of null under resampling as an argument. That is a real
possibility at small `n`, where neither design has converged to its limit; the
can-fail condition is that the pool size must be large enough for the limit law to
be visible and small enough that the two spectra have not both been washed into
Gaussianity.

Second falsifier: `fourthCumulantFromMoments_of_squared_standard_moments` reaches 6
by writing the product law's moments as `m₂·m₂` and `m₄·m₄`. **That is the
independence assumption, applied in the statement rather than derived from a joint
distribution** — the docstring says so in exactly those words. A simulator draws
from a joint distribution and either supplies the assumption or refutes it. This
is the one arm where a passing result would be genuinely informative, because the
Lean statement cannot get there.

`palindromicCycleDensityA`/`B` must equal the measured trace of `A^p`/`B^p`. That
is arithmetic on a fixed integer matrix and must pass; it is the positive control,
not the test.

---

### F5. `exp_functional_transport_identities` — 26 members. **Rank 5.**

**Members.** All of `TransportIdentities.lean`: `mean`, `variance`, `covariance`,
`expMse`, `bias`, `dot`, `linScore`, `secondMomentMatrix`, `covarianceMatrix`,
`crossCovVector`, `predictorCausalCovariance`, `contextCrossCovVector`,
`causalSignal`, `optimalWeightsFromMoments`, `transportedCovariance`, `locusTerm`,
`baselineWeight`, `transportFactor`, `explainableFraction`, `conditionalMean`,
`conditionalVariance`, `ConfusionMatrix.witness`, `prevalence`, `recallRate`,
`fpr`, `precision`.

**Generative process.** Instantiate the abstract `ExpFunctional Ω` — which the
module leaves as an arbitrary linear functional — by the empirical mean over `R`
draws from a joint law of predictors `X`, causal contexts `C` and outcome `Y`,
with a source-to-target kernel `K` mapping predictor loci to causal loci. Every
identity in the file then becomes a numeric statement about samples.

**What a simulator MEASURES.** `optimalWeightsFromMoments` against the OLS
solution refitted on the sample; `transportedCovariance` composed from
`baselineWeight` and `transportFactor` against the target covariance actually
realized when source weights are carried across; `explainableFraction`; the
conditional-mean/variance decomposition against a conditioned resample; and the
four `ConfusionMatrix` rates against a thresholded classifier's confusion counts.

**WHAT WOULD FALSIFY IT.** `optimalWeightsFromMoments` takes `sigmaInv` as an
argument rather than inverting the second-moment matrix itself, and the file
defines both `secondMomentMatrix` and `covarianceMatrix` — which differ whenever
`X` is not centered. If the corpus's weights are computed against the second-moment
matrix and the OLS fit uses the covariance matrix, the two differ on non-centered
predictors by exactly the outer product of the means, and the simulator will see
it. That is the split control: run with centered `X` (both must agree) and with a
mean shift injected (they must diverge by a predicted amount). The transport arm is
the one that can fail on its merits: `transportedCovariance` predicts what a
source-fitted weight vector achieves in the target, and nothing proved makes that
prediction correct for a kernel `K` the simulator chose.

**Note.** The coverage census records that one declaration in
`TransportIdentities.lean` fails the source parser — an anonymous `instance`. It is
an instance, not a definition, so it is in no denominator, but a translator-based
simulator author will meet it.

---

### F6. `orientation_arrow_information` — 12 members. **Rank 6, and the cheapest thing in the bucket.**

**Members.** `Permeability.binaryOrientationArrowPermeability`,
`totalBinaryOrientationArrowPermeability`,
`threeCycleOrientationArrowPermeability`; `EnsembleChannel.binaryFirstAnnotation`,
`binarySecondAnnotation`, `binaryTransitionArrowStatistic`,
`binaryOrientationStatisticMean`, `binaryOrientationArrowVariance`,
`threeCycleFeatureA`, `threeCycleFeatureB`, `threeCycleForwardCrossMoment`,
`threeCycleCrossFeatureArrow`.

**Generative process.** A stationary two-state chain on `{0,1}` with orientation
imbalance `θ`, and the deterministic three-cycle `0 → 1 → 2 → 0` carrying the
scaled feature pair. Sample ordered adjacent pairs and form the transition-arrow
statistic.

**What a simulator MEASURES.** The mean and variance of the arrow statistic against
`binaryOrientationStatisticMean` and `binaryOrientationArrowVariance θ = 1 − θ²`;
the reciprocal variance of the resulting `θ` estimator against
`binaryOrientationArrowPermeability θ = 1/(1 − θ²)`; the total from `m` pairs
against `m/(1 − θ²)`; and the three-cycle witness against the binary one.

**WHAT WOULD FALSIFY IT — and there is a live premise risk here.**
`totalBinaryOrientationArrowPermeability m θ = m/(1 − θ²)` is stated for **`m`
independent ordered pairs**. The only sampling scheme that naturally produces
ordered adjacent pairs is a chain of length `m+1`, whose `m` adjacent pairs
**overlap and are not independent**. If the measured information from one chain
falls below `m/(1 − θ²)` by a `θ`-dependent factor, the independence reading of the
law is refuted for the sampling scheme that generates its own object — while the
law remains true for `m` disjoint two-step chains. A simulator that only draws
disjoint pairs will confirm the law and learn nothing; **it must run both, and the
gap between them is the measurement.**

Second falsifier, and a clean one: `threeCycleOrientationArrowPermeability` is
claimed equal to the binary one by coding-scale invariance, the three-cycle arrow
being the binary sign scaled by `1/3`. Rescale the three-cycle features by an
arbitrary `c ≠ 1/3` and the measured permeability must not move. If it does, the
invariance is a property of the chosen constant and not of the coding.

Third: `binaryOrientationArrowPermeability 0 = 1` — the reversible centre must give
exactly one unit of information in the natural normalisation, isolating the
normalisation from the imbalance. Can-fail condition: `|θ|` must approach 1, where
`1/(1 − θ²)` diverges; a grid of `|θ| ≤ 0.2` makes the law and its linearisation
`1 + θ²` indistinguishable.

**Why this ranks high despite twelve members.** It is a two-state Markov chain —
no genome, no coalescent, minutes of compute. All twelve definitions landed within
the last day (commits "Derive binary arrow permeability law" and "Results: the
arrow is vacuous, and the cohort-partition law measured"), so none has met a
sample. And the related `twoUnitArrow` arrow was measured *vacuous* by the ensemble
family — forty-eight combinations, largest `|t|` anywhere −2.29 — which makes the
question of whether *this* arrow has an object a live one rather than a formality.

---

### F7. `moment_ladder_squaring_tower` — 15 members. **Rank 7.**

**Members.** `CondensationUnification.gaussianKurtosisMaf`, `hweLevelOne`,
`MafSpectrum.witness`, `moment`, `centeredSquareThirdMoment`,
`fourthMomentDispersion`, `squaringScaleSq`, `nextFloorFourthMoment`,
`squaringStep`, `squaringFixedPoint`, `varianceProfile`, `fourthMomentProfile`,
`jProfile`, `FiberSplitting.witness`, `FiberSplitting.displacement`.

**Generative process.** Draw a unit-variance coordinate — a standardized HWE
genotype at frequency `q`, and separately a Gaussian and a heavy-tailed control —
and iterate the squaring map `x ↦ (x² − 1)/scale`, tracking the moment sequence up
the ladder. Separately, average the per-locus moments over a `MafSpectrum` panel.

**What a simulator MEASURES.** The rung-to-rung fourth moment against
`nextFloorFourthMoment(m₂, m₄, m₆, m₈)`; the iterate's limit against
`squaringFixedPoint(scale)`; the frequency at which a HWE coordinate's kurtosis
equals the Gaussian value against `gaussianKurtosisMaf = (3 − √3)/6`; and panel
moments against `MafSpectrum.moment`, `centeredSquareThirdMoment`,
`fourthMomentDispersion`.

**WHAT WOULD FALSIFY IT.** `squaringFixedPoint` is the positive root of
`x² − σx − 1 = 0`. If iterating the squaring map from a generic start does **not**
converge to it, the fixed point is not attracting and the tower does not describe
iterated squaring — a two-line check that could plainly fail, since the map's
derivative at the fixed point is `2x/σ` and there is no proof in the file that it
is below one. `nextFloorFourthMoment` is a closed form in four moments; it holds
only if the squaring step's higher moments factor as assumed, so a heavy-tailed
coordinate is the can-fail case. Split control: the Gaussian input must reproduce
the known Gaussian rung values exactly, isolating the ladder arithmetic from the
input law.

`gaussianKurtosisMaf` is labelled **VALIDATED** against
`proofs/validation/empirical/blind_maf/` with a scope caveat of HWE and unlinked
loci; that arm is a re-run, not a new claim, and it is the family's positive
control.

---

### F8. `temporal_portability_decay` — 12 members. **Rank 8.**

**Members.** All of `LongitudinalPortability.lean`: `portabilityAtTime`,
`ldDecayPerGeneration`, `secularTrendBias`, `temporalMetricProfile`, `temporalR2`,
`ageDependentSignalShape`, `ageDependentSignalVariance`,
`ageDependentMetricProfile`, `ageDependentR2`, `temporalCalibrationInTheLarge`,
`temporalExactBrierRisk`, `modelStaleness`.

**Generative process.** A source cohort at `t = 0` with a fitted PGS, and target
cohorts at later times and at different ages, whose `R²` is degraded by three
separate channels: per-generation LD decay at rate `r`, a secular trend in the
outcome at rate `trend_rate`, and an age-dependent signal shape peaked at
`age_peak` with width `width`.

**What a simulator MEASURES.** Realized `R²(t)` against
`portabilityAtTime(r²₀, λ_total, t)`; realized `R²(age)` against `ageDependentR2`;
the observed-minus-predicted event rate against
`temporalCalibrationInTheLarge`; the realized Brier score against
`temporalExactBrierRisk`.

**WHAT WOULD FALSIFY IT.** The module composes three decay channels into a single
`lambda_total` and asserts one exponential. **If two channels acting together give
a decay that is not the product of their separate exponentials — and a secular
trend that shifts the outcome *mean* rather than attenuating its variance is
exactly such a channel — the composite is refuted while each single channel still
validates.** That is the split control and the whole point: run each channel alone,
then together, and check multiplicativity. `temporalCalibrationInTheLarge` is a
difference of two probabilities and must be exactly zero on a calibrated cohort and
nonzero on a miscalibrated one — a predicate never evaluated on a negative instance
is not a predicate.

---

### F9. `linear_scm_intervention_contrasts` — 7 members. **Rank 9, and it is a finding.**

**Members.** `BundleRigidity/LinearSCM.lean`: `LinearSCM.witness`,
`ChainSCM.mUnder`, `yUnder`, `yUnderXM`, `totalEffect`, `directEffect`,
`indirectEffect`, with `IsSolution` and `IsInterventionalSolution` as the sampler's
admissibility predicates.

**Generative process.** Sample noises `(n_X, n_M, n_Y)`, generate
`X = n_X`, `M = aX + n_M`, `Y = bX + cM + n_Y` observationally; separately generate
interventional samples under `do(X := x)` and under the joint
`do(X := x, M := m)`.

**What a simulator MEASURES.** The total, direct and indirect effects as *sample*
contrasts between interventional arms; the OLS coefficient of `Y` on `X` alone; the
OLS coefficients of `Y` on `(X, M)`.

**WHAT WOULD FALSIFY IT.** With independent noises, regressing `Y` on `X` alone
must recover `b + ca` and regressing on `(X, M)` must recover `b` and `c`; the
sampled total effect must equal `(b + ca)(x′ − x)`. The arm that can fail:
**correlate `n_M` and `n_Y`.** The regression estimate of the direct effect is then
biased while the interventional contrast is not, and the gap is measurable. The
`ChainSCM` equations assume independent noises and *these three definitions do not
say so* — the structure carries only `a`, `b`, `c`. A simulator that only ever runs
the independent case will confirm everything and will not have tested the model.

**THE FINDING.** `totalEffect`, `directEffect` and `indirectEffect` each carry
`Empirical status: NOT AN EMPIRICAL CLAIM -- an intervention contrast defined from
the model's own equations.` All three return `ℝ`, take real arguments, and are
exactly what a sampler measures when it runs the intervention. **This is semantic
inflation running the other way: a deflation label that exempts a checkable
definition from measurement.** The label is defensible as a statement about the
*definition* — a contrast is a definition, not a hypothesis — but it is read as a
statement about the *claim*, and it will keep these three out of any coverage
denominator built from status lines. `BundleRigidity/TwoAtom.lean`'s `mOne` and
`mTwo` carry the same `NOT AN EMPIRICAL CLAIM` label and are also real-valued
modulus curves that F2 above measures.

---

### F10. `lattice_exceedance_inflation` — 3 members. **Rank 10 by size, rank 1 by value per member.**

**Members.** `JetBarrier.latticeInflation`, `latticeBracket`,
`gaussianObservables`, with `logSqGaussianLaw`, `IsLatticeLaw`, `IsNonlatticeLaw`,
`LatticeDatum.Describes` and `IsChameleonObservable` as the sampler's law
constructors and predicates.

**Generative process.** Draw i.i.d. coordinates from (a) a law whose `log x²` is
lattice — hard-called standardized diploid dosage takes three values, so `log x²`
has finite support — and (b) a nonlattice law matched in the first two Mellin
moments, e.g. imputed dosage or a Gaussian. Run the size-biased walk and count
threshold exceedances at thresholds placed at distance `δ ∈ [0, h)` above the
nearest lattice point.

**What a simulator MEASURES.** The ratio of the lattice law's exceedance intensity
to the matched nonlattice law's, as a function of span `h` and offset `δ`.

**WHAT WOULD FALSIFY IT.** The measured intensity ratio differing from
`latticeBracket h δ = h·e^{−δ}/(1 − e^{−h})`, and in particular from
`h/(1 − e^{−h})` at `δ = 0`. **This is precisely the identification the corpus
declines to prove.** `inflated_intensity_ne_of_injective` carries it as the named
hypotheses `hIntensityLattice`, `hIntensityGauss` and `hInjective`, and its own
docstring says "This is not lattice detection and must not be cited as such …
supplying them is the whole difficulty." A simulator converts the leading one of
those three hypotheses into a measurement. That is the highest-value single arm in
this bucket by the criterion the lead set — a family whose simulator can only agree
is worthless, and this one can very obviously disagree.

Can-fail condition: `h` must be small enough that `h/(1 − e^{−h}) ≈ 1 + h/2` is
distinguishable from 1 only with enough replicates, and large enough that the
inflation is not swamped; and `δ` must sweep the full `[0, h)`, since at `δ → h`
the bracket falls back toward 1 and an aligned-threshold-only grid measures the
maximum and calls it the law.

`gaussianObservables`'s `nonlattice` field rests on `logSqGaussian_nonlattice`,
which is an explicit `sorry`. That is disclosed in the docstring, is one of the
corpus's eight declared sorries, and is not a defect I am reporting — it is the
corpus's own convention for a visible hole.

---

### F11. `covariance_pencil_relaxation` — 3 members plus a decidable control. **Rank 11.**

**Members.** `ErgodicCovariancePencil.twoSiteCovarianceEnergy`,
`localPencilTraceContribution`, `firstModeConditionalMean`, with
`coupledBinarySource`, `coordinatewiseMarginalPreserver`, `twoSlice`,
`StationarySpaceTimeField.witness` and `StationaryTwoSliceField.witness` as the
sampler's field constructors.

**Generative process.** A Gauss-Markov chain along the genomic coordinate at
lag-one correlation `a` for the source slice and `b` for the target slice, coupled
at time `τ` with relaxation `r = exp(−λτ)`.

**What a simulator MEASURES.** The contrast energy at direction `(1, −1)` against
`2(1 − ρ)`; the target/source Rayleigh ratio against `(1 − b)/(1 − a)`; and the
edge trace contribution under a first-eigenmode conditional mean against the
predicted split `localPencilTraceContribution(source, mean) − 2r·source(source −
mean)/(1 − source²)`.

**WHAT WOULD FALSIFY IT.** The pointwise split is proved algebra and must pass. The
empirical content is whether a *real* chain's conditional mean is first-eigenmode
affine: run a chain whose conditional mean is not affine in the source coordinate —
any nonlinear-drift or non-Jacobi chain — and the residual after subtracting the
predicted correction must be nonzero. If the residual is zero for every chain
tried, the "first eigenmode" qualifier is doing no work and the identity is
unconditional; if it is nonzero, the identity is correctly conditional and the
simulator has measured the condition. Either outcome is informative, which is the
test for a worthwhile arm.

**A decidable positive control sits inside, and it is not a simulation.**
`coupledBinarySource` and `coordinatewiseMarginalPreserver` are the module's
counterexample: a coordinatewise Markov update that preserves every coordinate
marginal and does not preserve the joint law. Over `Bool × Fin 2` that is four
states, so it is settled by exhaustive enumeration rather than sampling. Any
simulator for this family should enumerate it first; if the counterexample does not
reproduce, the sampler is wrong.

---

## 5. Findings on semantic inflation

The lead flagged `EpistaticChaos`, `JetBarrier`, `FoldedSpectrum` and
`BundleRigidity` as carrying names and docstrings claiming more than the
mathematics delivers. **The headline finding is that the cleanup has largely
landed.** All four modules now carry explicit scope statements that disclaim the
inflated reading, and in three cases the disclaimer is more precise than anything I
would have written:

* `JetBarrier.lean`'s header opens "Lattice arithmetic from the **withdrawn** Jet
  Barrier program", states that Theorems 1a and 1b are absent, and that what is
  proved is the arithmetic inequality `h/(1 − exp(−h)) > 1` and nothing more.
* `BundleRigidity.lean` states that its theorems are about realized finite panels,
  that over a continuous mixing measure single coverage never occurs and the
  argument does not start, and that "anyone quoting a rigidity statement about a
  continuous spectrum is quoting something this file does not prove".
* `FoldedSpectrum.lean` states that its §8 handles a Markov-modulated *parameter*
  chain and "is **not** correlation between genotypes at fixed frequencies, which
  is what linkage disequilibrium actually is", and calls that "the single most
  important caveat in this file".
* `EpistaticChaos.lean` self-flags its own weakest theorem:
  `fourthCumulantFromMoments_of_squared_standard_moments` is documented as applying
  the independence assumption "in the statement rather than derived from a joint
  distribution", and `twoPool_fourthCumulant_ne_zero : (6 : ℝ) ≠ 0` is documented
  as "arithmetic on two numerals" carrying "no genetics".

Reporting rather than filing quietly, here is what I judge is left:

1. **`BundleRigidity/LinearSCM`'s three `NOT AN EMPIRICAL CLAIM` labels** — F9
   above. Real-valued definitions with real arguments, exempted from measurement by
   a status line. Inflation in the deflationary direction. The same label sits on
   `BundleRigidity/TwoAtom.mOne` and `mTwo`.
2. **A recurring degenerate-witness pattern.** `JetBarrier` itself names the
   pattern — `dirac_isLatticeLaw`'s docstring says the example "is degenerate, and
   that is its whole job … It is not evidence that the lattice branch is
   *interesting*, only that it is not empty." The same construction appears
   unflagged elsewhere in my bucket:
   `StratificationConfounding.StratificationModel.witness` sets `β ≡ 0`, so the
   model it witnesses has **zero true genetic variance and pure bias**;
   `ErgodicCovariancePencil.StationarySpaceTimeField.witness` is the constant field
   satisfying stationarity by reflexivity (this one *is* flagged);
   `BundleRigidity.singleAtomFamily` has `atomValue ≡ 0` and `atomMass ≡ 1`;
   `CondensationUnification.FiberSplitting.witness` sets `mass ≡ 0`;
   `FoldedSpectrum.ScalarSecondMoments.witness` sets `moment ≡ 0`. Eight `.witness`
   definitions in `StratificationConfounding` alone set every field to 1 or 1/2.
   None of these is wrong; the finding is that **inhabitation witnesses in this
   bucket cluster at points where the quantity they witness is exactly zero**, and
   a coverage percentage that counts a witness as a covered real-valued definition
   is counting a definition whose value no generative process can move.
3. **The residual naming in `JetBarrier`.** The module, namespace and
   `IsChameleonObservable` still carry the vocabulary of the withdrawn program, and
   `isChameleonObservable_iff` proves the predicate is record equality spelled out
   field by field. The docstring says it is kept only because
   `PolygenicSpectroscopy` states its hard-call comparison in that vocabulary. That
   is a defensible reason to keep a name; it is not a reason for the name to keep
   promising a barrier.
4. **The `covarianceScoreInformation_gaussian` phantom member** in families.py's
   `portability_permeability_and_completion` list — §3 above. Not inflation, a
   bookkeeping defect, but it inflates a member count.

## 6. On `Conventions.lean` and the migration-convention question

The lead asked me to treat convention definitions in `Conventions.lean` with care
and to note anything that looks like a second disagreement of the same kind as the
running factor-of-two migration dispute.

**I did not find a second unsettled convention disagreement inside
`Conventions.lean`.** What is there is a settled one and two cross-module ones:

* **Nei versus Hudson is settled and documented.** `neiGst` computes Nei's `G_ST`,
  `hudsonFst` the Hudson ratio-of-averages, `hudsonFst_eq_of_neiGst` gives
  `Hudson = 2G/(1 + G)`, and the docstring records that the old `hudsonFst` name
  once sat on the Nei body and was removed rather than retained. The ratio between
  the conventions is documented as running from 2.0 at the small-differentiation
  end down toward 1, so a mix-up cannot be absorbed by a recalibration constant.
  This is the corpus at its best and I have nothing to add.
* **The migration-convention hub is single-sourced by design.** The
  `EquilibriumAgreements` section states that `fstMigrationDriftEquilibrium` is the
  one definition of `1/(1 + 4 Nₑ m)`, that a second spelling "would carry its own
  factor of four with nothing to hold it in step", and ties it to
  `scaledMigrationRate` by `fstMigrationDriftEquilibrium_eq_scaled`. The
  factor-of-two exposure is therefore concentrated in `ploidy` and
  `coalescentTimeScale`, each with exactly one bridge theorem per inlining
  definition. **If the running simulation settles the migration convention against
  the corpus, `Conventions.lean` is the file where the change costs one line** —
  which is what that section was built for.
* **The assortative-mating disagreement is settled and one side deleted.**
  `amInflationFactor r = 1/(1 − r)` versus `amEquilibriumVariance V_A r h² =
  V_A/(1 − r h²)`; forward simulation put the second within −5% to +1% and the
  first between +3% and +82% high, and the first is gone. The docstring records why
  the disagreement was invisible: the two coincide exactly at `h² = 1`, the only
  case anyone would check by inspection.

**The thing in this bucket that most resembles a second convention disagreement is
not in `Conventions.lean`.** It is
`StratificationConfounding.r2EstimatorVariance`'s status line versus its own
measured table — §F1 above. It is a claim-versus-evidence conflict, documented
in-file by whoever measured it, addressed to the file's owner, and still open.

The other structural hazard is the four hub primitives — §3 above. A hub is
coverage-neutral, and a mechanical membership pass will credit it as covered and
raise a percentage without measuring anything.

---

## 7. Summary of the ranked list

Counts are CHECKABLE members. Predicates and sampler constructors a family also
consumes are noted in parentheses and are counted in (c), not here, so the checkable
column sums to 198 without double counting.

| rank | family | checkable | new simulator | live disagreement or suspect definition inside |
|---|---|---:|---|---|
| — | (a) existing families, membership edit | 45 | none | phantom member `covarianceScoreInformation_gaussian` |
| 1 | `confounded_estimator_bias` | 34 | cheap, linear-Gaussian | YES — `r2EstimatorVariance` status line contradicts its own table |
| 2 | `bundle_spectrum_identifiability` | 49 (+16) | medium | YES — `falsifierP`/`falsifierQ` are a named falsifier never evaluated |
| 3 | `haplotype_phase_and_local_ancestry` | 20 | cheap, forward pedigree | built-in positive control from the settled tract-length falsification |
| 4 | `overlap_spectrum_null` | 17 (+11) | cheap | YES — the circulant witness is the file's whole load-bearing example |
| 5 | `exp_functional_transport_identities` | 26 | medium | second-moment vs covariance matrix in `optimalWeightsFromMoments` |
| 6 | `orientation_arrow_information` | 12 | cheapest | YES — `m` "independent" pairs from a chain that does not supply them |
| 7 | `moment_ladder_squaring_tower` | 15 | medium | `squaringFixedPoint` attractivity is unproved |
| 8 | `temporal_portability_decay` | 12 | cheap | three channels composed into one exponential, untested |
| 9 | `linear_scm_intervention_contrasts` | 7 (+2) | trivial | YES — three `NOT AN EMPIRICAL CLAIM` labels on measurable reals |
| 10 | `lattice_exceedance_inflation` | 3 (+5) | cheap | YES — measures the named hypothesis the corpus declines to prove |
| 11 | `covariance_pencil_relaxation` | 3 (+5) | cheap | decidable 4-state counterexample as positive control |
| | **new-family total** | **198** | | |

198 checkable definitions across eleven new families, 45 into existing families, 14
already members, 61 category errors of which 20 route to a consuming family by F3
rather than being parked. Nothing marked unsimulatable-as-stated, and §2 says why
that is the honest answer rather than an omission.

**If only three of these are built, build 1, 6 and 10.** Family 1 is the largest
cheap one and has a documented claim-versus-evidence conflict waiting inside it;
family 6 is a two-state Markov chain covering twelve definitions that landed
yesterday and has a premise that its own natural sampling scheme may not supply;
family 10 is three definitions but it is the only arm in this bucket that turns a
hypothesis the corpus explicitly declines to prove into a measurement.
