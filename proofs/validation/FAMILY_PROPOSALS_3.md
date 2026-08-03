# Family proposals, bucket 3

Classification of the definitions in the bucket led by `Probability.lean`,
`PCCorrectability/ImitationCapacity.lean`, `MetricSpecificPortability.lean`,
`ImitationRigidity.lean`, `GeneticArchitectureDiscovery.lean`,
`ProjectionShiftBounds.lean`, `BundleRigidity/Operator.lean`,
`ScoreDistribution.lean`, `PowerAnalysis.lean`, `CovarianceStructure.lean`,
`BundleRigidity/SingleModulus.lean`, `FiniteMinimax.lean`,
`AncestrySpecificPower.lean`, `PCCorrectability/Diagnostic.lean`, and the rest
of the `PCCorrectability/` group (`Core`, `Frequency`, `Overlap`, `Phase`,
`Threshold`, `Unified`).

**Scope, and what it is not.** Twenty files, **258 `def`/`abbrev`
declarations**, every one of them classified exactly once — the assignment was
built as a partition and checked to be one (no definition unassigned, no name
assigned twice, no name in a member list that is not in the tree). The brief
named 265; the 7-definition difference is a source-parse-versus-`defs.json`
difference and possibly corpus drift, not a set of definitions silently
dropped. The seven-file slice is excluded entirely and no module led by a
sibling agent (`PGSCalibrationTheory`, `TransferLearningPGS`, `Permeability`)
is touched.

**Ownership left open, deliberately.** `BundleRigidity/` has thirteen further
files (`Coverage`, `CoverageInvariance`, `Cycles`, `DeploymentCeiling`,
`Dichotomy`, `EntropySplit`, `Freshness`, `LinearSCM`, `Realizability`,
`Telescope`, `TwoAtom`, plus `BundleRigidity.lean` itself) holding about 43
further definitions. Only `Operator` and `SingleModulus` were named for this
bucket, so the rest are **not classified here** rather than duplicated. If no
sibling holds them they are an unclaimed remainder of roughly 43 definitions
and someone should be told.

Declarations are cited by **file and declaration name**. No line numbers: they
moved measurably within the hour on 2026-08-03.

---

## The headline

| outcome | defs | share |
|---|---:|---:|
| **(a)** joins an **existing** family | **62** | 24% |
| **(b)** belongs to a **new** family | **140** | 54% |
| **(c)** makes **no empirically checkable claim** | **36** | 14% |
| **(c′)** checkable in type, **unsimulatable as stated** | **20** | 8% |
| | **258** | |

Two facts dominate everything below.

**First: five simulators for this bucket already exist and are not in
`families.py`.** `empirical/pc_correctability/` (`bn_independent.py`,
`which_fst_inversion.py`, `which_fst.py`, `coalescent.py`, `analyze.py`),
`empirical/imitation_rigidity/check_imitation.py`,
`empirical/block_count/block_count_sim.py`,
`empirical/ridge_direction/ridge_direction.py` and
`empirical/meff_error_floor/check_meff_error_floor.py` all simulate definitions
in this bucket, against ground truth, today. Nothing in `families.py` refers to
any of them. Four of the twelve proposed families are therefore **registration
work, not simulator work** — which is the same finding
`COVERAGE_DENOMINATOR.md` reached about the 26 unfamilied in-slice statements,
reached again one level out.

**Second: 62 of the 258 fall into six families that are already SIMULATED AND
GREEN.** `hwe_genotype_score` alone absorbs 22 — the whole
Hardy-Weinberg/Berry-Esseen spine of `Probability.lean` plus the score moments
of `ScoreDistribution.lean` — against a simulator whose own status note calls
it "the only one whose reference is exact rather than asymptotic". That is the
cheapest coverage available anywhere in this bucket and it should be done
first.

---

## (a) Definitions that join an existing family — 62

Membership edits only. Each family's simulator must be **re-run** afterwards so
the credit is earned rather than asserted.

### `hwe_genotype_score` (+22) — `cluster/fam_metrics.py` (hwe arm), GREEN

The family's stated model is "Hardy-Weinberg genotypes at m independent loci, a
polygenic score as a weighted allele count; its exact mean and variance and the
error of the Gaussian approximation to its distribution". That is a literal
description of `Probability.lean`'s HWE section, which was never joined to it.

From `Calibrator/Probability.lean`: `altAlleleCount`,
`HardyWeinbergModel.witness`, `HardyWeinbergModel.refFreq`,
`HardyWeinbergModel.genotypeProb`, `HardyWeinbergModel.expectedAltAlleleCount`,
`HardyWeinbergModel.centeredAltAlleleCount`,
`HardyWeinbergModel.genotypeVariance`,
`HardyWeinbergModel.genotypeThirdAbsMoment`, `HWEScoreModel.scoreMean`,
`HWEScoreModel.scoreVariance`, `HWEScoreModel.scoreThirdAbsMomentBound`,
`berryEsseenErrorBound`, `HWEScoreModel.berryEsseenErrorBound`,
`approximationInterval`, `Phi`.

From `Calibrator/ScoreDistribution.lean`: `pgsMean`, `pgsVariance`,
`pgsMeanShift`, `externallyStandardized`, `internallyStandardized`.

From `Calibrator/AncestrySpecificPower.lean`: `genotypeVarianceHWE`,
`hweHeterozygosity`.

**Two new can-fail requirements come with this membership, and without them the
join is cosmetic.**

*(i) The Berry-Esseen arm must bind.* The family already measures the
Kolmogorov distance between the standardised score and the standard normal, on
a grid that reaches KS 0.536 at `m = 1, p = 0.01`. It does not compare that
distance to `HWEScoreModel.berryEsseenErrorBound`. Doing so is one line and it
can fail in both directions: at `C = 0.4748` and small `m` the bound may be
larger than 1 and vacuous, and at large `m` it may be **violated** if the
third-absolute-moment sum is mis-assembled. A bound nobody has ever compared
to a measurement is not a validated bound.

*(ii) `pgsVariance` must be exercised where the identity is allowed to break.*
The record here was corrected on 2026-08-03 (commit `cd30fcc9`, which corrects
`ad2fa5ba`). With weights `braw = beta / sqrt(2p(1-p))`, the body
`∑ β² · 2p(1-p)` collapses **identically** to `∑ beta²` under the stated
linkage-equilibrium assumption, so the predicted ratio to the true score
variance is exactly 1.000 with zero scatter, and the previously committed
"0.969, about three per cent low, the direction its assumption predicts" was
wrong in **both** halves: 0.969 sat about 1.8 standard errors from 1.000, and
cross terms being zero-mean over the beta draw puts the expected ratio slightly
**above** 1 by Jensen, not below. **The consequence for this family is a design
constraint, not a note:** a cell run in linkage equilibrium cannot fail, so it
must not be scored. The only informative cells put genuine LD among the causal
variants and read the deviation, and the deviation must not move with `h2` —
`h2` enters the phenotype and never the score variance, so movement there
indicts the pipeline, not the formula.

### `ascertainment` (+12) — `cluster/fam_ascertainment.py`, SIMULATED

Five of these (`discoveryNCP`, `noncentralityParam`, `powerAtThreshold`,
`effectiveFisherInformation`, `standardErrorSq`) are already declared members;
they are listed here because this bucket is where they physically live —
`Calibrator/GeneticArchitectureDiscovery.lean`, `Calibrator/PowerAnalysis.lean`
and `Calibrator/AncestrySpecificPower.lean` — which the family entry does not
record, and a membership list that does not say which file a member is in is
what let the earlier stale list survive.

Genuinely new, from `Calibrator/AncestrySpecificPower.lean`:
`fisherInformation`, `ncp`, `portableFraction`, `proportionalAllocation`. From
`Calibrator/PowerAnalysis.lean`: `GWASObservationModel.witness`,
`GWASObservationModel.standardError`, `GWASObservationModel.observedBeta`.

The `GWASObservationModel` triple is the structure form of exactly the process
the simulator's control (1) already runs (sampling variance alone, no threshold
and no LD), so it is covered by a cell that exists.

### `liability_threshold_metrics` (+13) — `cluster/fam_metrics.py` (liability arm), GREEN

From `Calibrator/Probability.lean`: `latentLiability`, `diseaseEvent`,
`etaLiabilityThreshold` — the liability decomposition `s + e` and the
threshold-crossing event, which is the family's generative process stated in
Lean.

From `Calibrator/MetricSpecificPortability.lean`: `R2DecompositionData.witness`,
`R2DecompositionData.r2`, `R2DecompositionData.discrimination`,
`R2DecompositionData.calibration`, `brierDiscriminationLoss`,
`brierCalibrationLoss`, `brierScoreMetric`, `metricPPV`,
`sensitivityPortabilityGap`, `ppvPortabilityGap`.

**Required new control.** The family's Brier arm currently measures the
*calibrated* Brier risk `π(1-π)(1-R²)`. The Murphy decomposition into
`brierDiscriminationLoss` and `brierCalibrationLoss` is a **sum**, and the
family's own spec says a combined check on a sum passes when the two terms are
swapped. Split controls, both cheap: a perfectly calibrated score must drive
`brierCalibrationLoss` to exactly 0 with the discrimination term unchanged, and
a score with no discriminating information (constant at the prevalence) must
drive `brierDiscriminationLoss` to exactly 0. `metricPPV` needs the prevalence
swept independently of sensitivity and specificity, or an error in the base
rate and an error in sensitivity cancel in the product.

### `estimator_moments` (+7) — `cluster/fam_metrics.py` (moments arm), GREEN

From `Calibrator/Probability.lean`: `mseRisk`, `predictionRiskY`,
`ConditionalMeanDGP.witness`, `ConditionalMeanDGP.toDGP`. These are the same
MSE-against-a-DGP quantity the family already decomposes, and the family's
existing split controls (oracle predictor, zero noise) apply unchanged.

From `Calibrator/PCCorrectability/ImitationCapacity.lean`: `weightedMean`,
`energyWeightedVariance`. From `Calibrator/ImitationRigidity.lean`:
`fairTwoPointVariance`. Plain weighted first and second moments; they belong
with the other moment conventions, and like them they fix a **denominator
convention** that every downstream consumer inherits.

### `ld_decay_recurrence` (+4) — `cluster/fam_ld_decay.py`, SIMULATED

From `Calibrator/ImitationRigidity.lean`: `stationaryLDEntry`, `markovLDStep`.
`stationaryLDEntry_eq_ldAfterGenerations` proves `stationaryLDEntry` is
`ldAfterGenerations` at unit initial LD, and `ldAfterGenerations` is already a
member — so this is the same quantity under a second name and the family's
control (a) at `c = 0` pins it.

From `Calibrator/CovarianceStructure.lean`: `ldCorrelationSq`,
`ldCorrelationSqOfHaplotypeD`. `r² = D²/(p_i(1-p_i)p_j(1-p_j))` is the
denominator convention of the family's own `sigma_d²` measurement, and the two
bodies exist under two names, which is precisely the situation the family
should be resolving rather than inheriting.

### `admixture` (+4) — `cluster/fam_admixture.py`, SIMULATED

From `Calibrator/CovarianceStructure.lean`: `haplotypeFreqAdmixed`,
`admixtureLDTwoLocus`, `admixtureLDAtGen`, `admixtureLDMagnitude`. The family
already covers `admixtureLD`; these are the two-locus haplotype form and its
per-generation decay `(1-r)^g`, which the family's pulse-admixture process
produces directly. `admixtureLDAtGen` and `admixtureLDMagnitude` take a
generation count `g` that the family's existing members do not, so — exactly as
with the finite-deme corrections in `island_migration_fst` — these are the
members that take the argument the simulator already varies.

---

## (b) New families — 140 definitions in twelve families

Ranked. Rank is members-covered × simulator-cheapness, promoted where a live
disagreement or a self-declared untested claim sits inside.

---

### 1. `bbp_spike_detection` — 28 members

**Generative process.** Draw an `n × M` genotype panel in which a demographic
contrast of subgroup size `m` at divergence `F_ST` induces a single rank-one
spike on top of isotropic noise, and diagonalise the `n × n` sample relatedness
matrix. Sweep `n`, `M`, `F_ST` and `m` across the Baik–Ben Arous–Péché edge so
that the leading sample eigenvector is sometimes informative about the
contrast and sometimes pure noise.

**Members.** `Calibrator/PCCorrectability/Overlap.lean`: `samplePCOverlapSq`,
`samplePCResidualAxisFraction`. `.../Threshold.lean`: `bbpProxyThreshold`,
`demographicSpike`, `effectiveSubgroupSize`, `pcCorrectabilityMargin`.
`.../Phase.lean`: `markerDangerIndex`, `EmpiricalPCOverlapModel.witness`.
`.../ImitationCapacity.lean`: `spikeOuter`, `spikeLoad`, `headroom`, `spiked`,
`exitLevels`, `imitationCapacity`, `frobeniusForm`, `traceForm`,
`traceWindowBudgetClass`, `diagonalEntryClass`, `EquiExit.witness`, `margin`,
`rejectionThreshold`, `traceWindowClass`, `diagonalGapForm`, `diagonalGapClass`,
`subgroupContrast`, `demographicSpikeDirection`,
`stratificationCertificateMargin`, `MomentContinuousFunctional.witness`.

**Measured.** Squared overlap between the leading sample eigenvector and the
true contrast direction; the empirical detection boundary in `(F_ST, m, n, M)`;
the recovered spike divided by `F · m(n-m)/n`; the residual axis fraction.

**Falsifiers, three of them, and the third is the reason this family ranks
first.**

1. `samplePCOverlapSq` writes `c = n/M` — samples over markers, the reciprocal
   of the usual Johnstone aspect ratio — and puts the edge at
   `bbpProxyThreshold = √(n/M)`. **Refuted if** the measured overlap follows
   `(1 - γ/λ²)/(1 + γ/λ)` at `γ = M/n` instead, or if the measured edge sits at
   `√(M/n)`. The two disagree by orders of magnitude whenever `n ≠ M`, so a
   grid with `n ≈ M` decides nothing and must be excluded.
2. `demographicSpike = 4·F·m(n-m)/n`. **Refuted if** the inverted spike/`F`
   ratio departs from 4. The docstrings already record 3.9920 ± 0.0045 and
   3.95–4.06 from `bn_independent.py` and `which_fst_inversion.py`, so this arm
   is *already measured and passing*; it is listed because a family whose
   passing cells are undocumented cannot be told from one that has none.
3. **The live disagreement.** `stratificationCertificateMargin
   headroom n M F m = demographicSpike n F m - (headroom + bbpProxyThreshold n M)`,
   with `stratificationCertificateMargin_zero_headroom` proving
   `pcCorrectabilityMargin` is its zero-headroom special case. Its own
   docstring says: "UNTESTED. Falsifiable against a simulation that varies the
   trace-window budget at fixed `n`, `M`, `F`: the detection boundary must move
   with `headroom`, which `pcCorrectabilityMargin` predicts it does not." Two
   definitions in one corpus make opposite predictions about the same measured
   boundary. **The simulator that varies the background budget at fixed
   `(n, M, F)` decides which is wrong**, and no cell in the corpus currently
   varies it.

**Cheapness.** A Gaussian matrix and one `eigh`. `bn_independent.py` and
`which_fst_inversion.py` already do arms 1 and 2; only arm 3 is new code.

---

### 2. `ar1_ld_kernel_frontier` — 26 members

**Generative process.** Simulate a chromosome of `nSites` variants whose LD
correlation is the stationary first-order Markov kernel `ρ^|i-j|` — a
Kac–Murdock–Szegő Toeplitz matrix — either by Markov haplotype propagation
along the chromosome or by direct construction, then take its exact spectrum
and inverse. Sweep `ρ` from 0 to near 1 and `nSites` from small to large, and
prune a low-frequency band of relative width `κ`.

**Members.** `Calibrator/ImitationRigidity.lean`: `ldKernelSymbol`,
`ldHardEdge`, `ldWhiteningGain`, `ldPrecisionTrace`.
`Calibrator/PCCorrectability/ImitationCapacity.lean`: `traceWindowSpikeLoad`,
`whitenedCapacity`, `inverseTraceCertificate`, `normalizedMoment`,
`blockSpectrum`, `meffPerturbed`, `meffFlat`.
`Calibrator/MetricSpecificPortability.lean`: `ldBandReconstructionShare`,
`ldBandDetectionShare`, `ldPruningDetectionDeficit`, `ldPanelRetentionFraction`,
`ldBlockDetectionShare`, `ldBlockPruningDeficit`,
`ldTightLinkageDetectionShare`. `Calibrator/ProjectionShiftBounds.lean`:
`detectionWeight`, `reconstructionWeight`, `wienerWeight`, `spectralCapture`,
`spectralTotal`, `reconstructionEfficiency`, `detectionEfficiency`,
`pruneAllocation`.

**Measured.** Smallest and largest eigenvalues of the finite `nSites × nSites`
kernel; `tr K⁻¹` exactly; the sum of `λ` and of `1/λ` over the retained band as
a fraction of the total; the ratio of detection to reconstruction share at
matched `κ`.

**Falsifiers.**

* `ldHardEdge ρ = (1-ρ)/(1+ρ)` is proved in Lean to be a lower bound on the
  **symbol** and attained at `θ = π`. Nothing proves it bounds the **finite
  matrix**. **Refuted if** the measured smallest eigenvalue at any `nSites`
  falls below it. The Toeplitz-versus-symbol gap closes only as `1/nSites`, so
  the `nSites` grid must start small (8, 16, 32) — a grid of large `nSites`
  validates the limit by construction and is the failure mode to avoid.
* `ldPrecisionTrace ρ n = (n(1+ρ²) - 2ρ²)/(1-ρ²)` is asserted to be the
  **exact** finite trace of the inverse, from a boundary-row stencil argument.
  This is the sharpest falsifier in the family: build the matrix, invert it,
  take the trace, and require agreement to machine precision, not to a
  tolerance. **Refuted by any disagreement at all.** It also fixes the finite-`n`
  boundary correction `-2ρ²/(1-ρ²)`, which `ldWhiteningGain` drops in the limit;
  a grid confined to large `n` cannot see the correction and validates the
  wrong thing.
* `ldBandDetectionShare ρ κ = κ - 2ρ sin(πκ)/(π(1+ρ²))` and
  `ldBandReconstructionShare ρ κ = (2/π)·arctan(((1+ρ)/(1-ρ))·tan(πκ/2))`.
  These make a **sign-opposed** prediction — pruning a band of relative width
  `κ` costs *less* than `κ` of detection weight and *more* than `κ` of
  reconstruction weight. **Refuted if** the measured shares fall on the same
  side of `κ`, which no amount of overall scale error can produce and which
  therefore cannot be faked by a mis-normalised simulator.
* Split control: at `ρ = 0` every one of these collapses (hard edge 1,
  whitening gain 1, both band shares exactly `κ`), isolating the band geometry
  from the correlation; at `κ = 1` both shares must be exactly 1, isolating the
  normalisation from the geometry.

**Cheapness.** `numpy.linalg.eigvalsh` on a `1000 × 1000` matrix.
`empirical/imitation_rigidity/check_imitation.py` already covers `ldHardEdge`,
`ldWhiteningGain` and `ldPrecisionTrace`; the band-share arm is new and is the
larger half of the members.

---

### 3. `stratification_bias_transmission` — 16 members

**Generative process.** A confounded GWAS: a phenotype carrying an
ancestry-gradient component uncorrelated with any causal genotype, marker
effects estimated with and without regressing out the top `K` sample PCs, and a
PGS built from the estimated effects. Sweep the confounding magnitude, the
number of PCs removed, `n`, and the marker count.

**Members.** `Calibrator/PCCorrectability/Diagnostic.lean`: `pgsTestAxisBias`,
`ancestryGradientSusceptibility`, `pcTargetAxisEfficacy`,
`ascertainmentAmplification`, `pgsStratificationRiskCoefficient`,
`standardizedResidualPGSBias`, `criticalConfoundingMagnitude`.
`.../Core.lean`: `PCCorrectionModel.witness`, `PCCorrectionModel.residualBias`,
`PCCorrectionModel.uncorrectedBias`, `PCCorrectionModel.removeTopPCs`,
`PCCorrectionModel.residualBiasEnergy`, `RecentFineScaleConfounding.canonical`,
`spectralResidualBiasEnergy`. `.../Phase.lean`:
`EmpiricalPCOverlapModel.residualBiasEnergy`. `.../Unified.lean`:
`modeledPCResidualSusceptibility`.

**Measured.** The bias in the PGS along the ancestry axis before and after PC
correction; the residual bias energy as a function of `K`; the confounding
magnitude at which the residual bias equals the true signal.

**Falsifiers.**

* `markerDangerIndex confounding n markers = confounding·√(markers/n)` and
  `pgsStratificationRiskCoefficient` predict that residual PGS bias grows as
  `√M` at fixed `n`. **Refuted if** the measured residual bias is flat or
  decreasing in the marker count. The direction is the whole claim, so a
  single-`M` grid tests nothing.
* `Phase.lean`'s `adding_subthreshold_pc_can_increase_total_error` asserts
  non-monotonicity in `K`. **Refuted if** the measured total error is monotone
  decreasing in `K` over the whole feasible range — that is, if the predicted
  regime where a sub-threshold PC costs more variance than it removes bias
  cannot be reached at any parameter setting. This is the family's positive
  control in reverse: it must find the non-monotone regime or the claim is
  vacuous in practice.
* Split control: at zero confounding the residual bias must be exactly 0 for
  every `K`, isolating the estimator from the confounding model; at `K = 0`
  the residual bias must equal `uncorrectedBias` exactly, isolating the
  correction from the bias model.

**Note on `modeledPCResidualSusceptibility`.** It composes the diagnostic
susceptibility with `samplePCOverlapSq`, so it is the one definition that
straddles this family and `bbp_spike_detection`. The mapping is legitimately
many-to-many; it is listed here because its *measurement* is a bias, not an
overlap, and it is the composition of the two families that a simulator
covering both must check.

---

### 4. `pgs_learning_curve` — 13 members

**Generative process.** Train a PGS by OLS or ridge on `n` samples over `m`
markers at heritability `h2` with `k` causal loci, and evaluate out-of-sample
`R²` on held-out data. Sweep `n` over at least two decades at fixed `m` and at
fixed `m/n`.

**Members.** `Calibrator/PowerAnalysis.lean`: `r2ScalingModel`,
`logarithmicRiskBenchmark`, `fixedGradeRiskBenchmark`,
`logarithmicBenchmarkSampleSize`, `fixedGradeBenchmarkSampleSize`.
`Calibrator/MetricSpecificPortability.lean`: `adaptationDifficultyIndex`,
`fisherTraceMSELowerBound`, `requiredEffectiveSampleSizeForTraceMSE`.
`Calibrator/GeneticArchitectureDiscovery.lean`: `olsEffectEstimationVariance`,
`expectedLinearEffectEstimate`, `perCausalLocusSignal`,
`taggedScoreEstimationRisk`, `ctMissedTargetSignal`.

**Measured.** Out-of-sample `R²(n)`; the empirical `n` required to reach a
target risk `ε`; the trace of the estimator's MSE matrix.

**Falsifiers.**

* `fisherTraceMSELowerBound nEff nParams infoPerSample = (nParams/infoPerSample)/nEff`
  is a **lower bound**, so it has a sign. **Refuted if** the measured trace-MSE
  of any estimator falls below it. This is the strongest falsifier in the
  family precisely because it is one-sided: an estimator that beats a claimed
  Cramér–Rao-style floor kills the claim outright, and a well-conditioned ridge
  estimator at `nParams ≫ nEff` is exactly where a naive orthogonal-Fisher
  bound tends to fail.
* `logarithmicBenchmarkSampleSize` and `fixedGradeBenchmarkSampleSize` are
  asserted inverses of `logarithmicRiskBenchmark` and `fixedGradeRiskBenchmark`.
  **Refuted if** composing them numerically does not return the input to
  machine precision — a pure algebra check that costs nothing and that no
  simulation is needed for, and which should be run first because if it fails
  the rest of the family is moot.
* Split control: at `k = 1` causal locus, `perCausalLocusSignal h2 k` must
  equal `h2` exactly, isolating the per-locus split from the learning curve;
  at infinite `n`, `R²` must saturate at `h2` exactly, isolating the curve
  from the ceiling.

---

### 5. `weighted_consensus_correction` — 11 members

**Generative process.** A collection of per-target quadratic costs
`w_i·(x - x_i)²` — one per deployment population — and a single shared scalar
correction `x` that must serve all of them. Draw the curvatures `w_i` and
optima `x_i` from a spread of regimes including near-zero and negative
curvature, and minimise the total cost numerically.

**Members.** `Calibrator/MetricSpecificPortability.lean`:
`targetCorrectionCurvature`, `targetCorrectionOptimum`,
`sharedCorrectionConsensus`, `sharedCorrectionSpread`, `sharedCorrectionCost`.
`Calibrator/ProjectionShiftBounds.lean`: `sharedCorrectionOptimum`,
`irreducibleDegradation`, `coefficientEnergy`, `chiSquareBudget`,
`directionalResidualCurvature`, `weightedResidualMoment`.

**Measured.** The numerical argmin and min of `sharedCorrectionCost` over `x`;
the residual after projecting `theta` onto `beta` in the `B` inner product.

**Falsifiers.**

* `sharedCorrectionConsensus` is claimed to be the argmin of
  `sharedCorrectionCost` and `sharedCorrectionSpread` its minimum value.
  **Refuted if** a one-dimensional numerical minimisation finds a lower cost
  anywhere, at any drawn `(w, x)`.
* `irreducibleDegradation B beta theta = coefficientEnergy B theta -
  (betaᵀBtheta)²/coefficientEnergy B beta` is a Cauchy–Schwarz residual and is
  therefore **non-negative only when `B` is positive semidefinite**. **Refuted
  as stated if** it is used anywhere the corpus does not carry a positive-
  semidefiniteness hypothesis on `B`: draw an indefinite `B`, watch the
  quantity go negative, and the word "irreducible" stops being true. This is
  the family's positive control and it is guaranteed to fire, which is what
  makes the passing cells mean something.
* Split control: `w_i` all equal must give the plain mean, isolating the
  weighting from the averaging; all `x_i` equal must give spread exactly 0,
  isolating the averaging from the weighting.

**Cheapness.** No random process is needed beyond drawing the parameters —
`scipy.optimize.minimize_scalar` and a matrix product. This is the cheapest
family in the bucket and it contains a guaranteed-firing control.

---

### 6. `cross_trait_borrowing` — 10 members

**Generative process.** Two traits with per-locus effect vectors drawn from a
bivariate normal at genetic correlation `rg`, GWAS'd at sample sizes `n₁` and
`n₂`; a score for trait B built partly from trait A's discoveries. Sweep `rg`
from 0 through 1 including negative values, and `n₁/n₂` across two decades.

**Members.** `Calibrator/GeneticArchitectureDiscovery.lean`:
`geneticCorrelation`, `multiTraitEffectiveSampleSize`, `multiTraitDiscoveryNCP`,
`borrowedTraitBCrossCov`, `traitBSpecificCrossCov`, `totalTraitBCrossCov`,
`borrowedTraitBProjection`, `totalTraitBProjection`, `commonOnlyPortableModel`,
`commonAndRarePortableModel`.

**Measured.** The realised power gain from a joint two-trait analysis relative
to trait B alone; the estimated genetic correlation against the one used to
generate; the cross-covariance decomposition into borrowed and specific parts.

**Falsifiers.**

* `multiTraitEffectiveSampleSize n₁ n₂ rg` claims the borrowed analysis behaves
  like a single-trait analysis at that `n`. **Refuted if** the measured
  noncentrality of the joint test at `(n₁, n₂, rg)` differs from the
  single-trait noncentrality at `n_eff`. The grid must include `rg = 0`, where
  the claim reduces to `n_eff = n₂` and any borrowing at all is a defect, and
  `rg < 0`, where naive borrowing must *hurt*. A grid confined to `rg > 0`
  cannot distinguish "borrowing helps by the right amount" from "borrowing
  helps".
* `totalTraitBCrossCov = borrowedTraitBCrossCov + traitBSpecificCrossCov` is a
  **sum**, so a combined check passes with the terms swapped. Split controls:
  `rg = 0` must send the borrowed term to exactly 0; a trait-B-null generative
  draw must send the specific term to exactly 0.

---

### 7. `frequency_resolved_information` — 8 members

**Generative process.** A cohort partitioned into allele-frequency classes,
each with its own sample size, per-allele effect and residual variance; a
weighted meta-analysis across classes at a chosen weight vector. Sweep the
class sample sizes across an order of magnitude so the weights matter.

**Members.** All in `Calibrator/PCCorrectability/Frequency.lean`:
`FrequencyResolvedCohort.witness`, `.classMargin`, `.classInformation`,
`.informationMatchedWeight`, `.totalInformation`, `.weightedSignal`,
`.weightedNoise`, `.weightedInformation`.

**Measured.** The signal-to-noise ratio `weightedSignal²/weightedNoise` of the
combined estimator, as a function of the weight vector.

**Falsifiers.** `informationMatchedWeight` is claimed to be *the* weighting
matched to the per-class information. **Refuted if** a numerical search over
the weight simplex finds a weight vector with strictly higher
`weightedInformation`, or if `totalInformation` does not equal
`weightedInformation` at the matched weight. Both are direct, and the search is
over a handful of dimensions. Split control: all classes identical must make
every weight vector with equal entries optimal, isolating the weighting rule
from the information model.

**Caveat, stated because it lowers the rank.** The `FrequencyResolvedCohort`
structure supplies its per-class information as a field, so the simulator can
check that the *weighting* is optimal **given** the information, but not that
the information is what a real frequency-stratified cohort has. That second
question needs genotypes and belongs to `bbp_spike_detection`'s process.

---

### 8. `ridge_self_consistent_risk` — 8 members

**Generative process.** Draw an `n × k` design from a covariance with a
prescribed eigenvalue spectrum, fit ridge regression at penalty `λ`, and
measure the resolvent functional `tr(B(S + λI)⁻¹)/k`. Sweep the aspect ratio
`k/n` through 1.

**Members.** `Calibrator/ImitationRigidity.lean`: `ridgeBalance`,
`ridgeSelfConsistentStep`, `scalarRowResolvent`, `rankOneCovarianceBump`,
`addRankOneSignal`, `lossGeometryRisk`, `gramForm`, `quadForm`.

**Measured.** The empirical resolvent functional against the value predicted by
the root of the self-consistency equation.

**Falsifier.** `ridgeSelfConsistentStep` is asserted to be a contraction whose
fixed point is the root of `ridgeBalance`. **Refuted if** iterating it fails to
converge, or converges to a `u` at which `ridgeBalance ≠ 0`, at any aspect
ratio. The grid must **straddle `aspect = 1`**: below it the ridge solution is
close to OLS and almost any fixed point lands near the truth, and the
interesting behaviour is at and above the interpolation threshold.

`empirical/imitation_rigidity/check_imitation.py` already runs this arm at a
5% tolerance and `empirical/ridge_direction/ridge_direction.py` settles the
adjacent effective-ridge question in exact rational arithmetic. This is
registration plus an aspect-ratio sweep, not new code.

---

### 9. `finite_decision_minimax` — 7 members

**Generative process.** Enumerate a small finite statistical decision problem —
`|Θ| = 3`, `|X| = 4`, `|A| = 3`, a random stochastic observation kernel and a
random loss matrix — and compute both sides of the minimax identity by brute
force: the primal by minimising worst-case risk over randomised rules (a linear
program), the dual by maximising the optimal Bayes risk over the prior simplex.

**Members.** All in `Calibrator/FiniteMinimax.lean`: `toMixtureExperiment`,
`risk`, `worstRisk`, `minimaxRisk`, `bayesRisk`, `optimalBayesRisk`,
`mixtureDualRisk`.

**Measured.** `minimaxRisk` and `mixtureDualRisk`, independently, on the same
problem instance.

**Falsifier, and why this family is here despite being small.**
`finite_minimax_duality` proves `minimaxRisk = mixtureDualRisk` by separating
the convex set of randomized-rule risk profiles from the open half-space below
the minimax value. Its transitive axiom closure contains only the approved Lean
foundations. Numerical evaluation is therefore a regression test of the
definitions and simulator, not evidence filling a proof gap. **Refuted if** the
two computed values differ on any instance. The informative control remains the
**positive control**: restrict the rule class to *deterministic* rules, where
the duality gap is generically strictly positive, and require the check to
fire. If it does not fire there, the harness is not evaluating the primal at
all. `Rule` is defined as `Fin (observationCount+1) → FinitePrior actionCount`,
i.e. genuinely randomised, so the restriction is a one-line change to the
simulator and cannot be confused with the corpus's own claim.

**Cheapness.** No sampling. `scipy.optimize.linprog` on a problem with a dozen
variables, plus a grid over a 2-simplex. Minutes to write and seconds to run.

---

### 10. `block_normal_approximation` — 6 members

**Generative process.** A polygenic score over `m` markers whose LD correlation
length is `L`, standardised; compare its distributional distance from normality
against a score over `m/L` genuinely independent markers. Sweep `L` and `m`.

**Members.** `Calibrator/ScoreDistribution.lean`: `effectiveBlockCount`,
`residualDiscreteness`, `excursionShapeFactor`, `berryEsseenBound`,
`thresholdStandardizedCoordinate`, `benchmarkHighScoreRate`.

**Measured.** Skewness, Kolmogorov distance and the upper-tail exceedance rate
of the standardised score.

**Falsifiers.** The block reduction claims
`deviation(m, L) = deviation(m/L, 1) = √L · deviation(m, 1)`. **Refuted if**
either equality fails outside Monte-Carlo error. `benchmarkHighScoreRate` is
`1 - Φ(thresholdStandardizedCoordinate)`; **refuted if** the measured
exceedance rate at a far-tail threshold departs from it by more than the
Berry-Esseen bound allows — and the threshold grid must reach the far tail
(`z ≥ 3`), because near the centre every candidate approximation agrees.

`empirical/block_count/block_count_sim.py` already runs this and writes
`block_count_results.json`. **Registration, not simulator work.**

**Why it is separate from `hwe_genotype_score`.** That family's process has
independent loci by construction. This one's process has correlated loci and
the correlation length is the swept parameter. They share a measurement and not
a process, and merging them would let a green cell from the independent arm be
quoted as coverage of the correlated claim.

---

### 11. `wf_absorption_information` — 4 members

**Generative process.** Wright–Fisher forward simulation from initial frequency
`p₀` for `t` coalescent units; record the fraction of replicates in which the
allele has been lost, and the Fisher information about `p₀` carried by the
loss/no-loss indicator alone.

**Members.** All in `Calibrator/ImitationRigidity.lean`:
`alleleLossProbability`, `absorptionInformation`, `absorptionChannelWeight`,
`informationCrossoverTime`.

**Measured.** `P(lost by t)` against `exp(-p₀/(2t))`; the argmax over `t` of the
absorption channel weight.

**Falsifier, and this is a suspicion, not a formality.**
`alleleLossProbability initial time = exp(-initial/(2·time))` **tends to 1 as
`time → ∞`**. Under the neutral Wright–Fisher diffusion the allele fixes with
probability `p₀`, so the true loss probability saturates at `1 - p₀`, strictly
below 1. **Refuted if** the measured long-time loss probability plateaus at
`1 - p₀` while the formula continues to approach 1 — and it must, unless the
definition is scoped to the rare-allele branching limit where `p₀ → 0` makes
the two agree.

`empirical/imitation_rigidity/check_imitation.py` already runs this arm, at
`p₀ ∈ {0.004, 0.010}` and `τ ∈ {0.5, 1.0, 2.0}` with a 0.03 tolerance. **That
grid cannot fail**: at `p₀ = 0.01` the fixation deficit is 0.01, one third of
the tolerance, and at `τ ≤ 2` the exponential has not saturated. The required
change is a grid extension, not a new simulator: `p₀` up to 0.3 and `τ` out to
8, where the two predictions differ by 30% and no tolerance can absorb it.

---

### 12. `ldsc_intercept_regression` — 3 members

**Generative process.** Simulate a GWAS on a genome with known LD scores under
a polygenic model with known `h²` and known confounding inflation, and regress
the per-marker `χ²` on the LD score.

**Members.** `Calibrator/CovarianceStructure.lean`: `ldsrExpectedBetaSq`,
`ldsrExpectedChi2`, `numBlocks`.

**Measured.** The slope and intercept of the `χ²`-on-LD-score regression.

**Falsifier.** `ldsrExpectedChi2 N h2 M ell_j a = N·h2·ell_j/M + a`. **Refuted
if** the fitted slope is not `N·h²/M` or the fitted intercept is not the
simulated confounding `a`. Split controls, both essential: at `a = 0` the
intercept must come out at exactly 1 (or exactly 0, depending on which
convention the definition intends — and **that ambiguity is itself the finding**,
since the body adds a bare `a` with no `1 +`, so a simulator will settle whether
the corpus's intercept is the LDSC intercept or the LDSC intercept minus one);
at `h2 = 0` the slope must be exactly 0.

Ranked last only for size. `empirical/ldsc_diff/` exists and should be checked
for overlap before writing anything.

---

## (c) No empirically checkable claim — 36 definitions

By the corpus's own rule (test **F1** in
`empirical/differential/cluster/families.py`, `falsify_unsimulatable`): a
declaration is checkable when it denotes a real, a vector or matrix of reals,
or a structure whose fields are reals. These 36 do not, and demanding a
simulator for them is asking what population a proposition is a claim about.

| kind | n | examples |
|---|---:|---|
| `Prop` | 15 | `IsNull`, `Active`, `ConstantDiagonal`, `ShiftInvariant`, `VarianceNonneg`, `BelowCeiling`, `gwasDiscovered`, `GWASObservationModel.isSelected`, `HasThresholdSetAtEveryRank`, `SameTransfer`, `IsSymmetry`, `IsTauOdd`, `IsTauEven`, `IsInvariantFn`, `HasTaskIndependentSpectralPortabilityScalar` |
| type alias / `abbrev` | 6 | `UnitProb`, `Phenotype`, `PGS`, `PC`, `Predictor`, `Rule` |
| `Measure` | 4 | `bernoulliMeasure`, `stdGaussianMeasure`, `stdNormalProdMeasure`, `noiseMeasureGivenX` |
| `Finset` / `Submodule` | 6 | `lassoActiveLoci`, `plusSide`, `minusSide`, `FrequencyResolvedCohort.correctableClasses`, `PCCorrectionModel.topPCSpan`, `PCCorrectionModel.fineScaleSubspace` |
| `ℕ`, `ℕ → ℕ`, `ℕ → ℝ` index constructions | 3 | `meffSize`, `adjacentBoundarySeparation`, `twoBlock` |
| coercions / equivalences / polymorphic plumbing | 2 | `DiploidGenotype.equivFin3`, `unitProbToNNReal` |

**`Probability.lean` is the module the brief anticipated, and the number is
worse than "heavy".** Of its 38 definitions, **15 — 39 per cent — are category
errors**: five type aliases (`UnitProb`, `Phenotype`, `PGS`, `PC`, `Predictor`,
each `def Phenotype := ℝ`-style plumbing that denotes a *type*, not a number),
four `Measure`-valued constructions, two `ENNReal`-valued KL divergences
(`bernoulliKL`, `klBern`), one `NNReal` coercion, one type equivalence, and two
polymorphic `Pop` combinators (`Pop.pair`, `Pop.withTarget`) that are generic in
`α : Sort*` and so cannot denote anything. `poly_n` is `x ↦ x^n` — a monomial,
scaffolding for a Weierstrass argument. **No family should be forced onto any
of it.** The remaining 23 definitions of `Probability.lean` are the
Hardy-Weinberg genotype model, the Berry-Esseen apparatus and the liability
threshold, and all 23 route into three families that already have green
simulators. That is the honest split: `Probability.lean` is not
"measure-theoretic scaffolding", it is 60 per cent real content sitting behind
40 per cent scaffolding, and the scaffolding is what a naive count of the
module would have inflated.

The two KL divergences deserve a sentence rather than a bullet. `bernoulliKL`
and `klBern` return `ENNReal`, which fails F1's marker set, but a KL divergence
between two Bernoullis *is* a number a simulator could estimate. They are
classified (c) **by the corpus's rule, under protest**: if a future revision
widens F1 to include `ENNReal`, these two move into a family and nothing else
in this bucket does. Recording the disagreement is cheaper than silently
resolving it.

---

## (c′) Checkable in type, unsimulatable as stated — 20 definitions

These denote reals or real-valued functionals and so pass F1, but **no
generative process can produce a different value for them**, which is the
condition the brief set. Marking them is a finding about the definitions.

### `BundleRigidity/Operator.lean` — all 13, unsimulatable as stated

`modulusMap`, `coTransfer`, `coTransferₗ`, `transfer`, `diracAt`, `pullback`,
`evenPart`, `oddPart` are constructions in the space of continuous linear
functionals on `C(T, ℝ)`; `SameTransfer`, `IsSymmetry`, `IsTauOdd`,
`IsTauEven`, `IsInvariantFn` are `Prop`s (counted in this 13, not in the 36
above, because the module is being ruled out as a unit).

**Why no falsifier exists.** `evenPart τ κ = (κ + κ∘pullback τ)/2` and
`oddPart` its complement. On a finite `T` these are vectors and the
decomposition is a two-line linear-algebra identity that Lean has already
proved. A simulator would evaluate the same expression twice and compare it to
itself. There is no external process — no sampling, no dynamics, no reference
implementation — whose disagreement would mean anything. **The claim being made
is definitional, and a definitional claim has no empirical content.**

The one thing that could be measured is whether the *bundle* `F : BundleFamily T d`
these functionals act on is ever instantiated at real data, and it is not
within this module. If another agent finds a `BundleFamily` built from measured
PGS transfer curves, this module becomes simulatable and this classification
should be revisited.

### `BundleRigidity/SingleModulus.lean` — 7 of 9, unsimulatable as stated

`SingleModulus.witness`, `wPlus`, `wMinus`, `threeAtom`,
`threeAtomWitness_threeFifths`, `threeAtomAtOne`, `fourAtom`. (`plusSide` and
`minusSide` are `Finset`-valued and are in the 36.)

**Why no falsifier exists.** `threeAtom` and `fourAtom` take their defining
constraints *as hypotheses* — `hA : A² = 1 + v`, `hB : B² = 1 - v`,
`hr : B = A·r` — and return a `SingleModulus` structure. The constraints are
not predictions to be tested; they are preconditions the caller must discharge,
and Lean has discharged them. A simulator that re-evaluated `A² - (1+v)` would
be checking floating-point arithmetic, not the corpus.

**What would make them simulatable, and it is a real suggestion.** These are
atomic measures with prescribed low-order moments. If the corpus stated that a
*measured* LD or effect-size spectrum is approximated by such an atomic measure
to some accuracy, that would be a claim with a generative process behind it. As
written, they are existence witnesses for an algebraic dichotomy, and existence
witnesses are proved, not measured.

---

## Ranked summary

| # | family | members | new? | simulator status | live disagreement inside |
|---|---|---:|---|---|---|
| 1 | `bbp_spike_detection` | 28 | new | 2 of 3 arms exist in `empirical/pc_correctability/` | **yes** — `stratificationCertificateMargin` vs `pcCorrectabilityMargin` on headroom |
| 2 | `ar1_ld_kernel_frontier` | 26 | new | half exists in `imitation_rigidity/check_imitation.py` | finite-`n` hard edge unproved; band-share sign claim untested |
| 3 | `hwe_genotype_score` | +22 | existing | GREEN, exact reference | `pgsVariance` is an identity, so the LE cells cannot fail |
| 4 | `stratification_bias_transmission` | 16 | new | none | non-monotonicity in `K` asserted, never reached |
| 5 | `liability_threshold_metrics` | +13 | existing | GREEN | Murphy decomposition is a sum with no split control |
| 6 | `pgs_learning_curve` | 13 | new | none | `fisherTraceMSELowerBound` is one-sided and beatable |
| 7 | `ascertainment` | +12 | existing | SIMULATED | — |
| 8 | `weighted_consensus_correction` | 11 | new | none — cheapest to write | **yes** — `irreducibleDegradation` goes negative at indefinite `B` |
| 9 | `cross_trait_borrowing` | 10 | new | none | borrowing at `rg < 0` must hurt; never tested |
| 10 | `frequency_resolved_information` | 8 | new | none | optimal-weight claim never optimised against |
| 11 | `ridge_self_consistent_risk` | 8 | new | exists in two places | grid never straddles `aspect = 1` |
| 12 | `estimator_moments` | +7 | existing | GREEN | — |
| 13 | `finite_decision_minimax` | 7 | new | none — hours to write | no — duality is proved; retain the deterministic-rule positive control |
| 14 | `block_normal_approximation` | 6 | new | **exists**, `block_count/block_count_sim.py` | — |
| 15 | `ld_decay_recurrence` | +4 | existing | SIMULATED | two names for `r²`, two names for LD decay |
| 16 | `admixture` | +4 | existing | SIMULATED | members take the `g` the simulator already varies |
| 17 | `wf_absorption_information` | 4 | new | exists but **the grid cannot fail** | **yes** — loss probability → 1 versus → `1 - p₀` |
| 18 | `ldsc_intercept_regression` | 3 | new | check `empirical/ldsc_diff/` first | intercept convention ambiguous (`a` versus `1 + a`) |

**If only three things are done**, they should be: register
`hwe_genotype_score`'s 22 new members and add the Berry-Esseen binding cell
(largest coverage per hour, on a green simulator); write
`weighted_consensus_correction` (cheapest simulator in the bucket, and it
contains a control guaranteed to fire); and extend the allele-loss grid in
`check_imitation.py` (four members, one parameter change, and it decides a
claim that is probably wrong).

---

*Classification only. No Lean build, no simulation, no `emit.py`, no numbers
invented, no results file. Counts are a source parse of the twenty files named
at the top, on 2026-08-03.*
