# Family proposals, bucket 1: the calibration / certification / blindness group

Classification only. No simulator was written, no Lean build was run, no
`emit.py` was run, and no number in this document is a measurement of anything
other than a count of declarations in the source text.

**What was classified.** Every `def` and `abbrev` in the 24 modules listed in
section 0, read from `proofs/Calibrator/*.lean` in the working tree on
2026-08-03. Declarations are cited by FILE and DECLARATION NAME. No line
numbers: they moved measurably within the hour today.

**How the count was taken.** `grep -cE '^(noncomputable )?(private )?(def|abbrev) '`
per file, then each declaration read together with its body. This counts
source keywords, which is the same population
`proofs/validation/empirical/COVERAGE_DENOMINATOR.md` section 2 counts and for
the same reason: none of the six things `Shared.isGenerated` excludes can
appear after a `def` keyword in a source file. It is a text census, not a Lean
environment census, and it is 263 for these 24 modules. The brief's estimate
was 266; the 3-declaration gap is which small modules land in this bucket
(section 0), not a disagreement about any file.

---

## 0. The bucket

Fourteen modules were named in the brief. The remaining ten were chosen as the
small modules thematically inside this group — validation statistics, the
blindness/counting-invariant witnesses, and the one-line portability leftovers
— and deliberately away from the `TransferLearningPGS`, `Probability` and
`Permeability` groups, from the seven-file slice, and from the
`PCCorrectability` subtree apart from `Core`, which was named.

| module | defs | module | defs |
|---|---:|---|---:|
| PGSCalibrationTheory | 74 | ImputationPortability | 7 |
| Conclusions | 25 | TransportedMinimax | 7 |
| CertificateGrading | 22 | CountingInvariantBlindness | 6 |
| SimulationValidation | 19 | ResonanceSpectrum | 5 |
| AssortativeMatingPGS | 14 | SelectionValidation | 4 |
| PolygenicSpectroscopy | 13 | OpenQuestions | 4 |
| DriftRegime | 12 | LumpedRateBlindness | 4 |
| ObservationalCeiling | 10 | CountingInvariantInstances | 3 |
| SpectralDegradation | 10 | DeclaredInteractionClass | 3 |
| PCCorrectability/Core | 9 | ValidationStatistics | 2 |
| BlindnessRegistry | 8 | AncestryCalibration | 1 |
| | | EquityAndImplementation | 1 |
| | | CumulantBlindness | 0 |
| | | **24 modules, total** | **263** |

`CumulantBlindness.lean` holds no definitions at all — theorems only. It is in
the bucket and it contributes nothing to any denominator. Worth recording,
because a module named in a coverage plan that turns out to be definition-free
is exactly the kind of thing that gets counted as an uncovered blind spot.

**Modules deliberately NOT touched, flagged rather than guessed:**
`PCCorrectability/{ImitationCapacity, Frequency, Diagnostic, Threshold, Phase,
Overlap, Unified, …}` (the `Core` naming in the brief implies the subtree is
split, and `ImitationCapacity` at 33 defs is too large to be an accident of
someone else's bucket); `Condensation.lean`, `CondensationUnification.lean` and
`JetBarrier.lean` (these are the natural neighbours of the
`hwe_mellin_condensation` family proposed below and should be classified
*with* it, by whoever owns them); `ClinicalUtilityFairness.lean` (the natural
neighbour of `clinical_decision_utility`); `PowerAnalysis.lean` (the natural
neighbour of `pgs_accuracy_vs_training_n`).

---

## 1. The split, in three numbers

| outcome | defs |
|---|---:|
| (a) joins an EXISTING family | **62** |
| (b) belongs to a NEW family proposed here | **180** |
| (c) makes no empirically checkable claim | **21** |
| total | **263** |

Not one definition in this bucket was left unclassifiable. Two judgment calls
are flagged in section 5 rather than hidden.

---

## 2. (a) The 62 that join families that already exist

This is the cheapest coverage in the bucket and it is 24 per cent of it. None
of these needs a new generative process; each needs a membership entry in
`families.py` and a re-run of the named simulator so the credit is earned.

**`linear_prediction_transport` — 12** (all in `SimulationValidation.lean`):
`mechanisticPortabilityRatio`, `sourceSquaredEffectMass`,
`identityDirectMetricModel`, `baselineMetricModel`, `targetLDShiftMetricModel`,
`baselineProxyTagMetricModel`, `targetTaggingShiftMetricModel`,
`targetEffectShiftMetricModel`, `targetContextShiftMetricModel`,
`targetPrevalenceShiftMetricModel`, `novelTargetOnlyTaggingMetricModel`,
`novelUntaggablePhenotypeMetricModel`.

These are not new claims. They are **concrete numeric fixtures of the family's
own model**, each perturbing exactly one channel of `CrossPopulationMetricModel`
away from `baselineMetricModel` — LD, tagging, effect size, context, prevalence,
novel tagging, novel untaggable variance. That is precisely the split-control
discipline the family specs demand, already written down in Lean and never
executed numerically. `fam_linear_transport.py` should be run *on these
fixtures* rather than on parameters of its author's choosing; the fixtures'
docstrings say "Empirical status: UNTESTED" in so many words.

**`generational_transport_kernel` — 7** (all in `SimulationValidation.lean`):
`baselineGenerationalPopGen`, `nondegenerateGenerationalPopGen`,
`popgenDrivenTagScale`, `popgenDrivenProxyScale`,
`popgenDrivenProxyGenerationalModel`, `timeVaryingAFGenerationalModel`,
`timeVaryingEffectGenerationalModel`.

`popgenDrivenTagScale = (7/6)·exp(−1)` and
`popgenDrivenProxyScale = (7/6)·exp(−15/14)` are **literal predicted constants
at generation 1** under a fully specified popgen parameter set
(`nondegenerateGenerationalPopGen`: Ne=1, μ=1/2, mig=1/8, recomb=1/4). They are
the highest-value re-run in this whole bucket: two numbers, one generation, no
asymptotics, and the existing simulator already builds the kernel that is
supposed to produce them.

**`liability_threshold_metrics` — 19**: from `Conclusions.lean` —
`brierScore`, `expectedBrierScore`, `exactBrierRiskOfCalibrated`,
`PosteriorPrediction.prob_mode`, `sigmoid`, `bernoulliLogLoss`,
`bernoulliKLReal`, `klBernReal`, `logLossRegret`, `logLossKLCertificate`,
`brierRegret`, `brierL2Certificate`, `logRisk`, `brierRisk`,
`brierBernoulliRisk`, `logBernoulliRisk`, `populationRisk`, `populationAUC`;
from `OpenQuestions.lean` — `f1Score`. The family's own model line already
reads "the AUC, Brier, log-loss and R² of a score on that liability, and the
regret of a miscalibrated score". These are that, stated generically.

**`drift_retention` — 5** (`DriftRegime.lean`):
`HeterozygosityTrajectory.measuredLoss`, `closedPopulation`, `lossOfRetention`,
`targetHetOfRetention`, `targetPgsVarOfRetention`. `closedPopulation` *is*
`(1 − 1/(2Ne))^t · H₀` — the family's model line verbatim — and the family's
recorded status is SIMULATED, MODEL ERROR: predicted retention 0.1352, measured
1.0017. `DriftRegime.lean` exists to name the two regimes that measurement
separated. Assigning these five puts the disagreement's own vocabulary inside
the family that carries it.

**`mutation_drift_balance` — 1**: `DriftRegime.mutationDriftBalance`
(stationary heterozygosity — the regime the simulation was in).

**`neutral_af_benchmark_transport` — 3**: `DriftRegime.benchmarkRatio`,
`DriftRegime.benchmarkRatioSquared`, `OpenQuestions.combinedPortability`.
`benchmarkRatioSquared` is a *deliberately wrong rival* retained in the source
so a design can be tested for the power to reject it. A family whose simulator
cannot distinguish `(1−F_T)/(1−F_S)` from its square has no power, and this
family currently has no simulator at all.

**`hwe_genotype_score` — 4** (`BlindnessRegistry.lean`):
`OneLocusArchitecture.averageEffect`, `OneLocusArchitecture.genotypicValue`,
`OneLocusArchitecture.meanValue`, `OneLocusArchitecture.valueDosageCovariance`.
Same generative process as the family (HWE genotypes, score as a weighted
allele count, exact mean and variance), extended by a dominance deviation `d`.
The family's simulator needs one new column — genotypic value with `d ≠ 0` —
and then it measures Fisher's one-locus decomposition directly.

**`ascertainment` — 3** (`ImputationPortability.lean`):
`ascertainment_loss`, `apparent_portability_loss`, `true_portability_loss`.
The family already covers tag/causal MAF mismatch; array coverage loss is the
same discovery-side process.

**`ld_decay_recurrence` — 1**: `OpenQuestions.ldTaggingDecay` (`exp(−λ d)`).

**`estimator_moments` — 1**: `OpenQuestions.snrPortabilityRatio`.

**`stepping_stone` — 1**: `AssortativeMatingPGS.ibdFst`
(`d/(4Nσ² + d)`) — isolation by distance, the Malécot/Wright IBD form. It is
in an assortative-mating file for no reason visible in the source and it is the
only member of that file that is not about assortative mating.

**`gxe_and_interaction` — 1**: `AncestryCalibration.epistaticVariancePairwise`.

**`ensemble_portability_channel` — 4** (`ResonanceSpectrum.lean`):
`PhasePanel.witness`, `cosPart`, `sinPart`, `intensity`. **Judgment call, see
section 5.** `intensity s = (Σ wᵢ cos(s φᵢ))² + (Σ wᵢ sin(s φᵢ))²` is the
squared modulus of the characteristic function of a discrete weight measure —
i.e. a spectral density of a stationary panel, which is that family's object,
with the Fejér kernel a special case. If the family's owner disagrees, this
becomes a 4-member new family `phase_panel_resonance` and nothing else in this
document changes.

---

## 3. (c) The 21 that make no empirically checkable claim

Applying the corpus's own F1 rule (`families.py`, `falsify_unsimulatable`): a
definition is checkable only if it denotes a real, a vector or matrix of reals,
or a structure whose fields are reals.

Fifteen return `Prop`: `PGSCalibrationTheory.classifiedHighRisk`,
`PGSCalibrationTheory.receivesTreatment`, `CertificateGrading.MomentMatched`,
`CertificateGrading.Feasible`, `CertificateGrading.GradeInsensitive`,
`CertificateGrading.IsComplete`, `PolygenicSpectroscopy.hweLatticeCondition`,
`DriftRegime.clusterCrossCheck`, `ObservationalCeiling.IsCompleteCatalogue`,
`ObservationalCeiling.IsUnionOfCertificates`,
`BlindnessRegistry.StructuralGuard.verdict`, `LumpedRateBlindness.Lumped`,
`DeclaredInteractionClass.Identifiable`, `ResonanceSpectrum.IsResonantAt`.
Two are type abbreviations: `Conclusions.TrueCondProb`,
`Conclusions.ProbPredictor`. Two return a `Submodule`:
`PCCorrectability.Core.PCCorrectionModel.topPCSpan` and `.fineScaleSubspace`.
One returns `ℤ`: `PolygenicSpectroscopy.hardCallLatticeIndex`. One returns
`FinitePrior`, a `PMF` synonym: `CertificateGrading.FinitePrior`. One returns a
function `ℝ → ℝ` and says so in its own docstring — "not an empirical claim.
This is a description of a test design" — `DriftRegime.diagonalDesign`.

**Two places where the F1 rule as coded gives the wrong answer, in opposite
directions.** Both are reported because they bear on any headline computed from
F1 as a flat string match:

1. **F1 would call `Conclusions.populationAUC` uncheckable.** It returns
   `ENNReal`, which contains no `ℝ` glyph and matches none of
   `("ℝ", "Matrix", "Profile", "Set ℝ")`. It is an AUC. It is the single most
   checkable quantity in the file. Any other `ENNReal`-valued definition in the
   corpus is being dropped from the denominator the same way.
2. **F1 would call all eight `ObservationalCeiling` blindness witnesses
   uncheckable**, and they are not — see the family in section 4.4. Their claim
   *is* a numeric equality (two probe outputs agree exactly while the property
   differs), it just is not in the return type.

Both are counted the way the definitions actually behave, not the way the
string match behaves: `populationAUC` is counted checkable, the eight witnesses
are counted checkable. If a future census wants to reproduce these 21, it must
use the same convention or it will get 21 ± 9.

---

## 4. (b) The fifteen proposed families, ranked

Ranking is by members covered, then by simulator cost, then by whether a live
disagreement sits inside the family. Where a family has a disagreement in it,
that is said in its own entry and it moves up.

### 4.1 `calibration_shift_transport` — 43 members — HIGHEST VALUE

**Generative process.** A source and a target population each carry a liability
or risk with its own mean, a deployed score with its own mean, and a deployment
intercept; the target differs from the source by an explicit budget of shifts —
disease prevalence, environmental mean, genetic mean, score mean, intercept —
plus a slope that may differ. Fit `observed = a + b·predicted` in each
population and read off calibration-in-the-large `a` and slope `b`; on the
logistic arm, the same with `logit π` as the observed mean.

**Members** (all `Calibrator/PGSCalibrationTheory.lean`):
`calibrationInTheLarge`, `calibrationSlopeDeviation`, `calibrationProfile`,
`CalibrationMoments.toProfile`, `CalibrationMoments.shifted`,
`identityCalibrationProfile`, `logisticCalibrationProfile`,
`hosmerLemeshowContrib`, `prevalenceLogit`, `prevalenceCITLShift`,
`prevalenceLogisticCalibrationProfile`, `interceptRecalibrated`,
`logisticRecalibrated`, `recalibratedCalibrationSlope`;
`CrossPopulationCalibrationShiftModel.{observedMeanShift, predictedMeanShift,
observedMean, predictedMean, calibrationMoments, calibrationProfile,
identityCalibrationProfile}`;
`CrossPopulationMechanisticCalibrationModel.{witness, deploymentIntercept,
observedMeanShift, scoreMean, scoreMeanShift, predictedMean, observedMean,
calibrationSlope, toShiftModel, calibrationProfile,
identityCalibrationProfile}`;
`CrossPopulationGenerationalCalibrationModel.{witness, tagMeanAt,
deploymentInterceptAt, observedMeanShiftAt, scoreMeanAt, scoreMeanShiftAt,
predictedMeanAt, observedMeanAt, toMechanisticCalibrationModelAt}`;
`targetCalibrationProfileAtGeneration`,
`targetIdentityCalibrationProfileAtGeneration`.

**A simulator must MEASURE**: CITL and fitted slope in both populations, by
actually regressing simulated observed outcomes on simulated predictions —
never by evaluating the definitions. Also the Hosmer-Lemeshow contribution per
risk decile, and the logistic-arm CITL against `logit π_T − logit π_S`.

**WHAT WOULD FALSIFY IT.** Three things, all reachable:
* `prevalenceCITLShift` says the intercept shift on the linear-predictor scale
  is exactly `logit π_T − logit π_S`. Simulate a target that differs from the
  source **only** in prevalence, refit, and measure the intercept shift. It is
  exactly the logit difference only if the score distribution is unchanged and
  the link is exactly logistic; under a probit-generated liability, or when the
  score variance also shifts, it is not. This is the falsifier that most likely
  fires.
* `CrossPopulationMechanisticCalibrationModel.calibrationSlope` is defined as
  `calibrationSlopeFromSourceWeights` — an algebraic function of the transport
  state. Measure the slope by regression instead. Disagreement falsifies.
* The additive shift budget: `observedMeanShift = prevalenceShift +
  environmentalObservedShift + geneticObservedShift`. Simulate all three
  channels **on at once** and measure whether the observed-mean shift is their
  sum. On the identity link it must be; on the logistic link additivity of
  prevalence with the other two is a claim, and a false one for large shifts.

**Cost**: cheap. Gaussian liability, logistic outcome, ordinary least squares.
No population genetics. The 11 generational members additionally need the
`generational_transport_kernel` simulator's tag-mean trajectory, so the natural
build order is: static arm first (32 members), generational arm second (11).

### 4.2 `probe_blindness_witnesses` — 27 members — HIGHEST VALUE

**Generative process.** Two configurations are constructed that a stated probe
cannot tell apart: the probe's output on the "positive" configuration equals its
output on the "negative" one to the last bit, while the property under test
holds of one and fails of the other. Run the probe on both, numerically, and
measure the discrepancy.

**Members**: `ObservationalCeiling.{and, ofWitnessFamily,
ApproxProbeBlindness.witness, LeveledBlindness.witness, toProbeBlindness,
atLevel, ProbeSeparation.witness, duplicate_separation}`;
`DriftRegime.{crossChecks_blind_to_retention, symmetricDesignBlindness}`;
`BlindnessRegistry.{guard_stack_blind_to_retention,
extra_algebraic_guard_adds_nothing, averageEffect_blind_to_dominance}`;
`CountingInvariantBlindness.{ApproxWitness.ofWitness, ghostGain,
countPredictedGain, ghostWitness, ghostWitnessExample, ApproxWitness.witness}`;
`CountingInvariantInstances.{momentDist, momentInvariant, meffApproxWitness}`;
`LumpedRateBlindness.{demeRate, generatorApply, generatorIter}`;
`DeclaredInteractionClass.{observable, actionGap}`.

**A simulator must MEASURE**: for each witness, the probe output on `positive`
and on `negative` and their difference (which the corpus claims is exactly
zero, or below `dist` for the approximate witnesses); and the value of the
property on each, which must differ. For `symmetricDesignBlindness`
specifically, the two rival benchmark forms evaluated on a symmetric design
grid and on an asymmetric one — the source already records `+214.0%` separation
asymmetric and `−0.4%` symmetric, and that pair of numbers is reproducible.
For `LumpedRateBlindness`, iterate the 3-state generator and check the
observable stays lumped as the exchange rate `b` is varied over decades.

**WHAT WOULD FALSIFY IT.** A probe output that *differs* between positive and
negative — i.e. a blindness claim that is false, meaning the design is not
actually blind and the ceiling argument built on it collapses. This is a
one-sided falsifier and that is a real weakness of the family, so the simulator
must be built to be capable of the other side too: for each witness, **also**
search a neighbourhood of the two configurations for a nearby pair the probe
*can* separate, and report the separation radius. A blindness that holds only
at the exact constructed point is a much weaker statement than the prose around
these witnesses reads as, and the radius measures which one is true.

**Cost**: cheapest simulator in the bucket. All finite arithmetic; no sampling
except in the `duplicate_separation`/`ProbeSeparation` arm. **This is the
family I would build first** — 27 members, floating-point evaluation only, and
its result bears directly on the corpus's own claim that structural guards
cannot catch a wrong number.

### 4.3 `clinical_decision_utility` — 21 members

**Generative process.** A patient carries a true risk and a predicted risk; a
decision rule treats when the predicted pathway has positive net QALY margin
over a discounted horizon of `T` follow-up periods; realised utility is
evaluated under the true pathway. Sweep the miscalibration between predicted
and true risk and integrate the loss over a population.

**Members** (all `Calibrator/PGSCalibrationTheory.lean`):
`qalyContributionAtTime`, `treatmentMargin`, `qalyGainUnderDecision`,
`qalyLoss`, `qalyDecisionRegretMargin`, `expectedQalyLoss`,
`screeningLongitudinalModel`, `screeningClinicalPathway`,
`screeningUtilityFromCounts`, `screeningUtilityFromRates`,
`qalyScreeningDecisionModel`, `screeningQalyGain`,
`decisionCurveScreeningModel`, `decisionCurveNetBenefit`,
`ThresholdTreatmentModel.witness`, `thresholdLongitudinalModel`,
`thresholdClinicalPathway`, `thresholdQalyGainUnderDecision`,
`thresholdQalyLoss`, `thresholdDecisionRegretMargin`,
`expectedThresholdQalyLoss`.

**A simulator must MEASURE**: expected QALY loss versus CITL shift and versus
calibration slope, on a simulated cohort with a known risk distribution; and
the net benefit curve versus threshold `t`, compared against
`decisionCurveNetBenefit` computed from simulated TP/FP counts.

**WHAT WOULD FALSIFY IT.** `qalyScreeningDecisionModel` sets
`threshold = harm/(benefit + harm)`, and `decisionCurveScreeningModel` sets
`harm = t/(1−t)` at threshold `t`. Together these assert that the
utility-optimal decision threshold is exactly the odds of harm to benefit.
Simulate: sweep the treatment threshold on a cohort with known risk
distribution, find the threshold that maximises measured expected QALY, and
compare it to `harm/(benefit+harm)`. The identity holds for a linear utility
with no discounting; it does **not** hold once `discount` and `followupWeight`
vary over the horizon, which `LongitudinalTreatmentModel` explicitly allows. A
measured optimum that moves with the discount schedule falsifies the
specialisation lemma tying the screening model to the longitudinal one.

**Cost**: cheap, and it connects the whole corpus to a decision-relevant
number, which nothing else in this bucket does.

### 4.4 `graded_moment_certificate` — 17 members — CONTAINS A SHARP, LIVE CLAIM

**Generative process.** Two finite priors on `Fin (n+1)` are chosen to match
the first `K` moments of a catalogue exactly while their prior-predictive
mixtures stay within total-variation `h`; the *modulus* is the largest
separation of the target functional achievable over all such feasible pairs.
Certified risk is `scale · modulus²`; the certification gap is the ratio of the
ungraded (`K = 0`) modulus to the grade-`K` one.

**Members** (all `Calibrator/CertificateGrading.lean`): `FinitePrior.probability`,
`FinitePrior.mean`, `targetGap`, `admissibleGaps`, `modulus`, `mixture`,
`totalVariation`, `certificateProblem`, `fixedGradeExponent`,
`fixedGradeGapScale`, `certificationGap`, `GradedModulus.Δ`,
`CertificateCalculus.scale`, `certifiedRisk`, `ungradedRisk`, `deficit`,
`explicitCalculus`.

**A simulator must MEASURE**: the modulus itself, by solving the finite program
— maximise `|E_P[target] − E_Q[target]|` over pairs of probability vectors
subject to `K` linear moment-equality constraints and one TV constraint. That
is a linear program in `2(n+1)` variables and it is exactly solvable; the
modulus is not an asymptotic object here. Then the certification gap as a
function of `n` at fixed `K`.

**WHAT WOULD FALSIFY IT.** `fixedGradeGapScale K n = (n+2)^(1/(2(K+1))) /
sqrt(log(n+2))` is an explicit growth rate for the ungraded-to-graded modulus
ratio. Solve the LP on a grid of `n` from 4 to a few hundred at `K = 1, 2, 3`,
fit the exponent of `n` in the measured `certificationGap`, and compare with
`fixedGradeExponent K / 2 = 1/(2(K+1))`. A measured exponent that does not
match — including one that is zero, meaning the gap does not grow at all for
the corpus's own `moment`/`target` catalogue — falsifies the fixed-grade
incompleteness claim. There is no way for this simulator to merely agree: it
produces a number with error bars against a stated exponent.

**Cost**: moderate. Needs an LP; `scipy.optimize.linprog` suffices, and the
absolute-value objective splits into two LPs. Highest falsification power per
line of code in the bucket.

### 4.5 `assortative_mating_equilibrium` — 13 members

**Generative process.** A population mates with phenotypic correlation `r`
between partners; additive genetic variance is inflated generation by
generation through `V ↦ (V(1 + r h²) + V₀)/2` until it reaches the fixed point
`V₀/(1 − r h²)`, which also induces directional LD between causal loci of the
same sign. Two populations with different `r` are then compared.

**Members** (all `Calibrator/AssortativeMatingPGS.lean`):
`AssortativeMatingModel.{witness, h2, equilibriumVariance, observedH2, pgsR2AM,
amGap}`, `amVarianceStep`, `amEquilibriumVariance`, `amInducedLD`,
`DifferentialAMModel.{witness, apparentPortability}`, `amCorrectedPortability`,
`CrossPopAMLD.witness`.

**A simulator must MEASURE**: the additive variance trajectory under simulated
assortative mating on a finite genome (draw partners by rank-correlated
phenotype at correlation `r`, produce offspring by Mendelian segregation),
compared to `amVarianceStep` iterated; the equilibrium `V_A` against
`V₀/(1 − r h²)`; the induced pairwise LD between causal loci against
`β_i β_j r h² / (1 − r h²)`; and the measured PGS R² ratio between two
populations differing only in `r`, against `apparentPortability`.

**WHAT WOULD FALSIFY IT.** The equilibrium formula is the standard
Fisher/Wright result under the infinitesimal model, and it is known to
overstate the inflation at finite locus number because `h²` in the recursion is
the *equilibrium* heritability, not the starting one. Simulate at 50, 500 and
5000 causal loci: if the measured equilibrium `V_A/V₀` converges to
`1/(1 − r h²)` only as the locus count grows, the formula is an infinitesimal
limit and every member that uses it at a finite genome inherits that
qualification. `amCorrectedPortability` would then be a correction that
overcorrects, in a measurable direction. That is a falsification the corpus
would have to record, and the locus-count sweep is the control that produces it
— a simulator run only at 5000 loci would agree by construction.

**Cost**: moderate; a real forward simulation, but small populations suffice.

### 4.6 `hwe_mellin_condensation` — 11 members

**Generative process.** Genotypes at a biallelic Hardy-Weinberg locus at
alternative-allele frequency `q`; the standardised dosage is squared, and the
log-moments of that squared value — its mean `c(q) = E[x² log x²]` (the Mellin
drift) and its variance (the jet variance) — govern the order of epistatic
product at which the Gaussian surrogate for the genotype breaks down, via
`maxSafeEpistaticOrder = log N / c(q)`.

**Members** (all `Calibrator/PolygenicSpectroscopy.lean`):
`HardyWeinbergModel.standardizedSquare`, `HardyWeinbergModel.mellinDrift`,
`hweMellinDrift`, `maxSafeEpistaticOrder`, `latticeCriticalMaf`,
`HardyWeinbergModel.mellinJetVariance`, `hweMellinJetVariance`,
`hardCallLatticeSpan`, `hardCallObservables`, `hweCodingInvariants`,
`HardyWeinbergModel.standardizedFourthMoment`.

**A simulator must MEASURE**: (i) the three log-moments by direct enumeration
over the three genotypes at a grid of `q` — this checks the closed forms
`hweMellinDrift`, `hweMellinJetVariance`, `standardizedFourthMoment` exactly and
costs nothing; (ii) the condensation claim, by drawing `N` standardised
genotypes, forming all products of order `k`, and measuring the ratio of the
largest term to the sum — the max-term ratio — as `k` crosses
`log N / c(q)`.

**WHAT WOULD FALSIFY IT.** Part (i) is a pure algebra check and can only agree
or reveal a typo; **it is not the falsifier and must not be reported as one**.
Part (ii) is: the corpus claims a *critical order*, so the measured max-term
ratio must show a transition near `log N / c(q)` and not near, say, `log N`
alone or `log N / c(q)²`. Run at `q = 0.05, 0.146447 (= q*), 0.3, 0.5`, where
`c(q)` varies by a large factor, and check that the transition order tracks
`1/c(q)`. If the transition point does not move with `q` at fixed `N`, the
drift is not the controlling constant and `maxSafeEpistaticOrder` is
dimensional analysis rather than a law.

**Cost**: moderate. Part (i) is minutes. Part (ii) needs care about what
"breakdown" is measured as, and the definition of the measured statistic must
be fixed *before* the run.

**Note for whoever owns them**: `Condensation.lean`, `CondensationUnification.lean`
and `JetBarrier.lean` are almost certainly members of this family and are in
someone else's bucket.

### 4.7 `spectral_readout_degradation` — 10 members

**Generative process.** A feature process and a target are jointly stationary
with per-band feature power `σ(b)`, cross-spectrum `c(b)` and target power; the
optimal bandwise linear readout is `c(b)/σ(b)`, and transporting the source
readout into a target with different spectra costs an excess risk that is a
`σ`-weighted squared difference of the two ratios.

**Members** (all `Calibrator/SpectralDegradation.lean`): `optimalReadout`,
`risk`, `degradation`, `degradationProfile`, `taskDegradation`, `rescale`,
`bandDegradation`, `twoBandBaseline`, `twoBandLowShift`, `twoBandHighShift`.

**A simulator must MEASURE**: simulate a two-band (then `B`-band) Gaussian
feature/target pair with the stated spectra, fit the readout by least squares
in the source, evaluate the risk in the target, and compare the measured excess
risk with `degradation`. The three `twoBand*` fixtures are the split controls
already written in Lean: a shift confined to the low band and one confined to
the high band.

**WHAT WOULD FALSIFY IT.** `degradation` assumes the bands are *independent* —
the risk is a plain sum over `b`. Simulate with a feature process whose bands
are correlated (finite sample estimation alone induces this) and measure
whether the excess risk still equals the sum of `degradationProfile`. It will
not, at finite sample; the interesting number is how large the cross-band term
is at realistic panel sizes. Second falsifier: `rescale` claims the degradation
is invariant to rescaling the source features by `c ≠ 0`. Fit on rescaled
features at finite sample and measure — invariance is exact in population and
approximate in sample, and the size of the gap is what a deployed score
actually suffers.

**Cost**: cheap. This family may belong inside
`portability_permeability_and_completion` or `ensemble_portability_channel`,
which already own Gaussian spectral channels; it is proposed separately because
its object is a bandwise *regression ratio* rather than a covariance channel,
but a merge would be defensible and would save a simulator. Flagged in section 5.

### 4.8 `transported_minimax_rates` — 7 members — CONTAINS A DISAGREEMENT THAT HAS ALREADY FIRED

**Generative process.** An estimator is regularised with ridge parameter `τ²`
and its loss is evaluated not in the source metric but in a transported one
that adds a robustness budget `r` to the signal scale `a`; separately, a
parametric family indexed by a smoothness/long-memory parameter is estimated
from `n` samples and its transported risk is measured against the claimed rate.

**Members** (all `Calibrator/TransportedMinimax.lean`):
`transportedRidgeParameter`, `robustRidgeCandidate`, `inflatedRidgeParameter`,
`longMemoryMetric`, `longMemoryVariance`, `momentBodyEntropyExponent`,
`hyperrectangleEntropyExponent`.

**A simulator must MEASURE**: (i) the risk-minimising ridge parameter, by grid
search on simulated data, against `τ²a/(a+r)`; (ii) the estimator variance as a
function of `δ`, `ε` and `n`, against `3δ³/(nε²)`; (iii) the entropy exponents,
by counting an `ε`-covering of the moment body and of its enclosing
hyperrectangle numerically and fitting `log N(ε)` versus `log(1/ε)`.

**WHAT WOULD FALSIFY IT — and one arm already has.** The docstring of
`longMemoryVariance` states in the source that the posited `3δ³/(nε²)` is
**retained as a named object, not endorsed**, and that the *measured* scaling is
`δ^{+1}` with no `ε` dependence, with the mechanism being that an efficient
estimator's transported loss is `p/(2n)` whatever the metric is. So this family
carries a recorded disagreement between a definition and a measurement, in the
source, today. A simulator here does not need to find a falsification — it
needs to **reproduce the one already claimed** and put an error bar on it, and
then decide whether `longMemoryVariance` should be deleted the way
`continuousSteppingStoneFst` was. That makes this family's simulator unusually
cheap to justify and it is why 7 members rank above larger ones below.

The ridge arm has its own falsifier: `inflatedRidgeParameter = τ²(1 + r/a)` and
`transportedRidgeParameter = τ²/(1 + r/a)` are reciprocal corrections, and the
file's own theorem says the factor "belongs under the ridge, not on it". Grid
search settles which one minimises measured risk. If neither does, both are
wrong.

### 4.9 `pc_correction_residual_confounding` — 7 members

**Generative process.** A genotype covariance with `p` eigenvalues carries a
confounding direction; regressing out the top `k` principal components removes
exactly the components with index `≤ k`, leaving a residual bias equal to the
confounder's mass on the trailing eigenvalues. Recent fine-scale structure is
the case where the confounder loads only on trailing directions.

**Members** (all `Calibrator/PCCorrectability/Core.lean`):
`PCCorrectionModel.witness`, `PCCorrectionModel.residualBias`,
`PCCorrectionModel.uncorrectedBias`, `PCCorrectionModel.removeTopPCs`,
`PCCorrectionModel.residualBiasEnergy`, `RecentFineScaleConfounding.canonical`,
`spectralResidualBiasEnergy`.

**A simulator must MEASURE**: simulate genotypes with a known population
structure plus a fine-scale confounder, run an actual PCA, regress the
phenotype on the top `k` PCs, and measure the residual association between the
confounder and the phenotype — then compare with `residualBias` and
`residualBiasEnergy`.

**WHAT WOULD FALSIFY IT.** `removeTopPCs` assumes PC correction removes
component `i` **completely** for `i ≤ k` and leaves component `i > k`
**untouched**. At finite sample the empirical eigenvectors are rotated relative
to the population ones, so correction both fails to remove the top components
fully and damages the trailing ones. Sweep the sample-to-marker ratio across
the BBP phase-transition regime and measure the leakage in both directions; a
measured residual bias larger than `residualBias` at realistic `n/p` falsifies
the sharp-projection idealisation, and the size of the excess is the number
worth publishing.

**Cost**: moderate. Needs a real PCA on simulated genotypes. Note that
`PCCorrectability/ImitationCapacity.lean` (33 defs) is very likely the bulk of
this family and is in another bucket — this proposal should be merged with
whatever that bucket proposes rather than standing alone.

### 4.10 `gaussian_summary_likelihood_test` — 6 members

**Generative process.** A model summary predicts an effect correlation and a
selected-variance statistic; each observed statistic is Gaussian about its
prediction with a stated noise variance; the profile log-likelihood is summed
and two competing summaries are compared by `−2Δ log L`.

**Members**: `ValidationStatistics.{gaussianProfileLogLik, likelihoodRatioStat}`;
`SelectionValidation.{SelectionValidationModel.witness, selectionSummaryLogLik,
missedSelectedVariance, selectionModelLRT}`.

**A simulator must MEASURE**: the null distribution of `selectionModelLRT` —
simulate under the null summary many times, compute the statistic, and compare
its distribution with χ²₁ (or χ²_df for the number of free parameters).

**WHAT WOULD FALSIFY IT.** The corpus proves only `likelihoodRatioStat ≥ 0`.
The *use* of an LRT presupposes a reference distribution, and here the "noise"
variances are **fixed constants supplied by the model**, not estimated, and the
two summaries are not nested in any stated way. If the measured null
distribution is not χ² with the nominal degrees of freedom, then every p-value
anyone computes from `selectionModelLRT` is wrong by a stated factor. That is a
clean falsifier with a clean consequence.

**Cost**: trivial — a few thousand Gaussian draws. Best effort-to-consequence
ratio in the bucket after 4.2.

### 4.11 `reclassification_nri` — 5 members

**Generative process.** Event and non-event score distributions; a decision
threshold; a downward intercept recalibration by `δ` moves exactly those
individuals whose score lies in the band `(threshold, threshold + δ]`; the NRI
is the net reclassification across the two distributions.

**Members** (all `Calibrator/PGSCalibrationTheory.lean`): `nri`,
`thresholdBandRate`, `downReclassificationRate`,
`nriFromDownwardInterceptRecalibration`, `reclassifiedBandEventPrevalence`.

**A simulator must MEASURE**: the reclassification counts directly, on a
simulated cohort, and the resulting NRI; and the event prevalence *within the
reclassified band* against `reclassifiedBandEventPrevalence`.

**WHAT WOULD FALSIFY IT.** `nriFromDownwardInterceptRecalibration` passes
`up_events = up_nonevents = 0` — it asserts that a downward intercept shift
produces **no upward** reclassifications at all. That is exactly true for a
uniform shift of every score, and exactly false for any recalibration that also
changes the slope, which `recalibratedCalibrationSlope` in the same file
contemplates. Simulate a joint intercept-and-slope recalibration and measure
the upward counts; non-zero upward movement falsifies the specialised NRI
formula for the general recalibration the same file defines.

**Cost**: trivial.

### 4.12 `bayes_risk_of_predictor_class` — 5 members

**Generative process.** A true conditional probability `η(z)` on a feature
space; a class `F` of predictors; the oracle risk is the infimum of population
risk over `F`, under log-loss or Brier.

**Members** (all `Calibrator/Conclusions.lean`): `oracleRisk`, `infRisk`,
`BayesRisk`, `logBayesRisk`, `brierBayesRisk`.

**A simulator must MEASURE**: the infimum, by minimising the empirical risk
over a concrete `F` (linear-in-score logistic predictors, say) on a large
sample, at several sample sizes so the optimisation gap can be extrapolated
away.

**WHAT WOULD FALSIFY IT.** With `F` the class of *all* measurable predictors,
`logBayesRisk` must equal the conditional entropy `E[H(η(Z))]` and
`brierBayesRisk` must equal `E[η(1−η)]`, both to Monte Carlo error. Measure
both. With `F` a restricted class, `oracleRisk_mono` claims monotonicity under
inclusion, which a measured optimisation can violate whenever the minimiser is
not found — so the same run doubles as a check that the measured infimum is an
infimum and not a local optimum.

**Caveat, stated rather than smoothed over**: these five definitions quantify
over an *arbitrary* `Set α`. Until `F` is instantiated they are not falsifiable,
because no generative process is specified. **Marked simulatable-only-under-
instantiation**; the two instantiations above are the ones proposed, and if the
corpus intends the definitions to carry content at arbitrary `F`, then the
family is unsimulatable-as-stated and that is the finding.

### 4.13 `imputation_attenuation` — 4 members

**Generative process.** A causal variant is observed only through an imputed
dosage with squared correlation `r²_imp` to the truth, itself falling off with
distance to the nearest typed marker; the score's explained variance is
attenuated by exactly `r²_imp` and the remainder becomes error variance.

**Members** (all `Calibrator/ImputationPortability.lean`): `attenuatedVariance`,
`imputationErrorVariance`, `meanImputationR2`, `total_portability_loss`.

**A simulator must MEASURE**: simulate haplotypes, mask a causal variant,
impute it from flanking typed markers, and measure both the achieved `r²_imp`
and the attenuation of the score's explained variance.

**WHAT WOULD FALSIFY IT.** Two claims, both checkable. (i)
`attenuatedVariance + imputationErrorVariance = β² h` exactly — an exact
variance split with no covariance term. Measured imputed dosages are *not*
orthogonal to their own error unless the imputation is the conditional
expectation; measure the cross term. (ii) `meanImputationR2 = max(0, 1 − c/L)`
is linear in distance and clamped at zero, whereas LD decays exponentially
(`ldTaggingDecay` in the same corpus is `exp(−λd)`). **The corpus contains both
forms and they disagree**; a distance sweep measures which one the simulated
imputation follows. That is a conflict inside the corpus, of the kind the brief
says was worth the most today.

**Cost**: moderate — needs a haplotype simulation with recombination, which
`fam_ld_decay.py` already has.

### 4.14 `recalibration_sample_size` — 3 members

**Generative process.** A recalibration model with `d` free parameters is fitted
on a target cohort containing `n_events` events, each carrying Fisher
information `I`; the trace of the parameter MSE is `d/(n_events · I)`, and
inverting gives the events and cohort size needed to hit a precision target.

**Members** (all `Calibrator/PGSCalibrationTheory.lean`):
`recalibrationTraceMSELowerBound`, `requiredEventsForRecalibration`,
`requiredTargetCohortSizeForRecalibration`.

**A simulator must MEASURE**: fit a two-parameter logistic recalibration on
simulated target cohorts of increasing size, and measure the trace of the
empirical parameter covariance against `d/(n_events · I)`.

**WHAT WOULD FALSIFY IT.** The formula is the Cramér-Rao bound at the *true*
parameter with an *orthogonal* Fisher information. Measure at small
`n_events` (20, 50, 100): maximum-likelihood logistic estimates are biased and
their variance exceeds the bound by an O(1/n) factor, and separation makes the
variance infinite below some event count. The claimed cohort size is therefore
a floor that is not attained, and the measurable question is by how much — the
ratio of measured trace-MSE to the bound as a function of `n_events` is the
result. `requiredEventsForRecalibration` is quoted as a requirement; if the
ratio is 1.4 at 50 events, the requirement understates by 40 per cent.

**Cost**: trivial.

### 4.15 `pgs_accuracy_vs_training_n` — 1 member

**Generative process.** A polygenic score trained on `n` individuals for a
trait of heritability `h²` spread over `M` effective independent loci attains
`R² = h² · (n h²)/(n h² + M)`.

**Member**: `EquityAndImplementation.expectedR2FromN`.

**A simulator must MEASURE**: simulate `M` independent causal loci, run a GWAS
at sample size `n`, build the score from the estimated effects, and measure `R²`
out of sample.

**WHAT WOULD FALSIFY IT.** This is the Daetwyler/Dudbridge law and it assumes
the score uses **all** markers with their OLS effects and that the `M` loci are
independent. Sweep: (i) a p-value threshold on marker inclusion — the measured
`R²` then falls below the formula and peaks at an intermediate threshold, which
the formula cannot represent; (ii) LD between loci, which makes `M` an effective
rather than an actual count and is the quantity the formula silently assumes is
known. Either sweep produces a measured curve the single-formula prediction
cannot match.

**Cost**: cheap. Ranked last only because it has one member here — but
`PowerAnalysis.lean` (11 defs, another bucket) and `AncestrySpecificPower.lean`
(8 defs) are very likely members, and if so this family is really ~15 members
and should be re-ranked accordingly by whoever holds those files.

---

## 5. Judgment calls, flagged rather than hidden

1. **`ResonanceSpectrum` into `ensemble_portability_channel`** (4 defs). The
   intensity of a weighted phase panel is a spectral density of a discrete
   measure and the Fejér kernel is a special case, so the generative process
   matches. If that family's owner reads its scope more narrowly, these become
   a 4-member family `phase_panel_resonance` with the falsifier: `intensity`
   must equal 1 at `s = 0` for every panel and the measured resonance set must
   be a lattice only when the phases are rationally commensurate — an
   incommensurate panel whose measured resonance set is still a lattice
   falsifies it.
2. **`spectral_readout_degradation` may belong inside
   `portability_permeability_and_completion`.** Proposed separately (section
   4.7) because its object is a regression ratio, not a covariance channel. A
   merge saves one simulator and loses nothing; the decision belongs to the
   agent holding `Permeability.lean`.
3. **`PolygenicSpectroscopy.hardCallLatticeIndex` returns `ℤ`** and is counted
   uncheckable, but it is the coding of a genotype lattice that
   `hardCallObservables` (checkable) depends on. It is a category error to
   simulate on its own and it is not evidence-free — it is a *convention* whose
   consequences are checkable through its dependents.
4. **The `ObservationalCeiling` combinators** (`and`, `ofWitnessFamily`,
   `toProbeBlindness`, `atLevel`, `duplicate_separation`) are *constructions on*
   witnesses rather than witnesses. They are counted into
   `probe_blindness_witnesses` because each asserts a numeric equality that a
   simulator can evaluate on any instance; a stricter reading would move all
   five to outcome (c) and reduce that family to 22 members.

---

## 6. Ranked summary

| # | family | members | simulator cost | live disagreement inside? |
|---|---|---:|---|---|
| 1 | calibration_shift_transport | 43 | cheap (OLS + logistic) | no, but 3 falsifiers reachable |
| 2 | probe_blindness_witnesses | 27 | cheapest | yes — the guards-are-blind claim |
| 3 | clinical_decision_utility | 21 | cheap | no |
| 4 | graded_moment_certificate | 17 | moderate (LP) | claims an explicit growth exponent |
| 5 | assortative_mating_equilibrium | 13 | moderate (forward sim) | infinitesimal-limit question |
| 6 | hwe_mellin_condensation | 11 | moderate | critical-order claim untested |
| 7 | spectral_readout_degradation | 10 | cheap | no |
| 8 | pc_correction_residual_confounding | 7 | moderate (PCA) | finite-sample leakage |
| 9 | transported_minimax_rates | 7 | cheap | **YES — already fired, in-source** |
| 10 | gaussian_summary_likelihood_test | 6 | trivial | LRT reference distribution |
| 11 | reclassification_nri | 5 | trivial | no-upward-movement assumption |
| 12 | bayes_risk_of_predictor_class | 5 | cheap | needs `F` instantiated to exist |
| 13 | imputation_attenuation | 4 | moderate | **YES — linear vs exponential LD decay** |
| 14 | recalibration_sample_size | 3 | trivial | bound-vs-attained |
| 15 | pgs_accuracy_vs_training_n | 1 (~15) | cheap | no |

**If only three get built**: `probe_blindness_witnesses` (27 members, finite
arithmetic, and it tests the corpus's own claim about what its guards can
catch), `graded_moment_certificate` (an explicit exponent that a linear program
either reproduces or does not), and `transported_minimax_rates` (7 members and
the disagreement is already recorded in the source — the simulator's job is to
put an error bar on it and decide whether a definition should be deleted).
