/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialStageComposition
import Descent.Portability.FiniteMixtureKernel
import Descent.Portability.RealizationBody
import Descent.Portability.AffineCaratheodoryCount
import Descent.Portability.EulerInvariantSet
import Descent.Portability.KernelRealizationPreservation
import Descent.Portability.EnlargedLowOrderLDGenerator
import Descent.Portability.EnlargedBodyClosedness
import Descent.Portability.SimplexResamplingKernel
import Descent.Portability.ResamplingJetExpansion
import Descent.Portability.RandomStageKernel
import Descent.Portability.PulseJetExpansion
import Descent.Portability.PulseStageKernel
import Descent.Portability.TwoLocusMicroscopicKernel
import Descent.Portability.Pi2GeneratorBridges
import Descent.Portability.TwoLocusMicroscopicApproximation
import Descent.Portability.TwoLocusRealizabilityPreservation
import Descent.Portability.PiecewiseConstantBodyPreservation
import Descent.Portability.StationaryRealization
import Descent.Portability.StationaryHaplotypeRealization
import Descent.Portability.AncestralHaplotypeRealization
import Descent.Portability.PipelineLDPairDomain
import Descent.Portability.PartialHaplotypeCarrier
import Descent.Portability.SubstochasticGeneratorSemigroup
import Descent.Portability.PoissonTruncationCertificate
import Descent.Portability.ConditionalReportCompilation
import Descent.Portability.SublawReportCertificate
import Descent.Portability.AdmixtureChronologyLaw
import Descent.Portability.ChronologyReportLaw
import Descent.Portability.AttainableChronologyCurve
import Descent.Portability.ExposureLaplaceConstraints
import Descent.Portability.FinitePulseExposure
import Descent.Portability.FourCellCohortLaw
import Descent.Portability.EmpiricalCorrelationDefinedness
import Descent.Portability.SmallCohortCorrelation
import Descent.Portability.SmallCohortConditionalMeans
import Descent.Portability.EmpiricalAUCUnbiasedness
import Descent.Portability.RationalReportClosure
import Descent.Portability.MeiosisGameteLaw
import Descent.Portability.ArchitectureEnvironmentRegion
import Descent.Portability.ReplicaMomentCompleteness
import Descent.Portability.ReplicaFiniteOrderNecessity
import Descent.Portability.ThetaFamilyNonclosure
import Descent.Portability.PositiveRatioExpansion
import Descent.Portability.ReplicaDomainCertificate
import Descent.Portability.SmallDenominatorRates
import Descent.Portability.JointRatioFailureMasks
import Descent.Portability.PortabilityRatioQueries
import Descent.Portability.UnboundedSlopeExample
import Descent.Portability.LogLossSeriesCertificate
import Descent.Portability.EmpiricalLawLipschitzBound
import Descent.Portability.IntervalEvaluatorCertificate
import Descent.Portability.FrontierCompletionRegion
import Descent.Portability.UniformPenetranceArchitecture
import Descent.Portability.HaltingExpectationBoundary
import Descent.Portability.LowOrderLDWitnesses
import Descent.Portability.EnlargedGeneratorBridges
import Descent.Portability.MultinomialMomentExpansion
import Descent.Portability.LinearFundamentalMatrix
import Descent.Portability.IntegrableRateHistoryRealization
import Descent.Portability.PolynomialFellerExtension
import Descent.Portability.FellerKernelRepresentation
import Descent.Portability.PartialHaplotypeDualGenerator
import Descent.Portability.SmallDenominatorLayerCake
import Descent.Portability.FiniteTraceTreeLaw
import Descent.Portability.PipelineWitnesses
import Descent.Portability.StageCompositionKernel
import Descent.Portability.EmpiricalTableLawMetrics
import Descent.Portability.ReplicaMeasureCertificate
import Descent.Portability.EmpiricalLawContinuityBound
import Descent.Portability.CylinderIntervalCertificate
import Descent.Portability.TwoLocusStageComposition
import Descent.Portability.PulseHistoryRealization
import Descent.Portability.RateGeneratorLipschitz
import Descent.Portability.IntegrableGeneratorPropagator
import Descent.Portability.IntegrableRateRealization
import Descent.Portability.FellerMarkovKernel
import Descent.Portability.TaggedMixtureCompleteness
import Descent.Portability.JointMetricMomentDeterminacy
import Descent.Portability.CylinderUniformDraw
import Descent.Portability.CylinderThresholdCertificate
import Descent.Portability.CylinderHaltingLaw
import Descent.Portability.ReferenceExperimentLaw
import Descent.Portability.PartialHaplotypeDualSemigroup
import Descent.Portability.InterleavedHistoryRealization
import Descent.Portability.MultinomialDriftStage
import Descent.Portability.SimultaneousMigrationPulse
import Descent.Portability.IntegralEquationDerivative
import Descent.Portability.NeutralFellerGenerator
import Descent.Portability.RationalParameterReports
import Descent.Portability.ReplicaMetricInstances
import Descent.Portability.ContinuousExampleCertificate
import Descent.Portability.ReferenceLogLossCertificate
import Descent.Portability.UniformPenetranceCertificate
import Descent.Portability.PartialHaplotypePanelLikelihood
import Descent.Portability.PartialHaplotypePulseKernel
import Descent.Portability.PortabilityMeasureQueries
import Descent.Portability.MultinomialRemainderConstant
import Descent.Portability.MultinomialJetCertificate
import Descent.Portability.MultinomialMicroscopicApproximation
import Descent.Portability.MeasureKernelRealization
import Descent.Portability.CylinderExponentialDraw
import Descent.Portability.CylinderGaussianDraw
import Descent.Portability.PortabilityRemainsJoint
import Descent.Portability.DriftOperatorCoordinates
import Descent.Portability.ChronologyIntegralEquation
import Descent.Portability.NonnegativeCoalescenceRealization
import Descent.Portability.NeutralPolynomialSemigroup
import Descent.Portability.NonnegativeIntegrableRealization
import Descent.Portability.PartialHaplotypeMicroscopicApproximation
import Descent.Portability.PartialHaplotypeRealizedPanel
import Descent.Portability.NeutralPolynomialPositivity
import Descent.Portability.NeutralBernsteinPositivity
import Descent.Portability.NeutralMicroscopicEulerLimit
import Descent.Portability.NeutralMicroscopicFloorLimit
import Descent.Portability.NeutralKernelPanelLikelihood
import Descent.Portability.NeutralMarkovKernelUniqueness
import Descent.Portability.NeutralHistoryKernel
import Descent.Portability.PartialHaplotypeEventHistoryRealization
import Descent.Portability.NeutralPulseHistoryKernel
import Descent.Portability.NeutralDemeRelabelKernel
import Descent.Portability.NeutralFellerProperty
import Descent.Portability.NeutralFellerContinuity
import Descent.Portability.NeutralRateHistoryRealization
import Descent.Portability.NeutralRateHistoryKernel
import Descent.Portability.ReferenceExperimentCohortRows
import Descent.Portability.CylinderGaussianQuadrant
import Descent.Portability.CylinderComputableCertificate
import Descent.Portability.MultinomialHistoryRealization
import Descent.Portability.PartialHaplotypeHistoryRealization
import Descent.Portability.NonnegativeMicroscopicApproximation
import Descent.Portability.CylinderUniformLaw
import Descent.Portability.CylinderBoxMullerLaw

namespace Descent.Program

/-!
# Exact portability laws: constructive realizability and the complete report law

References: the two research notes of 11 September 2026 against this archive. NOTE1 is
"Constructive realizability and exact report laws for demographic portability"; NOTE2 is "A
constructive input-to-output theory for genetic portability". Equation and theorem numbers
below are the notes' own. Every module listed was checked on the pinned toolchain with axioms
limited to `propext`, `Classical.choice` and `Quot.sound`. Where a statement is proved in a
narrower form, the scope line says so and the module docstring repeats it.

## The endpoint obligation

`Descent.Portability.EndToEndScoreLaw` required a realizability corollary: the propagated `DD`
kernel stays positive semidefinite, constructing `LDPairDomain` whenever within-deme `DD` is
nonzero. `Descent.Portability.PipelineLDPairDomain` discharges it for every visible pipeline
history, with no hypotheses: `present_locusExchangeable_realization`,
`PipelineDemographicHistory.twoLocusMoments_DD_quadraticForm_nonneg`,
`PipelineDemographicHistory.ldPairDomain`, and
`VisiblePipelineInput.unascertainedLDCorrelationSq_some_mem_unitInterval`.

## NOTE1: realizability of the low-order two-locus moment field

* §2.1 realization bodies and atom counts: `RealizationBody`, `AffineCaratheodoryCount`,
  `FiniteMixtureKernel`.
* Theorem 1 (positive microscopic approximation preserves the body): `EulerInvariantSet`,
  `KernelRealizationPreservation`; for microscopic kernels given by probability measures:
  `MeasureKernelRealization`.
* §2.2, equations (6) and (12), the enlarged left/right heterozygosity family, its generator
  and the embedding intertwining: `EnlargedLowOrderLDGenerator`, `EnlargedBodyClosedness`; the
  migration, mutation and recombination velocities of (8)-(9) as pulse jets: `PulseJetExpansion`.
* §2.3, equations (10)-(11), the physical kernels: `SimplexResamplingKernel`,
  `ResamplingJetExpansion`, `RandomStageKernel`, `PulseJetExpansion`, `PulseStageKernel`,
  `TwoLocusMicroscopicKernel`, `Pi2GeneratorBridges`, `EnlargedGeneratorBridges`; the
  multinomial moments of equation (10): `MultinomialMomentExpansion`; composing finitely many
  stages into one step with an explicit remainder for the cross terms: `StageCompositionKernel`;
  the literal composition of the two-locus physical stages as a second microscopic approximation
  of the enlarged generator, with nothing assumed: `TwoLocusStageComposition`; the note's
  multinomial drift stage with `⌈1/(c h)⌉` chromosomes and the simultaneous migration stage,
  each with its first-order expansion: `MultinomialDriftStage`, `SimultaneousMigrationPulse`; the
  uniform remainder `71 / N²` of (10): `MultinomialRemainderConstant`; polynomial certificates
  presenting every enlarged coordinate to (10): `MultinomialJetCertificate`; the stages assembled
  into a microscopic approximation whose branch type grows as the step shrinks, with Theorem 1
  for such approximations: `MultinomialMicroscopicApproximation`; the literal composition of the
  physical stages, simultaneous migration and multinomial resampling among them, as a microscopic
  approximation padded by Carathéodory's count to a fixed branch type:
  `MultinomialStageComposition`.
* Theorem 2 and Corollary 2.1, with no hypotheses: `TwoLocusMicroscopicApproximation`
  (`enlargedMicroscopicApproximation`, `rateEpoch_preserves_locusExchangeable_realization`,
  `history_present_locusExchangeable_realization`, `history_LDPairDomain`); one epoch through
  multinomial resampling: `MultinomialMicroscopicApproximation`
  (`multinomialEpoch_preserves_locusExchangeable_realization`); the closedness-taking
  forms are `TwoLocusRealizabilityPreservation`; histories that also carry admixture pulses:
  `PulseHistoryRealization`; finite interleavings of continuous-rate and integrable-rate segments
  with splits and pulses: `InterleavedHistoryRealization`.
* §2.4 time-varying rates: piecewise-constant rates through the rate epochs of
  `TwoLocusMicroscopicApproximation`, with `PiecewiseConstantBodyPreservation` the per-epoch
  form that takes an approximation as a hypothesis;
  `LinearFundamentalMatrix` and `IntegrableRateHistoryRealization` (rate paths whose generator is
  continuous in time); rate histories with integrable rate coordinates, with the generator
  Lipschitz in the rates and the propagator the unique continuous solution of the integral
  equation: `RateGeneratorLipschitz`, `IntegrableGeneratorPropagator`,
  `IntegrableRateRealization`; the almost-everywhere derivative `U' = A(t) U` and absolute
  continuity of that propagator: `IntegralEquationDerivative`. For the partial-haplotype dual of
  (20) with a continuous dual generator, the propagator of the rate history keeps the realization
  body invariant and is realized by a finitely supported law
  (`NeutralRateHistoryRealization.exists_rateHistoryLaw`), and the expected panel reports of the
  sampled epochs converge to it (`tendsto_integral_panelReport_sampledEpochs`). The sampled history
  kernels converge uniformly in law to the Markov kernel of the time-varying history
  (`NeutralRateHistoryKernel.tendstoUniformly_integral_sampledHistoryKernel`), under which the
  configuration moments are `U(T) H(x)` (`integral_momentPolynomial_rateHistoryKernel`) and the
  panel reports follow (`integral_panelReport_rateHistoryKernel`).
* §3 Theorem 3 and equations (14)-(16): `StationaryRealization`,
  `StationaryHaplotypeRealization`, `AncestralHaplotypeRealization`.
* §4.1 per-locus material grading and the loose configuration bound `C(K+B,B)`:
  `PartialHaplotypeCarrier`. §4.2 equation (19) in transition-rate form, with nonnegative rates
  and every transition preserving the budget (18): `PartialHaplotypeDualGenerator`; equation
  (20), the expected moment vector as the matrix exponential of the dual generator:
  `PartialHaplotypeDualSemigroup`; sampled-panel likelihoods at the seed configurations:
  `PartialHaplotypePanelLikelihood`; the finite substitution kernels of splits and admixture
  pulses: `PartialHaplotypePulseKernel`. §4.2 and §5.1
  substochastic semigroups and uniformization: `SubstochasticGeneratorSemigroup`,
  `PoissonTruncationCertificate`. §4.2a, the extension of a positive constant-preserving
  semigroup from polynomials and its representation by Markov kernels obeying
  Chapman-Kolmogorov: `PolynomialFellerExtension`, `FellerKernelRepresentation`,
  `FellerMarkovKernel`; Markov kernels whose generator on polynomials is the neutral diffusion
  generator, given the polynomial semigroup: `NeutralFellerGenerator`. The extended neutral
  semigroup is a Feller semigroup, strongly continuous at every time
  (`NeutralFellerProperty.continuous_neutralSemigroupExtension`), with a jointly continuous
  transition function (`continuous_integral_neutralMarkovKernel_prod`) and kernels continuous in
  the state for the weak topology (`continuous_neutralKernelProbability`). §4.3 equation (21) is
  `FiniteReportLaw.expectation_bind` of
  `ExactFiniteHistoryLaw`; equations (22)-(23): `ConditionalReportCompilation`.
* §5 equations (24)-(25): `SublawReportCertificate`.
* §6 equations (27)-(36), chronology to metrics: `AdmixtureChronologyLaw`,
  with (27) in integral form for locally integrable rates and unique among continuous solutions:
  `ChronologyIntegralEquation`; `ChronologyReportLaw`, `AttainableChronologyCurve`,
  `ExposureLaplaceConstraints`, `FinitePulseExposure`.
* §7 equations (37)-(42), finite cohorts: `FourCellCohortLaw`,
  `EmpiricalCorrelationDefinedness`, `SmallCohortCorrelation`, `SmallCohortConditionalMeans`,
  `EmpiricalAUCUnbiasedness`, with (42) and the finite-cohort intercept, accuracy and Brier laws
  restated for the corpus metrics of the empirical table law: `EmpiricalTableLawMetrics`.

Scope. Theorem 1 is proved for microscopic kernels given by probability measures with integrable
features, with the approximation hypothesis (3) in sup norm.
Equation (10) is proved for every polynomial of total degree at most four, with remainder
`71 · coefficientMass / N²`. The drift
operator (7) is stated literally on polynomials in `p`, `q`, `D`, with its two displayed
identities, and its sum against the coalescence rates is the drift row of the enlarged generator
on every stored coordinate: `DriftOperatorCoordinates`.
The epoch form of Theorem 2 is proved through the note's multinomial sample of size `⌈1/(c h)⌉`
in `MultinomialMicroscopicApproximation`, whose microscopic kernels change branch type with the
step size, for every deme count with at least one deme. The history forms of epochs, splits and
pulses go through the same multinomial sample: `MultinomialHistoryRealization`. The single-draw
route with `N = ⌈(c h)^(-1/2)⌉` remains in `TwoLocusMicroscopicApproximation`. The note's
literal composition of physical stages, with simultaneous migration and multinomial resampling,
is a microscopic approximation with a padded fixed branch type in `MultinomialStageComposition`.
The corpus rate laws have strictly positive coalescence, where the note allows `c_i ≥ 0`;
Theorem 2 and Corollary 2.1 extend to nonnegative coalescence for histories of constant-rate
epochs and splits, through the limit of perturbed corpus epochs:
`NonnegativeCoalescenceRealization`, and for rate histories with integrable rate coordinates:
`NonnegativeIntegrableRealization`. The microscopic kernel with the sampling stage omitted at
`c_i = 0` gives the epoch form directly: `NonnegativeMicroscopicApproximation`. §2.4 is proved
for rate histories with integrable rate coordinates; the propagator is characterized by the
integral equation. Theorem 2 covers histories of rate epochs, splits and admixture pulses;
the pipeline compiler emits nothing else. Of §4.2, mutation is symmetric. The forward moment
equation that (20) takes as a hypothesis is discharged for every neutral model by the realized
expectation family of the neutral microscopic approximation:
`PartialHaplotypeMicroscopicApproximation.realizedExpectation_forward`. That family matches the
diffusion on the moments of one fixed budget and is not shown to be the marginal law of a single
process across budgets; the exact panel reports follow with no hypothesis:
`PartialHaplotypeRealizedPanel`. Along a history of epochs, splits and admixture pulses the
realized moments compose in chronological order
(`PartialHaplotypeHistoryRealization.exists_historyLaw`,
`PartialHaplotypeEventHistoryRealization.expectedMomentVector_eventHistory_realized`), and so do
the neutral Markov kernels along epochs
(`NeutralHistoryKernel.integral_panelReport_neutralHistoryKernel`), along splits and pulses
(`NeutralPulseHistoryKernel.integral_momentPolynomial_historyEventKernel`) and across a change of
the deme set (`NeutralDemeRelabelKernel.integral_momentPolynomial_splitHistoryKernel`). The
neutral Markov
kernels are unique (`NeutralMarkovKernelUniqueness.existsUnique_neutralMarkovKernel`). The §4.2a
polynomial semigroup is constructed from the dual
matrix exponential, with its unit, semigroup law and dual representation
(`NeutralPolynomialSemigroup`), and is positive (`NeutralPolynomialPositivity`, and by a Bernstein
argument `NeutralBernsteinPositivity.nonneg_of_monomial_nonneg`), so every
hypothesis of `NeutralFellerGenerator.exists_markovKernel_neutralGenerator` is proved: neutral
Markov kernels exist for every neutral model, represent the polynomial semigroup, compose, and
carry the neutral generator on configuration moments (`exists_neutralMarkovKernel`). The Euler
limit holds: the microscopic kernel powers along `N` steps of size `t/N` converge uniformly to the
neutral semigroup on every continuous observable, and its Riesz kernels are Markov and compose
(`NeutralMicroscopicEulerLimit.tendstoUniformly_neutralSemigroupExtension`,
`neutralMarkovKernel_add`), and (19) holds for them
(`NeutralMicroscopicEulerLimit.hasDerivWithinAt_integral_neutralMarkovKernel`). The floor form
`K_h^{⌊t/h⌋} f → T_t f` holds as well and discharges the hypothesis of
`PolynomialFellerExtension.markov_of_euler_tendstoUniformly`
(`NeutralMicroscopicFloorLimit.neutralPolynomialSemigroup_markov_of_euler`), and the kernel
integrals converge uniformly along it (`tendstoUniformly_integral_neutralMarkovKernel_floor`).
Continuity at `t = 0` holds on each polynomial space and then on every continuous observable
(`NeutralFellerContinuity.tendsto_neutralSemigroupExtension_zero`,
`tendstoUniformly_integral_neutralMarkovKernel_zero`). Under those kernels,
one process for every budget, the configuration
moments of (20) and the panel reports of (22) hold:
`NeutralKernelPanelLikelihood.integral_panelReport_neutralMarkovKernel`. The kernels
are Markov kernels on pseudo-metrizable compact spaces, which include the haplotype-frequency
simplex. In §6 the attainable metric curve of NOTE1 Theorem 5 is proved exactly for lists of
discrete events, and for chronologies with continuous nonnegative rates at a positive horizon
with a positive migration total: `AttainableChronologyCurve.attainable_metric_curve_continuous`.

Guard witnesses: `LowOrderLDWitnesses` inhabits the corpus rate, epoch and history structures
from data alone, and `PipelineWitnesses` inhabits the pipeline structures of `EndToEndScoreLaw`
from a deme count.

## NOTE2: the input-to-output report law

* Theorem 1 and equation (7), the complete report law of a finite dependent trace tree, with
  forward propagation, backward evaluation and trace enumeration agreeing: `FiniteTraceTreeLaw`.
  The rational clause and equations (3)-(6): `RationalReportClosure`, `MeiosisGameteLaw`.
* §3.2 equations (9)-(10): `ArchitectureEnvironmentRegion`. Theorem 2: the joint input-output
  graph (8) of a finite algebraic experiment is an explicit finite union of polynomial
  sign-condition sets over its guard cells, and the attainable region is its projection:
  `RationalParameterReports`.
* Theorem 3 and §4.1 equations (12)-(14): `ReplicaMomentCompleteness`,
  `ReplicaFiniteOrderNecessity`, `ThetaFamilyNonclosure`; §4, the tagged source/target mixture
  determining the joint population law: `TaggedMixtureCompleteness`.
* §5 equations (15)-(20): `PositiveRatioExpansion`, `ReplicaDomainCertificate`,
  `SmallDenominatorRates`; Theorem 4 over an arbitrary probability measure, with convergence of
  both certificate endpoints: `ReplicaMeasureCertificate`; the sharp gamma constant of (20) and
  equations (28)-(29): `SmallDenominatorLayerCake`; §5.4, concrete population metrics as bounded
  replica ratios: `ReplicaMetricInstances`. §6.1 equations (24)-(26):
  `JointRatioFailureMasks`; joint moments determining the joint and masked metric laws:
  `JointMetricMomentDeterminacy`. §6.2:
  `PortabilityRatioQueries`, and under an arbitrary probability measure:
  `PortabilityMeasureQueries`; two couplings with the same marginal source and target laws and
  different comparison queries: `PortabilityRemainsJoint`. §6.3 example: `UnboundedSlopeExample`.
  §6.4 equation (30): `LogLossSeriesCertificate`.
* §7.1 equation (31): `EmpiricalLawLipschitzBound`; the modulus-of-continuity extension to every
  continuous functional: `EmpiricalLawContinuityBound`. §7.2, interval evaluators without nesting
  and Kraft's inequality for prefix enumerations: `IntervalEvaluatorCertificate`; Theorem 5 on
  genuine fair-bit cylinders, with nested certificates and a bracket of the shape of (18) at every
  stage: `CylinderIntervalCertificate`; the executed uniform draw:
  `CylinderUniformDraw`; the executed exponential draw `-log U`, with certificates converging to
  `E min(X, 1) = 1 - 1/e`: `CylinderExponentialDraw`; the Box-Muller pair on the even and odd
  bits, with radial certificates converging to `E min(Z₁² + Z₂², 2) = 2(1 - 1/e)`:
  `CylinderGaussianDraw`; the laws of the draws: the uniform draw is Lebesgue measure on `(0, 1)`
  and the exponential draw is `expMeasure 1` (`CylinderUniformLaw.map_uniformDraw`,
  `map_exponentialDraw`), and the Box-Muller pair has the standard bivariate Gaussian law with
  independent coordinates (`CylinderBoxMullerLaw.map_gaussianPair`, `indepFun_gaussianPair`);
  threshold comparisons with unresolved boundary mass and coordinate
  rounding: `CylinderThresholdCertificate`; equation (32), the report law of an almost surely
  terminating random-bit program: `CylinderHaltingLaw`.
* §8 equations (33)-(35): `FrontierCompletionRegion`, with (35) in `SublawReportCertificate`;
  the conditional-mean image of a convex set of completions need not be convex:
  `FrontierCompletionRegion.exists_convex_not_convex_conditionalMeans`.
* §9, the executed reference experiment: the model in corpus vocabulary, its exact source-side
  report law matching the attached results, and the 220 architecture, environment and census
  states of both histories, and the early-migration target squared-correlation definedness
  probability: `ReferenceExperimentLaw`; eighty-term log-loss
  certificates for any rational law of the experiment's observations:
  `ReferenceLogLossCertificate`.
* §9.1, the uniform penetrance architecture: `UniformPenetranceArchitecture`; its eighty-term
  replica certificate, of width below `10^-24`: `ContinuousExampleCertificate`; executed
  Theorem 5 on it, with cylinder certificates converging to the squared-correlation and AUC
  integrals: `UniformPenetranceCertificate`.
* §10, the halting boundary: `HaltingExpectationBoundary`.

Scope. Theorem 2's graph is presented through the sign cells of the experiment's supplied
polynomial guards, with regularity on each cell as a hypothesis; Mathlib's semialgebraic sets and
real quantifier elimination, which the note uses to eliminate parameters from (8), are not
available at this pin. The mixing
law of (31) ranges over finitely many contexts, and its Lipschitz class is taken on all of the
coordinate space. Equations (20), (28) and (29) take the pointwise bounds `0 ≤ D ≤ 1`, as the corpus
certificates do. Theorem 1 makes no complexity claim and covers no infinite branch set. Of §9,
the other population target table rows, the 3960 shared-context count and the full-square range
table are not yet proof-checked; the size-three cohort rows are proved in
`ReferenceExperimentCohortRows`.
`IntervalEvaluatorCertificate` assumes a
finite measure, a common bound and pointwise vanishing widths;
`CylinderIntervalCertificate` needs only almost sure vanishing widths on fair-bit streams; its
certificates are computed by recursion on word length (`CylinderComputableCertificate`,
`lowerSum_eq_cylinderSum`, `upperSum_eq_cylinderSum`), with the uniform and quadrant instances
evaluated in the kernel, and no efficient algorithm is given. (32) takes almost sure
termination of the program as a hypothesis; it is not decided. The exponential and Gaussian
certificates are executed for integrands of `min(X, 1)`, of the radius, and of the angle through
the positive quadrant (`CylinderGaussianQuadrant.tendsto_quadrant_certificate`); the laws of the
draws and the Box-Muller theorem are proved as measure identities.
Equations (33) and (34) are
proved for finitely many cells and coordinates, with the whole region attained by completions.
-/

end Descent.Program
