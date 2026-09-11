/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
  `KernelRealizationPreservation`.
* §2.2, equations (6)-(9) and (12), the enlarged left/right heterozygosity family, its generator
  and the embedding intertwining: `EnlargedLowOrderLDGenerator`, `EnlargedBodyClosedness`.
* §2.3, equations (10)-(11), the physical kernels: `SimplexResamplingKernel`,
  `ResamplingJetExpansion`, `RandomStageKernel`, `PulseJetExpansion`, `PulseStageKernel`,
  `TwoLocusMicroscopicKernel`, `Pi2GeneratorBridges`, `EnlargedGeneratorBridges`; the
  multinomial moments of equation (10): `MultinomialMomentExpansion`; composing finitely many
  stages into one step with an explicit O(h²) remainder: `StageCompositionKernel`; the literal
  composition of the two-locus physical stages as a second microscopic approximation of the
  enlarged generator, with nothing assumed: `TwoLocusStageComposition`.
* Theorem 2 and Corollary 2.1, with no hypotheses: `TwoLocusMicroscopicApproximation`
  (`enlargedMicroscopicApproximation`, `rateEpoch_preserves_locusExchangeable_realization`,
  `history_present_locusExchangeable_realization`, `history_LDPairDomain`); the closedness-taking
  forms are `TwoLocusRealizabilityPreservation`; histories that also carry admixture pulses:
  `PulseHistoryRealization`.
* §2.4 time-varying rates: `PiecewiseConstantBodyPreservation` (piecewise-constant),
  `LinearFundamentalMatrix` and `IntegrableRateHistoryRealization` (rate paths whose generator is
  continuous in time); rate histories with integrable rate coordinates, with the generator
  Lipschitz in the rates and the propagator the unique continuous solution of the integral
  equation: `RateGeneratorLipschitz`, `IntegrableGeneratorPropagator`,
  `IntegrableRateRealization`.
* §3 Theorem 3 and equations (14)-(16): `StationaryRealization`,
  `StationaryHaplotypeRealization`, `AncestralHaplotypeRealization`.
* §4.1 per-locus material grading: `PartialHaplotypeCarrier`. §4.2, the derivation of (19): the
  neutral diffusion generator on partial-haplotype moments, its Leibniz expansion over carriers,
  and the same-deme merger and killing terms: `PartialHaplotypeDualGenerator`. §4.2 and §5.1
  substochastic semigroups and uniformization: `SubstochasticGeneratorSemigroup`,
  `PoissonTruncationCertificate`. §4.2a, the extension of a positive constant-preserving
  semigroup from polynomials and its representation by Markov kernels obeying
  Chapman-Kolmogorov: `PolynomialFellerExtension`, `FellerKernelRepresentation`,
  `FellerMarkovKernel`. §4.3 equations
  (21)-(23): `ConditionalReportCompilation`.
* §5 equations (24)-(25): `SublawReportCertificate`.
* §6 equations (27)-(36), chronology to metrics: `AdmixtureChronologyLaw`,
  `ChronologyReportLaw`, `AttainableChronologyCurve`, `ExposureLaplaceConstraints`,
  `FinitePulseExposure`.
* §7 equations (37)-(42), finite cohorts: `FourCellCohortLaw`,
  `EmpiricalCorrelationDefinedness`, `SmallCohortCorrelation`, `SmallCohortConditionalMeans`,
  `EmpiricalAUCUnbiasedness`, with (42) restated for the corpus metrics of the empirical table
  law: `EmpiricalTableLawMetrics`.

Scope. Equation (10) is proved for every monomial of degree at most four with remainder at
most 71/N², but both microscopic approximations behind Theorem 2 use the single-draw resampling
step of §2.3, and `TwoLocusStageComposition` runs migration as one pulse per ordered pair rather
than one simultaneous mixture. §2.4 is proved for rate histories with integrable rate
coordinates; the propagator is characterized by the integral equation, and its
almost-everywhere derivative is not stated. Theorem 2 covers histories of rate epochs, splits
and admixture pulses; the pipeline compiler emits nothing else. Of §4.2, the migration,
recombination and mutation rates of (19) and equation (20) are not formalized. The §4.2a
kernels are Markov kernels on pseudo-metrizable compact spaces, which include the
haplotype-frequency simplex; the general compact Hausdorff case is not formalized. The
finite-cohort intercept and accuracy of §7 are not formalized.

Guard witnesses: `LowOrderLDWitnesses` inhabits the corpus rate, epoch and history structures
from data alone, and `PipelineWitnesses` inhabits the pipeline structures of `EndToEndScoreLaw`
from a deme count.

## NOTE2: the input-to-output report law

* Theorem 1 and equation (7), the complete report law of a finite dependent trace tree, with
  forward propagation, backward evaluation and trace enumeration agreeing: `FiniteTraceTreeLaw`.
  The rational clause and equations (3)-(6): `RationalReportClosure`, `MeiosisGameteLaw`.
* §3.2 equations (9)-(10): `ArchitectureEnvironmentRegion`.
* Theorem 3 and §4.1 equations (12)-(14): `ReplicaMomentCompleteness`,
  `ReplicaFiniteOrderNecessity`, `ThetaFamilyNonclosure`; §4, the tagged source/target mixture
  determining the joint population law: `TaggedMixtureCompleteness`.
* §5 equations (15)-(20): `PositiveRatioExpansion`, `ReplicaDomainCertificate`,
  `SmallDenominatorRates`; Theorem 4 over an arbitrary probability measure, with convergence of
  both certificate endpoints: `ReplicaMeasureCertificate`; the sharp gamma constant of (20) and
  equations (28)-(29): `SmallDenominatorLayerCake`. §6.1 equations (24)-(26):
  `JointRatioFailureMasks`; joint moments determining the joint and masked metric laws:
  `JointMetricMomentDeterminacy`. §6.2:
  `PortabilityRatioQueries`. §6.3 example: `UnboundedSlopeExample`. §6.4 equation (30):
  `LogLossSeriesCertificate`.
* §7.1 equation (31): `EmpiricalLawLipschitzBound`; the modulus-of-continuity extension to every
  continuous functional: `EmpiricalLawContinuityBound`. §7.2 Theorem 5 and equation (32):
  `IntervalEvaluatorCertificate`; Theorem 5 on genuine fair-bit cylinders with the coupled
  bracket (18) at every stage: `CylinderIntervalCertificate`; the executed uniform draw:
  `CylinderUniformDraw`; threshold comparisons with unresolved boundary mass and coordinate
  rounding: `CylinderThresholdCertificate`; equation (32), the report law of an almost surely
  terminating random-bit program: `CylinderHaltingLaw`.
* §8 equations (33)-(35): `FrontierCompletionRegion`, with (35) in `SublawReportCertificate`;
  the conditional-mean image of a convex set of completions need not be convex:
  `FrontierCompletionRegion.exists_convex_not_convex_conditionalMeans`.
* §9, the executed reference experiment: the model in corpus vocabulary and its exact
  source-side report law, including the defined probability `4051/6750` of the source squared
  correlation: `ReferenceExperimentLaw`.
* §9.1, the uniform penetrance architecture: `UniformPenetranceArchitecture`.
* §10, the halting boundary: `HaltingExpectationBoundary`.

Scope. Theorem 2's semialgebraic partition is proved only for the architecture/environment
square. Equations (20), (28) and (29) take the pointwise bounds `0 ≤ D ≤ 1`, as the corpus
certificates do. Theorem 1 makes no complexity claim and covers no infinite branch set. The
model and source rows of the §9 reference experiment are proved; its target histories and the
target rows of its table are not formalized yet. `IntervalEvaluatorCertificate` assumes a
finite measure, a common bound and pointwise vanishing widths;
`CylinderIntervalCertificate` needs only almost sure vanishing widths on fair-bit streams but
does not show that its rational values are computed by an algorithm. (32) takes almost sure
termination of the program as a hypothesis; it is not decided. Equations (33) and (34) are
proved for finitely many cells and coordinates, with the whole region attained by completions.
-/

end Descent.Program
