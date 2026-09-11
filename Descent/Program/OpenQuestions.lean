/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityDrift.PresentDayMetrics
import Descent.Portability.IndividualLossMoments
import Descent.Portability.MechanismIdentification
import Descent.Portability.ThresholdPolicyTransport
import Descent.Portability.LossInformationClassification
import Descent.Portability.LossMomentRange
import Descent.Portability.GaussianLossNoise
import Descent.Portability.TraitPortabilityRange
import Descent.Portability.PortabilityCurveClassification
import Descent.Portability.EvolutionaryMetricClosure
import Descent.Portability.MetricOrderingClassification
import Descent.Portability.LossNoiseCompletion
import Descent.Portability.ConditionalFourthMomentLaw
import Descent.Portability.ExplainabilityRay
import Descent.Portability.GaussianCeilingBound
import Descent.Portability.LossPredictorSynergy
import Descent.Portability.FourthMomentDuality
import Descent.Portability.GlobalFourthMomentRegion
import Descent.Portability.FourthMomentMinimizer
import Descent.Portability.FourthMomentAttainableRange
import Descent.Portability.FourthMomentStrongDuality
import Descent.Portability.ScoreMomentZonoid
import Descent.Portability.SymmetricScoreFourthMoment
import Descent.Portability.LossExplainabilityRegion
import Descent.Portability.TransportCoordinates
import Descent.Portability.AlignmentFactorization
import Descent.Portability.FixedBackgroundCurveRegion
import Descent.Portability.SimultaneousRealization
import Descent.Portability.SourceFixedRealization
import Descent.Portability.TurnoverDependence
import Descent.Portability.SynchronyEnvelope
import Descent.Portability.MarginalTurnoverRegion
import Descent.Portability.MarginalSupportBound
import Descent.Portability.UniversalReportMonotonicity
import Descent.Portability.TurnoverCouplingPolytope
import Descent.Portability.TurnoverTrajectoryRegion
import Descent.Portability.CouplingPolytopeExtrema
import Descent.Portability.ContinuousTrajectoryRegion
import Descent.Portability.ConvexOrderCoupling
import Descent.Portability.ContinuousTurnoverSemigroup
import Descent.Portability.TurnoverArchitectureMetrics
import Descent.Portability.BinomialAggregateEnvelope
import Descent.Portability.TurnoverQuadraticVariation
import Descent.Portability.TurnoverExtremalCouplings
import Descent.Portability.NonanticipationCost
import Descent.Portability.NearestDriftConfigurationCoupling
import Descent.Portability.OddLocusReportSolutions
import Descent.Portability.ChannelComparison
import Descent.Portability.ThresholdLawRegion
import Descent.Portability.NonaffineRepair
import Descent.Portability.MetricResponseEllipsoid
import Descent.Portability.MetricInfluenceFunctions
import Descent.Portability.CohortEvaluationOperators
import Descent.Portability.AngularReportClosure
import Descent.Portability.AngularSpectralBounds
import Descent.Portability.AngularExtremalReports
import Descent.Portability.AngularExtremePoints
import Descent.Portability.JointReportFeasibility
import Descent.Portability.FourthOrderLossObstruction
import Descent.Portability.ApproximationDuality
import Descent.Portability.RadialInterpolation
import Descent.Portability.RadialReportLaws
import Descent.Portability.IndependentRadialLaws
import Descent.Portability.SmoothedCoordinateLaws
import Descent.Portability.CubeAverageConvergence
import Descent.Portability.MomentOrderObstruction
import Descent.Portability.DenominatorAwareRecovery
import Descent.Portability.ConditionalOscillationDuality
import Descent.Portability.FiniteGeneticTransition
import Descent.Portability.MechanismReportDerivative
import Descent.Portability.InvariantReportSpace
import Descent.Portability.SparseExtremalLaws
import Descent.Portability.NonlinearMetricGridBound
import Descent.Portability.ReportRegionCertificates
import Descent.Portability.MarginalPathCoupling
import Descent.Portability.ExtraInformationRank
import Descent.Portability.FiniteDualityNoGap
import Descent.Portability.BellmanReportBounds
import Descent.Portability.UniversalConditionalSufficiency
import Descent.Portability.SummaryInvisibleDiameter
import Descent.Portability.CounterfactualRegion
import Descent.Portability.SquaredCorrelationZeroTest

namespace Descent.Program

open MeasureTheory
open scoped ProbabilityTheory
open PopGen.TransportedMetrics (r2FromSignalVariance)

/-!
# Formal Proofs for Open Questions in PGS Portability

Reference: Wang et al. (2026), "Three open questions in polygenic score portability",
Nature Communications 17:942.  DOI: 10.1038/s41467-026-68565-3

## The Three Open Questions

1. **Genetic distance poorly predicts individual-level accuracy.**
2. **Portability trends are trait-specific** (immune traits decay fastest).
3. **Portability depends on the prediction metric** (precision vs recall diverge).

We also formalize sub-questions:
4. Environmental variance heterogeneity confounds R² comparisons.
5. Winner's curse × allelic turnover amplification.
6. PGS variance non-monotonicity for immune traits.
7. Heterozygosity-driven predictor variance increase with distance.

## What this file proves

The mathematical answers are distributed across the imported modules. The labels TQ, UPT, DC
and PL refer to the four proof manuscripts of 10 September 2026 ("Three Questions Mathematical
Manuscript", "Unconditional Portability Theorems", "Dynamic Coupling and Reporting Proofs",
"Portability Is a Law, Not a Distance"); the numbering is the manuscripts' own. Every theorem
named below was checked on the pinned toolchain with axioms limited to `propext`,
`Classical.choice` and `Quot.sound`; every attainment claim is an explicit finite law whose
target quantity is computed exactly. Where a manuscript statement is proved in a narrower
form, the scope line says so and the module docstring repeats it.

### Question 1: individual squared-loss predictability

* `IndividualLossMoments`, `LossInformationClassification`, `LossMomentRange`,
  `GaussianLossNoise`: the squared-loss denominator from conditional second and fourth
  moments, the three-way sigma-algebra decomposition with its almost-sure sufficiency converse
  (TQ 2.1-2.4, UPT 2.1, PL 2.1), the (0,1] family at fixed conditional second moments, and
  the Gaussian squared-loss variance from the actual Gaussian measure.
* `LossNoiseCompletion`: TQ Theorem 2.5, the smallest conditional variance of squared error
  under independent environmental noise of fixed mean and variance, its two-point attaining
  law and the law attaining every larger value; Corollary 2.6, the exact fixed-architecture
  attainable interval of the distance-explainable fraction, every value attained.
* `ConditionalFourthMomentLaw`: UPT Lemma 2.2 (raw-moment completion, both directions) and
  UPT Theorem 2.3 / PL Theorem 2.2, the exact set of conditional squared-loss variances at
  fixed conditional first and second moments, with necessity and attainment.
* `ExplainabilityRay`: UPT Theorem 2.4 / PL Corollary 2.3, the simultaneous explainability
  vector over every summary lies on an explicitly realized ray (an iff), with the
  nested-summary gain (2.9). `GaussianCeilingBound`: the rest of TQ Proposition 2.7, the
  Gaussian interval ceiling, its attainment, and a non-Gaussian law with explainability one.
  `LossPredictorSynergy`: TQ Proposition 2.8, comparable-predictor and synergy constructions.
* `FourthMomentDuality`, `GlobalFourthMomentRegion`, `FourthMomentMinimizer`,
  `FourthMomentAttainableRange`, `FourthMomentStrongDuality`, `ScoreMomentZonoid`,
  `SymmetricScoreFourthMoment`, `LossExplainabilityRegion`: UPT Theorem 3.1 (feasibility of
  prescribed mean, cross-moments and second moment both ways; the minimal residual fourth
  moment; the quartic maximum (3.9) attained at the root of the manuscript's cubic; weak
  duality for every law and multiplier; no duality gap at every certified point, and for a
  finitely supported feature law at every triple strictly inside the region the dual
  supremum equals the primal minimum and is attained by explicit multipliers, (3.8), by
  separating the value point from the attainable moment set with the Slater point removing
  the degenerate coefficient; the
  conditional two-point minimizer; attainment of the minimum for finitely supported laws;
  every fourth moment in the half-line attained strictly inside the region; the singleton on
  the equality face), Theorem 3.2 with both forms of its criterion proved equivalent by
  separating the compact convex score zonoid, Corollaries 3.3 and 3.4 as exact closed forms
  with attaining laws and matching dual values, and Theorem 3.5, the sharp
  loss-explainability region on the variance of an actual multi-cell law with the
  manuscript's example.
  Scope: attainment of the minimum and strong duality are proved for finitely supported
  feature laws (the manuscript's weak compactness in L⁴ × L² is not formalized); three
  boundary statements hold in mean square in general and pointwise for finite support.

### Question 2: architecture statics

* `TransportCoordinates`: TQ Proposition 3.1 / Theorem 3.2 and UPT Theorem 4.3, the
  cross-moment vector in the range of the score second-moment matrix with no invertibility
  assumed, the excess-risk law of any deployed weight, the oracle value's independence of the
  chosen normal-equation solution, the expected target risk of a learned weight law and the
  centered-score squared correlation.
* `AlignmentFactorization`: UPT Theorem 4.1 / PL Theorem 3.1, squared correlation as the
  genotype-explained fraction times squared alignment, the chain 0 ≤ q ≤ H ≤ 1 and its
  equality case, with the residual orthogonality derived from the conditional kernel.
* `FixedBackgroundCurveRegion`: UPT Theorem 4.2 / PL Corollary 3.2, an arbitrary cellwise
  array of outcome variance, heritability and accuracy realized on an unchanged genotype
  background, and the exact product region; the general form of `TraitPortabilityRange`.
* `SimultaneousRealization`: TQ Theorem 8.1 in full (model (8.1), the cell loss mean, the
  sharp loss-fraction interval as an iff, the spike law) and TQ (3.6), with the four-cell
  example evaluated exactly. `SourceFixedRealization`: UPT Theorem 7.1, prescribed
  trait-specific accuracy curves coexisting with any prescribed positive distance-explainable
  loss fraction on an unchanged genotype and source-training law, through an explicit
  four-point residual law.

### Question 2: turnover, synchrony and coupling regions

* `TurnoverDependence`: TQ Theorem 3.5 (expected accuracy under turnover as the exact
  quadratic form (3.8), every sign configuration a complete `DeploymentPopulation`),
  Theorem 3.7 (independent and synchronized turnover share every one-locus law, including
  the two-state generator's exponential retention, yet give expected accuracies 1/2 and 1)
  and Corollary 3.8 (the general-weight law, the three-way monotonicity criterion with its
  time derivative, the random-weight law and the anti-aligned example).
* `SynchronyEnvelope`: TQ Theorem 3.6, the sharp envelope (3.9) for an arbitrary joint sign
  law with prescribed one-locus means and an explicit family attaining every value.
  `MarginalTurnoverRegion`, `MarginalSupportBound`: TQ Theorem 3.9, the attainable range at
  fixed marginal means is a closed interval with both ends attained, each by a law charging
  at most n+1 configurations.
* `UniversalReportMonotonicity`: UPT Theorem 5.1 (universal one-step and generator
  monotonicity, necessary and sufficient) and Corollary 5.2 (the recurrent-evolution
  obstruction, without a stationary law). `TurnoverCouplingPolytope`: UPT Theorem 5.3, the
  coadapted path laws are exactly the stated polytope, nonempty and convex, every intermediate
  report value attained. `TurnoverTrajectoryRegion`: UPT Theorem 5.4, the two-locus
  trajectory law necessary for every coadapted process and sufficient by an explicit flip
  coupling, with the terminal range in both directions. `CouplingPolytopeExtrema`: the
  extremal coadapted path laws exist at every finite horizon (truncation to the horizon and
  a Tychonoff product of unit intervals), so the attainable report set is exactly a closed
  interval. `ContinuousTrajectoryRegion`: UPT (5.10) at the level of agreement paths, every
  admissible path trapped in [e^{−2λt}, 1] and every value attained by an explicit path, with
  the discrete terminal bound at step t/n refining to the continuous lower endpoint as n → ∞.
  Scope: (5.10) is proved for differentiable paths and about paths rather than the
  continuous-time couplings that generate them; all loci share one state alphabet; the
  continuous-time half of UPT 5.1 takes the transition semigroup through its defining
  properties, witnessed by the two-state flip semigroup.

### Question 2: the dynamic theorem

* `ConvexOrderCoupling`: DC Lemmas 3.3-3.4 / PL (5.11)-(5.12) and DC Theorem 3.1 / PL
  Theorem 5.3 in the discrete skeleton with kernels indexed by the entire past: the
  nearest-drift coupling minimizes every convex aggregate functional among all
  rate-preserving, history-dependent couplings.
* `ContinuousTurnoverSemigroup`: the same theorem in continuous time for Markov generators,
  through the nearest-drift generator as a matrix on the count grid, DC Lemma 3.4's
  minimality, and an Euler-limit bridge to the matrix exponential; generator eigenvectors
  pass to the semigroup, every falling factorial is an eigenvector of the pure-death
  generator, and DC Corollary 3.5 holds as an identity of laws: the semigroup row from the
  top state is exactly the binomial law at p = e^{−γt}, with the sharp lower endpoint
  (1−2/n)p² + (2/n)p as its squared-count value; the history-dependent case stays in the
  discrete skeleton, which is complementary.
* `TurnoverArchitectureMetrics`: PL Theorem 5.1 / DC Theorem 4.1, the three exact report laws
  of one realized sign architecture on the corpus's own `DeploymentPopulation` metrics, DC
  (4.2)-(4.3), Proposition 4.6 and Theorem 4.5. `BinomialAggregateEnvelope`: DC Corollary
  3.5, Theorem 4.2, (4.5) / PL Corollary 5.4, the binomial lower envelope, the synchronous
  upper envelope, every intermediate value by mixing, and the invariant mean squared error.
* `TurnoverQuadraticVariation`, `TurnoverExtremalCouplings`, `NonanticipationCost`: DC
  Theorem 4.4 / PL Theorem 5.2 with both bounds of PL (5.6) attained by exhibited couplings,
  the symmetric count generator in closed form, and DC Theorem 5.1 with Corollary 5.2, the
  exact positive cost of nonanticipation.
* `NearestDriftConfigurationCoupling`: DC Lemma 3.2 at the configuration level, the
  pair-and-singleton nearest-drift kernel on sign vectors written as an explicit sum of Dirac
  rows, admissible with each coordinate's prescribed flip probability, whose count process is
  exactly the nearest-drift chain at every horizon, so the envelope's lower endpoint is the
  attained value of an actual joint sign process.
* `OddLocusReportSolutions`: DC Corollary 4.3 — the odd-locus backward system (4.6) has the
  explicit exponential-sum solution, verified clause by clause, unique by an integrating
  factor level by level, with a₃ and a₅ evaluated exactly, and the same values obtained as
  the odd-level generator's semigroup applied to the initial square report through the Euler
  limit; the odd-level generator is the lumping of the symmetric nearest-drift count generator
  under the aggregate map, the lumping intertwines the semigroups (reusable rectangular
  intertwining lemmas through powers, Euler approximants and the exponential), so aₙ(t) is
  exactly the expected terminal square under the minimizing count chain in continuous time.
  Scope: the Duhamel form of DC (4.8) is stated through its generator.

### Question 3: metric dependence

* `ChannelComparison`: TQ Theorem 4.9 / UPT Theorem 6.5, both directions: a row-stochastic
  garbling exists iff every decision rule after the coarser channel is matched at no larger
  expected loss after the finer one, for every finite action set, prior and loss, the
  converse by the closest-garbling minimizer with no hyperplane import.
* `ThresholdLawRegion`: UPT Theorem 6.2 / PL Theorem 4.2, the joint laws at a fixed finite
  score law and prevalence are exactly the submeasures of the score law with the right mass;
  UPT (6.5); TQ Theorem 4.5 / UPT (6.8) / PL (4.4), the sharp fixed-score confusion fiber
  with every value attained and realized as a thresholded score; UPT Corollary 6.3 in its
  finite-grid form and in its continuous form on the line, stated both against a density (a
  curve comes from a submeasure of the score law with the right mass exactly when it is the
  lower-tail integral of a measurable conditional risk bounded by one) and against an actual
  joint law of score and outcome assembled by the continuous Bernoulli construction, with
  the (6.6) increment bounds, endpoints and a uniform-rank-law witness.
* `NonaffineRepair`: TQ Proposition 4.2, over all functions of the score the least MSE is
  the mean conditional variance, attained by the conditional mean, with a strict three-point
  witness against every affine recalibration. `MetricOrderingClassification` and
  `ThresholdPolicyTransport` (earlier) hold TQ 4.1, 4.6, 4.8 and UPT 6.1, 6.4, (6.10).
* `MetricResponseEllipsoid`, `MetricInfluenceFunctions`: TQ Theorem 5.2 (the constrained
  metric-response set as the Gram image with unit quadratic form, the pseudoinverse-free form
  of the manuscript's ellipsoid, with the projection constructed by finite Gram-Schmidt),
  Corollaries 5.3 and 5.4, and all of Proposition 5.1 as derivatives at zero along
  information-preserving paths that remain positive laws.
  Nothing in this package is proved in a narrower form than the manuscript states.

### The reporting layer: the paper's cohort procedures

* `CohortEvaluationOperators`: TQ Theorem 4.3 / UPT 8.2 / DC 7.1-7.2 / PL 6.1, the group
  partial-R² operator as an angular ratio and as the relative reduction in residual sum of
  squares with both sums proved least-squares minima, the sequential residualization
  operator, TQ Proposition 4.4 (sequential equals joint iff the projections commute), the
  centered loss-regression report and UPT Corollary 8.3's fourth-order homogeneity.
* `AngularReportClosure`: PL Theorem 6.2, the angular identity with no symmetry hypothesis,
  the angular matrix of trace one and positive semidefinite, expected reports as traces
  against it; Proposition 6.4, the projective state for even scale-invariant reports.
* `AngularSpectralBounds`, `AngularExtremalReports`, `AngularExtremePoints`: PL Corollary
  6.3 (feasibility by explicit spectral realization, the attaining law on rank-many
  directions, the two-dimension-plus-direction interval, the Ky Fan optimum as an attained
  maximum, and the Barvinok-Pataki bound r(r+1)/2 ≤ m+1 for extreme angular matrices by an
  explicit perturbation inside the positive semidefinite cone), Theorems 9.2 and 9.4.
* `JointReportFeasibility`: PL Theorem 9.3 over a finite state set, the report region as a
  convex hull with its support bound, the dual certificate, and primal attainment.

### Obstructions and their exact price

* `FourthOrderLossObstruction`: TQ Theorem 8.2, two hierarchical mixtures with identical
  genotype and source laws, three-sign effect marginals, conditional first and second
  moments, cellwise MSE and squared-correlation summaries, whose distance-explainable loss
  fractions are exactly 1/12 and 2/27.
* `ApproximationDuality`: PL Theorem 8.1, the largest report disagreement compatible with the
  supplied moments is exactly twice the best uniform approximation error, with the extremal
  moment-matched pair built by separation and both optimal-recovery halves.
* `RadialInterpolation`, `RadialReportLaws`, `IndependentRadialLaws`, `SmoothedCoordinateLaws`,
  `CubeAverageConvergence`: PL Lemma 7.1,
  Theorem 7.2 with (7.4), Corollary 7.3 in both its expectation form and its
  total-variation form ((7.6): each direction marginal is within b/(a+b) of its target in
  `FiniteReportLaw.totalVariation`, hence so is every report law), Corollary 7.5, and Theorem
  7.4's independent finite-support core (for every finite raw-moment order, matched laws
  whose expected scale-invariant report sits arbitrarily close to opposite ends of its range)
  together with its smoothing and product steps: convolving each coordinate with uniform
  noise gives an absolutely continuous probability law with a bounded density whose moments
  are the convolved moments, and the product of the smoothed marginals is a genuinely
  independent bounded-density law whose joint raw moments still match through degree k,
  which is (7.7) in the manuscript's continuous form; and the product of smoothed marginals is
  a finite mixture of uniform cube laws about the atoms, whose expected report converges to
  the finite-support value as the smoothing vanishes (continuity at each atom, no null-set or
  dominated-convergence argument), so Theorem 7.4 holds in its absolutely-continuous form:
  for every order and tolerance, two independent bounded-density product laws with matched
  joint moments whose expected reports sit at opposite ends of the range.
* `MomentOrderObstruction`: DC Lemmas 8.1-8.2 and Theorems 8.3-8.4, no finite joint-moment
  order identifies expected partial R² or expected fitted loss-explainability, with the exact
  instances 27/1768 and −24900075/1099632872; Lemma 8.2 is proved in a stronger form than
  the manuscript's (a bounded nonconstant report has a nonzero forward difference at every
  order, by a step-doubling identity with no analyticity or calculus), so the every-order
  halves carry two independent proofs, the finite-difference one and the radial one.
* `DenominatorAwareRecovery`: PL Theorem 9.1, Chebyshev recovery with its closed-form error
  level. `ConditionalOscillationDuality`: PL Theorem 8.2 and Corollary 8.3 as one duality
  theorem in the noise level.
  Nothing in this package is proved in a narrower form than the manuscript states.

### The pipeline: finite report laws, regions and identification

* `FiniteGeneticTransition`, `MechanismReportDerivative`: TQ Theorems 6.1-6.3 and UPT
  Theorem 8.1, the exact finite genetic transition, the end-to-end report law it induces, and
  the mechanism-to-report derivative with its exponential-tilt form.
* `InvariantReportSpace`, `SparseExtremalLaws`, `NonlinearMetricGridBound`: TQ Theorem 7.2
  (the terminating minimal invariant report space), Theorem 7.3 and Proposition 7.4.
* `ReportRegionCertificates`, `MarginalPathCoupling`, `ExtraInformationRank`,
  `FiniteDualityNoGap`: DC Theorems 2.1-2.2 and Proposition 2.3 (finite refinement form),
  PL Theorems 10.1-10.2, the complete joint report region as a polytope with attained
  extrema, certificates in both directions, exact separation, the per-coordinate dual, the
  rank formula for the minimum extra linear information, and strong duality for DC (2.5) /
  PL (10.4) with an attained dual minimum under a box-form Slater condition.
* `BellmanReportBounds`: DC Theorems 6.1-6.3 and PL Theorem 10.3 in discrete horizon.
  `UniversalConditionalSufficiency`: UPT Theorem 9.1 (finite case).
  `SummaryInvisibleDiameter`: UPT Theorem 9.2 with its attaining law pair.
  `CounterfactualRegion`: UPT Theorem 10.1 and PL Theorem 11.1, complete agreement of reports
  does not imply agreement of causes. `SquaredCorrelationZeroTest`: the mathematical half of
  UPT Theorem 10.2.
  Scope: continuous-time optimality DC (6.5) / PL (10.7) and DC 2.3 in continuous time are
  not formalized (no predictable-rate jump processes at this pin); UPT 9.1 is proved in the
  finite case; UPT 10.2's computability half needs computable reals, absent at this pin.

### Earlier modules

* `MechanismIdentification` (TQ 3.10 nonidentification worlds), `TraitPortabilityRange`,
  `PortabilityCurveClassification` (the local trend law), `EvolutionaryMetricClosure`
  (TQ 7.1), `ThresholdPolicyTransport` (TQ 4.6), `MetricOrderingClassification`,
  `PortabilityMasterTheorem` (exact transport, metric non-equivalence and affine
  recalibration laws) and `Foundations.TransportIdentities` (the probability-space
  conditional variance results) remain the foundation the modules above build on.

These are exact identities, sharp regions and identification limits. They do not establish
the paper's empirical residual moments, identify immune-specific evolutionary causes, or
choose an application's costs. The elementary inequalities below retain their explicit
hypotheses and do not supply those missing measurements.

-/

/-!
## Open Question 1: Law of Total Variance and Weak Predictability

Individual-level squared prediction error ε²ᵢ has high within-group variance.
The law of total variance implies R²(ε², genetic_distance) is small whenever
the conditional variance E[Var(ε²|D)] dominates Var(E[ε²|D]).
-/

section Question1

theorem scalar_summary_insufficient_for_accuracy
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (distance accuracy : V →ₗ[ℝ] ℝ)
    (hnot : ¬ ∃ c : ℝ, accuracy = c • distance) :
    ∀ θ : V, ∃ θ' : V, distance θ' = distance θ ∧ accuracy θ' ≠ accuracy θ :=
  Foundations.scalar_summary_insufficient_of_not_scalar_factorization distance accuracy hnot

/-! The conditional-noise-floor and Gaussian-floor bounds on the explainable fraction answer
this question, and they are `explainable_fraction_bound_of_conditional_noise_floor` and
`explainable_fraction_bound_of_conditional_gaussian_floor` in
`Descent.Foundations.TransportIdentities`.

They were also restated here, suffixed `_exact`, each copying its original's eight-line
measure-theoretic binder block and citing the original as its proof.  Both live in the
`Descent` namespace already, so the copies renamed nothing and reached no reader the
originals did not; what they added was a second block of hypotheses to keep in step. -/

/-- **The between-group fraction of an assumed variance decomposition is at most one.**

    Previously `law_of_total_variance_r2_bound`, documented as the law of total variance
    identity `Var(Z) = E[Var(Z|D)] + Var(E[Z|D])`. The law is not proved here: it is the
    hypothesis `h_decomp`, three unrelated reals related by an equation. What remains after
    it is assumed is that a nonnegative summand's share of a positive total is at most one,
    which is `div_le_one` plus `linarith`.

    The real conditional-variance statements in this file are
    `explainable_fraction_bound_of_conditional_noise_floor_exact` and its Gaussian
    companion, which work against `conditionalVariance` and `conditionalMean` on an actual
    measure rather than against three scalars. Those are where the law of total variance
    is genuinely used. -/
theorem between_group_variance_fraction_le_one
    (varZ eVarZgivenD varEZgivenD : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (h_eVar_nonneg : 0 ≤ eVarZgivenD)
    :
    varEZgivenD / varZ ≤ 1 := by
  rw [div_le_one h_varZ_pos, h_decomp]
  linarith

/-- **The complementary share of a two-part decomposition:** if
    `varZ = a + b` with `varZ > 0` and `a ≥ (1 - δ)·varZ`, then `b/varZ ≤ δ`.

    Read as the law of total variance, `a` is `E[Var(Z|D)]`, `b` is
    `Var(E[Z|D])`, and the conclusion is a bound on `R²(Z,D)`. That reading is
    supplied entirely by `h_decomp`, which stipulates the decomposition: there
    is no `Z`, no `D`, no conditional expectation and no `R²` below, and the
    law of total variance is not invoked, only assumed in the shape of an
    equation between three reals. A measured `δ` for a fitted model is not an
    instance of this, whose variables are free. -/
theorem div_le_of_ge_one_sub_mul
    (varZ eVarZgivenD varEZgivenD δ : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (h_within_dominates : eVarZgivenD ≥ (1 - δ) * varZ)
    :
    varEZgivenD / varZ ≤ δ := by
  have h1 : varEZgivenD = varZ - eVarZgivenD := by linarith
  rw [h1, sub_div, div_self (h_varZ_pos.ne')]
  linarith [le_div_iff₀ h_varZ_pos |>.mpr (by linarith : (1 - δ) * varZ ≤ eVarZgivenD)]


/-- If two fractions are already known to be comparable and their sum bounded,
each is bounded. This does not establish empirical comparability of SES and
genetic distance. -/
theorem comparable_covariates_both_small
    (r2_d r2_s B ε : ℝ)
    (h_comparable : r2_d ≤ r2_s + ε)
    (h_sum_bound : r2_d + r2_s ≤ B)
    :
    r2_d ≤ (B + ε) / 2 := by
  linarith


end Question1


/-!
## Open Question 2: Trait-Specific Portability

Trait-specific portability is the exact consequence of locuswise transport
heterogeneity together with trait-specific baseline weights.
-/

section Question2

variable {J L : Type*}
variable [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **Heterozygosity increases toward 0.5.**
    Under divergent selection, allele freq p moves from extreme to
    intermediate → H = 2p(1-p) increases.
    This drives PGS variance increase for immune traits. -/
theorem two_mul_one_sub_lt_of_lt_of_le_half
    (p₁ p₂ : ℝ)
    (hp₁_lt_p₂ : p₁ < p₂)
    (hp₂_le_half : p₂ ≤ 1 / 2) :
    2 * p₁ * (1 - p₁) < 2 * p₂ * (1 - p₂) := by
  nlinarith [sq_nonneg (p₂ - p₁), sq_nonneg (1/2 - p₂)]

/-- **PGS variance increases when the large-effect locus gains more heterozygosity than the
small-effect locus loses.** This is the mechanism proposed for WBC/lymphocyte count.

    A statement taking `h_net : v_large_t - v_large_s > v_small_s - v_small_t` and
    concluding `v_large_s + v_small_s < v_large_t + v_small_t` would be no mechanism at all:
    those two inequalities are the *same inequality rearranged*, so the hypothesis would be
    the conclusion and the proof the rearrangement.

    This one cannot be rearranged into its own hypotheses, because the hypotheses
    are about **effect sizes and heterozygosities separately** and the conclusion is about
    the variance sum they generate. A locus at frequency `p` with effect `β` contributes
    `2β²p(1-p)` to score variance, so the claim has content precisely when the weighting by
    `β²` is doing work: the large-effect locus must actually be the larger-effect one
    (`hβ`), and its heterozygosity gain must exceed the small locus's loss
    (`hlarge_gains_more`). Neither follows from the conclusion.

    Use `two_mul_one_sub_lt_of_lt_of_le_half` to discharge the gain hypothesis from allele
    frequencies moving toward `1/2` under divergent selection, which is the biological step
    the prose describes. -/
theorem two_term_weighted_sum_lt_of_larger_weight_gain
    (βL βS pL pL' pS pS' : ℝ)
    (hβ : βS ^ 2 ≤ βL ^ 2)
    (hβL : 0 < βL ^ 2)
    (hsmall_loses : pS' * (1 - pS') ≤ pS * (1 - pS))
    (hlarge_gains_more :
      pS * (1 - pS) - pS' * (1 - pS') < pL' * (1 - pL') - pL * (1 - pL)) :
    2 * βS ^ 2 * (pS * (1 - pS)) + 2 * βL ^ 2 * (pL * (1 - pL)) <
      2 * βS ^ 2 * (pS' * (1 - pS')) + 2 * βL ^ 2 * (pL' * (1 - pL')) := by
  have hloss_nonneg : 0 ≤ pS * (1 - pS) - pS' * (1 - pS') := by linarith
  -- The small locus's loss is weighted by the smaller squared effect ...
  have hweighted : βS ^ 2 * (pS * (1 - pS) - pS' * (1 - pS'))
      ≤ βL ^ 2 * (pS * (1 - pS) - pS' * (1 - pS')) :=
    mul_le_mul_of_nonneg_right hβ hloss_nonneg
  -- ... and that loss is strictly smaller than the large locus's gain.
  have hgain : βL ^ 2 * (pS * (1 - pS) - pS' * (1 - pS'))
      < βL ^ 2 * (pL' * (1 - pL') - pL * (1 - pL)) :=
    (mul_lt_mul_iff_right₀ hβL).mpr hlarge_gains_more
  nlinarith [hweighted, hgain]

/-- **PGS variance increase + effect decorrelation = compounded R² drop.**
    R² ∝ Cov²/(Var_PGS · Var_Y). If Var_PGS↑ and Cov↓, R² drops faster
    than either mechanism alone. -/
theorem compound_r2_drop
    (cov_s cov_t vpgs_s vpgs_t vy : ℝ)
    (h_cov_drop : cov_t ^ 2 < cov_s ^ 2)
    (h_vpgs_up : vpgs_s < vpgs_t)
    (h_vy_pos : 0 < vy)
    (h_vpgs_pos : 0 < vpgs_s) :
    cov_t ^ 2 / (vpgs_t * vy) < cov_s ^ 2 / (vpgs_s * vy) := by
  have h_denom_s : 0 < vpgs_s * vy := mul_pos h_vpgs_pos h_vy_pos
  have h_denom_t : 0 < vpgs_t * vy := mul_pos (by linarith) h_vy_pos
  have h_denom_up : vpgs_s * vy < vpgs_t * vy := mul_lt_mul_of_pos_right h_vpgs_up h_vy_pos
  have key : cov_t ^ 2 * (vpgs_s * vy) ≤ cov_t ^ 2 * (vpgs_t * vy) := by
    apply mul_le_mul_of_nonneg_left (le_of_lt h_denom_up) (sq_nonneg cov_t)
  calc cov_t ^ 2 / (vpgs_t * vy)
      ≤ cov_t ^ 2 / (vpgs_s * vy) := by
        rwa [div_le_div_iff₀ h_denom_t h_denom_s]
    _ < cov_s ^ 2 / (vpgs_s * vy) :=
        div_lt_div_of_pos_right h_cov_drop h_denom_s

/-- **Sign-flip probability.**
    Effect in target ~ N(ρ·β, σ²). Z-score for sign concordance = ρ·β/σ.
    Smaller ρ → smaller z-score → more sign flips.
    (31.7% for lymphocyte vs 9.6% for triglycerides in Wang et al.) -/
theorem sign_flip_z_decreases_with_turnover
    (β σ ρ₁ ρ₂ : ℝ)
    (hβ : 0 < β) (hσ : 0 < σ)
    (hρ : ρ₂ < ρ₁) :
    ρ₂ * β / σ < ρ₁ * β / σ :=
  div_lt_div_of_pos_right (by nlinarith) hσ

end Question2


/-!
## Open Question 3: Metric-Specific Portability

Different metrics are different functionals of the same transported law.
For continuous traits this is the exact MSE identity; for binary traits it is
the exact prevalence-recall-FPR formula for precision.
-/

section Question3

variable {Ω : Type*}

theorem binary_precision_formula_exact (c : Foundations.ConfusionMatrix) :
    Foundations.ConfusionMatrix.precision c =
      (Foundations.ConfusionMatrix.prevalence c * Foundations.ConfusionMatrix.recallRate c) /
        (Foundations.ConfusionMatrix.prevalence c * Foundations.ConfusionMatrix.recallRate c +
          (1 - Foundations.ConfusionMatrix.prevalence c) * Foundations.ConfusionMatrix.fpr c) :=
  Foundations.ConfusionMatrix.precision_eq_prevalence_recall_fpr c

/-- **Precision-recall divergence is consistent.**
    There exist parameter configurations with fixed prevalence and fixed target
    precision where recall changes and the induced false-positive rate changes
    exactly as required by the precision identity. -/
theorem precision_recall_divergence_exists :
    ∃ (π p r₁ r₂ f₁ f₂ : ℝ),
      0 < π ∧ π < 1 ∧
      0 < p ∧ p < 1 ∧
      0 < r₁ ∧ r₁ < r₂ ∧ r₂ ≤ 1 ∧
      f₁ = π * r₁ * (1 - p) / ((1 - π) * p) ∧
      f₂ = π * r₂ * (1 - p) / ((1 - π) * p) ∧
      (π * r₁) / (π * r₁ + (1 - π) * f₁) = p ∧
      (π * r₂) / (π * r₂ + (1 - π) * f₂) = p := by
  refine ⟨1 / 2, 1 / 2, 1 / 4, 1 / 3,
    (1 / 2) * (1 / 4) * (1 - 1 / 2) / ((1 - 1 / 2) * (1 / 2)),
    (1 / 2) * (1 / 3) * (1 - 1 / 2) / ((1 - 1 / 2) * (1 / 2)), ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simpa using
      (Foundations.ConfusionMatrix.constant_precision_of_fpr_choice
        (π := 1 / 2) (p := 1 / 2) (r := 1 / 4) (by norm_num) (by norm_num) (by norm_num))
  · simpa using
      (Foundations.ConfusionMatrix.constant_precision_of_fpr_choice
        (π := 1 / 2) (p := 1 / 2) (r := 1 / 3) (by norm_num) (by norm_num) (by norm_num))


end Question3


/-!
## Open Question 4: Environmental Variance Heterogeneity
-/

section Question4

/-- **`Vg/(Vg + Ve)` decreases as `Ve` grows.**

    Read as `R²` under identical genetics, or as heritability, or as the attainable ceiling:
    they are one inequality. `Descent.GeneEnvironmentInterplay.env_variance_reduces_h2` is the
    same statement, kept there because that file's discussion needs it locally; this is not an
    independent result and should not be cited as one. -/
theorem env_variance_lowers_r2
    (Vg Ve₁ Ve₂ : ℝ)
    (hVg : 0 < Vg) (hVe₁ : 0 < Ve₁)
    (h_more_env : Ve₁ < Ve₂) :
    Vg / (Vg + Ve₂) < Vg / (Vg + Ve₁) := by
  apply div_lt_div_of_pos_left hVg (by linarith) (by linarith)

/-- **A nonzero product added to a coefficient changes it.**

    Kept under its old name because the arithmetic is what the surrounding discussion of
    omitted-variable bias appeals to, but read it as what it is: no regression, no
    estimator and no correlation appears in the statement. That the naive coefficient on
    genetic distance picks up exactly `β_ses · ρ` when SES is omitted is the standard
    omitted-variable formula, asserted in this docstring and derived nowhere in this
    corpus. What is proved is that adding a nonzero product to a number changes it. -/
theorem omitted_variable_bias
    (β_true β_ses ρ : ℝ)
    (h_ses : β_ses ≠ 0) (h_corr : ρ ≠ 0) :
    β_true + β_ses * ρ ≠ β_true := by
  intro h
  have : β_ses * ρ = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact h_ses h
  · exact h_corr h

/-- **Portability drop decomposes into genetic + environmental parts.** -/
theorem both_le_of_add_eq_of_nonneg
    (r2s r2t Δg Δe : ℝ)
    (h_eq : r2s - r2t = Δg + Δe)
    (hΔg : 0 ≤ Δg) (hΔe : 0 ≤ Δe) :
    Δg ≤ r2s - r2t ∧ Δe ≤ r2s - r2t := by
  constructor <;> linarith


end Question4


/-!
## Open Question 5: Winner's Curse × Allelic Turnover
-/

section Question5

/-- **Winner's curse prediction error model.**
    GWAS estimate β_hat = β_true + δ (inflation).
    Target effect β_t = ρ * β_true (turnover).
    Prediction error = β_hat - β_t = (1-ρ)*β + δ.
    Prediction error decomposes into turnover + inflation. -/
theorem prediction_error_decomp (β δ ρ : ℝ) :
    (β + δ) - ρ * β = (1 - ρ) * β + δ := by ring

/-- Prediction error is positive when both components are positive. -/
theorem prediction_error_positive
    (β δ ρ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hρ : ρ ≤ 1) :
    0 < (1 - ρ) * β + δ := by
  have : 0 ≤ (1 - ρ) * β := mul_nonneg (by linarith) (le_of_lt hβ)
  linarith

/-- **Winner's curse is worse with more turnover.**
    Relative error = ((1-ρ)β + δ) / (ρβ). As ρ↓, this increases. -/
theorem relative_error_increases_with_turnover
    (β δ ρ₁ ρ₂ : ℝ) (hβ : 0 < β) (hδ : 0 < δ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hρ : ρ₂ < ρ₁) :
    ((1 - ρ₁) * β + δ) / (ρ₁ * β) < ((1 - ρ₂) * β + δ) / (ρ₂ * β) := by
  rw [div_lt_div_iff₀ (mul_pos hρ₁ hβ) (mul_pos hρ₂ hβ)]
  nlinarith [sq_nonneg β, sq_nonneg δ, mul_pos hρ₁ hβ, mul_pos hρ₂ hβ,
             mul_pos hβ hδ, mul_pos hρ₁ hδ, mul_pos hρ₂ hδ]

/-- **Multiplying by a positive number preserves strict order:**
    `H_s < H_t` gives `β²·H_s < β²·H_t`.

    Read as genetics the two sides are one locus's contribution to score
    variance at two heterozygosities. That reading is the choice to call the
    factors `beta_sq` and `H`; no locus, no genotype and no score appears
    below. -/
theorem mul_lt_mul_left_of_pos'
    (beta_sq H_s H_t : ℝ) (hβ : 0 < beta_sq) (hH : H_s < H_t) :
    beta_sq * H_s < beta_sq * H_t :=
  mul_lt_mul_of_pos_left hH hβ


end Question5


/-!
## Open Question 6: PGS Variance Non-Monotonicity
-/

section Question6

/-- **Variance decomposition into large and small effect groups.** -/
theorem variance_decomposition
    {m : ℕ} (w : Fin m → ℝ) (S : Finset (Fin m)) :
    ∑ i, w i = ∑ i ∈ S, w i + ∑ i ∈ Sᶜ, w i := by
  rw [← Finset.sum_union disjoint_compl_right]
  congr 1; exact (Finset.union_compl S).symm

/-- **A net gain on a subset raises the total:** if the increase over `S`
    exceeds the decrease over `Sᶜ`, then `∑ w_s < ∑ w_t`.

    The genetics reading partitions loci into a highlighted set and its
    complement and reads the sums as predictor variance. Below there are no
    loci and no variance — `w_s` and `w_t` are arbitrary functions into `ℝ`,
    not constrained to be nonnegative or to be per-locus contributions of
    anything. Splitting a sum over a finset and its complement, plus
    `linarith`. -/
theorem sum_lt_sum_of_net_gain_on_subset
    {m : ℕ} (w_s w_t : Fin m → ℝ) (S : Finset (Fin m))
    (h_net :
      (∑ i ∈ S, w_t i) - (∑ i ∈ S, w_s i) >
        (∑ i ∈ Sᶜ, w_s i) - (∑ i ∈ Sᶜ, w_t i)) :
    ∑ i, w_s i < ∑ i, w_t i := by
  rw [variance_decomposition w_s S, variance_decomposition w_t S]
  linarith


end Question6


/-!
## Open Question 7: Brier Score Uncertainty Varies with Prevalence
-/

section Question7

/-- **Brier score irreducible noise = π(1-π).**
    This varies with prevalence, making R² comparisons across groups misleading. -/
theorem brier_uncertainty_formula (π : ℝ) :
    π * (1 - π) = -(π - 1/2) ^ 2 + 1/4 := by ring

/-- **Brier uncertainty is maximized at π = 1/2.** -/
theorem brier_uncertainty_max_at_half (π : ℝ) :
    π * (1 - π) ≤ 1/4 := by nlinarith [sq_nonneg (π - 1/2)]

/-- **Closer to 1/2 ↔ higher uncertainty.** -/
theorem closer_to_half_more_uncertainty
    (π₁ π₂ : ℝ)
    (h_closer : (π₂ - 1/2) ^ 2 < (π₁ - 1/2) ^ 2) :
    π₁ * (1 - π₁) < π₂ * (1 - π₂) := by
  nlinarith [brier_uncertainty_formula π₁, brier_uncertainty_formula π₂]

/-- **Prediction interval width increases as R² decreases.** -/
theorem interval_width_increases
    (r2₁ r2₂ : ℝ)
    (hr2₁ : r2₂ < r2₁) (hr2₁_lt : r2₁ < 1) :
    Real.sqrt (1 - r2₁) < Real.sqrt (1 - r2₂) :=
  Real.sqrt_lt_sqrt (by linarith) (by linarith)

end Question7


/-!
## Portability: the four-factor decomposition

Portability ratio = AF_factor × LD_factor × Effect_factor × Env_factor.
Genetic distance (Fst) captures only the AF factor, explaining why it
poorly predicts individual-level accuracy.
-/

section FourFactorDecomposition

/-- **The four-factor product is strictly below its AF factor alone.**

    Previously `single_factor_insufficient`, "No single factor captures the full ratio".
    Insufficiency of a single factor is a claim about approximation error, or about a
    factor failing to determine the product; neither is stated. What is proved is one
    strict inequality between the product and one of its factors, which is what you get
    from the other three being below one. It supports the surrounding argument — an Fst
    proxy that sees only the AF factor overstates portability — without being that
    argument. -/
theorem four_factor_product_lt_af_factor
    (af ld eff env : ℝ)
    (h_af : 0 < af)
    (h_ld_lt : ld < 1)
    (h_eff : 0 < eff) (h_eff_lt : eff < 1)
    (h_env : 0 < env) (h_env_le : env ≤ 1) :
    af * ld * eff * env < af := by
  have h1 : ld * eff < 1 := by
    calc ld * eff < 1 * eff := mul_lt_mul_of_pos_right h_ld_lt h_eff
      _ = eff := one_mul eff
      _ < 1 := h_eff_lt
  have h2 : ld * eff * env < 1 := by
    calc ld * eff * env < 1 * env := mul_lt_mul_of_pos_right h1 h_env
      _ = env := one_mul env
      _ ≤ 1 := h_env_le
  calc af * ld * eff * env
      = af * (ld * eff * env) := by ring
    _ < af * 1 := mul_lt_mul_of_pos_left h2 h_af
    _ = af := mul_one af

/-- **One positive summand's share of a sum of four positive summands is below one.**

    Previously `genetic_distance_variance_bound`, "R² of genetic distance on portability is
    bounded by the AF variance fraction". No R², no genetic distance and no portability
    appears in the statement, and no bound *by* the AF fraction is proved — what is proved
    is a bound *on* it, namely that it is under one, which holds of any of the four
    fractions and is `div_lt_one`. The variance-decomposition reading, in which these four
    numbers are the variances of independent contributions to portability, is asserted in
    the section prose and formalised nowhere. -/
theorem af_variance_fraction_lt_one
    (var_af var_ld var_eff var_env : ℝ)
    (h_af : 0 < var_af) (h_ld : 0 < var_ld)
    (h_eff : 0 < var_eff) (h_env : 0 < var_env) :
    var_af / (var_af + var_ld + var_eff + var_env) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith


end FourFactorDecomposition


/-!
## Selection-Driven Allelic Turnover Model

Under fluctuating selection across populations, effect sizes at
immune-associated loci change faster than at neutral loci.
-/

section SelectionModel

/-- **Effect retention under selection.**
    ρ ≤ selection correlation. Low selection correlation → low ρ → low portability. -/
theorem mul_sq_le_mul_sq_of_le_of_nonneg
    (r2_src ρ_eff ρ_sel : ℝ)
    (hr2 : 0 ≤ r2_src)
    (h_bound : ρ_eff ≤ ρ_sel)
    (h_eff_nn : 0 ≤ ρ_eff) :
    r2_src * ρ_eff ^ 2 ≤ r2_src * ρ_sel ^ 2 := by
  apply mul_le_mul_of_nonneg_left _ hr2
  exact sq_le_sq' (by linarith) h_bound

/-- **Neutral vs immune portability.**
    Neutral ρ = 1, immune ρ < 1. So neutral R² > immune R² at same distance. -/
theorem neutral_beats_immune
    (r2 ρ : ℝ) (hr2 : 0 < r2)
    (hρ_pos : 0 ≤ ρ) (hρ_lt : ρ < 1) :
    r2 * ρ ^ 2 < r2 * 1 ^ 2 := by
  rw [one_pow]
  apply mul_lt_mul_of_pos_left _ hr2
  nlinarith [sq_abs ρ, sq_nonneg ρ]

/-- **An effect-retention factor `ρ² < 1` strictly lowers target R² at a fixed target Fst.**

    Previously `drift_only_overestimates_immune_portability`, documented as "Under pure
    drift, portability ratio = (1-Fst_T)/(1-Fst_S). This is what Fst predicts." No ratio of
    source to target appears in the conclusion: **both sides are evaluated at `fstT`**, and
    the comparison is between including the turnover factor `ρ²` and omitting it. The
    source Fst enters no term.

    The linter caught it. The hypotheses `0 ≤ fstS` and `fstS < fstT` — the ones that made
    the statement look like a source-versus-target comparison — occurred in no proof term,
    and `fstS` itself occurred nowhere else, so all three are gone from the signature. What
    the theorem says is that a drift-only prediction, which omits `ρ²`, is higher than one
    that includes it; that supports the surrounding claim about immune traits without being
    a statement about genetic distance at all. -/
theorem effect_retention_lowers_target_r2_at_fixed_fst
    (V_A V_E fstT ρ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstT : fstT < 1)
    (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) :
    PopGen.TransportedMetrics.r2FromSignalVariance (ρ ^ 2 * Portability.presentDayPGSVariance V_A
      fstT) V_E <
      PopGen.TransportedMetrics.r2FromSignalVariance (Portability.presentDayPGSVariance V_A fstT)
        V_E := by
  apply Portability.expectedR2_strictMono_nonneg V_E _ _ hVE
  · have hpdv : 0 < Portability.presentDayPGSVariance V_A fstT := by
      unfold Portability.presentDayPGSVariance Portability.pgsVarianceFromHet Descent.Core.product
      exact mul_pos hVA (by linarith)
    exact le_of_lt (mul_pos (sq_pos_of_pos hρ_pos) hpdv)
  · have h_pdv_pos : 0 < Portability.presentDayPGSVariance V_A fstT := by
      unfold Portability.presentDayPGSVariance Portability.pgsVarianceFromHet Descent.Core.product;
        exact mul_pos hVA (by linarith)
    calc ρ ^ 2 * Portability.presentDayPGSVariance V_A fstT
        < 1 * Portability.presentDayPGSVariance V_A fstT := by
          apply mul_lt_mul_of_pos_right _ h_pdv_pos
          nlinarith [sq_abs ρ, sq_nonneg ρ]
      _ = Portability.presentDayPGSVariance V_A fstT := one_mul _

end SelectionModel


/-!
## LD Decay Interaction with Allelic Turnover

The paper shows that for immune traits, both LD patterns AND allelic effects
change simultaneously. The combined effect is worse than either alone.
We formalize this multiplicative interaction.
-/

section LDTurnoverInteraction

theorem faster_decay_lower_correlation
    (lam_slow lam_fast d : ℝ)
    (hlam_faster : lam_slow < lam_fast)
    (hd_pos : 0 < d) :
    Real.exp (-lam_fast * d) < Real.exp (-lam_slow * d) := by
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- **Combined LD + effect turnover portability.**
    Total portability = `R²_source · σ_d²(Nₑ, c) · ρ²_effect(d)`, at genetic
    distance `d` read as the recombination fraction `c`.

    The LD factor is `LDDecayTheory.ohtaKimuraSigmaDSq`, the corpus's validated
    neutral two-locus decay. It is hyperbolic in `4·Nₑ·c`; an exponential chart
    in genetic distance was measured against the same binned `r²` values with a
    free amplitude and a free rate and missed at both ends, so an exponential is
    not available here even as a convenience. The effect-turnover factor is a
    fitted exponential and remains no more than that: `lam_eff` has no
    derivation, and nothing below identifies it with a selection coefficient.

    Empirical status: UNTESTED as a product. The LD factor is validated
    separately at `ohtaKimuraSigmaDSq` and the turnover factor is a chart; that
    the two multiply is the modelling assumption this section is about, and no
    battery has put the product itself on trial. -/
noncomputable def combinedPortability
    (r2_src Ne lam_eff d : ℝ) : ℝ :=
  r2_src * PopGen.ohtaKimuraSigmaDSq Ne d * (Real.exp (-lam_eff * d)) ^ 2

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why.
The LD factor at zero scaled recombination is `5/11`, not `1`: complete linkage
in a finite population does not make the squared correlation one. -/
theorem combinedPortability_at_reference_point :
    combinedPortability 1 0 0 1 = 5 / 11 := by
  norm_num [combinedPortability, PopGen.ohtaKimuraSigmaDSq]

/-- **The LD factor is positive at every nonnegative distance**, which is what
lets the turnover comparisons below be strict. -/
theorem ohtaKimuraSigmaDSq_pos_of_nonneg {Ne d : ℝ} (hNe : 0 ≤ Ne) (hd : 0 ≤ d) :
    0 < PopGen.ohtaKimuraSigmaDSq Ne d := by
  have hrho : 0 ≤ 4 * Ne * d := by positivity
  unfold PopGen.ohtaKimuraSigmaDSq
  apply div_pos <;> nlinarith

/-- **At zero distance, combined portability is the source `R²` times the
complete-linkage value of `σ_d²`.** The `5/11` is the LD factor's own value at
`ρ = 0` and is not a portability loss to genetic distance. -/
theorem combined_portability_at_zero (r2_src Ne lam_eff : ℝ) :
    combinedPortability r2_src Ne lam_eff 0 = r2_src * (5 / 11) := by
  unfold combinedPortability PopGen.ohtaKimuraSigmaDSq
  norm_num

/-- **LD-only portability strictly exceeds combined portability at positive distance.**
    Adding effect turnover always makes portability worse. -/
theorem turnover_worsens_ld_only_portability
    (r2_src Ne lam_eff d : ℝ)
    (hr2 : 0 < r2_src) (hNe : 0 ≤ Ne)
    (hlam_eff : 0 < lam_eff) (hd : 0 < d) :
    combinedPortability r2_src Ne lam_eff d <
      r2_src * PopGen.ohtaKimuraSigmaDSq Ne d := by
  unfold combinedPortability
  have h_exp_lt : (Real.exp (-lam_eff * d)) ^ 2 < 1 := by
    have h1 : Real.exp (-lam_eff * d) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith [mul_pos hlam_eff hd]
    have h2 : 0 ≤ Real.exp (-lam_eff * d) := Real.exp_nonneg _
    nlinarith [sq_abs (Real.exp (-lam_eff * d))]
  have h_base_pos : 0 < r2_src * PopGen.ohtaKimuraSigmaDSq Ne d :=
    mul_pos hr2 (ohtaKimuraSigmaDSq_pos_of_nonneg hNe (le_of_lt hd))
  calc r2_src * PopGen.ohtaKimuraSigmaDSq Ne d * (Real.exp (-lam_eff * d)) ^ 2
      < r2_src * PopGen.ohtaKimuraSigmaDSq Ne d * 1 :=
        mul_lt_mul_of_pos_left h_exp_lt h_base_pos
    _ = r2_src * PopGen.ohtaKimuraSigmaDSq Ne d := mul_one _

/-- **Immune portability drops multiplicatively faster.**
    For immune traits (large λ_eff), the combined decay is much faster
    than for neutral traits (small λ_eff). -/
theorem immune_combined_decay_faster
    (r2_src Ne lam_eff_neutral lam_eff_immune d : ℝ)
    (hr2 : 0 < r2_src) (hNe : 0 ≤ Ne)
    (hlami : lam_eff_neutral < lam_eff_immune)
    (hd : 0 < d) :
    combinedPortability r2_src Ne lam_eff_immune d <
      combinedPortability r2_src Ne lam_eff_neutral d := by
  unfold combinedPortability
  have h_ld_pos : 0 < r2_src * PopGen.ohtaKimuraSigmaDSq Ne d :=
    mul_pos hr2 (ohtaKimuraSigmaDSq_pos_of_nonneg hNe (le_of_lt hd))
  apply mul_lt_mul_of_pos_left _ h_ld_pos
  apply sq_lt_sq'
  · linarith [Real.exp_pos (-lam_eff_immune * d), Real.exp_pos (-lam_eff_neutral * d)]
  · exact faster_decay_lower_correlation lam_eff_neutral lam_eff_immune d hlami hd

end LDTurnoverInteraction


/-!
## R² Non-Comparability Across Groups

R² depends on the variance of both predictor and outcome within each group.
When comparing R² across genetic ancestry groups, heterogeneity in both
genetic and environmental variance makes direct comparison misleading.
-/

section R2NonComparability

/-- **R² is not comparable when phenotypic variances differ.**
    Two populations with the same signal but different noise have different R². -/
theorem r2_incomparable_across_groups
    (v_signal v_noise₁ v_noise₂ : ℝ)
    (h_sig : 0 < v_signal)
    (h_n₁ : 0 < v_noise₁) (h_n₂ : 0 < v_noise₂)
    (h_noise_diff : v_noise₁ ≠ v_noise₂) :
    v_signal / (v_signal + v_noise₁) ≠ v_signal / (v_signal + v_noise₂) := by
  intro h_eq
  apply h_noise_diff
  have h_d₁ : (0 : ℝ) < v_signal + v_noise₁ := by linarith
  have h_d₂ : (0 : ℝ) < v_signal + v_noise₂ := by linarith
  have h_cross := (div_eq_div_iff (h_d₁.ne') (h_d₂.ne')).mp h_eq
  nlinarith

/-- **Heteroscedasticity inflates apparent portability loss.**
    If Var(Y) is larger in the target (due to environmental factors),
    R²_target < R²_source even with identical signal. -/
theorem heteroscedasticity_inflates_loss
    (v_sig v_noise_s v_noise_t : ℝ)
    (h_sig : 0 < v_sig)
    (h_ns : 0 < v_noise_s)
    (h_more_noise : v_noise_s < v_noise_t) :
    v_sig / (v_sig + v_noise_t) < v_sig / (v_sig + v_noise_s) :=
  div_lt_div_of_pos_left h_sig (by linarith) (by linarith)

/-- **Corrected portability ratio accounts for noise differences.**
    The "true" portability ratio should compare signal-to-noise ratios,
    not R² values directly.
    SNR_s = v_sig_s / v_noise_s, SNR_t = v_sig_t / v_noise_t.
    Portability = SNR_t / SNR_s, which is invariant to noise scaling. -/
noncomputable def snrPortabilityRatio
    (v_sig_s v_noise_s v_sig_t v_noise_t : ℝ) : ℝ :=
  (v_sig_t / v_noise_t) / (v_sig_s / v_noise_s)

/-- **snrPortabilityRatio where its denominator vanishes, named.** The guard `v_sig_s / v_noise_s`
is zero at `v_sig_s = 0`, `v_noise_s = 1`. Lean returns `0` there rather than the value the
modelled quantity takes, and no type error marks the point. Consumers must require `v_sig_s /
v_noise_s ≠ 0`. -/
theorem snrPortabilityRatio_at_vsigs0vnoises1_is_junk (v_sig_t : ℝ) (v_noise_t : ℝ) :
    snrPortabilityRatio 0 1 v_sig_t v_noise_t = 0 := by
  unfold snrPortabilityRatio
  norm_num

/-- **SNR portability depends only on signal ratio when noise is constant.** -/
theorem snr_portability_signal_only
    (v_sig_s v_sig_t v_noise : ℝ)
    (h_ns : v_noise ≠ 0) :
    snrPortabilityRatio v_sig_s v_noise v_sig_t v_noise = v_sig_t / v_sig_s := by
  unfold snrPortabilityRatio
  field_simp

/-- **The `R²` ratio is the SNR ratio times the outcome-variance ratio**, which is this
section's claim written as an equation instead of an argument.

`Descent.Core.share v_sig v_noise` is `v_sig / (v_sig + v_noise)` -- the `R²` the corpus
computes everywhere -- and the section above says a portability quoted as a ratio of `R²`
values is not comparing signal transport, because `Var(Y)` differs between populations.
Here is the exact discrepancy: the two ratios agree only when `v_sig_t + v_noise` equals
`v_sig_s + v_noise`, that is only when the signal itself is unchanged, which is the case
where there is no portability loss to quote. Everywhere else the `R²` ratio is off by a
factor that depends on the outcome variances and not on transport at all.

This also ties these definitions to the corpus: `snrPortabilityRatio` lives in the register
of open questions, and until now nothing outside it constrained the quantity, so a wrong
body here would have been consistent with everything else. -/
theorem snrPortabilityRatio_eq_share_ratio_mul (v_sig_s v_sig_t v_noise : ℝ)
    (hn : 0 < v_noise) (hs : 0 < v_sig_s) (ht : 0 < v_sig_t) :
    snrPortabilityRatio v_sig_s v_noise v_sig_t v_noise
      = (Descent.Core.share v_sig_t v_noise / Descent.Core.share v_sig_s v_noise)
          * ((v_sig_t + v_noise) / (v_sig_s + v_noise)) := by
  have h1 : v_sig_s ≠ 0 := ne_of_gt hs
  have h2 : v_noise ≠ 0 := ne_of_gt hn
  have h3 : v_sig_t + v_noise ≠ 0 := ne_of_gt (by linarith)
  have h4 : v_sig_s + v_noise ≠ 0 := ne_of_gt (by linarith)
  unfold snrPortabilityRatio Descent.Core.share
  field_simp

end R2NonComparability


/-!
## Local Ancestry and Portability

The paper notes that measures of genetic distance based on global PCs are
"plausibly sub-optimal" and suggests local ancestry may better predict portability.
We formalize why local ancestry should be more informative.
-/

section LocalAncestry

/-- **Variance in local Fst across loci creates additional prediction error.**
    If local Fst varies (some loci have high Fst, others low), the prediction
    error has a "locus heterogeneity" component not captured by global Fst. -/
theorem mul_sum_lt_sum_mul_of_nonneg_of_exists_pos
    {m : ℕ} (β : Fin m → ℝ) (fst : Fin m → ℝ) (fst_global : ℝ)
    (h_nonneg : ∀ i, 0 ≤ β i ^ 2 * (fst i - fst_global))
    (i₀ : Fin m)
    (h_strict : 0 < β i₀ ^ 2 * (fst i₀ - fst_global)) :
    fst_global * (∑ i, β i ^ 2) < ∑ i, β i ^ 2 * fst i := by
  have hsum_strict :
      0 < ∑ i, β i ^ 2 * (fst i - fst_global) := by
    have hsingle :
        β i₀ ^ 2 * (fst i₀ - fst_global)
          ≤ ∑ i, β i ^ 2 * (fst i - fst_global) := by
      simpa only using
        (Finset.single_le_sum
          (f := fun i ↦ β i ^ 2 * (fst i - fst_global))
          (fun i _ ↦ h_nonneg i)
          (Finset.mem_univ i₀))
    exact lt_of_lt_of_le h_strict hsingle
  have hrewrite :
      ∑ i, β i ^ 2 * (fst i - fst_global)
        = (∑ i, β i ^ 2 * fst i) - fst_global * (∑ i, β i ^ 2) := by
    calc
      ∑ i, β i ^ 2 * (fst i - fst_global)
          = ∑ i, (β i ^ 2 * fst i - β i ^ 2 * fst_global) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i, β i ^ 2 * fst i) - ∑ i, β i ^ 2 * fst_global := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ i, β i ^ 2 * fst i) - fst_global * (∑ i, β i ^ 2) := by
              rw [Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              ring
  have hgap :
      0 < (∑ i, β i ^ 2 * fst i) - fst_global * (∑ i, β i ^ 2) := by
    rw [← hrewrite]
    exact hsum_strict
  linarith

/-- **A weighted average exceeds a constant when the weighted deviations from
    it are positive:** `c < (∑ β² x) / (∑ β²)`.

    The genetics reading is that a genome-wide `F_ST` is a biased proxy for the
    effect-weighted average of local `F_ST`, so global and local carry
    different information. What is proved is that the weighted mean of `x`
    exceeds `c` when `∑ β²(x - c) > 0` — an arithmetic fact about weights, with no ancestry, no
    locus, no LD and no accuracy in it, and in particular no
    comparison of how informative two quantities are. -/
theorem lt_weighted_mean_of_weighted_deviation_pos
    {m : ℕ} (β : Fin m → ℝ) (fst_local : Fin m → ℝ) (fst_global : ℝ)
    (h_nonneg : ∀ i, 0 ≤ β i ^ 2 * (fst_local i - fst_global))
    (i₀ : Fin m)
    (h_strict : 0 < β i₀ ^ 2 * (fst_local i₀ - fst_global))
    (hweight_pos : 0 < ∑ i, β i ^ 2) :
    fst_global < (∑ i, β i ^ 2 * fst_local i) / (∑ i, β i ^ 2) :=
  (lt_div_iff₀ hweight_pos).2
    (mul_sum_lt_sum_mul_of_nonneg_of_exists_pos β fst_local fst_global h_nonneg i₀ h_strict)

end LocalAncestry


/-!
## Disease-Specific Portability

For binary traits (asthma, T2D), portability depends on additional factors:
- Prevalence differences across populations
- The specific metric used (precision, recall, F1, AUC)
- Threshold choice for classification
-/

section DiseasePortability

/-! **`f1Score` is not here any more.** It, `f1Score_at_precision0sensitivity0_is_junk`,
`f1_symmetric` and `f1_le_arithmetic_mean` moved to `Core/Decision.lean`, beside
`positivePredictiveValue`, `netBenefit` and `nriFromOperatingPoints`, which are the family
it belongs to. An F1 score is the harmonic mean of two reals and carries no programme
content; keeping it here meant `Portability/MetricSpecificPortability/PrecisionRecall.lean`
imported this module -- the audit layer, at the top of the graph -- to reach a formula in
two arguments, which is the `Portability -> Program` edge the layer order forbids. -/

/-
Two theorems were deleted from this section rather than renamed.

`prevalence_dominates_sensitivity_for_recall` assumed
`sens₁ / sens₂ < n_cases₂ / n_cases₁` and concluded `n_cases₁ * sens₁ < n_cases₂ * sens₂`.
Those are the same inequality: the proof was `rwa [div_lt_div_iff₀ ...] at h_sens_ratio`,
cross-multiplication and nothing else. The docstring said "The net effect on recall depends
on whether the prevalence increase dominates the sensitivity decrease. We prove the
sufficient condition" — but the sufficient condition *is* the conclusion, restated as a
ratio, so proving it from itself decides nothing about which effect dominates. Four of its
eight hypotheses, including the one saying the target has more cases, were unused.

`different_diseases_different_portability_patterns` took four inequalities as hypotheses
and returned their conjunction, `⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩`. Conjunction-introduction over
one's own premises is the case the corpus proof policy names explicitly. Nothing about
asthma, T2D, or a prevalence-distance relationship enters; the statement is true of any
four numbers with those orderings, which is what "qualitatively different patterns" was
being read off from.

The genuine metric-divergence result for this section is
`precision_recall_divergence_exists` above, which exhibits explicit witnesses satisfying
the precision identity rather than assuming the divergence.
-/

end DiseasePortability


/-!
## Calibrated PGS: When Portability is Recoverable

Not all portability loss is irrecoverable. Some can be addressed by:
1. Re-calibration (adjusting intercept and slope)
2. Ancestry-specific spline adjustments
3. Multi-ancestry training

We formalize which components of portability loss are recoverable.
-/

section RecoverablePortability


/-- **Rescaling by `1/r` inverts a slope change by `r`.**

    The nonvanishing hypothesis is real content: no rescaling recovers a slope that has
    been multiplied by zero. Read the name narrowly all the same. This is not
    recoverability by re-calibration, because recovering the slope requires knowing `r`,
    which this statement supplies to itself. -/
theorem slope_rescaling_inverts_slope_change
    (b r pgs : ℝ) (hr : r ≠ 0) :
    (b * r * pgs) * (1 / r) = b * pgs := by
  field_simp

/-- **LD mismatch is NOT recoverable by linear re-calibration.**
    If the LD structure changes, the normal equations have a different solution.
    No linear transformation of the source weights can recover the target optimum.
    (This reuses the existing source_erm_solves_source_not_target_normal_equations.) -/
theorem mulVec_smul_ne_of_not_aligned
    (w_source : Fin 2 → ℝ)
    (σ_target : Matrix (Fin 2) (Fin 2) ℝ)
    (cross_target : Fin 2 → ℝ)
    -- σ_target.mulVec is linear, so scaling w_source just scales the image
    -- The image of the source direction doesn't align with cross_target
    -- (cross_target is not a scalar multiple of σ_target.mulVec w_source)
    (h_not_aligned : ∀ α : ℝ, α • σ_target.mulVec w_source ≠ cross_target) :
    -- Then no linear re-calibration can recover target-optimal weights
    ∀ α : ℝ, σ_target.mulVec (α • w_source) ≠ cross_target := by
  intro α
  rw [Matrix.mulVec_smul]
  exact h_not_aligned α


end RecoverablePortability

end Descent.Program
