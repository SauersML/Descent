/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem
import Descent.Portability.NeutralFellerProperty
import Descent.Portability.PartialHaplotypeDualSemigroup
import Descent.Portability.NeutralPulseHistoryKernel
import Descent.Portability.NeutralRateHistoryKernel
import Descent.Portability.TwoLocusMicroscopicApproximation
import Descent.Portability.PipelineLDPairDomain
import Descent.Portability.PortabilityExactLocality
import Descent.Portability.HistoryExactLocality
import Descent.Portability.EndToEndPortabilityLaw
import Descent.Portability.EndToEndCorrelationSeries
import Descent.Portability.EndToEndPortabilityLipschitz
import Descent.Portability.EndToEndPortabilityRateLipschitz
import Descent.Portability.PortabilityMetricCompilation
import Descent.Portability.EndToEndCalibrationLaw
import Descent.Portability.EndToEndPooledCalibration
import Descent.Portability.EndToEndDiscriminationLaw
import Descent.Portability.EndToEndBrierLaw
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.EndToEndDiploidLaw
import Descent.Portability.EndToEndDiploidHistoryLaw
import Descent.Portability.EndToEndGWASTrainingLaw
import Descent.Portability.EndToEndGWASTrainingHistory
import Descent.Portability.EndToEndAscertainedLaw
import Descent.Portability.EndToEndAscertainedWitness
import Descent.Portability.TwoLocusPortabilityDecay
import Descent.Portability.PolygenicPortabilityDecay
import Descent.Portability.MigrationPortabilityFactor
import Descent.Portability.EndToEndSensitivityLaw
import Descent.Portability.EndToEndSensitivityMetrics
import Descent.Portability.EndToEndSensitivityArchitecture
import Descent.Portability.EndToEndSensitivityRates
import Descent.Portability.SelectionHistoryMoments
import Descent.Portability.EndToEndSelectionLaw
import Descent.Portability.SelectionMomentExpansion
import Descent.Portability.SelectionMomentUniqueness
import Descent.Portability.PortabilityCurveIdentifiability
import Descent.Portability.PortabilitySizeBlindness
import Descent.Portability.PortabilityMinimaxLowerBound
import Descent.Portability.PortabilityTwoHistoryInstance
import Descent.Portability.PortabilityMinimaxRate
import Descent.Portability.PortabilityIdentification

namespace Descent.Program

/-!
# Polygenic score portability: the theory from demography to every metric

A polygenic score is built in some populations and used in others, and its portability is how
its metrics change between them.  This header assembles the corpus's theory of that change as
one chain of proved laws, read from the input to the output.

1. A demographic history is a Markov process law on multi-deme haplotype frequencies, constructed
   from the neutral diffusion and not assumed.
2. The metrics of any score are polynomial functionals of the population laws that process
   produces, or convergent series of them.  So every metric is a propagator applied to the
   initial configuration moments, followed by one rational function or one series.
3. Ploidy, training, ascertainment and selection act on that chain at stated moment budgets.
4. The closed-form decay laws, the sensitivities, and the limits of what data can identify then
   follow.

Every module named here was checked on the pinned toolchain with axioms limited to `propext`,
`Classical.choice` and `Quot.sound`.  Nothing in the chain is a literature input.  The process
law is built from generators, the metrics are the corpus population metrics, and every constant is
derived.  Where a law carries a hypothesis, the Scope section at the end names it.

## 1. The input: a demography is a process law

* The neutral multi-deme diffusion is a Feller semigroup, strongly continuous at every time
  (`NeutralFellerProperty.continuous_neutralSemigroupExtension`).  Its configuration moments move
  by the matrix exponential of an explicit finite dual generator, NOTE1 (20)
  (`PartialHaplotypeDualSemigroup.expectedMomentVector_eq_matrixExponential`).
* A history of epochs, splits and admixture pulses is a Markov kernel
  (`NeutralPulseHistoryKernel.historyEventKernel`, `isMarkovKernel_historyEventKernel`), under
  which the configuration moments are the chronological propagator applied to the initial
  moments (`integral_momentPolynomial_historyEventKernel`).  That propagator is substochastic
  (`historyEventPropagator_substochastic`).  A rate path with continuous dual generator is a
  Markov kernel too, the uniform limit of its sampled histories
  (`NeutralRateHistoryKernel.rateHistoryKernel`, `tendstoUniformly_integral_sampledHistoryKernel`,
  `integral_momentPolynomial_rateHistoryKernel`).
* Every propagated two-locus moment field is realized by a haplotype law, so the linkage
  coordinates are genuine and not merely formal
  (`TwoLocusMicroscopicApproximation.history_present_locusExchangeable_realization`,
  `history_LDPairDomain`, and for compiled pipeline histories `PipelineLDPairDomain`).
* Neutral portability is exactly local.  No dual transition adds a locus, so the report of a
  score on a set of loci does not depend on the model outside it
  (`PortabilityExactLocality.expectedMomentVector_eq_of_agreeOn`,
  `HistoryExactLocality.expectedPortability_eq_of_agreeOn`).

## 2. The output: every metric of every score

* **Second-moment metrics of any deployment.**  For arbitrary scored and causal variant sets,
  arbitrary population-specific effects, an arbitrary residual carrying environment, interaction
  and non-additivity, and arbitrary weights, the master theorem gives the exact `R²`, calibration
  slope, intercept and mean squared error (`PortabilityMasterTheorem.r2_eq`,
  `calibrationSlope_eq`, `calibrationIntercept_eq`, `deployedMse_eq`).
  * Source-to-target movement splits into tagging, turnover and context channels with no
    remainder (`predictiveCovariance_transport`, `r2_transport_factorisation`).
  * A three-real statistic determines `R²` and slope (`metrics_eq_of_statistic_eq`), its range is
    the Cauchy–Schwarz cone (`exists_deployment_with_statistic`), and each coordinate is
    necessary (`scoreVariance_coordinate_necessary`, `predictiveCovariance_coordinate_necessary`,
    `outcomeVariance_coordinate_necessary`), so no score-side summary determines `R²`
    (`no_score_side_summary_determines_r2`).
  * The affine gauge is the repairable part of portability loss (`bestAffine_mse_eq`,
    `r2_affine_invariant`).  A fitted score is calibrated where it was fitted
    (`calibrationSlope_optimalWeights`), and deploying it costs the target oracle plus a quadratic
    form (`deployedMse_excess`).
  * Nothing beyond second moments is covered: two deployments equal in every second-moment metric
    refer different numbers above a cut-off (`statistic_does_not_determine_exceedance`).
* **Squared correlation.**  Along any history the expected correlation numerator and denominator
  are coefficient vectors dotted with the propagated budget-4 moments, so expected portability is
  an explicit rational function of `U · H₄(x₀)`
  (`EndToEndPortabilityLaw.expectedPortability_historyEventKernel`,
  `expectedPortability_rateHistoryKernel`), and the joint ratio of NOTE2 (27) is one of
  `U · H₈(x₀)` (`expectedJointPortability_historyEventKernel`).  The expected squared correlation
  itself is the series `Σ_k c_k ⬝ (U · H_{4(k+1)}(x₀))`
  (`EndToEndCorrelationSeries.expectedSquaredCorrelation_eq_tsum`,
  `expectedSquaredCorrelation_historyEventKernel`).
* **Calibration.**  Slope, calibration portability and intercept of expectations are rational in
  the propagated budget-2 and budget-3 moments
  (`EndToEndCalibrationLaw.expectedCalibrationSlope_historyEventKernel`,
  `expectedCalibrationPortability_historyEventKernel`,
  `expectedCalibrationIntercept_historyEventKernel`), and each is the score-variance-weighted
  expectation of the per-population metric (`expectedCalibrationSlope_eq_weighted`).  The pooled
  covariance is the expected within-population covariance plus the covariance of the deme means
  (`EndToEndPooledCalibration.covariance_pooledLaw`).  The deployment slope, intercept and minimum
  recalibrated error follow at budgets 2, 3 and 4 (`expectedDeploymentSlope_historyEventKernel`,
  `expectedDeploymentIntercept_historyEventKernel`,
  `expectedMinimumRecalibratedMse_historyEventKernel`).  The deployed error is exact at budget 1
  (`integral_deployedMse_historyEventKernel`), and no fixed recalibration beats the pooled line
  (`integral_recalibratedMse_ge`, `integral_bestAffineMse_eq`).
* **Discrimination.**  AUC portability is rational in the budget-2 moments and the expected AUC is
  a series (`EndToEndDiscriminationLaw.expectedAUCPortability_historyEventKernel`,
  `expectedAUC_historyEventKernel`).  The budget that fixes squared-correlation portability
  already fixes AUC portability
  (`expectedPortability_and_expectedAUCPortability_eq_of_moments_eq`,
  `moments_forall_four_iff_forall_two`).
* **Brier loss and calibration error.**  The repaired Brier loss is an exact series whose budgets
  grow by one per term, with a budget-1 upper bound from any fixed recalibration.  The calibration
  error lies between a budget-1 and a budget-2 computation
  (`EndToEndBrierLaw.expectedRepairedBrier_historyEventKernel`,
  `expectedRepairedBrier_historyEventKernel_le`,
  `expectedCalibrationError_bounds_historyEventKernel`).
* **Stability.**  Propagators of two rate paths differ by at most
  `(∫‖Q₁ − Q₂‖) e^{∫‖Q₁‖} e^{∫‖Q₂‖}`
  (`EndToEndPortabilityLipschitz.norm_rateHistoryDualPropagator_sub_le`).  Expected portability,
  calibration portability and the pooled slope are Lipschitz in the rate history on the
  realization body
  (`EndToEndPortabilityRateLipschitz.abs_expectedPortability_rateHistory_sub_le`,
  `EndToEndCalibrationLaw.abs_expectedCalibrationPortability_rateHistory_sub_le`,
  `EndToEndPooledCalibration.abs_compiledSlope_pooledLaw_rateHistory_sub_le`), through the
  compiled metric bounds (`PortabilityMetricCompilation.abs_crossRatio_sub_le`).
* **The moment ladder.**  What a demography contributes to all of this is one statistic.
  * Agreement of two histories on the propagated budget-4 moments fixes the whole report: pooled
    laws, slopes, intercepts, and calibration, squared-correlation and AUC portability
    (`PortabilityMomentLadder.portabilityReport_eq_of_momentsAgreeAt_four`).
  * Budget 8 adds the joint ratio and GWAS-trained accuracy at every cohort size
    (`portabilityReport_and_training_eq_of_momentsAgreeAt_eight`).
  * Every budget fixes the expected per-population metrics
    (`expectedMetrics_eq_of_momentsAgreeAt_all`).

## 3. The individual: ploidy

* Diploid additive scores port exactly as haploid ones for any within-deme inbreeding `F ∈ [0, 1]`:
  numerator and denominator both scale by `4 (1 + F)²`
  (`EndToEndDiploidLaw.squaredCorrelation_inbredMating_diploidSum`,
  `expectedDiploidPortability_historyEventKernel`).  A dominance observable breaks the transfer
  (`diploidProduct_breaks_ploidy_transfer`).
* With dominance the law holds at budget 8, along event and rate histories
  (`EndToEndDiploidHistoryLaw.expectedDiploidPortability_historyEventKernel_budgetEight`,
  `expectedDiploidPortability_rateHistoryKernel_budgetEight`).  For additive scores it agrees with
  the haploid budget-4 function (`diploidMomentPortability_diploidSum_historyEventKernel`).

## 4. The score: training and ascertainment

* **A finite-sample GWAS.**
  * Marginal weights from `n` source individuals have second moments
    `w_i w_j + E_ij/n + P_ij/(n(n − 1))`
    (`EndToEndGWASTrainingLaw.expectation_gwasWeights_mul`).
  * Each accuracy accumulator decreases in `n` to its population value (`trainedNumerator_eq`,
    `trainedNumerator_antitone`, `tendsto_trainedAccuracy`).
  * Accuracy itself is a mediant, not a deflated population value (`samplingForm_div_le_iff`).
    It is exact with one tag (`trainedAccuracy_unique`) and not monotone in `n`: finite training
    can beat the population score (`populationAccuracy_lt_trainedAccuracy`,
    `trainingWitness_accuracy`).
  * Along any history it is rational in the budget-8 moments and `n`
    (`EndToEndGWASTrainingHistory.expectedTrainedAccuracy_historyEventKernel`).
* **Ascertainment.**
  * A panel rule passes with probability a polynomial of degree at most `n`
    (`EndToEndAscertainedLaw.totalDegree_acceptancePolynomial_le`), so ascertained portability
    is rational in the budget-`(n + 4)` moments (`ascertainedPortability_historyEventKernel`,
    `ascertainedPortability_eq_conditionalOnPassing`).
  * When the target is uncorrelated with passing, ascertainment lowers portability exactly when
    passing raises source accuracy (`ascertainedPortability_lt_expectedPortability_iff`).
  * A founder event realizes the loss
    (`EndToEndAscertainedWitness.ascertainedPortability_founderWitnessKernel_lt`), and on a shared
    draw independent panels do not multiply (`founderWitnessLaw_sharedDraw_ne_prod`).

## 5. Closed-form decay

* **Two loci.**  On the low-order moment system, the cross-population squared correlation of a
  tag-locus score relative to its value at a split `T` ago is `e^{-2rT}`, and drift cancels
  exactly (`TwoLocusPortabilityDecay.splitPortabilityRatio_eq`).  It decreases in time and in
  recombination and tends to zero (`portabilityDecay_antitone_duration`,
  `portabilityDecay_antitone_rate`, `tendsto_portabilityDecay_atTop`).
* **Many loci.**  The ratio of a polygenic score is the signal-weighted sum of the per-pair decays
  (`PolygenicPortabilityDecay.scorePortabilityRatio_eq`), with floor the share of signal at zero
  recombination, set by causal coverage (`tendsto_scorePortabilityRatio_atTop`,
  `coverageFloor_eq_rateShare`).  Correlated pairs add a survivor term
  (`crossScorePortabilityRatio_eq_diagonal_add`), and sign-cancelling pairs make the ratio rise
  (`not_antitoneOn_cancellingDecay`).  The tag-locus retention surface is `e^{-r(d) τ(t)}`
  (`splitLDRetention_eq`).
* **Migration.**  Under symmetric migration `m` the split ratio is
  `(e^{-ρ̄T} + m·A_D)/(1 + m·A_π)`
  (`MigrationPortabilityFactor.splitPortabilityRatio_withSymmetricMigration`).

## 6. Response: how accuracy moves with every input

* The derivative of an epoch propagator is Duhamel's
  (`EndToEndSensitivityLaw.hasDerivAt_matrixExponential_of_hasDerivAt`).  A history's derivative
  is the sum over stages of forward law, event derivative and backward value
  (`hasDerivAt_dotProduct_historyEventPropagator`).
* Squared-correlation, calibration and AUC portability have explicit derivatives, and portability
  decreases exactly when the target's relative sensitivity is below the source's
  (`EndToEndSensitivityMetrics.hasDerivAt_expectedPortability_historyEventKernel`,
  `crossRatioDerivative_neg_iff_of_pos`).  Portability strictly decreases in the target
  environment variance
  (`EndToEndSensitivityArchitecture.portability_environmentVariance_derivative_neg`).
* The dual generator is linear in the rates, so along any segment of rate laws these derivatives
  hold with no differentiability hypothesis
  (`EndToEndSensitivityRates.hasDerivAt_dualGenerator_rateSegment`,
  `hasDerivAt_expectedPortability_segmentHistory`,
  `hasDerivAt_expectedCalibrationPortability_segmentHistory`).

## 7. Selection

* With haploid fitness bounded by `σ`, the selected moments along any history stay within `BσT`
  of the neutral propagation (`SelectionHistoryMoments.norm_expectedMomentVector_sub_propagator_le`,
  `EndToEndSelectionLaw.norm_selectedHistory_sub_propagator_le`).  Portability moves by at most an
  explicit multiple of `σT` (`abs_selectedPortability_sub_neutral_le`).
* No finite-budget law exists: frequency mixtures agreeing on every budget-4 moment have different
  selection terms (`not_exists_budgetFour_selectionClosure`,
  `not_budgetFour_moments_eq_of_selection`).
* The next term is exact: one epoch equals the neutral propagator plus an explicit first-order
  correction, up to `O(σ² d²)`
  (`SelectionMomentExpansion.norm_expectedMomentVector_sub_firstOrder_le`,
  `abs_expectedPolynomial_sub_firstOrder_le`).
* Bounded selected moment families are determined by their initial moments
  (`SelectionMomentUniqueness.moments_eq_of_selectedMomentEquation`,
  `expectedMoments_eq_of_selectedForward`).

## 8. What data can tell: identification and its limits

* **Curves.**  The split-law average of the portability ratio is the Laplace curve `E[e^{-rT}]`
  for any drift, and its values at `k r₀` determine the split-time law
  (`PortabilityCurveIdentifiability.meanSplitPortabilityRatio_eq`,
  `splitLaw_eq_of_meanSplitPortabilityRatio_eq`).  The ratio of expectations depends on drift
  (`pooledSplitPortabilityRatio_depends_on_drift`).  The averaged curve is blind to population
  size, and no estimator of size from it has bounded error
  (`PortabilitySizeBlindness.meanSizeHistoryPortabilityRatio_eq_of_splitLaw`,
  `populationSize_error_ge`).
* **Minimax.**  Source data cannot fix target portability.  Two histories with close source laws
  and different targets force a worst-case error floor at every sample size
  (`PortabilityMinimaxLowerBound.lowerBound_cohortLaw_pow`).  On the reference model half the
  target gap is the exact minimax risk (`PortabilityTwoHistoryInstance.isLeast_worstRisk`,
  `minimax_floor_r2`).  With the coupling supplied the rate `count^(-1/2)` is optimal
  (`PortabilityMinimaxRate.minimaxRate_dichotomy`).
* **Identification.**  The target report law is a transport of the source law by the coupling
  of the exposure law, the plug-in is consistent at rate `n^{-1/2}`, and together with the
  minimax bound this is an exact information boundary
  (`PortabilityIdentification.expectation_chronologyLaw_eq_transportExpectation`,
  `expectation_abs_plugIn_chronologyLaw_sub_le`, `logTwo_informationBoundary`).

Scope.
* Selection laws take the forward moment equation with selection as a hypothesis on the moment
  families: the selected diffusion is not constructed, one fitness table covers the whole
  history, and fitness is haploid at one locus.
* The expectation of each population's calibration slope is not a rational function of finitely
  many moments and is not stated.  Whether the expected calibration error is finite-moment is
  open.
* Environment enters through its moments per deme, supplied as model inputs, not measured
  constants.
* The rate-history kernels need continuous dual generators.  Integrable rate histories are
  realized (`NeutralIntegrableRateRealization`) but not carried to metric kernels.
* Inbreeding `F < 0`, locus-dependent `F`, sex-specific frequencies and assortative mating are not
  covered.  Training is the marginal GWAS or population ridge, with no LD adjustment.
* The minimax bounds are two-point bounds over finite report laws.
-/

end Descent.Program
