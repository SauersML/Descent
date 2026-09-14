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
import Descent.Portability.EndToEndLogLossLaw
import Descent.Portability.EndToEndLogLossBounds
import Descent.Portability.EndToEndMutualInformationPinsker
import Descent.Portability.PortabilityMomentLadderBrier
import Descent.Portability.EndToEndDecisionLaw
import Descent.Portability.EndToEndGWASCalibrationLaw
import Descent.Portability.MigrationPortabilityFirstOrderFactor
import Descent.Portability.EndToEndDiploidGWASTraining
import Descent.Portability.EndToEndSensitivityRatePathMetrics
import Descent.Portability.EndToEndDeploymentLaw
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.PortabilityMomentLadderSharpness
import Descent.Portability.PortabilityMomentLadderDeployment
import Descent.Portability.PortabilityMomentLadderSeries
import Descent.Portability.PortabilityMomentLadderEntropy
import Descent.Portability.EndToEndDiploidLaw
import Descent.Portability.EndToEndDiploidHistoryLaw
import Descent.Portability.EndToEndGWASTrainingLaw
import Descent.Portability.EndToEndGWASTrainingHistory
import Descent.Portability.EndToEndGWASThresholdLaw
import Descent.Portability.TwoTimeRatePropagator
import Descent.Portability.SelectionHistoryFirstOrder
import Descent.Portability.SelectionMetricsFirstOrder
import Descent.Portability.PortabilityMomentLadderDecision
import Descent.Portability.PortabilityMomentLadderEight
import Descent.Portability.EndToEndAscertainedLaw
import Descent.Portability.EndToEndAscertainedWitness
import Descent.Portability.TwoLocusPortabilityDecay
import Descent.Portability.PolygenicPortabilityDecay
import Descent.Portability.MigrationPortabilityFactor
import Descent.Portability.MigrationPortabilityFirstOrder
import Descent.Portability.EndToEndSensitivityLaw
import Descent.Portability.EndToEndSensitivityMetrics
import Descent.Portability.EndToEndSensitivityArchitecture
import Descent.Portability.EndToEndSensitivityRates
import Descent.Portability.FundamentalMatrixParameterDerivative
import Descent.Portability.EndToEndSensitivityRatePath
import Descent.Portability.EndToEndSensitivitySeries
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
* **The accuracy calculator.**  Under any history the expected deployment moments of each deme,
  the tag, tag–causal and causal covariances and means, are the deployment moments of the
  propagated budget-2 moments (`EndToEndDeploymentLaw.expectedDemeMoments_historyEventKernel`,
  `expectedDemeMoments_rateHistoryKernel`).  So weights trained in a source deme and deployed in a
  target deme have a deployed `R²`, slope, intercept and error computed from `U · H₂(x₀)`
  (`transferReport_historyEventKernel`, `transferReport_eq_of_moments_eq`).  The score–outcome
  covariance moves through a tagging, an architecture and an environment channel, and the score
  variance only through tagging (`predictiveCovariance_sub_channels`, `scoreVariance_sub_channel`,
  `outcomeVariance_sub_channels`).
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
* **Log loss, entropy and mutual information.**  The log loss of the forecast repaired to each
  score group's realized rate is the conditional entropy of the outcome given the score
  (`EndToEndLogLossLaw.expectation_neg_log_repairedGroupForecast`,
  `conditionalEntropy_eq_repairedLogLoss`).  The entropy function is the division-free series
  `η(x) = Σ_k x (1 − x)^{k+1}/(k + 1)` with tail at most `(1 − x)^{K+1}/(K + 1)`
  (`negMulLog_hasSum`, `negMulLog_truncation_mem`), so the expected entropy, conditional entropy
  and mutual information along any history are series of propagated-moment dot products with
  explicit truncation certificates (`expectedEntropy_eq_tsum_dotProduct`,
  `expectedConditionalEntropy_eq_tsum_dotProduct`, `expectedMutualInformation_eq_tsum_dotProduct`).
  The log loss of any fixed forecast is exact at budget 1, never below the conditional entropy,
  and infinite exactly when a ruled-out outcome has positive mass
  (`expectedForecastLogLoss_eq_dotProduct`, `conditionalEntropy_le_forecastLogLoss`,
  `expectedLogLoss_groupForecast_eq_top`).  Pseudo-`R²` and its portability are ratios of these
  series (`pseudoRSquaredPortability_eq_tsum_dotProduct`).  Mutual information is a sum of
  divergence terms, between zero and the outcome entropy, and zero exactly when score and outcome
  are independent, so pseudo-`R²` lies in `[0, 1]` in every population and in expectation along
  any history (`EndToEndLogLossBounds.mutualInformation_eq_sum_divergenceTerm`,
  `mutualInformation_nonneg`, `mutualInformation_le_outcomeEntropy`,
  `mutualInformation_eq_zero_iff`, `expectedPseudoRSquared_mem`,
  `expectedMutualInformation_eq_zero_iff`, `logLossBounds_historyEventKernel`).  Away from
  independence the bound is quantitative: a Padé-type inequality for the divergence term and
  Cauchy–Schwarz give Pinsker's inequality `I(S; Y) ≥ ½ (Σ |m − q_s p_b|)²`, derived in Lean with
  no constant taken from outside, so pseudo-`R²` is at least the squared independence gap over
  `2 H(Y)`, in every population and in expectation along any history
  (`EndToEndMutualInformationPinsker.pinsker_finite`,
  `half_sq_independenceGap_le_mutualInformation`, `two_mul_sq_totalVariation_le_mutualInformation`,
  `sq_independenceGap_div_le_pseudoRSquared`,
  `half_sq_integral_independenceGap_le_expectedMutualInformation`, `pinsker_historyEventKernel`,
  `pinsker_rateHistoryKernel`).
* **Clinical decision metrics.**  The confusion cells of any rule are linear in the haplotype
  frequencies, so along any history the expected confusion table is the table of the budget-1
  propagated moments (`EndToEndDecisionLaw.ruleConfusion_pushforward`,
  `expectedConfusion_eq_momentConfusion`, `expectedConfusion_historyEventKernel`).  Net benefit is
  exact at budget 1 and equals the net benefit of the expected table, and the comparison with
  treating everyone is one dot product (`expectedNetBenefit_eq_dotProduct`,
  `expectedNetBenefit_eq_expectedConfusion`, `expectedNetBenefit_sub_treatAll_eq_dotProduct`).
  Sensitivity, specificity, PPV, NPV, F1, Youden's J and relative risk port as functions of the
  budget-1 moments, and budget-2 agreement fixes them together with AUC portability
  (`expectedMetricPortability_eq_momentConfusion`,
  `expectedAUCPortability_and_expectedMetricPortability_eq_of_moments_eq`).  Expected
  per-population recall and precision are series of propagated moments
  (`expectedPositiveQuotient_eq_tsum_dotProduct`).  With equal recall and false positive rate,
  precision ports exactly when prevalence ports, and an explicit prevalence shift from `1/2` to
  `1/5` moves precision from `4/5` to `1/2` (`precision_eq_iff_prevalence_eq`,
  `prevalenceShift_witness`).
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
    (`portabilityReport_and_training_eq_of_momentsAgreeAt_eight`).  Agreement up to degree eight
    fixes the joint ratio under any process law, and an event history and a rate history with
    equal budget-8 moments give every score the same report, joint ratio and trained accuracy
    (`PortabilityMomentLadderEight.expectedJointPortability_eq_of_polynomialsAgreeAt_eight`,
    `reports_historyEvent_eq_rateHistory_eight`).
  * Every budget fixes the expected per-population metrics
    (`expectedMetrics_eq_of_momentsAgreeAt_all`), and so does agreement on every polynomial
    expectation under any process law, term by term through the series; an event history and a
    rate history with equal moment sequences give every score the same expected squared
    correlation and expected AUC
    (`PortabilityMomentLadderSeries.expectedMetrics_eq_of_polynomialsAgreeAt_all`,
    `expectedMetrics_historyEvent_eq_rateHistory`).  The same rung fixes the expected entropy,
    conditional entropy and mutual information of every report map
    (`PortabilityMomentLadderEntropy.expectedInformation_eq_of_polynomialsAgreeAt_all`,
    `expectedInformation_historyEvent_eq_rateHistory`), and the expected repaired Brier loss of
    every report map
    (`PortabilityMomentLadderBrier.expectedRepairedBrier_eq_of_polynomialsAgreeAt_all`,
    `expectedRepairedBrier_historyEvent_eq_rateHistory`).
  * Clinical decisions read the lowest rung.  Agreement up to degree one fixes the whole decision
    report, every deme's expected confusion table, case probability, called fraction and net
    benefit at every threshold, and the portability of every threshold metric; budget four fixes
    it together with the portability report, and every degree fixes expected recall and precision
    (`PortabilityMomentLadderDecision.decisionReport_eq_of_polynomialsAgreeAt_one`,
    `portabilityReport_and_decisionReport_eq_of_polynomialsAgreeAt_four`,
    `expectedRecallPrecision_eq_of_polynomialsAgreeAt_all`,
    `decisionReport_historyEvent_eq_rateHistory`).
  * None of this is special to histories of epochs.  Any two process laws with dual moments that
    agree on degree-four polynomial expectations have one report
    (`polynomialsAgreeAt_of_hasDualMoments`, `portabilityReport_eq_of_polynomialsAgreeAt_four`).
    An event history and a continuous rate history with equal propagated budget-4 moments are
    therefore indistinguishable by every metric of the report
    (`portabilityReport_historyEvent_eq_rateHistory`).
  * The first rung is sharp.  A founder event that fixes the source deme on one sampled
    haplotype keeps every expected frequency, so every metric of the pooled law, but moves the
    calibration slope of a varying score from one to zero
    (`PortabilityMomentLadderSharpness.integral_mass_founderEventLaw`,
    `expectedFrequencies_eq_and_calibrationSlope_ne`).
  * The calculator reads the same ladder.  Agreement up to degree two fixes the expected
    deployment moments of every deme, so every ridge-trained score has one deployed `R²`, slope,
    intercept and error under two process laws that agree there, an event history and a rate
    history included, and one rung, budget four, fixes both reports
    (`PortabilityMomentLadderDeployment.expectedDemeMoments_eq_of_polynomialsAgreeAt_two`,
    `transferReport_eq_of_polynomialsAgreeAt_two`, `transferReport_historyEvent_eq_rateHistory`,
    `reports_eq_of_polynomialsAgreeAt_four`).

## 3. The individual: ploidy

* Diploid additive scores port exactly as haploid ones for any within-deme inbreeding `F ∈ [0, 1]`:
  numerator and denominator both scale by `4 (1 + F)²`
  (`EndToEndDiploidLaw.squaredCorrelation_inbredMating_diploidSum`,
  `expectedDiploidPortability_historyEventKernel`).  A dominance observable breaks the transfer
  (`diploidProduct_breaks_ploidy_transfer`).
* With dominance the law holds at budget 8, along event and rate histories
  (`EndToEndDiploidHistoryLaw.expectedDiploidPortability_historyEventKernel_budgetEight`,
  `expectedDiploidPortability_rateHistoryKernel_budgetEight`).  For additive scores it agrees with
  the haploid budget-4 function, along event histories and along rate histories
  (`diploidMomentPortability_diploidSum_historyEventKernel`,
  `EndToEndDiploidGWASTraining.diploidMomentPortability_diploidSum_rateHistoryKernel`).

## 4. The score: training and ascertainment

* **Population ridge training.**  In its own deme a ridge score has covariance with the outcome
  equal to its variance plus the penalty times the squared weight norm, so its calibration slope is
  `1 + λ ‖w‖² / Var S`, at least one for a nonnegative penalty and exactly one for least squares,
  where `R² = Var S / Var Y`
  (`EndToEndDeploymentLaw.predictiveCovariance_trainedWeights`, `calibrationSlope_trainedWeights`,
  `one_le_calibrationSlope_trainedWeights`, `calibrationSlope_trainedWeights_zero`,
  `r2_trainedWeights_zero`).  Pooled training at a unit share is training in that deme
  (`pooledTrainedWeights_single`).
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
  * Trained on diploid individuals, the gamete-pair masses have degree two in the haplotype
    frequencies, so the trained numerator and denominator are polynomials of total degree at most
    sixteen in the two demes, and the expected diploid trained accuracy is rational in the
    propagated budget-16 moments and `n`, along event and rate histories
    (`EndToEndDiploidGWASTraining.trainedNumerator_stateGenotypeLaw`,
    `totalDegree_diploidTrainedPolynomial_le`, `expectedDiploidTrainedAccuracy_eq_moment`,
    `expectedDiploidTrainedAccuracy_historyEventKernel`,
    `expectedDiploidTrainedAccuracy_rateHistoryKernel`,
    `expectedDiploidTrainedAccuracy_eq_of_moments_eq`).
* **Calibration of a GWAS-trained score.**  The trained score's expected target covariance with the
  outcome carries no sampling term, while its expected variance is `α + β/n + γ/(n(n − 1))`, so
  the calibration slope of expectations is the population slope times the exact attenuation factor
  `α/(α + τ_n)`, which lies in `[0, 1]`, rises with `n` and tends to one
  (`EndToEndGWASCalibrationLaw.trainedCovariance_eq`, `trainedVariance_eq`,
  `trainedCalibrationSlope_eq_mul_attenuationFactor`, `tendsto_trainedCalibrationSlope`).  The
  attenuation is strict at every finite `n` when the population covariance is positive
  (`trainedCalibrationSlope_lt_populationCalibrationSlope`).  Unlike accuracy, calibration moves
  monotonically with the cohort size (`trainedCalibrationSlope_monotone`), and a one-tag law keeps
  accuracy fixed while strictly attenuating the slope (`calibrationWitness`).  Along any history
  the trained slope is rational in the budget-6 moments and the intercept in the budget-7 moments
  (`expectedTrainedCalibrationSlope_historyEventKernel`,
  `expectedTrainedCalibrationIntercept_historyEventKernel`).
* **Thresholding on the training cohort, and the winner's curse.**
  * Any statistic of the training cohort is a learner, and its expected accuracy reads the
    second-moment matrix of the learned weights against the target matrices
    (`EndToEndGWASThresholdLaw.learnedNumerator_eq`, `learnedDenominator_eq`).  Keeping a tag's
    sample covariance only above a threshold is the corpus p-value stage read on the cohort's own
    table (`covarianceThresholdWeights_eq_thresholdWeights`).
  * Along any history the expected thresholded accuracy is rational in the budget-`(n + 4)`
    moments: the cohort absorbs the source degree, only the target adds four
    (`expectedLearnedAccuracy_historyEventKernel`, `expectedLearnedAccuracy_rateHistoryKernel`,
    `expectedLearnedAccuracy_eq_of_moments_eq`).
  * In magnitude the curse holds for every cohort size, threshold and tag: conditional on being
    selected, the estimate is on average at least as large as the true effect
    (`abs_marginalWeights_mul_le_expectation_abs`, `abs_marginalWeights_le_conditional`).  The
    signed statement fails for two-sided selection, and on the same law the population
    thresholded accuracy is zero while a cohort of two gives positive accuracy
    (`curseWitness_marginalWeights`, `curseWitness_selection`, `curseWitness_accuracy`).
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
  (`MigrationPortabilityFactor.splitPortabilityRatio_withSymmetricMigration`).  Read on the history
  without migration, the heterozygosity stencil is an explicit combination of exponentials, and
  it is nonnegative, so to first order migration raises the heterozygosity denominator
  (`MigrationPortabilityFirstOrder.heterozygosityMigrationStencil_noMigration`,
  `heterozygosityMigrationStencil_noMigration_nonneg`).  The generator is affine in `m`, so the
  split ratio has an exact derivative at `m = 0`, one-sided on `m ≥ 0`, the first-order migration
  factor `A_D − e^{-ρ̄T} A_π`; at zero recombination it is
  `φ₁(T) = 2 (cosh cT − 1)(π₀ − DD₀)(π₀ + Dz₀)/(c·DD₀·π₀)`, nonnegative when `DD₀ ≤ π₀` and
  `π₀ + Dz₀ ≥ 0`, so weak migration then raises portability to first order
  (`MigrationPortabilityFirstOrderFactor.augmentedLowOrderLDGenerator_withSymmetricMigration`,
  `hasDerivWithinAt_splitPortabilityRatio_withSymmetricMigration`).

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
* A whole time-varying rate history moves the same way.  Along a segment of two rate histories the
  fundamental matrix has the lower-left block of a doubled generator path as its derivative
  (`FundamentalMatrixParameterDerivative.hasDerivAt_fundamentalMatrix_affinePath`), so the
  propagator and expected portability of the rate history have exact derivatives
  (`EndToEndSensitivityRatePath.hasDerivAt_rateHistoryDualPropagator_segment`,
  `hasDerivAt_expectedPortability_rateSegment`).  The block form is the Duhamel integral: the
  two-time propagator `U(t, s)` of a generator path is constructed, with `U(t, t) = 1`,
  Chapman–Kolmogorov and both Kolmogorov equations, and the derivative of `U_θ(T, 0)` is
  `∫₀ᵀ U(T, s) Δ(s) U(s, 0) ds` (`TwoTimeRatePropagator.twoTimePropagator_self`,
  `twoTimePropagator_mul`, `hasDerivWithinAt_twoTimePropagator_left`,
  `hasDerivWithinAt_twoTimePropagator_right`, `hasDerivAt_twoTimePropagator_affinePath`,
  `ratePathSensitivity_eq_integral`).  Calibration and AUC move the same way along a rate path:
  the calibration slope, calibration portability, intercept and AUC portability of expectations
  have exact derivatives in Duhamel form, and calibration or AUC portability decreases exactly
  when the target's relative sensitivity is below the source's
  (`EndToEndSensitivityRatePathMetrics.hasDerivAt_expectedCalibrationPortability_rateSegment`,
  `hasDerivAt_expectedAUCPortability_rateSegment`, `ratePathSensitivity_eq_duhamelSensitivity`,
  `deriv_expectedCalibrationPortability_rateSegment_neg_iff`,
  `deriv_expectedAUCPortability_rateSegment_neg_iff`).  The expected squared correlation is
  differentiated termwise along segment histories
  (`EndToEndSensitivitySeries.summable_integral_seriesTerm`,
  `hasDerivAt_expectedSquaredCorrelation_segmentHistory`).

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
* Along a whole history the first-order law composes.  The selected moments equal the neutral
  propagation plus a history correction, the rest-of-history propagator applied to each epoch's
  correction, within `B S (B + 1) σ T²`
  (`SelectionHistoryFirstOrder.norm_selectedHistory_sub_firstOrder_le`).  The correction is linear
  in the fitness table and is the right derivative of the moments in the selection strength
  (`historyCorrection_scaledModel`, `norm_scaledHistory_sub_firstOrder_le`,
  `hasDerivWithinAt_selectedHistory_firstOrder`).  So portability under selection is the neutral
  portability plus `σ` times an explicit first-order term, within an explicit `O(σ² T²)`
  remainder, and selection raises portability to first order exactly when the target accuracy's
  relative first-order change exceeds the source's
  (`abs_selectedPortability_sub_firstOrder_le`, `hasDerivWithinAt_selectedPortability_firstOrder`,
  `portabilityFirstOrder_pos_iff`).
* The same first-order law holds for calibration and discrimination.  The calibration slope,
  intercept and calibration portability of expectations, and AUC portability, each equal their
  neutral values plus `σ` times an explicit correction within an `O(σ² T²)` remainder, each
  correction is the right derivative in `σ` at zero, and selection raises calibration or AUC
  portability to first order exactly when the target's relative change exceeds the source's
  (`SelectionMetricsFirstOrder.abs_selectedCalibrationSlope_sub_firstOrder_le`,
  `abs_selectedCalibrationPortability_sub_firstOrder_le`,
  `abs_selectedAUCPortability_sub_firstOrder_le`,
  `hasDerivWithinAt_selectedCalibrationPortability_firstOrder`,
  `calibrationPortabilityFirstOrder_pos_iff`, `aucPortabilityFirstOrder_pos_iff`).

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
* The termwise derivative of the expected squared correlation takes a summable bound on the term
  sensitivities as a hypothesis.
* Environment enters through its moments per deme, supplied as model inputs, not measured
  constants.
* The rate-history kernels need continuous dual generators.  Integrable rate histories are
  realized (`NeutralIntegrableRateRealization`) but not carried to metric kernels.
* Inbreeding `F < 0`, locus-dependent `F`, sex-specific frequencies and assortative mating are not
  covered.  Training is the marginal GWAS or population ridge, with no LD adjustment.
* The minimax bounds are two-point bounds over finite report laws.
-/

end Descent.Program
