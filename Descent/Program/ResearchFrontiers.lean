/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.InfiniteGenomeRate
import Descent.Pangenome.GraphCoalescent.CompressionHiddenStateCount
import Descent.Pangenome.GraphCoalescent.MarkovCompressions
import Descent.Pangenome.AncestralLocality.InhomogeneousLocalityTransition
import Descent.Pangenome.AncestralLocality.SelectionDecisions
import Descent.Portability.PortabilityMinimaxLowerBound
import Descent.Portability.EndToEndPortabilityLaw
import Descent.Pangenome.GraphCoalescent.CompressionLoadAchievability
import Descent.Pangenome.AncestralLocality.SelectionClosure
import Descent.Portability.PortabilityTwoHistoryInstance
import Descent.Portability.EndToEndPortabilityLipschitz
import Descent.Portability.PortabilityMetricCompilation
import Descent.Portability.PortabilityExactLocality
import Descent.Portability.PortabilityIdentification
import Descent.Portability.EndToEndCorrelationSeries
import Descent.Portability.EndToEndPortabilityRateLipschitz
import Descent.Portability.TwoLocusPortabilityDecay
import Descent.Portability.PortabilityCurveIdentifiability
import Descent.Portability.PortabilitySizeBlindness
import Descent.Pangenome.GraphCoalescent.ReportNonMarkovFromSingletons
import Descent.Pangenome.GraphCoalescent.FiberSizeIdentifiability
import Descent.Pangenome.GraphCoalescent.FiberSizeSymmetricRecovery
import Descent.Pangenome.GraphCoalescent.ConnectionLawIdentifiability
import Descent.Pangenome.GraphCoalescent.HiddenClockCorrection
import Descent.Pangenome.GraphCoalescent.FiberSizeMultisetRecovery
import Descent.Pangenome.AncestralLocality.SelectionLightCone
import Descent.Pangenome.AncestralLocality.SelectionSemigroupPerturbation
import Descent.Portability.SelectionPortabilityBound
import Descent.Pangenome.GraphCoalescent.PanelSizeIdentifiability
import Descent.Pangenome.GraphCoalescent.FiberSizeIdentifiabilityFour
import Descent.Pangenome.GraphCoalescent.ReportInhomogeneousMarkov
import Descent.Pangenome.GraphCoalescent.PanelSizeTopCoefficient
import Descent.Pangenome.GraphTransitVariance
import Descent.Portability.PortabilityMinimaxRate
import Descent.Portability.HistoryExactLocality
import Descent.Pangenome.GraphSiteFrequencySpectrum
import Descent.Portability.PolygenicPortabilityDecay
import Descent.Portability.EndToEndDiscriminationLaw
import Descent.Portability.EndToEndDiploidLaw

namespace Descent.Program

/-!
# Research frontiers: theorems beyond the three research notes

The research notes of 11 September 2026 on exact portability laws, the pangenome hidden-lineage
clock and ancestral locality are formalized in `ExactPortabilityLaws`, `PangenomeHiddenClock` and
`AncestralLocality`. This header records theorems proved on top of them that the notes do not
state. Every module listed was checked on the pinned toolchain with axioms limited to `propext`,
`Classical.choice` and `Quot.sound`, and each module docstring carries its own Scope paragraph.

## Results

* An explicit rate for the infinite-genome limit: `InfiniteGenomeRate`. Along an exhaustion by
  balls of radius `ℓ_m`, the finite-genome semigroups converge to the infinite-genome semigroup
  within `2‖f‖ min {1, n|A| e^{DT} (2eDT/ℓ_m)^{ℓ_m}}`
  (`norm_operator_sub_infiniteGenomeSemigroup_le`), and so do sampling polynomials read through a
  finite window (`norm_windowPullback_operator_sub_infiniteGenomeSemigroup_le`).
* How much a pangenome compression hides: `CompressionHiddenStateCount`. The coarsest Markov
  refinement of the report has exactly as many states as the report when the interface is
  injective (`coarsestStateCount_eq_reportStateCount_of_injective`), and strictly more once two
  individuals share a graph state on an interface of width at least two
  (`reportStateCount_lt_coarsestStateCount`).
* Which compressions keep ancestry Markov: `MarkovCompressions`. The report of an interface of
  width `w` on `n` individuals is a strong lumping of Kingman's coalescent exactly when `w = n` or
  `w ≤ 1` (`isReportLumping_iff`), and the corpus criterion that also counts covers into a state's
  own report holds exactly for injective interfaces (`observablyMarkov_iff_injective`); every
  report component carries at most `|C| - w_C + 1` hidden lineages
  (`hiddenLoad_add_componentWidth_le`), and every positive load assignment constant on components
  within that bound is attained
  (`CompressionLoadAchievability.exists_observed_eq_hiddenLoad_eq_iff`).
* The end-to-end law of portability: `EndToEndPortabilityLaw`. For a neutral history of epochs,
  splits and pulses, or a continuous rate path, the expected correlation numerator and denominator
  of a score in each deme are coefficient vectors dotted with the propagated budget-4 moments, so
  expected portability is an explicit rational function of `U · H₄(x₀)`
  (`expectedPortability_historyEventKernel`, `expectedPortability_rateHistoryKernel`), the joint
  ratio of NOTE2 (27) of `U · H₈(x₀)` (`expectedJointPortability_historyEventKernel`), and two
  histories that agree on those moments have equal portability
  (`expectedPortability_eq_of_moments_eq`). Portability is Lipschitz in the rate path: the
  propagators of two continuous rate paths differ by at most
  `(∫₀ᵀ ‖Q₁ - Q₂‖) e^{∫‖Q₁‖} e^{∫‖Q₂‖}`
  (`EndToEndPortabilityLipschitz.norm_rateHistoryDualPropagator_sub_le`), and so does expected
  portability, up to `1/δ⁴` where the denominators stay above `δ`
  (`abs_expectedPortability_sub_le`); composed with the analysis of the metric, expected
  portability is Lipschitz in the rate history on the realization body with an explicit constant
  (`EndToEndPortabilityRateLipschitz.abs_expectedPortability_rateHistory_sub_le`). The metric
  side is explicit: the squared correlation, the
  calibration slope and the portability ratio are rational functions of five second moments, with
  explicit Lipschitz constants on the realization body
  (`PortabilityMetricCompilation.squaredCorrelation_eq_compiled`,
  `abs_compiledPortabilityRatio_sub_le`, `abs_crossRatio_sub_le`). The expected squared correlation
  itself, not only the ratio of expectations, is the series
  `Σ_k c_k ⬝ (U · H_{4(k+1)}(x₀))` (`EndToEndCorrelationSeries.expectedSquaredCorrelation_eq_tsum`,
  `expectedSquaredCorrelation_historyEventKernel`), so it too depends on the history only through
  propagated moments (`expectedSquaredCorrelation_eq_of_moments_eq`).
  The binary AUC goes through the same kernels. Its numerator and denominator have degree two,
  so AUC portability is a rational function of the budget-2 propagated moments
  (`EndToEndDiscriminationLaw.expectedAUCPortability_historyEventKernel`,
  `expectedAUCPortability_eq_of_moments_eq`), and the expected AUC is a series in propagated
  moments (`expectedAUC_historyEventKernel`). Diploid scores port exactly as haploid ones: for
  additive lifts and any within-deme inbreeding `F`, the correlation numerator and denominator
  both scale by `4 (1 + F)²`, so the squared correlation and expected portability are unchanged
  along any history (`EndToEndDiploidLaw.squaredCorrelation_inbredMating_diploidSum`,
  `expectedDiploidPortability_historyEventKernel`); a dominance observable breaks the transfer
  (`diploidProduct_breaks_ploidy_transfer`).
* The closed-form decay of portability through linkage: `TwoLocusPortabilityDecay`. On the NOTE1
  low-order moment system, for a source and a target split `T` ago with drift and recombination,
  the cross-population expected squared correlation of a tag-locus score relative to its value at
  the split is `e^{-2rT}`, with drift cancelling exactly (`crossSquaredCorrelation_eq`,
  `splitPortabilityRatio_eq`); it decreases in `T` and in the recombination rate
  (`portabilityDecay_antitone_duration`, `portabilityDecay_antitone_rate`), tends to zero
  (`tendsto_portabilityDecay_atTop`) and is identically one without recombination
  (`portabilityDecay_zero_rate`); the cross-heterozygosity form has its own exact decay law
  (`crossHeterozygosityPortabilityRatio_eq`).
* The polygenic law of portability decay: `PolygenicPortabilityDecay`. For a score over several
  tag–causal pairs on the same moment system, the cross-population ratio is the signal-weighted
  sum of the per-pair decays with drift cancelling (`scorePortabilityRatio_eq`); it decreases in
  the split time and in every recombination rate (`scorePortabilityRatio_antitone_duration`,
  `scorePortabilityRatio_antitone_recombination`) and tends to the signal share at zero
  recombination, the floor set by causal coverage (`tendsto_scorePortabilityRatio_atTop`,
  `coverageFloor_eq_rateShare`). The curve determines that share at every recombination rate
  (`rateShare_pairShare_eq_of_scorePortabilityRatio_eq`). Correlated pairs add a survivor term
  (`crossScorePortabilityRatio_eq_diagonal_add`) that vanishes for uncorrelated ancestral LD
  (`crossScorePortabilityRatio_eq_of_uncorrelated`), and sign-cancelling pairs make the ratio
  rise (`not_antitoneOn_cancellingDecay`).
* What a portability curve identifies: `PortabilityCurveIdentifiability`. With a random split
  time, the split-law average of each history's ratio is the Laplace curve `E[e^{-rT}]` for any
  drift (`meanSplitPortabilityRatio_eq`), and its values at `k r₀` determine the split-time law
  (`splitLaw_eq_of_meanSplitPortabilityRatio_eq`). The ratio of expectations is `L(c + r)/L(c)`
  and does depend on drift (`pooledSplitPortabilityRatio_eq`,
  `pooledSplitPortabilityRatio_depends_on_drift`). The averaged curve is blind to population
  size: histories with one split-time law and any size histories give one curve
  (`PortabilitySizeBlindness.meanSizeHistoryPortabilityRatio_eq_of_splitLaw`), and no estimator
  of the population size from it has bounded worst-case error (`populationSize_error_ge`).
* Neutral portability is exactly local: `PortabilityExactLocality`. No dual transition adds a locus,
  so configurations on loci within `A` are invariant (`dualTransitions_lociWithin`), and two
  neutral models that agree on the rates of `A` give the same expected moments on `A` at every time
  (`expectedMomentVector_eq_of_agreeOn`): the report of a score on `A` does not depend on the model
  outside `A` at all.
  Along whole histories the same holds: histories that agree event by event on `A`, from states
  with equal budget-4 moments over `A`, give equal expected portability
  (`HistoryExactLocality.expectedPortability_eq_of_agreeOn`,
  `integral_momentPolynomial_historyEventKernel_eq_of_agreeOn`).
* The compressed report is not Markov from the singletons: `ReportNonMarkovFromSingletons`. For an
  interface of width `2 ≤ w < n`, no time-homogeneous transition law on reports reproduces the law
  of the report history of Kingman's jump chain from the singletons (`not_isReportMarkovFromBot`),
  while an injective interface gives a Markov report (`isReportMarkovFromBot_of_injective`); on
  three haplotypes the report stays put with probability `1/3` after one step and `0` after two
  (`example_stay_given_one`, `example_stay_given_two`). A transition law that may depend on the
  jump count does exist when at most one graph state holds two or more haplotypes
  (`ReportInhomogeneousMarkov.isReportInhomogeneousMarkov_of_atMostOneHeavy`) and at width two
  (`isReportInhomogeneousMarkov_of_width_eq_two`), the three-haplotype example included
  (`example_isReportInhomogeneousMarkov`); for those interfaces only time homogeneity fails.
* What a compressed pangenome reveals about its hidden fiber sizes: `FiberSizeIdentifiability`.
  The connectivity cumulant, and hence the law of the reported connection time, determines the
  product of the fiber sizes at every width (`prod_eq_of_cumulantOfSizes_eq`), the unordered pair
  at width two (`coeff_one_deficitCumulant_card_two`, `coeff_two_deficitCumulant_card_two`), and
  the elementary symmetric polynomials of the sizes, so the multiset itself, at width three
  (`esymm_eq_of_cumulantOfSizes_eq_three`), which determine the multiset of sizes by Vieta
  (`FiberSizeSymmetricRecovery.multiset_nat_eq_of_esymm_eq`). At width four the next coefficient
  fixes the multiset when two profiles on a panel of at least five share a fiber size
  (`FiberSizeIdentifiabilityFour.fiberSizes_eq_of_cumulantOfSizes_eq_four_of_shared`); the
  general width-four case and widths five and more are open. The
  law of the reported connection time carries exactly the information of the cumulant, each
  determining the other
  (`ConnectionLawIdentifiability.map_connectionTime_eq_iff_connectivityCumulant_eq`,
  `survivalAt_eq_iff_connectivityCumulant_eq`). Composed, for interfaces of width at most three the
  law of the reported connection time determines the multiset of fiber sizes itself
  (`FiberSizeMultisetRecovery.fiberSizes_graphKer_eq_of_map_connectionTime_eq`). With the width
  unknown the law does not determine the panel size: every interface of width at most one gives
  the point mass at zero (`PanelSizeIdentifiability.exists_panelSize_collision`); two first-step
  laws with nonzero top spectral coefficients come from equal panel sizes
  (`panelSize_eq_of_survivalAt_eq`). The top coefficient has a residue formula
  (`PanelSizeTopCoefficient.spectralCoeff_bot_self_eq`), and `σ_n C(2n-2, n-1)` is an iterated
  forward difference of weighted stopping probabilities
  (`spectralCoeff_bot_self_mul_choose_eq_fwdDiff`). For an injective interface
  `σ_n C(2n-2, n-1) = (-1)^n n`, so the coefficient is nonzero and the panel size is identified
  (`spectralCoeff_bot_self_mul_choose_of_injective`,
  `panelSize_eq_of_survivalAt_eq_of_injective`). Whether it is nonzero at every width two or
  more is open.
* The spread of the graph coalescent's transit time: `GraphTransitVariance`. A graph entering at
  width `w` reports a smaller transit-time variance than its panel, short by exactly the phases
  between `w` and `n` (`graphVarianceDeficit_eq`), and a coarser construction loses more
  (`graphVarianceDeficit_antitone`); the lower bound `1` survives compression
  (`one_le_graphVarTransitTime`).
* The site-frequency spectrum a graph reports: `GraphSiteFrequencySpectrum`. In haplotypes,
  pairwise diversity is `θ(n² - Σ c_a²)/(n(n-1))` (`graphHaplotypeDiversity_eq`), so a graph
  biases Tajima's D numerator by exactly `θ((n² - Σ c_a²)/(n(n-1)) - a_{w-1}/a_{n-1})`
  (`graphHaplotypeTajimaNumerator_eq`), with no bias at `w = n` or `w ≤ 1`
  (`graphHaplotypeTajimaNumerator_eq_zero_of_width_eq`,
  `graphHaplotypeTajimaNumerator_eq_zero_of_width_le_one`) and a balanced-fiber bound
  (`graphHaplotypeTajimaNumerator_le_balanced`).
* Correcting the apparent coalescence clock: `HiddenClockCorrection`. The panel's time to common
  ancestry is the connection time plus a residual time on every path
  (`panelTime_eq_connectionTime_add_residualTime`); the hidden load at connection satisfies
  `E[1/B] = E τ_q / 2 + 1/n` (`inv_stoppingLevel_mean_eq`); the residual has mean
  `2 - 2/n - E τ_q` (`residualTime_mean_eq`), so the corrected clock is unbiased for the time to
  common ancestry with error the residual variance (`variance_residualTime_eq`), while the naive
  clock `2 - 2/w` overstates the connection time (`connectionTime_mean_le_two_sub`).
* Selection and hereditary closure: `SelectionClosure`. Selection size-biases the parents
  (`selectedReproduce_eq`); the closure predicting the selected next generation is the closure of
  the observation joined with fitness, the greatest autonomous partition below the observation on
  whose blocks fitness is constant (`isGreatest_selectionClosure`), and it equals the neutral
  closure exactly when fitness is constant on the neutral closure's blocks
  (`selectionClosure_eq_hereditaryClosure_iff`); under unbiased copying, fitness on a hidden
  feature breaks autonomy by hitchhiking (`selectionAutonomous_halfMix_iff`).
* What source data cannot tell you about the target: `PortabilityMinimaxLowerBound`. Two
  histories with source report laws `P`, `Q` and target values `τ_P`, `τ_Q` force every estimator
  from `n` source replicas to worst-case error at least `(|τ_P - τ_Q|/2) (1 - TV(P, Q))^n`
  (`lowerBound_cohortLaw_pow`), and at least `(|τ_P - τ_Q|/2) max {0, 1 - n TV(P, Q)}`
  (`lowerBound_cohortLaw_totalVariation`); for admixed source cohorts of NOTE1 §6 the bound is
  explicit (`sourceCohort_lowerBound`, `logTwo_sourceCohort_lowerBound`). On the NOTE2 §9 reference
  model the early and late migration histories give one source law and different targets, so half
  the target gap is the exact minimax risk for any number of source replicas
  (`PortabilityTwoHistoryInstance.isLeast_worstRisk`), with explicit floors for the target squared
  correlation and the portability ratio (`minimax_floor_r2`, `minimax_floor_r2Portability`).
  With the coupling supplied the plug-in rate `count^(-1/2)` is optimal: for the doubly-donor
  cell every estimator has risk at least `3/(32 √count)` at some donor fraction, through the
  Hellinger affinity of the replica laws; an estimator that ignores the coupling has risk at
  least `1/8` at every count (`PortabilityMinimaxRate.minimaxRate_dichotomy`,
  `exists_le_chronologyRisk`).
* What identifies target portability: `PortabilityIdentification`. In the NOTE1 §6 chronology
  model the target report law is a transport of the source law by the coupling `L_ν(1)` of the
  exposure law ν (`expectation_chronologyLaw_eq_transportExpectation`,
  `normalisedCoupling_eq_measureLaplace_one`); two histories with one source law and one exposure
  law have one target law (`chronologyMass_eq_of_source_eq_of_exposureLaw_eq`), and the plug-in
  that uses ν has error at most `2B √(3/n)` from `n` source replicas
  (`expectation_abs_plugIn_chronologyLaw_sub_le`). With the minimax bound this is an exact
  information boundary: at `M = R = log 2` source-only estimators keep worst-case error `3/8` while
  the ν-informed estimator has none (`logTwo_informationBoundary`).
* The locality transition on inhomogeneous checking graphs: `InhomogeneousLocalityTransition`.
  For independent edges dominated by a rank-one kernel with weights `w`, the expected hereditary
  closure of `A` is at most `|A| + (Σ_{r∈A} w_r)/(1 - ν)` with `ν = Σ w² / Σ w < 1`, for every
  genome size (`productExpect_card_reach_le_of_lt_one`, `productExpect_card_directedReach_le`),
  including Chung-Lu graphs (`chungLu_card_reach_le_of_lt_one`).
* Selection as ancestral decisions: `SelectionDecisions`. Selection at rate `σ` is a kernel event
  with the classical drift `p_z (s(z) - s̄(p))` (`selectionGenerator_eq_drift`); the generator
  identity of Theorem 6 holds for every kernel event, and for selection it is the ancestral
  selection graph (`kernelDriftTerm_samplingObservable`, `selectionGenerator_samplingObservable`);
  one uniqueness theorem covers every linear branching gain (`moments_eq_of_branchingEquation`),
  and the support drift under decisions and selection is at most `(3D + σ(1 + |S|)) Z`
  (`supportDrift_le`). For the support chain truncated after `M` decisions and selections, the
  expectation bounds (8.2), (8.3), (9.1) and (9.2) hold under selection with constants independent
  of `M` (`SelectionLightCone.sum_selectionChainLaw_mul_tagCount_le`,
  `sum_selectionChainLaw_escape_le_radius`). Weak selection moves the window semigroup by at most
  `2 n R t ‖f‖` at total event rate `R`
  (`SelectionSemigroupPerturbation.norm_decisionWindowSemigroup_sub_neutral_le`). When `σ`
  bounds each event's rate instead, the constant must grow with the number of events
  (`mul_card_le_of_norm_sub_neutral_le`). The portability of expected accuracies moves from
  its neutral value by at most `128 R t / δ⁴`
  (`SelectionPortabilityBound.abs_windowPortability_sub_neutral_le`).

Scope. The rate takes the sampling duality through the truncated circuit law, and agreement of the
finite models until escape, as hypotheses. The state counts compare numbers of values of the two
statistics; the exact count as a function of the fiber sizes is not yet proved. The minimax bound is
a two-point bound over finite report laws. The inhomogeneous transition covers the subcritical
side only. Selection takes fitness values in `[0, σ]`, and its Theorem 7-8 part is stated at
generator level.
-/

end Descent.Program
