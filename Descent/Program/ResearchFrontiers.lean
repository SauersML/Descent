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
import Descent.Portability.PortabilityLightCone
import Descent.Portability.EndToEndCorrelationSeries
import Descent.Pangenome.GraphCoalescent.ReportNonMarkovFromSingletons

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
  (`abs_expectedPortability_sub_le`). The metric side is explicit: the squared correlation, the
  calibration slope and the portability ratio are rational functions of five second moments, with
  explicit Lipschitz constants on the realization body
  (`PortabilityMetricCompilation.squaredCorrelation_eq_compiled`,
  `abs_compiledPortabilityRatio_sub_le`, `abs_crossRatio_sub_le`). The expected squared correlation
  itself, not only the ratio of expectations, is the series
  `Σ_k c_k ⬝ (U · H_{4(k+1)}(x₀))` (`EndToEndCorrelationSeries.expectedSquaredCorrelation_eq_tsum`,
  `expectedSquaredCorrelation_historyEventKernel`), so it too depends on the history only through
  propagated moments (`expectedSquaredCorrelation_eq_of_moments_eq`).
* Neutral portability is exactly local: `PortabilityLightCone`. No dual transition adds a locus,
  so configurations on loci within `A` are invariant (`dualTransitions_lociWithin`), and two
  neutral models that agree on the rates of `A` give the same expected moments on `A` at every time
  (`expectedMomentVector_eq_of_agreeOn`): the report of a score on `A` does not depend on the model
  outside `A` at all.
* The compressed report is not Markov from the singletons: `ReportNonMarkovFromSingletons`. For an
  interface of width `2 ≤ w < n`, no time-homogeneous transition law on reports reproduces the law
  of the report history of Kingman's jump chain from the singletons (`not_isReportMarkovFromBot`),
  while an injective interface gives a Markov report (`isReportMarkovFromBot_of_injective`); on
  three haplotypes the report stays put with probability `1/3` after one step and `0` after two
  (`example_stay_given_one`, `example_stay_given_two`).
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
  (`supportDrift_le`).

Scope. The rate takes the sampling duality through the truncated circuit law, and agreement of the
finite models until escape, as hypotheses. The state counts compare numbers of values of the two
statistics; the exact count as a function of the fiber sizes is not yet proved. The minimax bound is
a two-point bound over finite report laws. The inhomogeneous transition covers the subcritical
side only. Selection takes fitness values in `[0, σ]`, and its Theorem 7-8 part is stated at
generator level.
-/

end Descent.Program
