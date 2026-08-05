/-
Released under AGPL-3.0-or-later as described in the file LICENSE.
-/
import Descent.DeclaredInteractionClass
import Descent.ContinuumCalibration
import Descent.CorrectionWidths
import Descent.DescentGeometry
import Descent.DirichletTransfer
import Descent.ErgodicCovariancePencil
import Descent.EnsembleChannel
import Descent.FrequencySpectrumStability
import Descent.HorizonCurve
import Descent.LandscapeSuperposition
import Descent.MarkedBreakoutUniversality
import Descent.XiFromMarkedBreakouts
import Descent.MultipleMergerBlindness
import Descent.PencilEnvironment
import Descent.FunctionalDescent
import Descent.SpectralUniversalityFailure
import Descent.SpectrumIdentifiability
import Descent.TrafficInvariantSeparation

namespace Descent

open MarkedBreakout
open XiFromMarks
open TrafficInvariantSeparation
open scoped Matrix Topology

/-!
# The dynamics contrast: state, geometry, value, and observation, kept apart

This module gives the operator program a biological dictionary without conflating four
mathematically different layers.

* A finite state `x` is a population, ancestry, environment, age, or other biological
  context, and `transition x y` is its transport law.
* `Σ(x)` is observable genotype geometry.  Its generalized eigenvalues are handled by
  `Descent.ErgodicCovariancePencil`.
* `θ(x)` is context-specific biological value.  The cost of adapting a readout to it is
  handled by `Descent.DirichletTransfer`.
* A probe exposes the parameter only modulo a declared nuisance class.  Identification is
  governed by `Descent.DeclaredInteractionClass`, independently of the transport and
  pencil calculations.

The separation matters.  Averaging a target-only score after a stationary transition cannot
measure temporal portability: stationarity removes the transition exactly.  A genuinely
temporal quantity must couple source and target, for example by evaluating a source-chosen
readout at the target or by taking an autocorrelation.  The first section proves this repair
and gives a two-state witness where every target-only average agrees while cross-state
performance changes from perfect to zero.

The final theorem packages eight independent obstructions that a unified biological model
must keep visible: stationarity blindness, loss of joint dependence under marginal summaries,
rank-two value/allocation conflict even in a common eigenbasis, failure of freeness for
operators sharing a local genomic geometry, and four failures of *descent* — of a criterion to
be a function of the label it is reported against.  The descent layer comes from
`Descent.DescentGeometry`: a cross-state criterion is not a function of the target context,
reportability along each margin does not compose to the pair, dropping a stratum destroys
reportability both finer labels have, and — although every functional descends along posterior
ancestry — the ancestry-weighted average of component values is not the descended report.

## Epistemic boundary

This file does not promote the analytic claims in the motivating program to Lean theorems.
In particular, Donsker--Varadhan regularity, infinite-volume density of states, a Thouless
formula, Minami/Poisson statistics, and hard-edge random-operator limits require hypotheses
and proofs absent from this corpus.  The formal content here is finite and exact; those
claims remain research interfaces rather than axioms disguised as results.  For the genuine
hard-selection `N`-BRW, the selected derivative-martingale flux law, reproductive-value pruning
estimate, and uniform two-colour common-profile relaxation are likewise not asserted.  The
theorems below isolate what each would imply and keep the three inputs distinct.
-/

open scoped BigOperators

/-! ## Cohort landscape superposition

Independent cohort objectives add as landscapes, while their covariance kernels add with
squared row weights.  The exact level-resolved calculus therefore gives only a persistence
theorem: a common forbidden overlap at every admissible pair of cohort levels remains
forbidden after pooling.  It does not prove dissolution.  The explicit spherical calculation
below records the complementary biological mechanism: genetic structure shared by cohorts
survives mixing, whereas cohort-specific higher-order structure is diluted.
-/

section CohortLandscapeSuperposition

variable {Cohort Genotype Overlap : Type*}

/-- A level-resolved forbidden overlap in at least one cohort remains forbidden for the pooled
cohort objective.  In biological language, pooling cannot create a pair of high-fitness
genotypes unless every cohort admits that overlap at the component levels realized by the
pair. -/
theorem pooledCohort_forbiddenOverlap_of_levelResolved_cover
    (active : Finset Cohort) (weight : Cohort → ℝ) (fitness : Cohort → Genotype → ℝ)
    (overlap : Genotype → Genotype → Overlap) (target : ℝ)
    (hweight : ∀ cohort ∈ active, 0 ≤ weight cohort) (q : Overlap)
    (hcover : ∀ leftLevel rightLevel,
      AdmissibleLevels active weight target leftLevel →
        AdmissibleLevels active weight target rightLevel →
          ∃ cohort ∈ active,
            q ∉ ComponentAchievableOverlaps fitness overlap leftLevel rightLevel cohort) :
    q ∉ SuperposedAchievableOverlaps active weight fitness overlap target :=
  forbiddenOverlap_of_levelResolved_cover active weight fitness overlap target hweight q hcover

end CohortLandscapeSuperposition

/-! ## Population overlap geometry under ancestry-environment mixing -/

/-- The active sparse-LD correlation after pooling two environments with correlations `rho`
and `-rho`.  This is the biological name for the landscape parameter itself.

    Empirical status: UNTESTED. The pooling formula is arithmetic on the two
    environment correlations; what is untested is the modelling step before it, that an
    ancestry-environment mixture is described by two correlations of equal size and
    opposite sign. No dataset here bears on that. -/
noncomputable def ancestryMixtureCorrelation (rho positiveEnvironmentMass : ℝ) : ℝ :=
  mixedEnvironmentCorrelation rho positiveEnvironmentMass

/-- A balanced ancestry-environment mixture cancels the active correlation exactly. -/
@[simp] theorem ancestryMixtureCorrelation_balanced (rho : ℝ) :
    ancestryMixtureCorrelation rho (1 / 2) = 0 := by
  exact mixedEnvironmentCorrelation_half rho

/-- **Two individually gapped LD environments can pool to an ungapped population profile.**

At active correlation `4/5`, both signs lie beyond the golden threshold and have a negative
population gap certificate.  Equal environment mass cancels the active correlation, leaving
certificate one.  This is a population-landscape statement only: it does not infer a
polynomial-time algorithm from absence of the gap. -/
theorem ancestryMixture_pure_gapped_balanced_ungapped :
    populationGapCertificate (4 / 5) < 0 ∧
      populationGapCertificate (-(4 / 5)) < 0 ∧
      populationGapCertificate (ancestryMixtureCorrelation (4 / 5) (1 / 2)) = 1 := by
  have hthreshold : goldenCorrelationThreshold < (4 / 5 : ℝ) := by
    have hgold := goldenCorrelationThreshold_sq_add_self
    have hpositive := goldenCorrelationThreshold_mem_Ioo.1
    nlinarith
  have habsPositive : |(4 / 5 : ℝ)| = 4 / 5 := by norm_num
  have habsNegative : |(-(4 / 5) : ℝ)| = 4 / 5 := by norm_num
  have hpositive := populationGapCertificate_neg_of_golden_lt_abs
    (4 / 5) (by norm_num) (by rw [habsPositive]; exact hthreshold)
  have hnegative := populationGapCertificate_neg_of_golden_lt_abs
    (-(4 / 5)) (by norm_num) (by rw [habsNegative]; exact hthreshold)
  refine ⟨hpositive, hnegative, ?_⟩
  simp [ancestryMixtureCorrelation, mixedEnvironmentCorrelation, populationGapCertificate]

/-- **Scope of the explicit diversity mechanism.**  If the two ancestry environments carry
the same active LD correlation, pooling leaves that correlation unchanged at every mixture
weight.  The proven gap-closing construction therefore uses opposite-sign LD, not diversity
alone. -/
theorem sameSignAncestryPooling_preservesActiveCorrelation (rho mix : ℝ) :
    pooledEnvironmentCorrelation rho rho mix = rho :=
  pooledEnvironmentCorrelation_same rho mix

/-! ## Demographic resolution budget from the frequency spectrum -/

/-- **Exact fixed-epoch design budget.**  The first conjunct is the spectrum-precision
multiplier needed to halve reconstruction error; the second is the independent-genomic-data
multiplier under root-sample spectrum error.  These are algebraic consequences of the sharp
`1 / (2K - 3)` inverse exponent. -/
theorem fixedEpochDemography_halving_budget :
    (spectrumPrecisionMultiplier 2 2 = 2 ∧
      spectrumPrecisionMultiplier 3 2 = 8 ∧
      spectrumPrecisionMultiplier 4 2 = 32 ∧
      spectrumPrecisionMultiplier 5 2 = 128) ∧
    (independentSampleMultiplier 2 2 = 4 ∧
      independentSampleMultiplier 3 2 = 64 ∧
      independentSampleMultiplier 4 2 = 1024 ∧
      independentSampleMultiplier 5 2 = 16384) :=
  ⟨spectrumPrecisionMultiplier_halving_table,
    independentSampleMultiplier_halving_table⟩

/-- A five-epoch demographic sieve inherits the slow `sampleSize⁻¹ᐟ¹⁴` stability rate. -/
theorem fiveEpochDemography_sampleRateExponent :
    fixedEpochSampleRateExponent 5 = 1 / 14 :=
  fixedEpochSampleRateExponent_five

/-- **Kingman SFS identifiability boundary.**  The complete quadratic rate ladder has a
summable reciprocal, while every finite observation map has a nonzero direction on a sieve
with one additional coefficient.  The first fact is the Müntz obstruction's spectral input;
the second says finite-sample analyticity alone cannot restore identification. -/
theorem kingmanSpectrum_identifiabilityBoundary :
    Summable (fun k : ℕ ↦
      1 / SpectrumIdentifiability.coalescentRate (k + 2)) ∧
      ∀ n : ℕ, ∀ observation : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ),
        ∃ direction : Fin (n + 1) → ℝ,
          direction ≠ 0 ∧ observation direction = 0 :=
  ⟨SpectrumIdentifiability.summable_one_div_coalescentRate,
    fun _ observation ↦ SpectrumIdentifiability.exists_invisible_perturbation observation⟩

/-- **The usable positive boundary for demographic inference.** A linear demographic target
is determined by the SFS on an admissible history class exactly when every admissible history
difference invisible to the SFS is also invisible to that target. Thus failure to identify the
entire history does not automatically invalidate every demographic summary. -/
theorem demographicTarget_identifiable_iff_nullDirections_annihilated
    {V W Z : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z]
    (spectrumObservation : V →ₗ[ℝ] W) (target : V →ₗ[ℝ] Z)
    (historyClass : Set V) :
    TargetIdentifiableUnderLinearObservation spectrumObservation target historyClass ↔
      modelDifferenceSet historyClass ∩ LinearMap.ker spectrumObservation ⊆
        LinearMap.ker target :=
  targetIdentifiableUnderLinearObservation_iff_differenceSet_inter_kernel_subset_ker
    spectrumObservation target historyClass

/-- At the stationary Cauchy root, the per-dimension inverse-conditioning base is the exact
ratio `(1 + θ²) / (1 - θ²)`. -/
theorem demographicSieveConditioning_exactBase
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hstationary : SpectrumIdentifiability.CauchyConditioningStationary θ) :
    Real.exp (SpectrumIdentifiability.cauchyConditioningProfile θ / 2) =
      (1 + θ ^ 2) / (1 - θ ^ 2) :=
  SpectrumIdentifiability.exp_half_cauchyConditioningProfile_at_stationary
    θ hθ0 hθ1 hstationary

/-! ## Multiple-merger genealogy: pairwise blindness -/

/-- **Pairwise diversity cannot identify a normalized multiple-merger regime.**  Every
probability-normalized merger law has pair-merger rate one, whereas the three-lineage rate is
its first merger-fraction moment.  The displayed point-mass pair is the smallest exact
witness: identical at two lineages and separated at three. -/
theorem pairwiseGenealogy_blind_threeLineage_visible :
    lambdaCoalescentMergerRate (MeasureTheory.Measure.dirac 0) 2 2 =
        lambdaCoalescentMergerRate (MeasureTheory.Measure.dirac 1) 2 2 ∧
      lambdaCoalescentMergerRate (MeasureTheory.Measure.dirac 0) 3 3 = 0 ∧
      lambdaCoalescentMergerRate (MeasureTheory.Measure.dirac 1) 3 3 = 1 :=
  pairwise_blind_three_lineage_separates_dirac

/-- **Speed-conditioned genealogy is identified at three lineages, not two.**  In the
normalized `Beta(1, β + 1)` chart the pair rate is identically one, while the inverse of the
three-lineage rate recovers `β` exactly.  This is the finite observable consequence of the
regular-variation speed-tilt theorem. -/
theorem speedConditionedGenealogy_pairBlind_tripleRecovers (β : ℝ) :
    speedTiltBetaMergerRate β 2 2 = 1 ∧
      speedBiasParameterFromTripleRate (speedTiltBetaMergerRate β 3 3) = β :=
  ⟨speedTiltBetaMergerRate_two_two β,
    speedBiasParameterFromTripleRate_recovers β⟩

/-- **Why the regular-variation genealogy has no simultaneous disjoint mergers.**  At tail
scale `d`, a two-family pair-pair collision is smaller than a one-family pair collision by the
explicit factor `d (β + 1) / ((β + 2) (β + 3))`.  The factor is one order smaller in the
rare-family scale, not merely bounded by an unspecified error. -/
theorem speedConditionedGenealogy_twoFamilyToPairRatio
    {β d : ℝ} (hβ : -1 < β) (hd : d ≠ 0) :
    speedTiltTwoFamilyCollisionScale β d / speedTiltPairCollisionScale β d =
      d * (β + 1) / ((β + 2) * (β + 3)) :=
  speedTiltTwoFamilyCollisionScale_div_pair hβ hd

/-- Along every vanishing regular-variation tail scale, simultaneous two-family collisions
disappear on the pair-collision clock.  This is the biology-facing separation between the
single-event `Λ` limit here and the mass-partition `Ξ` limit needed for genuinely simultaneous
families. -/
theorem speedConditionedGenealogy_simultaneousMergersVanish
    {ι : Type*} {l : Filter ι} (β : ℝ) {tailScale : ι → ℝ}
    (hscale : Filter.Tendsto tailScale l (nhds 0)) :
    Filter.Tendsto
      (fun index ↦ tailScale index * (β + 1) / ((β + 2) * (β + 3)))
      l (nhds 0) :=
  tendsto_speedTiltTwoFamilyToPairRatio_comp β hscale

/-- **The biology core consumes the marked successful-family measure itself.**  At zero tilt its
weighted pushforward is exactly the unconditioned genealogy measure, and for every merger size
the Bernoulli family-participation rate is the corresponding `Λ`-rate.  This is the formal
replacement for treating a coalescent measure alone as the universal branching-front object. -/
theorem markedSuccessfulFamilyMeasure_determinesGenealogy
    (ν : MeasureTheory.Measure SuccessfulFamilyMark)
    (b k : ℕ) (hk : 2 ≤ k) :
    speedTiltedGenealogyMeasure 0 ν = genealogyMeasure ν ∧
      markedEventMergerRate ν b k = markedLambdaMergerRate ν b k :=
  ⟨speedTiltedGenealogyMeasure_zero ν,
    markedEventMergerRate_eq_lambda ν b k hk⟩

/-- The marked second-moment condition is exactly the finite-rate condition consumed by the
biology core: it makes the weighted genealogy projection a finite measure. -/
theorem markedSuccessfulFamilyMeasure_finiteGenealogy_of_finiteIntensity
    {ν : MeasureTheory.Measure SuccessfulFamilyMark}
    (hν : HasFiniteGenealogicalIntensity ν) :
    genealogyMeasure ν Set.univ < ⊤ :=
  genealogyMeasure_finite_of_secondMoment hν

/-- **The speed-conditioned genealogy retains the response mark.**  This measurable-set formula
is the biology-facing version of `Λθ(dx) = x² ∫ exp(-θr) ν(dx,dr)`: it exposes the full marked
intensity rather than silently replacing it by its unconditioned fraction marginal. -/
theorem speedConditionedGenealogy_markedMeasure_formula
    (theta : ℝ) (ν : MeasureTheory.Measure SuccessfulFamilyMark)
    {s : Set ℝ} (hs : MeasurableSet s) :
    speedTiltedGenealogyMeasure theta ν s =
      ∫⁻ mark in familyFraction ⁻¹' s,
        ENNReal.ofReal
          (familyFraction mark ^ 2 *
            Real.exp (-(theta * frontDisplacement mark))) ∂ν :=
  speedTiltedGenealogyMeasure_apply theta ν hs

/-- **But the speed-conditioned chart is not universal.**  The `Beta` interpolation is an
invariant of the front-displacement law, not a consequence of the unconditioned genealogy.  A
marked breakout measure whose displacement is linear in the family fraction has exactly the
same unconditioned Bolthausen--Sznitman limit and a different conditioned three-lineage rate,
so no deterministic time change relates the two charts.

The biological reading is a constraint on inference: fitting the `Beta` chart to
three-lineage data identifies the tilt parameter only if the displacement law is the
logarithmic one.  The chart is a model assumption about front response, not a fact about
multiple-merger genealogies. -/
theorem speedConditionedGenealogy_chart_not_universal :
    MarkedBreakout.linearDisplacementTripleRate 1 ≠ speedTiltBetaMergerRate 1 3 3 :=
  MarkedBreakout.tripleRate_separates_at_unit_tilt

/-- **And what the chart does rest on, exactly.**  The logarithmic displacement law is what
makes the tilt factor a power of the surviving fraction, and additive displacement noise
independent of the family fraction is absorbed by normalization.  These two identities are the
forward calculation; the following theorem supplies the exact transform-level converse. -/
theorem speedConditionedGenealogy_chart_invariant
    (gamma theta x noise : ℝ) (hgamma : gamma ≠ 0) (hx : x < 1) :
    Real.exp (-(theta * MarkedBreakout.logDisplacement gamma x))
        = (1 - x) ^ (theta / gamma) ∧
      Real.exp (-(theta * (MarkedBreakout.logDisplacement gamma x + noise)))
        = (1 - x) ^ (theta / gamma) * Real.exp (-(theta * noise)) :=
  ⟨MarkedBreakout.logDisplacement_laplace_factors gamma theta x hgamma hx,
    MarkedBreakout.displacementNoise_factors gamma theta x noise hgamma hx⟩

/-! ## Sweep multiplicity: what allele-frequency data cannot decide -/

/-- **A hard sweep and a soft sweep with the same frequency trajectory leave different
genealogies.**

A beneficial allele reaching frequency `x` from a single origin, and the same allele reaching
`x` from two independent origins carrying `x/2` each, have identical allele-frequency
trajectories: same times, same increments, same endpoint.  No frequency statistic separates
them, at any sample size or sequencing depth, because there is nothing to separate.

Their genealogies differ twice over.  The soft sweep coalesces a sampled pair at half the rate,
so it leaves twice the diversity for the same frequency change -- which is why a diversity
level read against a frequency trajectory does not measure selection strength unless
multiplicity is already known.  And four sampled lineages can fall two-and-two into distinct
origin classes under the soft sweep, an event the hard sweep cannot produce at all.

The second fact is the usable one: it is a difference in the SHAPE of the genealogy, not its
rate, so no rescaling of time or effective size reproduces it. -/
theorem sweepTrajectory_does_not_determine_genealogy (finalFrequency : ℝ)
    (hpolymorphic : finalFrequency ≠ 0) :
    XiFromMarks.paintboxWeight ![finalFrequency]
        ≠ XiFromMarks.paintboxWeight ![finalFrequency / 2, finalFrequency / 2] ∧
      XiFromMarks.disjointPairMergeProbability ![finalFrequency] = 0 ∧
      0 < XiFromMarks.disjointPairMergeProbability
        ![finalFrequency / 2, finalFrequency / 2] :=
  XiFromMarks.front_does_not_determine_genealogy finalFrequency hpolymorphic

/-- **The sample-size ladder for reading a selected genealogy.**

Two lineages see nothing: every normalized merger law has pairwise rate one, so heterozygosity
and mean pairwise coalescence time are blind to the regime.  Three lineages see the merger rate
and recover the tilt parameter exactly.  Four lineages are the first that can see how many
origins a sweep had, because two-and-two assignment into distinct origin classes is the
event that distinguishes multiplicity.

Read as a design constraint: a study powered on pairwise diversity cannot detect a selection
regime however large it is, and a study using three-lineage statistics can measure the rate but
still cannot tell one origin from several. -/
theorem selectedGenealogy_sampleSize_ladder (β finalFrequency : ℝ)
    (hpolymorphic : finalFrequency ≠ 0) :
    speedTiltBetaMergerRate β 2 2 = 1 ∧
      speedBiasParameterFromTripleRate (speedTiltBetaMergerRate β 3 3) = β ∧
      XiFromMarks.disjointPairMergeProbability ![finalFrequency] = 0 ∧
      0 < XiFromMarks.disjointPairMergeProbability
        ![finalFrequency / 2, finalFrequency / 2] :=
  ⟨speedTiltBetaMergerRate_two_two β,
    speedBiasParameterFromTripleRate_recovers β,
    XiFromMarks.disjointPairMerge_single_zero finalFrequency,
    (XiFromMarks.front_does_not_determine_genealogy finalFrequency hpolymorphic).2.2⟩

/-- **The sweep-origin count a frequency trajectory would have to supply, and cannot.**

The pioneer change of variables turns a reproductive-weight tail into the population-fraction
intensity and the frequency response into the logarithmic displacement law, so the whole
reduction rests on those two maps and nothing else.  Recording it here is what makes the
previous theorem a statement about a mechanism rather than about two arbitrary partitions. -/
theorem sweepResponse_is_logarithmic (gamma reproductiveWeight : ℝ)
    (hweight : 0 < reproductiveWeight) :
    XiFromMarks.pioneerWeightDisplacement gamma reproductiveWeight
      = MarkedBreakout.logDisplacement gamma
        (XiFromMarks.pioneerWeightFraction reproductiveWeight) :=
  XiFromMarks.pioneerDisplacement_eq_logDisplacement gamma reproductiveWeight hweight

/-- **The biology core consumes the complete mass-partition mark.**  Collision integrability
simultaneously makes every fixed-sample event rate finite and makes zero speed tilt recover the
unconditioned `Ξ` measure.  Thus the successful-event object is not merely an allele-frequency
measure with an informal multiplicity annotation: the mass partition is part of its type. -/
theorem markedMassPartitionMeasure_determinesXi
    (n : ℕ) (ν : MeasureTheory.Measure MarkedMassPartition)
    (hν : HasFiniteCollisionIntensity ν) :
    speedTiltedXiMeasure 0 ν = xiMeasure ν ∧
      samplePartitionChangeRateBound n ν < ⊤ :=
  ⟨speedTiltedXiMeasure_zero ν,
    samplePartitionChangeRateBound_lt_top_of_finiteCollision n hν⟩

/-- **The two-colour response is an exact algebraic interface.**  Rank-one relaxation converts
the pioneer amplitude into its descendant fraction, while the associated logarithmic
translation restores the pre-breakout amplitude.  Applying this interface to hard selection
still requires the unavailable uniform two-colour concentration estimate. -/
theorem twoColourPioneerResponse_exact
    (conversion gamma reproductiveWeight : ℝ)
    (hconversion : conversion ≠ 0) (hgamma : gamma ≠ 0)
    (hweight : -1 < reproductiveWeight) :
    conversion * reproductiveWeight /
        (conversion * 1 + conversion * reproductiveWeight) =
          pioneerWeightFraction reproductiveWeight ∧
      Real.exp (-(gamma * pioneerWeightDisplacement gamma reproductiveWeight)) *
          (1 + reproductiveWeight) = 1 := by
  refine ⟨spectralResponse_pioneerFraction conversion reproductiveWeight hconversion ?_,
    spectralResponse_shift_restoresAmplitude gamma reproductiveWeight hgamma hweight⟩
  linarith

/-- **The light-tailed BRW boundary transform is an algebraic identity.**  The critical
log-mgf equation normalizes additive mass, while choosing speed equal to the log-mgf derivative
centers the derivative mass.  What remains model-specific is passage through rightmost-`N`
selection, not this transformation. -/
theorem branchingRandomWalkBoundaryTransform_isCritical
    (logMgf logMgfDerivative criticalParameter criticalSpeed : ℝ)
    (hboundary : criticalParameter * criticalSpeed - logMgf = Real.log 2)
    (hspeed : criticalSpeed = logMgfDerivative) :
    boundaryTiltMass logMgf criticalParameter criticalSpeed = 1 ∧
      boundaryTiltCenteredFirstMoment
        logMgf logMgfDerivative criticalParameter criticalSpeed = 0 :=
  ⟨boundaryTiltMass_eq_one logMgf criticalParameter criticalSpeed hboundary,
    boundaryTiltCenteredFirstMoment_eq_zero
      logMgf logMgfDerivative criticalParameter criticalSpeed hspeed⟩

/-- **Selected derivative flux supplies the breakout tail and makes double breakouts
quadratic.**  This is the finite-block kernel of weighted heavy-tail Poissonization.  The
derivative-martingale theorem supplies the Pareto tail constant; the unresolved hard-selection
input is the selected reproductive-value flux `blockScale · fluxConstant`. -/
theorem selectedDerivativeFlux_controlsBreakouts
    {Pioneer : Type*} [Fintype Pioneer] [DecidableEq Pioneer]
    (tailConstant threshold blockScale fluxConstant : ℝ)
    (weight : Pioneer → ℝ)
    (htail : 0 ≤ tailConstant) (hthreshold : 0 < threshold)
    (hweight : ∀ pioneer, 0 ≤ weight pioneer)
    (hflux : selectedPioneerFlux weight = blockScale * fluxConstant) :
    (∑ pioneer,
        paretoExceedanceMass tailConstant threshold (weight pioneer)) =
        blockScale * (tailConstant * fluxConstant / threshold) ∧
      distinctPairExceedanceMass
          (fun pioneer ↦ paretoExceedanceMass
            tailConstant threshold (weight pioneer)) ≤
        (blockScale * (tailConstant * fluxConstant / threshold)) ^ 2 := by
  constructor
  · rw [weightedParetoExceedanceMass_eq_flux, hflux]
    ring
  · exact distinctPairParetoExceedanceMass_le_blockScale_sq
      tailConstant threshold blockScale fluxConstant weight
      htail hthreshold hweight hflux

/-- **Potential-pioneer survival is precisely the pruning gap.**  An exogenous full-tree flux
law transfers to the selected system once the reproductive-value flux removed by intermediate
rightmost-`N` pruning vanishes on the same scale.

Assumes: `IsSelectedFluxDecomposition fullTreeFlux selectedFlux prunedFlux`. -/
theorem selectedPioneerFlux_follows_from_fullTreeFlux_and_negligiblePruning
    (fullTreeFlux selectedFlux prunedFlux : ℕ → ℝ) (fluxConstant : ℝ)
    (hdecomposition :
      IsSelectedFluxDecomposition fullTreeFlux selectedFlux prunedFlux)
    (hfull : Filter.Tendsto fullTreeFlux Filter.atTop (nhds fluxConstant))
    (hpruned : Filter.Tendsto prunedFlux Filter.atTop (nhds 0)) :
    Filter.Tendsto selectedFlux Filter.atTop (nhds fluxConstant) :=
  selectedFlux_tendsto_of_exogenous_of_pruned
    fullTreeFlux selectedFlux prunedFlux fluxConstant hdecomposition hfull hpruned

/-- **One pioneer gives one atom, but its sample fraction still needs common-profile
relaxation.**  The first conjunct is pathwise ancestry bookkeeping.  The second consumes the
separate two-colour profile hypothesis, and the third uses the real-valued amplitude front.

Assumes: `HasCommonProfileRelaxation conversion 1 w backgroundCount pioneerCount`. -/
theorem uniquePioneer_commonProfile_markedResponse
    (conversion gamma w backgroundCount pioneerCount : ℝ)
    (hconversion : conversion ≠ 0)
    (hcount : backgroundCount + pioneerCount ≠ 0)
    (hprofile : HasCommonProfileRelaxation conversion 1 w
      backgroundCount pioneerCount) :
    (totalFamilyFraction ![pioneerWeightFraction w] = pioneerWeightFraction w ∧
      paintboxWeight ![pioneerWeightFraction w] = pioneerWeightFraction w ^ 2 ∧
        disjointPairMergeProbability ![pioneerWeightFraction w] = 0) ∧
      pioneerCount / (backgroundCount + pioneerCount) = pioneerWeightFraction w ∧
        amplitudeFront gamma (1 + w) - amplitudeFront gamma 1 =
          pioneerWeightDisplacement gamma w :=
  ⟨oneSuccessfulAncestor_produces_onePaintboxAtom (pioneerWeightFraction w),
    pioneerCountFraction_eq_of_commonProfile
      conversion w backgroundCount pioneerCount hconversion hcount hprofile,
    amplitudeFront_pioneerShift gamma w⟩

/-- **The reciprocal-rate inversion is localized at the pulled boundary.**  Linear pulled
clocks have divergent reciprocals; every stable exponent above one, including the quadratic
Kingman order, has summable reciprocals.  This removes one Müntz obstruction only after the
demographic observation operator is proved to use this exponential rate ladder. -/
theorem selectedGenealogy_muntzRateDichotomy
    (coefficient alpha : ℝ) (hcoefficient : 0 < coefficient) (halpha : 1 < alpha) :
    (¬Summable fun n : ℕ ↦
        1 / criticallyPulledLinearRateLadder coefficient n) ∧
      Summable (fun n : ℕ ↦ 1 / stablePowerRateLadder alpha n) ∧
        Summable (fun n : ℕ ↦ 1 / stablePowerRateLadder 2 n) :=
  ⟨not_summable_one_div_criticallyPulledLinearRateLadder coefficient hcoefficient,
    summable_one_div_stablePowerRateLadder alpha halpha,
    summable_one_div_quadraticRateLadder⟩

/-! ## Traffic depth, mesoscopic LD structure, and iterative genomic procedures -/

/-- **The complete genomic procedure-risk signature is the canonical coarsest
sufficient design invariant.**  It reconstructs every model/loss risk directly,
while equality under any other sufficient invariant forces equality of the
complete signature.  Uniformity is encoded by the single reconstruction map
shared across all designs. -/
theorem genomicAlgorithmicRiskSignature_isCoarsestSufficientInvariant
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) :
    RiskSignaturesFactorThrough risk (algorithmicRiskSignature risk) ∧
      ∀ (Invariant : Type*) (invariant : Design → Invariant),
        RiskSignaturesFactorThrough risk invariant →
          ∀ left right, invariant left = invariant right →
            algorithmicRiskSignature risk left =
              algorithmicRiskSignature risk right :=
  algorithmicRiskSignature_isCoarsestSufficientInvariant risk

/-- **Contracted genomic traffic graphs supply their own rank-one decay
bound.**  Positive even degrees and the handshaking identity imply `|V| ≤ |E|`
for every all-even contracted term, hence the complete finite spike correction
vanishes without assuming either the cardinal or minimum-degree inequality. -/
theorem genomicRankOneTrafficCorrection_vanishes_of_positiveEvenDegreeData
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (degree : ∀ term, Fin (vertices term) → ℕ)
    (hpositive : ∀ term, hasOddDegree term = false →
      ∀ vertex, 0 < degree term vertex)
    (heven : ∀ term, hasOddDegree term = false →
      ∀ vertex, Even (degree term vertex))
    (hhandshake : ∀ term, hasOddDegree term = false →
      ∑ vertex, degree term vertex = 2 * edges term) :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0) :=
  finiteRankOneTrafficCorrection_tendsto_zero_of_positiveEvenDegreeData
    coefficient hasOddDegree vertices edges degree hpositive heven hhandshake

/-- **One concrete genomic LD covariance carries the whole counterexample.**
The bundled witness certifies PSD order, fixed-traffic invisibility, the exact
finite Rademacher Hamiltonian, an unchanged lower ground state, thermodynamic
convergence, and strict supercritical pressure for the same matrices. -/
theorem positiveLDBalancedRankOneCovariance_fullWitness
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (baseline spikeStrength temperature : ℝ)
    (hbaseline : 0 ≤ baseline) (hspike : 0 < spikeStrength)
    (hcritical : 1 < temperature * spikeStrength) :
    ConcreteBalancedPSDPressureWitness coefficient hasOddDegree vertices edges
      baseline spikeStrength temperature :=
  concreteBalancedPSDPressureWitness coefficient hasOddDegree vertices edges
    hconnected baseline spikeStrength temperature hbaseline hspike hcritical

/-- **A rare LD subspace is invisible to every fixed traffic coordinate but survives a
logarithmic number of power iterations.**  The exceptional fraction is `4⁻ᵏ`; each fixed graph
sum loses it, while `k` iterations amplify its squared output by `4ᵏ`. -/
theorem rareLDSubspace_fixedTrafficInvisible_logRuntimeVisible :
    FixedTrafficLogRuntimeSeparation :=
  fixedTraffic_invisible_logRuntime_visible

/-- **Fixed polynomial degree is not a limiting-traffic guarantee.**  The
degree-one normalized LD trace discrepancy vanishes, but multiplying it by
the natural mesoscopic resolution `p_k / r_k = 4^k` keeps a separation of two
at every dimension. -/
theorem rareLDSubspace_limitingTrafficInsufficientForDegreeOne
    (baseline : ℝ) :
    Filter.Tendsto
        (fun iteration ↦ diagonalTrafficCorrection baseline 1 iteration)
        Filter.atTop (nhds 0) ∧
      ∀ iteration,
        amplifiedDegreeOneTrafficDifference baseline iteration = 2 :=
  limitingTraffic_insufficient_for_unstableDegreeOne baseline

/-- **Bulk LD spectrum does not determine extremal spectral or SDP behavior.**
A single positive LD outlier vanishes from every normalized spectral test
average, while changing both the exact spectral maximum and the full
trace-one positive-semidefinite SDP optimum by its complete strength. -/
theorem genomicBulkSpectralLaw_invisible_extremalSpectrumAndSDP_visible
    (baseline spikeStrength : ℝ) (hspike : 0 < spikeStrength) :
    BulkSpectralLawExtremalSDPSeparation baseline spikeStrength :=
  bulkSpectralLaw_invisible_extremalSpectrumAndSDP_visible
    baseline spikeStrength hspike

/-- **A positive LD rank-one perturbation is invisible to every fixed genomic
traffic graph after the finite spike expansion, yet has strictly positive
variational pressure above the exact Curie--Weiss threshold.**  The contracted
graph condition is the finite combinatorial input; no finite-volume LDP is
smuggled into the statement. -/
theorem positiveLDSpike_fixedTrafficInvisible_variationalPressureVisible
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (tlam : ℝ) (hcritical : 1 < tlam) :
    Filter.Tendsto
        (fun population : ℕ ↦
          finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
            (population + 1))
        Filter.atTop (nhds 0) ∧
      0 < cwVariationalPressureGap tlam :=
  finiteRankOneTraffic_invisible_variationalPressure_visible
    coefficient hasOddDegree vertices edges hconnected tlam hcritical

/-- **Actual finite-volume genomic pressure counterexample throughout the
full supercritical regime.**  Every fixed LD traffic correction vanishes, but
for every `tλ > 1` the exact binomially grouped Rademacher pressure has a
positive population-uniform lower bound and converges to the strictly positive
variational pressure.  Its companion theorem below proves the exact
subcritical convergence boundary; no LDP is used. -/
theorem positiveLDSpike_fixedTrafficInvisible_finitePressureVisible
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (tlam : ℝ) (hcritical : 1 < tlam) :
    RankOneSpikeInvisibleWithFinitePressure coefficient hasOddDegree vertices edges tlam :=
  finiteRankOneTraffic_invisible_finitePressure_visible
    coefficient hasOddDegree vertices edges hconnected tlam hcritical

/-- **Finite genomic Gibbs lower bound.**  At every nonempty population, each
interior LD magnetisation objective lower-bounds the genuine Rademacher
pressure.  This is the exact finite change-of-measure theorem behind the sharp
counterexample. -/
theorem genomicFiniteCWPressure_dominatesVariationalObjective
    (population : ℕ) (tlam m : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) (hm : |m| < 1) :
    cwObjective tlam m ≤ finiteCWPressureGap population tlam :=
  finiteCWPressureGap_ge_cwObjective
    population tlam m hpopulation htlam hm

/-- Every admissible genomic magnetisation class has normalized Gibbs mass
at most one at and below the Curie--Weiss threshold.  This is the finite
typewise estimate that controls the full partition function without an LDP. -/
theorem genomicFiniteCWTypeMass_le_one_of_subcritical
    (population upSpins : ℕ) (tlam : ℝ) (hcritical : tlam ≤ 1)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    finiteCWTypeMass population tlam upSpins ≤ 1 :=
  finiteCWTypeMass_le_one_of_subcritical population upSpins tlam
    hcritical hupSpins

/-- **Exact finite genomic pressure phase boundary.**  For nonnegative LD
coupling, the genuine normalized finite-population Rademacher pressure tends
to its unspiked value exactly when `tλ ≤ 1`; throughout `tλ > 1` a uniform
interior genotype-frequency witness prevents convergence to zero. -/
theorem genomicFiniteCWPressure_exactCriticalPoint
    (tlam : ℝ) (htlam : 0 ≤ tlam) :
    Filter.Tendsto
        (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
        Filter.atTop (nhds 0) ↔
      tlam ≤ 1 :=
  finiteCWPressureGap_tendsto_zero_iff tlam htlam

/-- The genuine finite genomic Curie--Weiss pressure converges to the complete
variational LD pressure for every nonnegative coupling, with no asymptotic
principle assumed beyond the proved finite type-count squeeze. -/
theorem genomicFiniteCWPressure_convergesToVariational
    (tlam : ℝ) (htlam : 0 ≤ tlam) :
    Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds (cwVariationalPressureGap tlam)) :=
  finiteCWPressureGap_tendsto_variationalPressure tlam htlam

/-- Finite genomic Curie--Weiss pressure converges uniformly to its
variational LD pressure over the entire nonnegative coupling half-line. -/
theorem genomicFiniteCWPressure_convergesUniformlyOnNonnegative :
    TendstoUniformlyOn
      (fun population : ℕ ↦ fun tlam : ℝ ↦
        finiteCWPressureGap (population + 1) tlam)
      cwVariationalPressureGap Filter.atTop (Set.Ici 0) :=
  finiteCWPressureGap_tendstoUniformlyOn_nonnegative

/-- Every positive finite genomic population already has the same sharp
half-Lipschitz pressure stability as the thermodynamic limit. -/
theorem genomicFiniteCWPressure_isHalfLipschitz
    (population : ℕ) (hpopulation : 0 < population) :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal)
      (finiteCWPressureGap population) :=
  finiteCWPressureGap_lipschitzWith population hpopulation

/-- Every positive finite genomic population has pressure monotone in
effective LD coupling. -/
theorem genomicFiniteCWPressure_isMonotone
    (population : ℕ) (hpopulation : 0 < population) :
    Monotone (finiteCWPressureGap population) :=
  monotone_finiteCWPressureGap population hpopulation

/-- The same finite-volume statement in direct pressure language: the
rank-one LD-spiked genomic pressure is strictly larger than the unspiked
baseline at every nonempty population throughout `tλ > 1`. -/
theorem positiveLDSpike_finitePressureExceedsBaseline
    (baseline : ℝ) (population : ℕ)
    (temperature spikeStrength : ℝ) (hpopulation : 0 < population)
    (hcritical : 1 < temperature * spikeStrength) :
    finiteBaselineRademacherPressure baseline temperature <
      finiteRankOneRademacherPressure
        baseline population temperature spikeStrength :=
  finiteRankOneRademacherPressure_gt_baseline
    baseline population temperature spikeStrength hpopulation hcritical

/-- The direct spiked-minus-baseline genomic pressure converges to zero
exactly when the nonnegative effective LD coupling is at most one. -/
theorem positiveLDSpike_pressureDifference_exactCriticalPoint
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    FiniteRankOnePressureCriticalStatement baseline temperature spikeStrength :=
  finiteRankOneRademacherPressure_difference_tendsto_zero_iff
    baseline temperature spikeStrength hcoupling

/-- The full finite LD-spiked genomic pressure converges to baseline plus the
exact Curie--Weiss variational pressure. -/
theorem positiveLDSpike_pressure_convergesToVariational
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    FiniteRankOnePressureVariationalLimitStatement
      baseline temperature spikeStrength :=
  finiteRankOneRademacherPressure_tendsto_variational
    baseline temperature spikeStrength hcoupling

/-- At fixed nonnegative temperature, the finite LD-spiked genomic pressure
converges uniformly over every nonnegative spike strength. -/
theorem positiveLDSpike_pressure_convergesUniformlyOnNonnegativeStrength
    (baseline temperature : ℝ) (htemperature : 0 ≤ temperature) :
    FiniteRankOnePressureUniformLimitStatement baseline temperature :=
  finiteRankOneRademacherPressure_tendstoUniformlyOn_nonnegativeSpike
    baseline temperature htemperature

/-- **One genomic counterexample to both C2 and C3.**  A single positive LD
rank-one spike is invisible to every fixed traffic graph, preserves the exact
lower genotype ground state through an orthogonal genotype, changes the upper
energy through an aligned genotype, and has positive variational pressure once
`temperature * spikeStrength > 1`. -/
theorem positiveLDSpike_refutesTrafficAndGroundStateDichotomies
    {Term Genotype : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (alignment : Genotype → ℝ) (orthogonal aligned : Genotype)
    (baseline spikeStrength population temperature : ℝ)
    (hspike : 0 < spikeStrength) (hpopulation : population ≠ 0)
    (horthogonal : alignment orthogonal = 0)
    (haligned : alignment aligned = population)
    (hcritical : 1 < temperature * spikeStrength) :
    RankOneSpikeRefutesBothDichotomies coefficient hasOddDegree vertices edges
      alignment orthogonal aligned baseline spikeStrength population temperature :=
  rankOneTraffic_groundState_pressure_counterexample
    coefficient hasOddDegree vertices edges hconnected alignment orthogonal aligned
    baseline spikeStrength population temperature hspike hpopulation horthogonal haligned
    hcritical

/-- **A positive LD spike can preserve the lower genetic ground state while changing an
exponential pressure.**  One genotype direction is orthogonal to the spike and attains the
baseline, every direction has no lower energy, and the fully aligned Curie–Weiss state has
strictly positive pressure objective once `2 log 2 < tλ`. -/
theorem positiveLDSpike_groundStateDoesNotFixPressure
    (baseline spikeStrength population tlam : ℝ) (hspike : 0 ≤ spikeStrength)
    (hlarge : 2 * Real.log 2 < tlam) :
    ((∀ state : Bool, baseline ≤
        rankOneEnergyDensity baseline spikeStrength population
          (if state = true then population else 0)) ∧
      rankOneEnergyDensity baseline spikeStrength population
        (if false = true then population else 0) = baseline) ∧
      0 < cwObjective tlam 1 := by
  refine ⟨rankOne_groundState_certificate
    (fun state : Bool ↦ if state = true then population else 0) false
    baseline spikeStrength population hspike ?_, curieWeiss_supercritical_witness tlam hlarge⟩
  simp

/-- **The positive LD-spike pressure has its exact Curie–Weiss critical point.**  The pressure
objective is nonpositive for every admissible overlap when `tλ ≤ 1`, and an explicit interior
overlap has positive objective as soon as `tλ > 1`. -/
theorem ldOverlapPressure_exactCriticalPoint (tlam : ℝ) :
    (tlam ≤ 1 → ∀ m : ℝ, |m| ≤ 1 → cwObjective tlam m ≤ 0) ∧
      (1 < tlam → ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m) :=
  curieWeiss_critical_dichotomy tlam

/-- **The supremal LD pressure, not merely its pointwise objective, has exact
critical point `tλ = 1`.**  The pressure gap is zero precisely on the
subcritical side and strictly positive above it. -/
theorem ldVariationalPressureGap_exactCriticalPoint (tlam : ℝ) :
    cwVariationalPressureGap tlam = 0 ↔ tlam ≤ 1 :=
  cwVariationalPressureGap_eq_zero_iff tlam

/-- The limiting LD pressure is globally stable under coupling changes: it is
`1/2`-Lipschitz, continuous, monotone, and convex. -/
theorem ldVariationalPressureGap_globalRegularity :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal) cwVariationalPressureGap ∧
      Continuous cwVariationalPressureGap ∧
        Monotone cwVariationalPressureGap ∧
          ConvexOn ℝ Set.univ cwVariationalPressureGap :=
  ⟨cwVariationalPressureGap_lipschitzWith,
    continuous_cwVariationalPressureGap,
    monotone_cwVariationalPressureGap,
    convexOn_cwVariationalPressureGap⟩

/-- **The matched-Bayes random-design question reduces to its scalar channel
with the sharp two-error ledger.**  A scalar mutual-information gap `Δ` loses
at most the sum of the independently certified left and right errors. -/
theorem matchedBayes_randomDesignGap_fromScalarGap_asymmetric
    (scalarLeft scalarRight randomLeft randomRight leftError rightError delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ leftError)
    (hright : |randomRight - scalarRight| ≤ rightError)
    (hgap : scalarRight - scalarLeft = delta) :
    delta - (leftError + rightError) ≤ randomRight - randomLeft :=
  randomDesign_gap_of_scalarGap_asymmetric scalarLeft scalarRight randomLeft randomRight
    leftError rightError delta hleft hright hgap

/-- The equal-error specialization loses at most `2ε`. -/
theorem matchedBayes_randomDesignGap_from_scalarGap
    (scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ epsilon)
    (hright : |randomRight - scalarRight| ≤ epsilon)
    (hgap : scalarRight - scalarLeft = delta) :
    delta - 2 * epsilon ≤ randomRight - randomLeft :=
  randomDesign_gap_of_scalarGap scalarLeft scalarRight randomLeft randomRight epsilon delta
    hleft hright hgap

/-- A positive genomic scalar-channel gap survives under independently
vanishing left and right random-design comparison errors. -/
theorem matchedBayes_randomDesignEventuallySeparates_fromAsymmetricErrors
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta : ℝ)
    (randomLeft randomRight leftError rightError : Index → ℝ)
    (hleft : ∀ index, |randomLeft index - scalarLeft| ≤ leftError index)
    (hright : ∀ index, |randomRight index - scalarRight| ≤ rightError index)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (hleftVanishing : Filter.Tendsto leftError regime (nhds 0))
    (hrightVanishing : Filter.Tendsto rightError regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_asymmetric regime
    scalarLeft scalarRight delta randomLeft randomRight leftError rightError
    hleft hright hgap hpositive hleftVanishing hrightVanishing

/-- **A positive genomic scalar-channel information gap survives at all
sufficiently advanced points of any regime whose random-design comparison
error vanishes.**  Taking the regime to be increasing aspect ratio gives the
large-`δ` reduction claimed in the matched-Bayes programme. -/
theorem matchedBayes_randomDesignEventuallySeparates_fromScalarGap
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta : ℝ)
    (randomLeft randomRight comparisonError : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤ comparisonError index)
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤ comparisonError index)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (herrorVanishing :
      Filter.Tendsto comparisonError regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap regime
    scalarLeft scalarRight delta randomLeft randomRight comparisonError
    hleft hright hgap hpositive herrorVanishing

/-- With the explicit inverse-square-root aspect-ratio comparison rate, a
scalar genomic information gap transfers at every finite aspect ratio for
which the gap exceeds twice the error. -/
theorem matchedBayes_randomDesignSeparates_ofLargeAspect
    (scalarLeft scalarRight randomLeft randomRight : ℝ)
    (aspectRatio constant delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ constant / Real.sqrt aspectRatio)
    (hright : |randomRight - scalarRight| ≤ constant / Real.sqrt aspectRatio)
    (hgap : scalarRight - scalarLeft = delta)
    (hthreshold : 2 * (constant / Real.sqrt aspectRatio) < delta) :
    randomLeft < randomRight :=
  randomDesign_separates_of_scalarGap_of_inverseSqrtAspect
    scalarLeft scalarRight randomLeft randomRight aspectRatio constant delta
    hleft hright hgap hthreshold

/-- The two large-sample genomic parameterizations are literally reciprocal:
diverging sample/dimension aspect is equivalent to its inverse approaching
zero from above, and their stated square-root error scales agree pointwise. -/
theorem matchedBayes_aspectWishartRatioBridge
    {Index : Type*} (regime : Filter Index)
    (aspectRatio : Index → ℝ) (constant : ℝ) :
    (Filter.Tendsto aspectRatio regime Filter.atTop ↔
      Filter.Tendsto (fun index ↦ (aspectRatio index)⁻¹) regime (𝓝[>] 0)) ∧
    (∀ index, constant / Real.sqrt (aspectRatio index) =
      constant * Real.sqrt ((aspectRatio index)⁻¹)) := by
  constructor
  · exact aspectAtTop_iff_inverseTendstoNhdsGTZero regime aspectRatio
  · intro index
    exact div_sqrt_eq_mul_sqrt_inv constant (aspectRatio index)

/-- A fixed positive scalar genomic information gap eventually survives
whenever the random-design aspect ratio diverges and comparison error has the
Wishart-scale `constant / sqrt aspectRatio` form. -/
theorem matchedBayes_randomDesignEventuallySeparates_ofAspectAtTop
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta constant : ℝ)
    (aspectRatio randomLeft randomRight : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤ constant / Real.sqrt (aspectRatio index))
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤ constant / Real.sqrt (aspectRatio index))
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (haspectRatio : Filter.Tendsto aspectRatio regime Filter.atTop) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_of_aspectAtTop regime
    scalarLeft scalarRight delta constant aspectRatio randomLeft randomRight
    hleft hright hgap hpositive haspectRatio

/-- A genomic matched-information error bounded at the derived Wishart scale
vanishes when the adjusted dimension/sample ratio tends to zero. -/
theorem matchedBayes_wishartInformationErrorVanishes
    {Index : Type*} (regime : Filter Index)
    (informationError adjustedRatio : Index → ℝ) (constant : ℝ)
    (hratio : Filter.Tendsto adjustedRatio regime (nhds 0))
    (herror : ∀ index,
      |informationError index| ≤ constant * Real.sqrt (adjustedRatio index)) :
    Filter.Tendsto informationError regime (nhds 0) :=
  matchedInformationError_tendsto_zero_of_wishartRatio
    regime informationError adjustedRatio constant hratio herror

/-- Two genomic design sequences may have different aspect ratios and
different Wishart comparison constants.  Independent vanishing of their two
explicit error scales still transfers every positive scalar information gap. -/
theorem matchedBayes_randomDesignEventuallySeparates_ofAsymmetricWishartRatios
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta leftConstant rightConstant : ℝ)
    (leftRatio rightRatio randomLeft randomRight : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤
        leftConstant * Real.sqrt (leftRatio index))
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤
        rightConstant * Real.sqrt (rightRatio index))
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (hleftRatio : Filter.Tendsto leftRatio regime (nhds 0))
    (hrightRatio : Filter.Tendsto rightRatio regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_of_asymmetricWishartRatios regime
    scalarLeft scalarRight delta leftConstant rightConstant leftRatio rightRatio
    randomLeft randomRight hleft hright hgap hpositive hleftRatio hrightRatio

/-- At the explicit Wishart rate, every fixed positive scalar genomic
information gap eventually transfers when `(p+1)/n` tends to zero. -/
theorem matchedBayes_randomDesignEventuallySeparates_ofWishartRatio
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta constant : ℝ)
    (adjustedRatio randomLeft randomRight : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤
        constant * Real.sqrt (adjustedRatio index))
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤
        constant * Real.sqrt (adjustedRatio index))
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (hratio : Filter.Tendsto adjustedRatio regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_of_wishartRatio regime
    scalarLeft scalarRight delta constant adjustedRatio randomLeft randomRight
    hleft hright hgap hpositive hratio

/-- A bounded genomic rank-one covariance perturbation has vanishing matched
information-density effect once its certified path nuclear distance is
identified with the concrete singular spectrum. -/
theorem matchedBayes_certifiedRankOnePerturbation_isAsymptoticallyInvisible
    (certificate : ℕ → MatchedInformationPathCertificate)
    (varianceBound spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength)
    (hvarianceBound : ∀ population,
      (certificate population).variance ≤ varianceBound)
    (hnuclear : ∀ population,
      (certificate population).nuclearDistance =
        (finiteRankOneSingularSpectrum population spikeStrength hspike).normalizedNuclearDistance) :
    Filter.Tendsto
      (fun population ↦ (certificate population).informationPath 1 -
        (certificate population).informationPath 0)
      Filter.atTop (nhds 0) :=
  matchedInformationPath_rankOne_tendsto_zero_of_varianceBound
    certificate varianceBound spikeStrength hspike hvarianceBound hnuclear

/-- The genomic matched-information nuclear estimate follows from a certified
matrix I--MMSE interpolation path and its posterior-covariance trace bound. -/
theorem matchedBayes_informationPath_nuclearBound
    (certificate : MatchedInformationPathCertificate) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      certificate.variance / 2 * certificate.nuclearDistance :=
  matchedInformationPath_nuclear_bound certificate

/-- The complete genomic Wishart comparison ledger: I--MMSE sensitivity,
nuclear-to-Frobenius control, and the Wishart Frobenius scale yield the exact
normalized `sqrt ((p+1)/n)` information error. -/
theorem matchedBayes_wishartFrobeniusComparisonRate
    (dimension sampleSize signal variance operatorBound : ℝ)
    (informationError nuclearError frobeniusError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hsignal : 0 ≤ signal) (hvariance : 0 ≤ variance)
    (hinformation : |informationError| ≤
      signal * variance / (2 * dimension) * nuclearError)
    (hnuclear : nuclearError ≤ Real.sqrt dimension * frobeniusError)
    (hfrobenius : frobeniusError ≤ operatorBound *
      Real.sqrt (dimension * ((dimension + 1) / sampleSize))) :
    |informationError| ≤ signal * variance * operatorBound / 2 *
      Real.sqrt ((dimension + 1) / sampleSize) :=
  matchedInformationError_le_of_wishartFrobenius
    dimension sampleSize signal variance operatorBound informationError nuclearError
    frobeniusError hdimension hsampleSize hsignal hvariance hinformation
    hnuclear hfrobenius

/-- Starting only from the exact Wishart second-moment identity, covariance
trace bounds, and the I--MMSE/nuclear/Frobenius comparisons, the genomic
matched-information error has the explicit normalized rate. -/
theorem matchedBayes_wishartMomentIdentityComparisonRate
    (dimension sampleSize signal variance operatorBound covarianceTrace
      covarianceTraceSq frobeniusSecondMoment frobeniusError nuclearError
      informationError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hsignal : 0 ≤ signal) (hvariance : 0 ≤ variance)
    (hoperator : 0 ≤ operatorBound)
    (htrace : |covarianceTrace| ≤ dimension * operatorBound)
    (htraceSq : covarianceTraceSq ≤ dimension * operatorBound ^ 2)
    (hmoment : frobeniusSecondMoment =
      (covarianceTrace ^ 2 + covarianceTraceSq) / sampleSize)
    (hfrobenius : frobeniusError ≤ Real.sqrt frobeniusSecondMoment)
    (hnuclear : nuclearError ≤ Real.sqrt dimension * frobeniusError)
    (hinformation : |informationError| ≤
      signal * variance / (2 * dimension) * nuclearError) :
    |informationError| ≤ signal * variance * operatorBound / 2 *
      Real.sqrt ((dimension + 1) / sampleSize) :=
  matchedInformationError_le_of_wishartMomentIdentity
    dimension sampleSize signal variance operatorBound covarianceTrace
    covarianceTraceSq frobeniusSecondMoment frobeniusError nuclearError
    informationError hdimension hsampleSize hsignal hvariance hoperator htrace
    htraceSq hmoment hfrobenius hnuclear hinformation

/-- Certified genomic matched-information paths become asymptotically
indistinguishable whenever their covariance perturbations have vanishing rank
fraction and their prior variances admit one uniform bound. -/
theorem matchedBayes_certifiedSublinearRank_isInvisible_ofVarianceBound
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → MatchedInformationPathCertificate)
    (varianceBound operatorBound : ℝ) (rankFraction : Index → ℝ)
    (hvarianceBound : ∀ index, (certificate index).variance ≤ varianceBound)
    (hrankVanishing : Filter.Tendsto rankFraction regime (nhds 0))
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) :
    MatchedInformationPathGapTendsToZero regime certificate :=
  matchedInformationPath_lowRank_tendsto_zero_of_varianceBound regime certificate
    varianceBound operatorBound rankFraction hvarianceBound
    hrankVanishing hnuclearRank

/-- Exact common variance is only a specialization of uniform boundedness. -/
theorem matchedBayes_certifiedSublinearRank_isInvisible
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → MatchedInformationPathCertificate)
    (operatorBound : ℝ) (rankFraction : Index → ℝ)
    (hvariance : ∃ variance : ℝ, ∀ index, (certificate index).variance = variance)
    (hrankVanishing : Filter.Tendsto rankFraction regime (nhds 0))
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) :
    MatchedInformationPathGapTendsToZero regime certificate :=
  matchedInformationPath_lowRank_tendsto_zero regime certificate operatorBound
    rankFraction hvariance hrankVanishing hnuclearRank

/-- **A genomic covariance perturbation occupying a vanishing rank fraction
cannot create an order-one matched information-density separation under the
matrix I-MMSE/nuclear estimate.**  Thus the extensive-rank requirement for a
negative matched-Bayes witness is an asymptotic theorem, not only a finite
inequality. -/
theorem matchedBayes_sublinearRankPerturbation_isAsymptoticallyInvisible
    (densityGap rankFraction : ℕ → ℝ) (constant : ℝ)
    (hrankVanishing : Filter.Tendsto rankFraction Filter.atTop (nhds 0))
    (hnuclear : ∀ index,
      |densityGap index| ≤ constant * rankFraction index) :
    Filter.Tendsto densityGap Filter.atTop (nhds 0) :=
  matchedDensity_lowRank_tendsto_zero_of_nuclearEstimate
    densityGap rankFraction constant hrankVanishing hnuclear

/-- A fixed positive matched genomic information-density gap forces an
explicit positive covariance-rank fraction under the matrix I--MMSE/nuclear
estimate. -/
theorem matchedBayes_positiveGap_forcesExtensiveRank
    (densityGap constant rankFraction delta : ℝ)
    (hconstant : 0 < constant) (hdelta : 0 < delta)
    (hgap : delta ≤ |densityGap|)
    (hnuclear : |densityGap| ≤ constant * rankFraction) :
    0 < rankFraction ∧ delta / constant ≤ rankFraction :=
  matchedDensity_positiveGap_forces_rankFraction
    densityGap constant rankFraction delta hconstant hdelta hgap hnuclear

/-- A finite genomic information gap certified directly by an I--MMSE path
forces an explicit rank fraction under only a prior-variance upper bound. -/
theorem matchedBayes_certifiedPositiveGap_forcesExtensiveRank
    (certificate : MatchedInformationPathCertificate)
    (varianceBound operatorBound rankFraction delta : ℝ)
    (hvarianceBound : certificate.variance ≤ varianceBound)
    (hvariancePositive : 0 < varianceBound) (hoperator : 0 < operatorBound)
    (hdelta : 0 < delta)
    (hgap : delta ≤
      |certificate.informationPath 1 - certificate.informationPath 0|)
    (hnuclearRank : certificate.nuclearDistance ≤ operatorBound * rankFraction) :
    0 < rankFraction ∧
      delta / (varianceBound * operatorBound / 2) ≤ rankFraction :=
  matchedInformationPath_positiveGap_forces_rankFraction_of_varianceBound
    certificate varianceBound operatorBound rankFraction delta hvarianceBound
    hvariancePositive hoperator hdelta hgap hnuclearRank

/-- A persistent genomic information gap certified by I--MMSE paths forces
the exact eventual extensive-rank lower bound and excludes sublinear rank. -/
theorem matchedBayes_certifiedPersistentGap_requiresExtensiveRank
    {Index : Type*} (regime : Filter Index) [regime.NeBot]
    (certificate : Index → MatchedInformationPathCertificate)
    (varianceBound operatorBound delta : ℝ) (rankFraction : Index → ℝ)
    (hvariancePositive : 0 < varianceBound) (hoperator : 0 < operatorBound)
    (hdelta : 0 < delta)
    (hvarianceBound : ∀ index, (certificate index).variance ≤ varianceBound)
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index)
    (hgap : ∀ᶠ index in regime, delta ≤
      |(certificate index).informationPath 1 -
        (certificate index).informationPath 0|) :
    (∀ᶠ index in regime,
      delta / (varianceBound * operatorBound / 2) ≤ rankFraction index) ∧
      ¬ Filter.Tendsto rankFraction regime (nhds 0) :=
  matchedInformationPath_persistentGap_requires_extensiveRank regime certificate
    varianceBound operatorBound delta rankFraction hvariancePositive hoperator
    hdelta hvarianceBound hnuclearRank hgap

/-- A persistent order-one matched genomic information gap cannot be produced
by a perturbation whose covariance-rank fraction vanishes. -/
theorem matchedBayes_persistentGap_requiresExtensiveRank
    {Index : Type*} (regime : Filter Index) [regime.NeBot]
    (densityGap rankFraction : Index → ℝ) (constant delta : ℝ)
    (hconstant : 0 < constant) (hdelta : 0 < delta)
    (hgap : ∀ᶠ index in regime, delta ≤ |densityGap index|)
    (hnuclear : ∀ index,
      |densityGap index| ≤ constant * rankFraction index) :
    (∀ᶠ index in regime, delta / constant ≤ rankFraction index) ∧
      ¬ Filter.Tendsto rankFraction regime (nhds 0) :=
  ⟨matchedDensity_eventualGap_forces_eventualRankFraction
      regime densityGap rankFraction constant delta hconstant hdelta hgap hnuclear,
    matchedDensity_eventualGap_not_sublinearRank
      regime densityGap rankFraction constant delta hconstant hdelta hgap hnuclear⟩

/-- A degree-limited genomic risk functional cannot distinguish designs with the same truncated
traffic profile, so the complete Bayes gap transfers to every procedure in the class. -/
theorem degreeLimitedGenomicRisk_fullGapHardness
    {Algorithm : Type*} {D : ℕ} (risk : Algorithm → TruncatedTrafficRisk D)
    (left right : Fin (D + 1) → ℝ) (htraffic : left = right)
    (bayesLeft bayesRight : ℝ)
    (hoptimalRight : ∀ algorithm, bayesRight ≤ (risk algorithm).evaluate right)
    (algorithm : Algorithm) :
    bayesRight - bayesLeft ≤ (risk algorithm).evaluate left - bayesLeft :=
  truncatedTraffic_hardness risk left right htraffic bayesLeft bayesRight hoptimalRight algorithm

/-- **The corrected stable low-degree theorem.**  A degree-`D` genomic graph
polynomial is quantitatively controlled by the maximum retained LD-traffic
error times its coefficient `ℓ¹` mass.  Thus exact finite factorization
passes to limiting traffic only with a coefficient-growth/resolution bound. -/
theorem stableDegreeLimitedGenomicRisk_quantitativeTrafficBound
    {D : ℕ} (risk : TruncatedTrafficRisk D)
    (left right : Fin (D + 1) → ℝ) (epsilon : ℝ)
    (hcoordinate : ∀ graph, |left graph - right graph| ≤ epsilon) :
    |risk.evaluate left - risk.evaluate right| ≤
      (∑ graph, |risk.coefficient graph|) * epsilon :=
  truncatedTrafficRisk_abs_sub_le_coefficientMass_mul
    risk left right epsilon hcoordinate

/-- Uniformly bounded coefficient mass turns quantitative LD-traffic
convergence into convergence of the corresponding stable low-degree genomic
procedure. -/
theorem stableDegreeLimitedGenomicRisk_convergesOfBoundedCoefficientMass
    {D : ℕ} (risk : ℕ → TruncatedTrafficRisk D)
    (left right : ℕ → Fin (D + 1) → ℝ)
    (discrepancy coefficientBound : ℝ)
    (hdiscrepancy : ∀ index graph,
      |left index graph - right index graph| ≤
        discrepancy * (1 / 2 : ℝ) ^ index)
    (hcoefficient : ∀ index,
      (∑ graph, |(risk index).coefficient graph|) ≤ coefficientBound)
    (hdiscrepancyNonneg : 0 ≤ discrepancy) :
    Filter.Tendsto
      (fun index ↦ (risk index).evaluate (left index) -
        (risk index).evaluate (right index))
      Filter.atTop (nhds 0) :=
  truncatedTrafficRisk_tendsto_zero_of_boundedCoefficientMass
    risk left right discrepancy coefficientBound hdiscrepancy hcoefficient
      hdiscrepancyNonneg

/-- **High-temperature matched free energies agree once the cluster
expansion is certified.**  Equal finite LD-traffic truncations and a common
geometric polymer tail force equality of the two limiting pressures.  The
model-specific uniqueness/cluster-expansion certificate remains explicit. -/
theorem highTemperatureTrafficLimitsAgree_ofGeometricCertificate
    (leftLimit rightLimit C q : ℝ) (commonTruncation : ℕ → ℝ)
    (hqNonneg : 0 ≤ q) (hq : q < 1)
    (hleft : ∀ depth,
      |leftLimit - commonTruncation depth| ≤
        C * q ^ (depth + 1) / (1 - q))
    (hright : ∀ depth,
      |rightLimit - commonTruncation depth| ≤
        C * q ^ (depth + 1) / (1 - q)) :
    leftLimit = rightLimit :=
  highTemperatureTrafficLimit_eq_of_geometricTruncation
    leftLimit rightLimit C q commonTruncation hqNonneg hq hleft hright

/-- **Every finite LD-traffic depth is strictly weaker than the next.**  For
each `D`, two genuine probability laws on uniformly conditioned diagonal LD
values in `[1,2]` agree on every connected diagonal traffic coordinate with at
most `D` edges and differ at `D+1` edges. -/
theorem genomicLDTrafficHierarchy_strictAtEveryDegree (D : ℕ) :
    ∃ left right : Fin (D + 2) → ℝ,
      IsMomentMatchedProbabilityPair D left right ∧
        SeparatesAtNextDiagonalTraffic D left right :=
  exists_probabilityWeights_matchingMoments_through_degree D

/-- **At every finite LD-traffic depth there is one probability pair blind to
the entire graph-polynomial risk class.**  This is stronger than pairwise
moment matching: the same pair equalizes every truncated risk functional while
its next traffic coordinate remains different. -/
theorem genomicLDTrafficBlindPair_existsAtEveryDegree (D : ℕ) :
    ∃ left right : Fin (D + 2) → ℝ,
      IsBlindPairForEveryTruncatedTrafficRisk D left right :=
  exists_probabilityPair_blindToEveryTruncatedTrafficRisk D

/-- **Finite permutation-equivariant genomic polynomials factor through LD
traffic graphs.**  Endpoint equality patterns encode the rooted or unrooted
graph, and label-permutation invariance forces coefficients to be constant on
those graph classes. -/
theorem permutationInvariantGenomicPolynomial_factorsThroughLDGraphs
    {Slot Locus Graph : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Locus] [Fintype Graph] [DecidableEq Graph]
    (shape : (Slot → Locus) → Graph)
    (coefficient value : (Slot → Locus) → ℝ)
    (hshape : ∀ left right, shape left = shape right →
      SameEqualityPattern left right)
    (hinvariant : ∀ (permutation : Equiv.Perm Locus) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    (∑ monomial, coefficient monomial * value monomial) =
      ∑ graph, graphShapeCoefficient shape coefficient graph *
        ∑ monomial, if shape monomial = graph then value monomial else 0 :=
  invariantPolynomial_graphSum_factorization shape coefficient value hshape hinvariant

/-- **Canonical finite genomic traffic factorization.**  The graph index is
the quotient of endpoint assignments by equality pattern, so callers need not
provide or validate a separate graph-shape encoding. -/
theorem permutationInvariantGenomicPolynomial_factorsThroughCanonicalLDGraphs
    {Slot Locus : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Locus]
    (coefficient value : (Slot → Locus) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Locus) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    CanonicalTrafficFactorizationStatement coefficient value :=
  invariantPolynomial_canonicalTraffic_factorization coefficient value hinvariant

/-- **Canonical rooted genomic traffic factorization.**  The distinguished
`none` slot records the output locus, formally supplying the rooted graph
version needed for permutation-equivariant vector estimators. -/
theorem permutationEquivariantGenomicPolynomial_factorsThroughRootedLDGraphs
    {Slot Locus : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Locus]
    (coefficient value : (Option Slot → Locus) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Locus) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    RootedCanonicalTrafficFactorizationStatement coefficient value :=
  rootedInvariantPolynomial_canonicalTraffic_factorization coefficient value hinvariant

/-- A genomic polynomial of total degree at most `D`, decomposed into its
homogeneous degrees, factors exactly through canonical LD traffic graphs with
at most `D` ordered edges. -/
theorem degreeLimitedGenomicPolynomial_factorsThroughCanonicalLDGraphs
    {D : ℕ} {Locus : Type*} [Fintype Locus]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Locus) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Locus) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial) :
    DegreeAtMostTrafficFactorizationStatement coefficient value :=
  degreeAtMostInvariantPolynomial_canonicalTraffic_factorization
    coefficient value hinvariant

/-- The corresponding degree-limited permutation-equivariant genomic vector
polynomial factors through rooted LD graphs with the same edge bound. -/
theorem degreeLimitedGenomicEquivariantPolynomial_factorsThroughRootedLDGraphs
    {D : ℕ} {Locus : Type*} [Fintype Locus]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Locus) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Locus) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial) :
    DegreeAtMostRootedTrafficFactorizationStatement coefficient value :=
  degreeAtMostRootedInvariantPolynomial_canonicalTraffic_factorization
    coefficient value hinvariant

/-- Equal canonical LD profiles make every invariant scalar genomic
polynomial of degree at most `D` exactly equal on the two designs. -/
theorem degreeLimitedGenomicPolynomial_eq_ofCanonicalLDProfileEq
    {D : ℕ} {Locus : Type*} [Fintype Locus]
    (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Locus) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Locus) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial)
    (htraffic : degreeAtMostCanonicalTrafficProfile leftValue =
      degreeAtMostCanonicalTrafficProfile rightValue) :
    (∑ degree : Fin (D + 1),
      ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
      ∑ degree : Fin (D + 1),
        ∑ monomial, coefficient degree monomial * rightValue degree monomial :=
  degreeAtMostInvariantPolynomial_eq_of_canonicalTrafficProfile_eq
    coefficient leftValue rightValue hinvariant htraffic

/-- Equal rooted LD profiles likewise make every equivariant genomic
polynomial coordinate of degree at most `D` exactly equal. -/
theorem degreeLimitedGenomicEquivariantPolynomial_eq_ofRootedLDProfileEq
    {D : ℕ} {Locus : Type*} [Fintype Locus]
    (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Locus) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Locus) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial)
    (htraffic : degreeAtMostRootedCanonicalTrafficProfile leftValue =
      degreeAtMostRootedCanonicalTrafficProfile rightValue) :
    (∑ degree : Fin (D + 1),
      ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
      ∑ degree : Fin (D + 1),
        ∑ monomial, coefficient degree monomial * rightValue degree monomial :=
  degreeAtMostRootedInvariantPolynomial_eq_of_canonicalTrafficProfile_eq
    coefficient leftValue rightValue hinvariant htraffic

/-- **Direct genomic fixed-degree hardness.**  Equal canonical LD profiles
force every uniform invariant degree-`D` polynomial procedure to have the same
risk on both designs, so right-design Bayes optimality transfers the complete
Bayes gap to one common left-design hard instance. -/
theorem degreeLimitedGenomicPolynomial_fullGapHardness_fromCanonicalLDProfile
    {Algorithm : Type*} {D : ℕ} {Locus : Type*} [Fintype Locus]
    (coefficient : Algorithm → (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Locus) → ℝ))
    (leftValue rightValue : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Locus) → ℝ))
    (hinvariant : ∀ algorithm degree (permutation : Equiv.Perm Locus) monomial,
      coefficient algorithm degree (permutation ∘ monomial) =
        coefficient algorithm degree monomial)
    (htraffic : degreeAtMostCanonicalTrafficProfile leftValue =
      degreeAtMostCanonicalTrafficProfile rightValue)
    (bayesLeft bayesRight : ℝ)
    (hoptimalRight : ∀ algorithm,
      bayesRight ≤ ∑ degree : Fin (D + 1),
        ∑ monomial,
          coefficient algorithm degree monomial * rightValue degree monomial)
    (algorithm : Algorithm) :
    bayesRight - bayesLeft ≤
      (∑ degree : Fin (D + 1),
        ∑ monomial,
          coefficient algorithm degree monomial * leftValue degree monomial) -
        bayesLeft :=
  degreeAtMostInvariantPolynomial_hardness_of_canonicalTrafficProfile_eq
    coefficient leftValue rightValue hinvariant htraffic bayesLeft bayesRight
    hoptimalRight algorithm

/-- **A finite tilt net quantitatively controls the full genomic pressure
profile.**  Uniform `K`-Lipschitz control converts radius-`ρ` coordinate error
into the global bound `2Kρ + ε`. -/
theorem genomicPressureProfiles_dist_le_of_tiltNet
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (left right : Parameter → ℝ)
    (hleft : LipschitzWith K left) (hright : LipschitzWith K right)
    (net : Set Parameter) (radius coordinateError : ℝ)
    (hnet : ∀ parameter, ∃ representative ∈ net,
      dist parameter representative ≤ radius)
    (hagrees : ∀ representative ∈ net,
      dist (left representative) (right representative) ≤ coordinateError) :
    ∀ parameter,
      dist (left parameter) (right parameter) ≤
        2 * (K : ℝ) * radius + coordinateError :=
  lipschitzPressureProfiles_dist_le_of_net
    K left right hleft hright net radius coordinateError hnet hagrees

/-- **Dense rational genomic tilt coordinates determine the complete pressure
profile.**  Two uniformly Lipschitz profiles agreeing on the dense enumerated
family agree at every tilt. -/
theorem genomicPressureProfiles_eq_of_eqOn_denseTilts
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (left right : Parameter → ℝ)
    (hleft : LipschitzWith K left) (hright : LipschitzWith K right)
    (parameters : Set Parameter) (hdense : Dense parameters)
    (hagrees : Set.EqOn left right parameters) :
    left = right :=
  lipschitzPressureProfiles_eq_of_eqOn_dense
    K left right hleft hright parameters hdense hagrees

/-- **Functional genomic right-profile compactness.**  On a compact tilt
domain, the uniformly bounded pressure functions sharing one Lipschitz constant
form a compact family in the uniform metric. -/
theorem genomicBoundedLipschitzPressureFamily_isCompact
    {Parameter : Type*} [PseudoMetricSpace Parameter] [CompactSpace Parameter]
    (K : NNReal) (bound : ℝ) :
    IsCompact (boundedLipschitzPressureFamily
      (Parameter := Parameter) K bound) :=
  isCompact_boundedLipschitzPressureFamily K bound

/-- Every sequence in the bounded equi-Lipschitz genomic pressure family has
a uniformly convergent subsequence and its limit stays in the same family. -/
theorem genomicBoundedLipschitzPressureFamily_hasUniformlyConvergentSubsequence
    {Parameter : Type*} [PseudoMetricSpace Parameter] [CompactSpace Parameter]
    (K : NNReal) (bound : ℝ)
    (profiles : ℕ → BoundedContinuousFunction Parameter ℝ)
    (hprofiles : ∀ index,
      profiles index ∈ boundedLipschitzPressureFamily K bound) :
    ∃ limit ∈ boundedLipschitzPressureFamily (Parameter := Parameter) K bound,
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit) :=
  boundedLipschitzPressureFamily_tendsto_subseq K bound profiles hprofiles

/-- **The nonperturbative genomic LD profile has a genuine compact state space.**
Uniformly bounded countable pressure coordinates admit one common subsequence
on which every prior/replica/tilt coordinate converges.  This is the exact
diagonal compactness statement needed before any model-specific identification
of the limiting right-convergence profile. -/
theorem genomicExponentialProfile_hasCommonCoordinatewiseSubsequence
    (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound) :
    ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        ∀ coordinate : ℕ,
          Filter.Tendsto (fun n ↦ profiles (subsequence n) coordinate)
            Filter.atTop (nhds (limit coordinate)) :=
  boundedExponentialProfile_common_coordinatewise_subsequence bound profiles

/-- **The explicit exponential-profile formula is a genuine separating
distance.**  It is nonnegative, symmetric, triangular, and vanishes exactly on
identical genomic LD pressure profiles. -/
theorem genomicExponentialProfileDistance_metricLaws
    {bound : ℝ} (left middle right : BoundedExponentialProfile bound) :
    0 ≤ exponentialProfileDistance left right ∧
      exponentialProfileDistance left right = exponentialProfileDistance right left ∧
      exponentialProfileDistance left right ≤
        exponentialProfileDistance left middle + exponentialProfileDistance middle right ∧
      (exponentialProfileDistance left right = 0 ↔ left = right) :=
  ⟨exponentialProfileDistance_nonneg left right,
    exponentialProfileDistance_comm left right,
    exponentialProfileDistance_triangle left middle right,
    exponentialProfileDistance_eq_zero_iff left right⟩

/-- **The genomic right-profile formula is an actual compact metric space.**
The installed metric is exactly the weighted capped-coordinate distance, and
its complete carrier is compact in the ordinary topological sense. -/
theorem genomicExponentialProfilePoint_isCompactMetricSpace (bound : ℝ) :
    IsCompact (Set.univ : Set (ExponentialProfilePoint bound)) :=
  isCompact_univ

/-- Standard convergence in the bundled genomic right-profile metric is
exactly simultaneous convergence of every prior/replica/tilt coordinate. -/
theorem genomicExponentialProfilePoint_converges_iff_coordinatewise
    {bound : ℝ} {profiles : ℕ → ExponentialProfilePoint bound}
    {limit : ExponentialProfilePoint bound} :
    Filter.Tendsto profiles Filter.atTop (nhds limit) ↔
      ∀ coordinate : ℕ,
        Filter.Tendsto (fun n ↦ profiles n coordinate)
          Filter.atTop (nhds (limit coordinate)) :=
  exponentialProfilePoint_tendsto_iff_coordinatewise

/-- **The explicit genomic right-profile distance induces exactly coordinatewise
pressure convergence.**  Thus convergence in the metric is neither weaker nor
stronger than simultaneous convergence of every enumerated prior/replica/tilt
coordinate. -/
theorem genomicExponentialProfileDistance_converges_iff_coordinatewise
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound} :
    Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
        Filter.atTop (nhds 0) ↔
      ∀ coordinate : ℕ,
        Filter.Tendsto (fun n ↦ profiles n coordinate)
          Filter.atTop (nhds (limit coordinate)) :=
  exponentialProfileDistance_tendsto_zero_iff_coordinatewise

/-- **Finite genomic pressure data approximate the full right profile with an
explicit modulus.**  The profile space has diameter at most two, and agreement
on coordinates `0,…,K-1` leaves distance at most the geometric tail `2·2⁻ᴷ`. -/
theorem genomicExponentialProfileDistance_finitePrefixControl
    {bound : ℝ} (left right : BoundedExponentialProfile bound)
    (prefixLength : ℕ)
    (hprefix : ∀ coordinate < prefixLength, left coordinate = right coordinate) :
    exponentialProfileDistance left right ≤ 2 ∧
      exponentialProfileDistance left right ≤
        2 * (1 / 2 : ℝ) ^ prefixLength :=
  ⟨exponentialProfileDistance_le_two left right,
    exponentialProfileDistance_le_geometricTail_of_prefix_eq
      left right prefixLength hprefix⟩

/-- **Bounded genomic exponential profiles are sequentially compact in the
explicit weighted distance.**  The same subsequence works simultaneously for
every enumerated prior/replica/tilt coordinate. -/
theorem genomicExponentialProfile_compactInExplicitDistance
    (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound) :
    ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        Filter.Tendsto
          (fun n ↦ exponentialProfileDistance (profiles (subsequence n)) limit)
          Filter.atTop (nhds 0) :=
  boundedExponentialProfile_compact_subsequence_in_distance bound profiles


/-- **Exact criterion for the Beta curve.**  At conditional-Laplace-transform level the Beta
power profile is equivalent to an `x`-independent transform after subtracting the logarithmic
front response.  When the transforms determine the laws, this is the claimed common-noise
representation and is both necessary and sufficient. -/
theorem speedConditionedGenealogy_beta_iff_logResponse
    (gamma : ℝ) (conditionalLaplace : ℝ → ℝ → ℝ) :
    HasBetaTiltInvariant gamma conditionalLaplace ↔
      HasFractionIndependentCenteredTransform gamma conditionalLaplace :=
  hasBetaTiltInvariant_iff_centeredTransformIndependent gamma conditionalLaplace

/-- **The `log³ N` clock is a front-response statement.**  At susceptibility exponent three the
genealogical clock is the cube of the front width; the coalescent rate law contributes no cube. -/
theorem pioneerSusceptibility_setsGenealogicalClock (width : ℝ) :
    genealogicalTimescale width 3 = width ^ 3 :=
  genealogicalTimescale_three width

section StationarityRepair

variable {State : Type*} [Fintype State]

/-- Mean performance of a target-only biological score under the one-point state law. -/
noncomputable def onePointPerformance (weight : State → ℝ) (score : State → ℝ) : ℝ :=
  ∑ y, weight y * score y

/-- Reference evaluation on a two-state law with distinct weights and scores. -/
theorem onePointPerformance_at_reference_point :
    onePointPerformance (![1, 3] : Fin 2 → ℝ) (![2, 5] : Fin 2 → ℝ) = 17 := by
  norm_num [onePointPerformance, Fin.sum_univ_two]


/-- Mean performance obtained by transporting to `y` and then evaluating a score that sees
only `y`.  Under stationarity this is exactly `onePointPerformance`; it contains no temporal
information. -/
noncomputable def targetOnlyTransportPerformance
    (weight : State → ℝ) (transition : State → State → ℝ) (score : State → ℝ) : ℝ :=
  ∑ x, weight x * ∑ y, transition x y * score y

/-- A source-target performance.  Unlike `targetOnlyTransportPerformance`, the quality can
depend on the source decision and the target state simultaneously. -/
noncomputable def crossStatePerformance
    (weight : State → ℝ) (transition : State → State → ℝ)
    (quality : State → State → ℝ) : ℝ :=
  ∑ x, weight x * ∑ y, transition x y * quality x y

/-- **Stationarity repair.**  A target-only average after a stationary transition is the
one-point average, exactly.  Thus a lag parameter in this expression is syntactic but not
identified by the value. -/
theorem targetOnlyTransportPerformance_eq_onePoint
    (weight : State → ℝ) (transition : State → State → ℝ) (score : State → ℝ)
    (hstationary : ∀ y, ∑ x, weight x * transition x y = weight y) :
    targetOnlyTransportPerformance weight transition score =
      onePointPerformance weight score := by
  unfold targetOnlyTransportPerformance onePointPerformance
  calc
    ∑ x, weight x * ∑ y, transition x y * score y =
        ∑ x, ∑ y, weight x * (transition x y * score y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ = ∑ y, ∑ x, weight x * (transition x y * score y) := Finset.sum_comm
    _ = ∑ y, (∑ x, weight x * transition x y) * score y := by
          apply Finset.sum_congr rfl
          intro y _
          simp_rw [← mul_assoc]
          rw [← Finset.sum_mul]
    _ = ∑ y, weight y * score y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hstationary y]

end StationarityRepair

/-! ## An exact two-state biological witness -/

abbrev BinaryBiologicalState := Fin 2

/-- Uniform invariant law on two biological contexts. -/
noncomputable def binaryStateWeight (_ : BinaryBiologicalState) : ℝ := 1 / 2

/-- Reference evaluation: the two states are equally weighted. -/
@[simp] theorem binaryStateWeight_at_reference_point (x : BinaryBiologicalState) :
    binaryStateWeight x = 1 / 2 := rfl


/-- The biological context law is the canonical balanced calibration weight. -/
@[simp] theorem binaryStateWeight_eq_balancedBinaryWeight (x : BinaryBiologicalState) :
    binaryStateWeight x = balancedBinaryWeight x := by
  rfl

/-- A transition that preserves the context. -/
noncomputable def persistentTransition
    (x y : BinaryBiologicalState) : ℝ := if x = y then 1 else 0

/-- Reference evaluations: the persistent kernel is the identity matrix on two states. -/
theorem persistentTransition_at_reference_point :
    persistentTransition 0 0 = 1 ∧ persistentTransition 0 1 = 0 := by
  constructor <;> norm_num [persistentTransition]


/-- A transition that swaps the two contexts. -/
noncomputable def switchingTransition
    (x y : BinaryBiologicalState) : ℝ := if x = y then 0 else 1

/-- Reference evaluations: the switching kernel is the exchange matrix. -/
theorem switchingTransition_at_reference_point :
    switchingTransition 0 0 = 0 ∧ switchingTransition 0 1 = 1 := by
  constructor <;> norm_num [switchingTransition]


/-- A target-only annotation distinguishing state `1`. -/
noncomputable def targetAnnotation (y : BinaryBiologicalState) : ℝ :=
  if y = 1 then 1 else 0

/-- Reference evaluations: the annotation is the indicator of the distinguished state. -/
theorem targetAnnotation_at_reference_point :
    targetAnnotation 1 = 1 ∧ targetAnnotation 0 = 0 := by
  constructor <;> norm_num [targetAnnotation]


/-- Quality of a source-adapted readout: one exactly when source and target contexts match.

The same function as `persistentTransition`, read as a readout quality rather than as a
transition.  `Descent.contextMatchQuality_eq_persistentTransition` says so; the body is
written out here rather than delegating, because the witness proofs below evaluate this
definition by `simp` and a delegation stops them one unfolding short. -/
noncomputable def contextMatchQuality
    (x y : BinaryBiologicalState) : ℝ := if x = y then 1 else 0

/-- Reference evaluations: quality one on a match, zero on a mismatch. -/
theorem contextMatchQuality_at_reference_point :
    contextMatchQuality 0 0 = 1 ∧ contextMatchQuality 0 1 = 0 := by
  constructor <;> norm_num [contextMatchQuality]


/-- **The two-context biological witness runs on the horizon-curve kernels.**

`HorizonCurve.stayKernel` is the Kronecker delta on two states, and so are the transition
that preserves the biological context and the readout quality of a design used in the
context it was built for — `HorizonCurve.agreement` is that same delta read as an
efficiency. Four readings, one matrix: the biological witness is not a second two-state
example but the horizon example under biological names, and a change to either file's
delta contradicts this. -/
theorem persistentTransition_contextMatchQuality_agreement_eq_stayKernel
    (x y : BinaryBiologicalState) :
    persistentTransition x y = stayKernel x y ∧
      contextMatchQuality x y = stayKernel x y ∧
        agreement x y = stayKernel x y :=
  ⟨rfl, rfl, rfl⟩

/-- **Complete context switching is the horizon curve's swap kernel**, the off-diagonal
counterpart of the identification above. -/
theorem switchingTransition_eq_swapKernel (x y : BinaryBiologicalState) :
    switchingTransition x y = swapKernel x y := rfl

theorem binaryStateWeight_stationary_persistent (y : BinaryBiologicalState) :
    ∑ x, binaryStateWeight x * persistentTransition x y = binaryStateWeight y := by
  fin_cases y <;>
    norm_num [binaryStateWeight, persistentTransition, Fin.sum_univ_two]

theorem binaryStateWeight_stationary_switching (y : BinaryBiologicalState) :
    ∑ x, binaryStateWeight x * switchingTransition x y = binaryStateWeight y := by
  fin_cases y <;>
    norm_num [binaryStateWeight, switchingTransition, Fin.sum_univ_two]

/-- Target-only performance is identical under persistence and complete switching. -/
theorem targetOnlyPerformance_blind_to_binary_dynamics :
    targetOnlyTransportPerformance binaryStateWeight persistentTransition targetAnnotation =
      targetOnlyTransportPerformance binaryStateWeight switchingTransition targetAnnotation := by
  rw [targetOnlyTransportPerformance_eq_onePoint _ _ _
      binaryStateWeight_stationary_persistent]
  rw [targetOnlyTransportPerformance_eq_onePoint _ _ _
      binaryStateWeight_stationary_switching]

/-- Cross-state performance detects the dynamics: a source-adapted readout is perfect when
the context persists. -/
theorem crossStatePerformance_persistent_eq_one :
    crossStatePerformance binaryStateWeight persistentTransition contextMatchQuality = 1 := by
  norm_num [crossStatePerformance, binaryStateWeight, persistentTransition,
    contextMatchQuality, Fin.sum_univ_two]

/-- The same readout has zero value when the context always switches. -/
theorem crossStatePerformance_switching_eq_zero :
    crossStatePerformance binaryStateWeight switchingTransition contextMatchQuality = 0 := by
  norm_num [crossStatePerformance, binaryStateWeight, switchingTransition,
    contextMatchQuality, Fin.sum_univ_two]

/-! ## The stationarity repair is a descent failure

The repair above says a target-only average cannot see the dynamics.  `Descent.DescentGeometry`
says what kind of statement that is: the target context is a *label*, the two dynamics are two
*populations* on source-target pairs, and a criterion is reportable by target context exactly
when it descends along that label.  The target-only annotation descends; the source-adapted
quality does not.  So the quantity a cross-state criterion measures is a function of the pair
(target context, population), not of the target context — which is why no relabelling of the
target average recovers it. -/

/-- A source-target pair of biological contexts. -/
abbrev TransportPair := BinaryBiologicalState × BinaryBiologicalState

/-- The joint law of source and target contexts under a transition. -/
noncomputable def jointTransportLaw
    (transition : BinaryBiologicalState → BinaryBiologicalState → ℝ) (g : TransportPair) : ℝ :=
  binaryStateWeight g.1 * transition g.1 g.2

/-- Reference evaluation: half the mass of the persistent kernel sits on each diagonal pair. -/
theorem jointTransportLaw_at_reference_point :
    jointTransportLaw persistentTransition (0, 0) = 1 / 2 := by
  norm_num [jointTransportLaw, persistentTransition, binaryStateWeight]


/-- The two-population family: the context persists, or the context switches. -/
noncomputable def binaryTransportFamily (persists : Bool) : TransportPair → ℝ :=
  jointTransportLaw (if persists then persistentTransition else switchingTransition)

/-- Both members of the persistence/switching family are genuine nonnegative finite laws. -/
theorem binaryTransportFamily_nonneg (persists : Bool) (g : TransportPair) :
    0 ≤ binaryTransportFamily persists g := by
  rcases g with ⟨x, y⟩
  cases persists <;> fin_cases x <;> fin_cases y <;>
    norm_num [binaryTransportFamily, jointTransportLaw, binaryStateWeight,
      persistentTransition, switchingTransition]

/-- Target-only performance is the mean of a target-measurable kernel under the joint law. -/
theorem targetOnlyTransportPerformance_eq_conditionalSectionMean
    (transition : BinaryBiologicalState → BinaryBiologicalState → ℝ)
    (score : BinaryBiologicalState → ℝ) :
    targetOnlyTransportPerformance binaryStateWeight transition score =
      conditionalSectionMean (fun g : TransportPair ↦ score g.2)
        (jointTransportLaw transition) := by
  rw [targetOnlyTransportPerformance, conditionalSectionMean, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [jointTransportLaw]
  ring

/-- Cross-state performance is the mean of a kernel that reads both coordinates. -/
theorem crossStatePerformance_eq_conditionalSectionMean
    (transition : BinaryBiologicalState → BinaryBiologicalState → ℝ)
    (quality : BinaryBiologicalState → BinaryBiologicalState → ℝ) :
    crossStatePerformance binaryStateWeight transition quality =
      conditionalSectionMean (fun g : TransportPair ↦ quality g.1 g.2)
        (jointTransportLaw transition) := by
  rw [crossStatePerformance, conditionalSectionMean, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [jointTransportLaw]
  ring

/-- Both dynamics put half the mass on each target context. -/
theorem labelMass_binaryTransportFamily (persists : Bool) (y : BinaryBiologicalState) :
    labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y = 1 / 2 := by
  cases persists <;> fin_cases y <;>
    norm_num [labelMass, binaryTransportFamily, jointTransportLaw, binaryStateWeight,
      persistentTransition, switchingTransition, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Every fiber of either transport family carries mass, so the fiber conditional is
defined at every state.

Both diameter theorems below open by establishing this for `true` and for `false`, and both
did it by rewriting `labelMass_binaryTransportFamily` and calling `norm_num`, twice each.
Stated once, the four copies become four applications. -/
theorem labelMass_binaryTransportFamily_ne_zero (persists : Bool)
    (y : BinaryBiologicalState) :
    labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0 := by
  rw [labelMass_binaryTransportFamily]
  norm_num

/-- A target-only annotation descends along the target context: it is reportable there. -/
theorem descends_targetAnnotation_along_targetState :
    DescendsAlong (fun g : TransportPair ↦ g.2) binaryTransportFamily
      (conditionalSectionMean (fun g : TransportPair ↦ targetAnnotation g.2)) :=
  descendsAlong_sectionMean_of_labelFunction _ binaryTransportFamily targetAnnotation

/-- Under persistence, the source-adapted readout is perfect on every target fiber. -/
theorem contextMatchQuality_value_persistent (y : BinaryBiologicalState) :
    conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily true) y) = 1 := by
  rw [conditionalSectionMean_fiberConditional, labelMass_binaryTransportFamily]
  fin_cases y <;>
    norm_num [binaryTransportFamily, jointTransportLaw, binaryStateWeight, persistentTransition,
      contextMatchQuality, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Under complete switching, the same readout is worthless on the same fiber. -/
theorem contextMatchQuality_value_switching (y : BinaryBiologicalState) :
    conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily false) y) = 0 := by
  rw [conditionalSectionMean_fiberConditional, labelMass_binaryTransportFamily]
  fin_cases y <;>
    norm_num [binaryTransportFamily, jointTransportLaw, binaryStateWeight, switchingTransition,
      contextMatchQuality, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **The cross-state criterion does not descend along the target context.**  No function of the
target context reproduces it across the two dynamics, so a temporal criterion is a function of
the pair (context, population).  The target-only annotation of the previous theorem does descend:
descent, not sensitivity, is what separates the two quantities. -/
theorem not_descends_contextMatchQuality_along_targetState :
  ¬ DescendsAlong (fun g : TransportPair ↦ g.2) binaryTransportFamily
      (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)) := by
  rintro ⟨value, hvalue⟩
  have hpersist := hvalue true 0 (by
    change labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily true) 0 ≠ 0
    rw [labelMass_binaryTransportFamily]
    norm_num)
  have hswitch := hvalue false 0 (by
    change labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily false) 0 ≠ 0
    rw [labelMass_binaryTransportFamily]
    norm_num)
  change conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily true) 0) = value 0
    at hpersist
  change conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily false) 0) = value 0
    at hswitch
  rw [contextMatchQuality_value_persistent 0] at hpersist
  rw [contextMatchQuality_value_switching 0] at hswitch
  rw [← hpersist] at hswitch
  norm_num at hswitch

/-- The largest change in source-adapted context-match quality across supported biological
dynamics at one target state.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite section oscillation. -/
noncomputable def contextMatchSectionOscillation (y : BinaryBiologicalState) : ℝ :=
  finiteSectionOscillation
    (fun persists y ↦
      labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
    (fun persists y ↦
      fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
    (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2))
    (fun a b : ℝ ↦ |a - b|) y

/-- The total-variation diameter of supported dynamics on one biological target-state fiber.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite section diameter. -/
noncomputable def contextMatchTotalVariationDiameter (y : BinaryBiologicalState) : ℝ :=
  finiteSectionDiameter
    (fun persists y ↦
      labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
    (fun persists y ↦
      fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
    totalVariationGap y

/-- **Sharp range-sensitive portability bound for the two-dynamics family.**  Across persistence
and switching, the largest observable change in source-adapted quality on a target-state fiber is
bounded by half the `ℓ¹` total-variation diameter.  The factor `1/2` uses both facts that the fiber
conditionals are probability laws and that quality lies in `[0,1]`; the cruder sup-norm argument
loses this factor.  The maximum is over the whole finite family, not a pointwise restatement. -/
theorem contextMatch_sectionOscillation_le_half_totalVariationDiameter
    (y : BinaryBiologicalState) :
    contextMatchSectionOscillation y ≤ contextMatchTotalVariationDiameter y / 2 := by
  unfold contextMatchSectionOscillation contextMatchTotalVariationDiameter
  apply finiteSectionOscillation_le_modulus_diameter
      (omega := fun t ↦ t / 2) (x := y)
  · exact totalVariationGap_nonneg
  · intro s t hst
    linarith
  · norm_num
  · intro persists switches hpersist hswitch
    have hquality : ∀ g : TransportPair,
        0 ≤ contextMatchQuality g.1 g.2 ∧ contextMatchQuality g.1 g.2 ≤ 1 := by
      rintro ⟨x, z⟩
      fin_cases x <;> fin_cases z <;> norm_num [contextMatchQuality]
    have hbound := abs_sectionMean_sub_le_half_range
      (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily switches) y)
      0 1 hquality
      (sum_fiberConditional (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily persists) y hpersist)
      (sum_fiberConditional (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily switches) y hswitch)
    simpa [div_eq_mul_inv, mul_comm] using hbound

/-- The two biological conditionals are opposite point masses on every target fiber, so their
`ℓ¹` total-variation diameter is exactly two. -/
theorem contextMatch_totalVariationDiameter_eq_two (y : BinaryBiologicalState) :
    contextMatchTotalVariationDiameter y = 2 := by
  unfold contextMatchTotalVariationDiameter
  apply le_antisymm
  · apply finiteSectionDiameter_le_of_pairwise
      (supported := fun persists y ↦
        labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
      (conditionalSection := fun persists y ↦
        fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
      (rho := totalVariationGap) (x := y) (C := 2) (by norm_num)
    intro persists switches hpersist hswitch
    apply totalVariationGap_le_two_of_probabilityMasses
    · intro g
      exact fiberConditional_nonneg (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily persists) y (binaryTransportFamily_nonneg persists) hpersist g
    · intro g
      exact fiberConditional_nonneg (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily switches) y (binaryTransportFamily_nonneg switches) hswitch g
    · exact sum_fiberConditional (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily persists) y hpersist
    · exact sum_fiberConditional (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily switches) y hswitch
  · have hpersist := labelMass_binaryTransportFamily_ne_zero true y
    have hswitch := labelMass_binaryTransportFamily_ne_zero false y
    have hlower := sectionPairDistance_le_finiteSectionDiameter
      (fun persists y ↦
        labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
      (fun persists y ↦
        fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
      totalVariationGap y true false hpersist hswitch
    have hgap :
        totalVariationGap
          (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily true) y)
          (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily false) y) = 2 := by
      fin_cases y <;>
        norm_num [totalVariationGap, fiberConditional, labelMass, binaryTransportFamily,
          jointTransportLaw, binaryStateWeight, persistentTransition, switchingTransition,
          Fintype.sum_prod_type, Fin.sum_univ_two]
    rwa [hgap] at hlower

/-- **The quantitative obstruction is attained.**  On every target state the source-adapted
readout changes from one under persistence to zero under switching, so the section oscillation is
exactly one.  Together with `contextMatch_totalVariationDiameter_eq_two`, this proves equality in
the sharp range-sensitive bound above rather than merely exhibiting non-descent. -/
theorem contextMatch_sectionOscillation_eq_one (y : BinaryBiologicalState) :
    contextMatchSectionOscillation y = 1 := by
  unfold contextMatchSectionOscillation
  apply le_antisymm
  · calc
      finiteSectionOscillation
          (fun persists y ↦
            labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
          (fun persists y ↦
            fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
          (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2))
          (fun a b : ℝ ↦ |a - b|) y ≤
          finiteSectionDiameter
            (fun persists y ↦
              labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
            (fun persists y ↦
              fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
            totalVariationGap y / 2 :=
        contextMatch_sectionOscillation_le_half_totalVariationDiameter y
      _ = 1 := by
        change contextMatchTotalVariationDiameter y / 2 = 1
        rw [contextMatch_totalVariationDiameter_eq_two]
        norm_num
  · have hpersist := labelMass_binaryTransportFamily_ne_zero true y
    have hswitch := labelMass_binaryTransportFamily_ne_zero false y
    have hlower := sectionPairValueDistance_le_finiteSectionOscillation
      (fun persists y ↦
        labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
      (fun persists y ↦
        fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
      (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2))
      (fun a b : ℝ ↦ |a - b|) y true false hpersist hswitch
    rw [contextMatchQuality_value_persistent y, contextMatchQuality_value_switching y] at hlower
    norm_num at hlower ⊢
    exact hlower

/-! ## Continuum-calibration core, instantiated in biology -/

/-- With no information favoring persistence over switching after observing the target context,
the posterior on the two biological dynamics is uniform. -/
noncomputable def binaryDynamicsPosterior
    (_ : BinaryBiologicalState) (_ : Bool) : ℝ := 1 / 2

/-- The uninformative dynamics posterior is the canonical balanced calibration weight. -/
@[simp] theorem binaryDynamicsPosterior_eq_balancedBinaryWeight
    (y : BinaryBiologicalState) (persists : Bool) :
    binaryDynamicsPosterior y persists = balancedBinaryWeight persists := by
  rfl

/-- Conditional source-adapted quality for one dynamics and one target context, constructed from
the same fiber conditional used by the descent theorem above. -/
noncomputable def binaryConditionalContextMatch
    (persists : Bool) (y : BinaryBiologicalState) : ℝ :=
  conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
    (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)

/-- The constructed conditional-quality field is one for persistence and zero for switching. -/
@[simp] theorem binaryConditionalContextMatch_eq_indicator
    (persists : Bool) (y : BinaryBiologicalState) :
    binaryConditionalContextMatch persists y = if persists then 1 else 0 := by
  cases persists
  · simp [binaryConditionalContextMatch, contextMatchQuality_value_switching]
  · simp [binaryConditionalContextMatch, contextMatchQuality_value_persistent]

/-- The binary dynamics posterior is normalized on every biological target context. -/
theorem binaryDynamicsPosterior_sum_eq_one (y : BinaryBiologicalState) :
    ∑ persists, binaryDynamicsPosterior y persists = 1 := by
  norm_num [binaryDynamicsPosterior]

/-- Pooling persistence and switching makes the source-adapted quality look exactly one-half on
every target context.  This is the posterior-mean predictor of the calibration core. -/
theorem posteriorMean_binaryConditionalContextMatch_eq_half (y : BinaryBiologicalState) :
    posteriorMean binaryDynamicsPosterior binaryConditionalContextMatch y = 1 / 2 := by
  norm_num [posteriorMean, binaryDynamicsPosterior]

/-- **Biological drift defect.**  Persistence has conditional quality one and switching has
quality zero, while the pooled posterior mean is one-half.  Averaging across the two target
contexts leaves an irreducible squared index-wise calibration defect of exactly `1/4`. -/
theorem binaryContextMatch_calibrationDriftDefectSq_eq_quarter :
    calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch = 1 / 4 := by
  have hposterior : binaryDynamicsPosterior =
      twoIndexPosterior (fun _ : BinaryBiologicalState ↦ 1 / 2) := by
    funext y persists
    cases persists <;> norm_num [binaryDynamicsPosterior, twoIndexPosterior]
  have hconditional : binaryConditionalContextMatch =
      twoIndexConditional (fun _ : BinaryBiologicalState ↦ 1)
        (fun _ : BinaryBiologicalState ↦ 0) := by
    funext persists y
    rw [binaryConditionalContextMatch_eq_indicator]
    cases persists <;> norm_num [twoIndexConditional]
  rw [hposterior, hconditional, twoIndex_calibrationDriftDefectSq_eq]
  norm_num [binaryStateWeight, Fin.sum_univ_two]

/-- **The biological defect is pairwise disagreement.**  The quarter-unit portability loss is
exactly half the expected squared quality difference between two independent posterior draws of
the biological dynamics, averaged over target contexts.  Thus the binary persistence/switching
calculation is a concrete face of the arbitrary finite-population pairwise drift law rather than
an isolated two-state formula. -/
theorem binaryContextMatch_pairwiseCalibrationDriftEnergy_eq_quarter :
    pairwiseCalibrationDriftEnergy binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch = 1 / 4 := by
  rw [← calibrationDriftDefectSq_eq_pairwiseCalibrationDriftEnergy
    binaryStateWeight binaryDynamicsPosterior binaryConditionalContextMatch
    binaryDynamicsPosterior_sum_eq_one]
  exact binaryContextMatch_calibrationDriftDefectSq_eq_quarter

/-- At each target context, the same pairwise disagreement price is already `1/4`; averaging over
contexts does not create the obstruction, it only preserves a pointwise ancestry/dynamics defect. -/
theorem binaryContextMatch_posteriorPairwiseDriftEnergy_eq_quarter
    (y : BinaryBiologicalState) :
    posteriorPairwiseDriftEnergy binaryDynamicsPosterior
      binaryConditionalContextMatch y = 1 / 4 := by
  rw [posteriorPairwiseDriftEnergy_eq_posteriorDriftEnergy
    binaryDynamicsPosterior binaryConditionalContextMatch y
    (binaryDynamicsPosterior_sum_eq_one y)]
  norm_num [posteriorDrift, posteriorMean_binaryConditionalContextMatch_eq_half,
    binaryDynamicsPosterior]

/-- A sealed support boundary: the deployed population contains only persistent dynamics and
assigns zero posterior mass to switching dynamics.  The conditional field is unchanged; only its
represented support changes. -/
noncomputable def persistentOnlyDynamicsPosterior
    (_ : BinaryBiologicalState) (persists : Bool) : ℝ := binarySecondAnnotation persists

/-- The support-sealed biological posterior remains normalized. -/
theorem persistentOnlyDynamicsPosterior_sum_eq_one (y : BinaryBiologicalState) :
    ∑ persists, persistentOnlyDynamicsPosterior y persists = 1 := by
  norm_num [persistentOnlyDynamicsPosterior, binarySecondAnnotation]

/-- Its posterior masses are nonnegative. -/
theorem persistentOnlyDynamicsPosterior_nonnegative
    (y : BinaryBiologicalState) (persists : Bool) :
    0 ≤ persistentOnlyDynamicsPosterior y persists := by
  cases persists <;> norm_num [persistentOnlyDynamicsPosterior, binarySecondAnnotation]

/-- **Biological sealing law at zero support.**  Persistence and switching still have conditional
qualities one and zero, but after switching receives zero posterior mass the calibration defect is
exactly zero.  This is not conditional invariance; it is categorical blindness created by the
support wall, and it is certified by the general support-aware theorem. -/
theorem persistentOnly_contextMatch_calibrationDriftDefectSq_eq_zero :
    calibrationDriftDefectSq binaryStateWeight persistentOnlyDynamicsPosterior
      binaryConditionalContextMatch = 0 := by
  apply (calibrationDriftDefectSq_eq_zero_iff_on_support
    binaryStateWeight persistentOnlyDynamicsPosterior binaryConditionalContextMatch
    (fun y ↦ by norm_num [binaryStateWeight])
    persistentOnlyDynamicsPosterior_sum_eq_one
    persistentOnlyDynamicsPosterior_nonnegative).mpr
  intro y _ s t hs ht
  cases s
  · norm_num [persistentOnlyDynamicsPosterior, binarySecondAnnotation] at hs
  · cases t
    · norm_num [persistentOnlyDynamicsPosterior, binarySecondAnnotation] at ht
    · rfl

/-! ## Finite correction cannot recover a pooled biological contrast -/

/-- Pool the two biological dynamics into one unlabeled observation.  The sum is intentionally
unnormalized: its kernel, not its scale, is the information boundary. -/
noncomputable def dynamicsPoolingObservation : (Bool → ℝ) →ₗ[ℝ] ℝ where
  toFun β := β false + β true
  map_add' β γ := by simp; ring
  map_smul' c β := by simp; ring

/-- The persistence-versus-switching contrast erased by pooling. -/
noncomputable def dynamicsContrast : Bool → ℝ := fun persists ↦ if persists then 1 else -1

/-- Pooling annihilates the biological dynamics contrast exactly. -/
theorem dynamicsContrast_mem_pooling_kernel :
    dynamicsContrast ∈ LinearMap.ker dynamicsPoolingObservation := by
  rw [LinearMap.mem_ker]
  norm_num [dynamicsPoolingObservation, dynamicsContrast]

/-- **Uniform finite-order correction barrier in biology.**  Every correction assembled from any
nonempty finite dictionary of post-processors acts through the pooled observation, hence erases the
persistence/switching contrast.  Increasing the dictionary order cannot restore information that
pooling removed. -/
theorem every_uniform_pooled_correction_erases_dynamicsContrast
    (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : C ∈ UniformCorrectionFamily dynamicsPoolingObservation k) :
    C dynamicsContrast = 0 := by
  apply factorsThrough_apply_eq_zero_of_mem_ker dynamicsPoolingObservation C
  · exact uniformCorrectionFamily_subset_factorsThrough dynamicsPoolingObservation k hC
  · exact dynamicsContrast_mem_pooling_kernel

/-- Adaptive coefficients do not rescue the contrast either: every vector they can synthesize from
the pooled contrast is zero. -/
theorem adaptive_pooled_correctionSet_dynamicsContrast_eq_zero
    (k : ℕ) (T : Fin k → ℝ →ₗ[ℝ] (Bool → ℝ)) :
    adaptiveCorrectionSet dynamicsPoolingObservation T dynamicsContrast = {0} :=
  adaptiveCorrectionSet_of_mem_ker dynamicsPoolingObservation T dynamicsContrast
    dynamicsContrast_mem_pooling_kernel

/-- The pooled correction residual is the entire contrast, not merely a positive lower bound. -/
theorem uniform_pooled_correction_residual_eq_dynamicsContrast
    (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : C ∈ UniformCorrectionFamily dynamicsPoolingObservation k) :
    dynamicsContrast - C dynamicsContrast = dynamicsContrast := by
  rw [every_uniform_pooled_correction_erases_dynamicsContrast k C hC]
  exact sub_zero _

/-- The correction-theory contrast is exactly twice the calibration drift field of the biological
context-match example.  This equality wires the two obstruction theories to the same biological
direction rather than merely placing their theorems in one file. -/
theorem dynamicsContrast_eq_two_mul_contextMatchDrift
    (persists : Bool) (y : BinaryBiologicalState) :
    dynamicsContrast persists =
      2 * posteriorDrift binaryDynamicsPosterior binaryConditionalContextMatch persists y := by
  cases persists <;>
    norm_num [dynamicsContrast, posteriorDrift,
      posteriorMean_binaryConditionalContextMatch_eq_half]

/-- Broadcast one pooled scalar equally back to the two biological dynamics.  The factor `1/2`
undoes the unnormalized sum in `dynamicsPoolingObservation`. -/
noncomputable def dynamicsBroadcast : ℝ →ₗ[ℝ] (Bool → ℝ) where
  toFun z := fun _ ↦ z / 2
  map_add' z w := by funext persists; dsimp; ring
  map_smul' c z := by funext persists; dsimp; ring

/-- The shared biological mode, invariant between persistence and switching. -/
noncomputable def dynamicsCommonMode (persists : Bool) : ℝ :=
  binaryFirstAnnotation persists + binarySecondAnnotation persists

/-- Reference evaluations: the common mode is one in both Boolean states, which is exactly why
it carries no contrast. -/
theorem dynamicsCommonMode_at_reference_point :
    dynamicsCommonMode true = 1 ∧ dynamicsCommonMode false = 1 := by
  constructor <;> norm_num [dynamicsCommonMode, binaryFirstAnnotation, binarySecondAnnotation]


/-- Pooling followed by broadcasting recovers the common mode exactly. -/
theorem dynamicsBroadcast_pooling_commonMode :
    dynamicsBroadcast (dynamicsPoolingObservation dynamicsCommonMode) =
      dynamicsCommonMode := by
  funext persists
  cases persists <;>
    norm_num [dynamicsBroadcast, dynamicsPoolingObservation, dynamicsCommonMode,
      binaryFirstAnnotation, binarySecondAnnotation]

/-- The common mode is a nonzero eigen-direction of the pooled correction. -/
theorem dynamicsCommonMode_mem_nonzeroCorrectionEigencone :
    dynamicsCommonMode ∈
      NonzeroCorrectionEigencone dynamicsPoolingObservation dynamicsBroadcast := by
  exact ⟨1, one_ne_zero, by
    simpa using dynamicsBroadcast_pooling_commonMode⟩

/-- **Thin-class phase change in biology.**  The same one-term adaptive dictionary that cannot
produce any part of `dynamicsContrast` recovers `dynamicsCommonMode` exactly.  Adaptivity is thus
not generically weak or strong: it is exact on the observable eigencone and absolutely blind on
the pooled kernel. -/
theorem dynamicsCommonMode_mem_adaptive_pooled_correctionSet :
    dynamicsCommonMode ∈ adaptiveCorrectionSet dynamicsPoolingObservation
      (fun _ : Fin 1 ↦ dynamicsBroadcast) dynamicsCommonMode :=
  mem_adaptiveCorrectionSet_singleton_of_mem_nonzeroEigencone
    dynamicsPoolingObservation dynamicsBroadcast dynamicsCommonMode
    dynamicsCommonMode_mem_nonzeroCorrectionEigencone

/-- The biological conditional-quality field decomposes into one half common mode plus one half
contrast.  Pooling retains the former and erases the latter. -/
theorem binaryConditionalContextMatch_eq_half_common_add_contrast
    (persists : Bool) (y : BinaryBiologicalState) :
    binaryConditionalContextMatch persists y =
      (1 / 2) * dynamicsCommonMode persists + (1 / 2) * dynamicsContrast persists := by
  cases persists <;>
    norm_num [binaryConditionalContextMatch_eq_indicator, dynamicsCommonMode, dynamicsContrast,
      binaryFirstAnnotation, binarySecondAnnotation]

/-- **The calibration price is one quarter of squared section oscillation.**  This identifies the
`L²` posterior-field obstruction with the sharp functional-descent geometry in the same biological
model, rather than merely evaluating the two theories on unrelated witnesses. -/
theorem binaryContextMatch_calibrationDriftDefectSq_eq_quarter_oscillationSq
    (y : BinaryBiologicalState) :
    calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch =
        (1 / 4) * contextMatchSectionOscillation y ^ 2 := by
  rw [binaryContextMatch_calibrationDriftDefectSq_eq_quarter,
    contextMatch_sectionOscillation_eq_one]
  norm_num

/-- **Equivalent total-variation price.**  Since the two biological fibers are maximally
separated in total variation, the same obstruction is one sixteenth of the squared fiber
diameter. -/
theorem binaryContextMatch_calibrationDriftDefectSq_eq_sixteenth_tvDiameterSq
    (y : BinaryBiologicalState) :
    calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch =
        (1 / 16) * contextMatchTotalVariationDiameter y ^ 2 := by
  rw [binaryContextMatch_calibrationDriftDefectSq_eq_quarter,
    contextMatch_totalVariationDiameter_eq_two]
  norm_num

/-- The pooled predictor is perfectly aggregate-calibrated in the persistence/switching model. -/
theorem binaryContextMatch_aggregateCalibrationEnergy_eq_zero :
    aggregateCalibrationEnergy binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch
      (posteriorMean binaryDynamicsPosterior binaryConditionalContextMatch) = 0 :=
  aggregateCalibrationEnergy_posteriorMean _ _ _

/-- **No aggregate/index-wise trade-off in the biological model.**  The same pooled predictor
that has zero aggregate error has index-wise energy exactly `1/4`, the drift defect.  This is the
finite biological realization of the continuum program's central Pythagorean obstruction. -/
theorem binaryContextMatch_indexWiseCalibrationEnergy_eq_quarter :
    indexWiseCalibrationEnergy binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch
      (posteriorMean binaryDynamicsPosterior binaryConditionalContextMatch) = 1 / 4 := by
  rw [indexWiseCalibrationEnergy_posteriorMean_eq_driftDefectSq
    binaryStateWeight binaryDynamicsPosterior binaryConditionalContextMatch
    binaryDynamicsPosterior_sum_eq_one]
  exact binaryContextMatch_calibrationDriftDefectSq_eq_quarter

/-! ## The adaptation time and the transport time are one time -/

/-- **A single-rate integrated autocorrelation time is the inverse-dissipation frontier
time.**

`DirichletTransfer.autocorrTime` is `Σ wᵢ / λᵢ`, the time the value signal stays informative;
`CirculationDefect.frontierTime` is `1 / s`, the time scale a transfer frontier runs on. At
one mode of unit weight they are the same number, and that is what puts the two layers of
this dictionary on one clock: the cost of adapting a readout to `θ(x)` is measured in the
units the transport frontier is measured in.

The link matters because `CirculationDefect` proves that a mixing diagnostic *understates*
`frontierTime` whenever the demography circulates, by the factor `1 + (a/s)²`. Through this
identity that understatement is an understatement of the adaptation time too, rather than a
fact about a separate quantity that happens to be written the same way. -/
theorem autocorrTime_singleton_eq_frontierTime {ι : Type*} (i : ι) (lam : ι → ℝ) :
    autocorrTime {i} (fun _ ↦ (1 : ℝ)) lam = frontierTime (lam i) := by
  unfold autocorrTime frontierTime
  simp

/-! ## Geometry and effect recovery are separate gates -/

/-- The observable covariance geometry and the biological effect field require different
conditions.  Invertibility transfers generalized eigenvalues to the precision pencil, while
effect identification is exactly transversality against the declared nuisance class.  The
conjunction prevents either condition from being silently used as a substitute for the
other. -/
theorem geometry_and_effect_recovery_gates
    {n Context Probe Param : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (lambda : ℝ)
    (hA : IsUnit A.det) (hB : IsUnit B.det)
    (M : ObservationModel Context Probe Param) :
    ((B - lambda • A).det = 0 ↔ (A⁻¹ - lambda • B⁻¹).det = 0) ∧
      (Identifiable M ↔
        ∀ theta theta' h h', h ∈ M.nuisance → h' ∈ M.nuisance →
          actionGap M theta theta' = (fun x p ↦ h' x p - h x p) → theta = theta') := by
  exact ⟨covariancePencil_det_zero_iff_precisionPencil_det_zero A B lambda hA hB,
    identifiable_iff_transversal M⟩

/-! ## The obstruction bundle -/

/-- Twenty-four logically distinct failures and boundaries that a biological transport theory must
not collapse into one scalar "portability" parameter.  The final six fields make continuum
calibration and finite correction part of the core theorem rather than adjacent examples. -/
structure DynamicsObstructions : Prop where
  /-- Stationary target averaging cannot distinguish persistence from switching. -/
  targetOnlyBlind :
    targetOnlyTransportPerformance binaryStateWeight persistentTransition targetAnnotation =
      targetOnlyTransportPerformance binaryStateWeight switchingTransition targetAnnotation
  /-- A source-target criterion does distinguish them. -/
  crossStateSeparates :
    crossStatePerformance binaryStateWeight persistentTransition contextMatchQuality ≠
      crossStatePerformance binaryStateWeight switchingTransition contextMatchQuality
  /-- Coordinate marginals do not determine the joint biological field law. -/
  marginalsLoseDependence :
    (∀ omega : Bool, coupledBinarySource omega 0 = coupledBinarySource omega 1) ∧
      (∀ omega : Bool, coordinatewiseMarginalPreserver omega 0 ≠
        coordinatewiseMarginalPreserver omega 1)
  /-- At rank two, value allocation can conflict maximally even in a common eigenbasis. -/
  commutingAllocationConflict : (2 : ℝ) < 3 ∧ (3 : ℝ) / 10 < 2 / 1
  /-- Shared local genomic geometry leaves a positive mixed fourth path moment. -/
  sharedGeometryNotFree :
    0 < 2 * (1 : ℝ) * 1 + 4 * (0 : ℝ) ^ 2 * 0 ^ 2
  /-- Equal LD eigenvalues do not determine the third-order orientation invariant in the locus
  basis where the effect-size prior factorizes. -/
  isospectralLDLosesOrientation :
    Isospectral2 (localizedCovarianceBlock (3 / 2))
        (rotatedCovarianceBlock (3 / 2)) ∧
      blockEntryCubeMean (localizedCovarianceBlock (3 / 2)) ≠
        blockEntryCubeMean (rotatedCovarianceBlock (3 / 2))
  /-- Under the centered sparse architecture, that missing LD orientation changes the cubic
  low-SNR information coefficient by exactly `11 / 24`. -/
  skewedLDChangesLowSNRCoefficient :
    ∀ aspect m1 m2 m3 : ℝ,
      lowSNRThirdCoefficient aspect 2 2 m1 m2 m3
          (blockEntryCubeMean (rotatedCovarianceBlock (3 / 2))) -
        lowSNRThirdCoefficient aspect 2 2 m1 m2 m3
          (blockEntryCubeMean (localizedCovarianceBlock (3 / 2))) = 11 / 24
  /-- Coding-symmetric sparse architectures still lose LD orientation: the third-order term
  vanishes, but the exactly isospectral blocks differ in their fourth-cumulant invariant. -/
  symmetricSparseLDLosesOrientation :
    Isospectral2 (localizedCovarianceBlock (3 / 2))
        (rotatedCovarianceBlock (3 / 2)) ∧
      blockEntryFourthMean (localizedCovarianceBlock (3 / 2)) ≠
        blockEntryFourthMean (rotatedCovarianceBlock (3 / 2))
  /-- For a coding-symmetric Rademacher architecture, the missing LD orientation changes the
  fourth-order low-SNR information coefficient by exactly `49 / 96`. -/
  symmetricLDChangesLowSNRCoefficient :
    ∀ c m1 m2 m3 m4 : ℝ,
      lowSNRFourthCoefficient c 1 (-2) m1 m2 m3 m4 rotatedUniformFourthInvariant -
          lowSNRFourthCoefficient c 1 (-2) m1 m2 m3 m4 localizedUniformFourthInvariant =
        49 / 96
  /-- Both signs of a strong sparse-LD direction have a population gap, while a balanced
  environment mixture cancels it. -/
  environmentMixtureClosesPopulationGap :
    populationGapCertificate (4 / 5) < 0 ∧
      populationGapCertificate (-(4 / 5)) < 0 ∧
      populationGapCertificate (ancestryMixtureCorrelation (4 / 5) (1 / 2)) = 1
  /-- Equal-sign active LD cannot be diluted by mixing; the explicit closure theorem is a
  sign-cancellation result. -/
  sameSignEnvironmentPoolingDoesNotMoveGapParameter :
    ∀ rho mix : ℝ, pooledEnvironmentCorrelation rho rho mix = rho
  /-- Five demographic epochs already reduce root-sample spectrum estimation to a
  `sampleSize⁻¹ᐟ¹⁴` history-reconstruction exponent. -/
  fiveEpochDemographyIsSeverelyIllConditioned :
    fixedEpochSampleRateExponent 5 = 1 / 14
  /-- Kingman's complete rate ladder has the convergent reciprocal sum behind the all-sample
  Müntz obstruction, and every finite spectrum has an explicit rank null direction. -/
  kingmanSpectrumHasIdentifiabilityBoundary :
    Summable (fun k : ℕ ↦
      1 / SpectrumIdentifiability.coalescentRate (k + 2)) ∧
      ∀ n : ℕ, ∀ observation : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ),
        ∃ direction : Fin (n + 1) → ℝ,
          direction ≠ 0 ∧ observation direction = 0
  /-- Normalized pairwise genealogy is speed-blind, while the three-lineage merger rate exactly
  recovers the speed-bias parameter. -/
  speedConditionedGenealogyNeedsThreeLineages :
    ∀ β : ℝ, speedTiltBetaMergerRate β 2 2 = 1 ∧
      speedBiasParameterFromTripleRate (speedTiltBetaMergerRate β 3 3) = β
  /-- The universal branching-front object is a marked successful-family measure: its weighted
  fraction projection gives every unconditioned merger rate, while zero tilt recovers that
  projection exactly. -/
  markedSuccessfulFamilyMeasureDeterminesGenealogy :
    ∀ (ν : MeasureTheory.Measure SuccessfulFamilyMark) (b k : ℕ),
      2 ≤ k →
        speedTiltedGenealogyMeasure 0 ν = genealogyMeasure ν ∧
          markedEventMergerRate ν b k = markedLambdaMergerRate ν b k
  /-- General successful events are complete mass partitions.  Their collision-weighted marked
  measure is the `Ξ` genealogy law, and collision integrability controls every fixed sample. -/
  markedMassPartitionMeasureDeterminesXi :
    ∀ (n : ℕ) (ν : MeasureTheory.Measure MarkedMassPartition),
      HasFiniteCollisionIntensity ν →
        speedTiltedXiMeasure 0 ν = xiMeasure ν ∧
          samplePartitionChangeRateBound n ν < ⊤
  /-- A complete front trajectory cannot identify whether a sweep has one origin or two: the
  collision rate changes and only the two-origin mechanism admits a simultaneous pair-pair
  merger. -/
  frontTrajectoryDoesNotDetermineXi :
    ∀ x : ℝ, x ≠ 0 →
      paintboxWeight ![x] ≠ paintboxWeight ![x / 2, x / 2] ∧
        disjointPairMergeProbability ![x] = 0 ∧
          0 < disjointPairMergeProbability ![x / 2, x / 2]
  /-- Rank-one two-colour response gives the pioneer fraction and logarithmic amplitude repair
  exactly; the remaining hard-selection obstruction is the uniform probabilistic estimate. -/
  twoColourPioneerResponseIsExact :
    ∀ conversion gamma w : ℝ, conversion ≠ 0 → gamma ≠ 0 → -1 < w →
      conversion * w / (conversion * 1 + conversion * w) = pioneerWeightFraction w ∧
        Real.exp (-(gamma * pioneerWeightDisplacement gamma w)) * (1 + w) = 1
  /-- The critical log-mgf transform has unit additive mass and zero centered derivative mass. -/
  branchingRandomWalkBoundaryTransformIsCritical :
    ∀ logMgf logMgfDerivative criticalParameter criticalSpeed : ℝ,
      criticalParameter * criticalSpeed - logMgf = Real.log 2 →
      criticalSpeed = logMgfDerivative →
        boundaryTiltMass logMgf criticalParameter criticalSpeed = 1 ∧
          boundaryTiltCenteredFirstMoment
            logMgf logMgfDerivative criticalParameter criticalSpeed = 0
  /-- Selected derivative flux gives the one-breakout scale and a quadratic two-breakout bound. -/
  selectedDerivativeFluxControlsBreakouts :
    ∀ (Pioneer : Type) [Fintype Pioneer] [DecidableEq Pioneer]
      (tailConstant threshold blockScale fluxConstant : ℝ)
      (weight : Pioneer → ℝ),
      0 ≤ tailConstant → 0 < threshold →
      (∀ pioneer, 0 ≤ weight pioneer) →
      selectedPioneerFlux weight = blockScale * fluxConstant →
        (∑ pioneer,
            paretoExceedanceMass tailConstant threshold (weight pioneer)) =
            blockScale * (tailConstant * fluxConstant / threshold) ∧
          distinctPairExceedanceMass
              (fun pioneer ↦ paretoExceedanceMass
                tailConstant threshold (weight pioneer)) ≤
            (blockScale * (tailConstant * fluxConstant / threshold)) ^ 2
  /-- A full-tree flux law transfers exactly when the flux discarded by selection vanishes. -/
  selectedPioneerFluxFollowsFromNegligiblePruning :
    ∀ (fullTreeFlux selectedFlux prunedFlux : ℕ → ℝ) (fluxConstant : ℝ),
      IsSelectedFluxDecomposition fullTreeFlux selectedFlux prunedFlux →
      Filter.Tendsto fullTreeFlux Filter.atTop (nhds fluxConstant) →
      Filter.Tendsto prunedFlux Filter.atTop (nhds 0) →
        Filter.Tendsto selectedFlux Filter.atTop (nhds fluxConstant)
  /-- One pioneer gives one atom pathwise; `w/(1+w)` additionally consumes common-profile
  relaxation, and the amplitude-front response is real-valued even on lattice BRWs. -/
  uniquePioneerCommonProfileDeterminesMarkedResponse :
    ∀ conversion gamma w backgroundCount pioneerCount : ℝ,
      conversion ≠ 0 → backgroundCount + pioneerCount ≠ 0 →
      HasCommonProfileRelaxation conversion 1 w backgroundCount pioneerCount →
        (totalFamilyFraction ![pioneerWeightFraction w] = pioneerWeightFraction w ∧
          paintboxWeight ![pioneerWeightFraction w] = pioneerWeightFraction w ^ 2 ∧
            disjointPairMergeProbability ![pioneerWeightFraction w] = 0) ∧
          pioneerCount / (backgroundCount + pioneerCount) = pioneerWeightFraction w ∧
            amplitudeFront gamma (1 + w) - amplitudeFront gamma 1 =
              pioneerWeightDisplacement gamma w
  /-- Linear pulled clocks and superlinear stable clocks lie on opposite sides of reciprocal
  summability; using this as an identifiability theorem still requires the transform-system
  reduction. -/
  selectedGenealogyHasMuntzRateDichotomy :
    ∀ coefficient alpha : ℝ, 0 < coefficient → 1 < alpha →
      (¬Summable fun n : ℕ ↦
          1 / criticallyPulledLinearRateLadder coefficient n) ∧
        Summable (fun n : ℕ ↦ 1 / stablePowerRateLadder alpha n) ∧
          Summable (fun n : ℕ ↦ 1 / stablePowerRateLadder 2 n)
  /-- The complete uniform procedure-risk signature is sufficient and is
  coarser than every other sufficient genomic design invariant. -/
  genomicAlgorithmicRiskSignatureIsCoarsest :
    ∀ (Algorithm Design Model Loss : Type)
      (risk : Algorithm → Design → Model → Loss → ℝ),
      RiskSignaturesFactorThrough risk (algorithmicRiskSignature risk) ∧
        ∀ (Invariant : Type) (invariant : Design → Invariant),
          RiskSignaturesFactorThrough risk invariant →
            ∀ left right, invariant left = invariant right →
              algorithmicRiskSignature risk left =
                algorithmicRiskSignature risk right
  /-- Positive-even graph-local degrees and handshaking force the full finite
  genomic rank-one traffic correction to vanish. -/
  genomicRankOneTrafficExpansionFollowsFromHandshake :
    ∀ (Term : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ)
      (degree : ∀ term, Fin (vertices term) → ℕ),
      (∀ term, hasOddDegree term = false →
        ∀ vertex, 0 < degree term vertex) →
      (∀ term, hasOddDegree term = false →
        ∀ vertex, Even (degree term vertex)) →
      (∀ term, hasOddDegree term = false →
        ∑ vertex, degree term vertex = 2 * edges term) →
        Filter.Tendsto
          (fun population : ℕ ↦
            finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
              (population + 1))
          Filter.atTop (nhds 0)
  /-- The same concrete balanced matrices simultaneously certify PSD order,
  traffic invisibility, the finite Hamiltonian, ground-state equality, and
  supercritical pressure separation. -/
  positiveLDBalancedRankOneCovarianceHasFullWitness :
    ∀ (Term : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ),
      (∀ term, hasOddDegree term = false → vertices term ≤ edges term) →
      ∀ baseline spikeStrength temperature : ℝ,
        0 ≤ baseline → 0 < spikeStrength →
        1 < temperature * spikeStrength →
          ConcreteBalancedPSDPressureWitness coefficient hasOddDegree vertices edges
            baseline spikeStrength temperature
  /-- A mesoscopic LD block vanishes from every fixed traffic coordinate but has unit normalized
  energy after a logarithmic number of power iterations. -/
  rareLDSubspaceEvadesFixedTrafficAtLogRuntime :
    FixedTrafficLogRuntimeSeparation
  /-- Even degree one can resolve a vanishing mesoscopic LD mass when its
  coefficient grows at the reciprocal traffic resolution. -/
  rareLDSubspaceEvadesLimitingTrafficAtDegreeOne :
    ∀ baseline : ℝ,
      Filter.Tendsto
          (fun iteration ↦ diagonalTrafficCorrection baseline 1 iteration)
          Filter.atTop (nhds 0) ∧
        ∀ iteration,
          amplifiedDegreeOneTrafficDifference baseline iteration = 2
  /-- The genuine finite diagonal iteration realizes the same separation with
  ambient dimension `16^k`, exceptional rank `4^k`, fixed-time decay, and
  unit logarithmic-time normalized output. -/
  rareLDSubspaceConcreteGFOMEvadesFixedTrafficAtLogRuntime :
    ConcreteGFOMLogRuntimeSeparation
  /-- A positive rank-one LD outlier is invisible to every limiting bulk
  spectral observable but changes the spectral maximum and trace-one PSD SDP
  optimum at every finite size. -/
  genomicBulkSpectralLawDoesNotDetermineExtremalSpectrumOrSDP :
    ∀ baseline spikeStrength : ℝ, 0 < spikeStrength →
      BulkSpectralLawExtremalSDPSeparation baseline spikeStrength
  /-- Every finite contracted rank-one LD traffic expansion vanishes, while
  the associated variational pressure is positive above `tλ = 1`. -/
  positiveLDSpikeFixedTrafficInvisibleVariationalPressureVisible :
    ∀ (Term : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ),
      (∀ term, hasOddDegree term = false → vertices term ≤ edges term) →
      ∀ tlam : ℝ, 1 < tlam →
        Filter.Tendsto
            (fun population : ℕ ↦
              finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
                (population + 1))
            Filter.atTop (nhds 0) ∧
          0 < cwVariationalPressureGap tlam
  /-- Every fixed genomic traffic coordinate misses the positive LD spike, but
  its genuine finite Rademacher pressure has a positive uniform lower bound
  throughout the exact supercritical regime, with no LDP premise. -/
  positiveLDSpikeFixedTrafficInvisibleFinitePressureVisible :
    ∀ (Term : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ),
      (∀ term, hasOddDegree term = false → vertices term ≤ edges term) →
      ∀ tlam : ℝ, 1 < tlam →
        RankOneSpikeInvisibleWithFinitePressure
          coefficient hasOddDegree vertices edges tlam
  /-- Every interior magnetisation objective lower-bounds genuine finite
  genomic pressure at each nonempty population. -/
  genomicFiniteCWPressureDominatesVariationalObjective :
    ∀ (population : ℕ) (tlam m : ℝ),
      0 < population → 0 ≤ tlam → |m| < 1 →
        cwObjective tlam m ≤ finiteCWPressureGap population tlam
  /-- Every finite genotype-count type has mass at most one at and below the
  critical LD coupling. -/
  genomicFiniteCWTypeMassLeOneOfSubcritical :
    ∀ (population upSpins : ℕ) (tlam : ℝ),
      tlam ≤ 1 → upSpins ∈ Finset.range (population + 1) →
        finiteCWTypeMass population tlam upSpins ≤ 1
  /-- For nonnegative coupling, the actual finite genomic pressure converges
  to baseline exactly at and below the Curie--Weiss threshold. -/
  genomicFiniteCWPressureHasExactCriticalPoint :
    ∀ tlam : ℝ, 0 ≤ tlam →
      (Filter.Tendsto
          (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
          Filter.atTop (nhds 0) ↔
        tlam ≤ 1)
  /-- The actual finite genomic pressure converges to its full variational LD
  value for all nonnegative couplings. -/
  genomicFiniteCWPressureConvergesToVariational :
    ∀ tlam : ℝ, 0 ≤ tlam →
      Filter.Tendsto
        (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
        Filter.atTop (nhds (cwVariationalPressureGap tlam))
  /-- The full finite genomic pressure limit is uniform over all nonnegative
  LD couplings. -/
  genomicFiniteCWPressureConvergesUniformlyOnNonnegative :
    TendstoUniformlyOn
      (fun population : ℕ ↦ fun tlam : ℝ ↦
        finiteCWPressureGap (population + 1) tlam)
      cwVariationalPressureGap Filter.atTop (Set.Ici 0)
  /-- Every nonempty finite genomic population has globally half-Lipschitz
  pressure in effective coupling. -/
  genomicFiniteCWPressureIsHalfLipschitz :
    ∀ population : ℕ, 0 < population →
      LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal)
        (finiteCWPressureGap population)
  /-- Every nonempty finite genomic population has pressure monotone in
  effective LD coupling. -/
  genomicFiniteCWPressureIsMonotone :
    ∀ population : ℕ, 0 < population →
      Monotone (finiteCWPressureGap population)
  /-- At every nonempty population, the genuine rank-one-spiked genomic
  pressure strictly exceeds the unspiked baseline throughout `tλ > 1`. -/
  positiveLDSpikeFinitePressureExceedsBaseline :
    ∀ (baseline : ℝ) (population : ℕ)
      (temperature spikeStrength : ℝ),
      0 < population → 1 < temperature * spikeStrength →
        finiteBaselineRademacherPressure baseline temperature <
          finiteRankOneRademacherPressure
            baseline population temperature spikeStrength
  /-- The genuine spiked-minus-baseline genomic pressure has exact critical
  effective coupling one. -/
  positiveLDSpikePressureDifferenceHasExactCriticalPoint :
    ∀ baseline temperature spikeStrength : ℝ,
      0 ≤ temperature * spikeStrength →
        FiniteRankOnePressureCriticalStatement baseline temperature spikeStrength
  /-- The complete finite LD-spiked pressure converges to baseline plus its
  variational pressure correction. -/
  positiveLDSpikePressureConvergesToVariational :
    ∀ baseline temperature spikeStrength : ℝ,
      0 ≤ temperature * spikeStrength →
        FiniteRankOnePressureVariationalLimitStatement
          baseline temperature spikeStrength
  /-- At fixed nonnegative temperature, finite LD-spiked pressure converges
  uniformly over all nonnegative spike strengths. -/
  positiveLDSpikePressureConvergesUniformlyOnNonnegativeStrength :
    ∀ baseline temperature : ℝ, 0 ≤ temperature →
      FiniteRankOnePressureUniformLimitStatement baseline temperature
  /-- One positive LD spike simultaneously defeats fixed traffic sufficiency
  and the lower-ground-state characterization. -/
  positiveLDSpikeRefutesTrafficAndGroundStateDichotomies :
    ∀ (Term Genotype : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ),
      (∀ term, hasOddDegree term = false → vertices term ≤ edges term) →
      ∀ (alignment : Genotype → ℝ) (orthogonal aligned : Genotype)
        (baseline spikeStrength population temperature : ℝ),
        0 < spikeStrength → population ≠ 0 →
        alignment orthogonal = 0 → alignment aligned = population →
        1 < temperature * spikeStrength →
          RankOneSpikeRefutesBothDichotomies coefficient hasOddDegree vertices edges
            alignment orthogonal aligned baseline spikeStrength population temperature
  /-- Positive-cone order and the lower genetic ground state do not determine exponential
  pressure: an orthogonal state preserves the minimum while an aligned state separates. -/
  positiveLDSpikeGroundStateDoesNotFixPressure :
    ∀ baseline spikeStrength population tlam : ℝ, 0 ≤ spikeStrength →
      2 * Real.log 2 < tlam →
        ((∀ state : Bool, baseline ≤
            rankOneEnergyDensity baseline spikeStrength population
              (if state = true then population else 0)) ∧
          rankOneEnergyDensity baseline spikeStrength population
            (if false = true then population else 0) = baseline) ∧
          0 < cwObjective tlam 1
  /-- The positive-temperature LD-spike pressure separates at exactly `tλ = 1`. -/
  ldOverlapPressureHasExactCriticalPoint :
    ∀ tlam : ℝ,
      (tlam ≤ 1 → ∀ m : ℝ, |m| ≤ 1 → cwObjective tlam m ≤ 0) ∧
        (1 < tlam → ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m)
  /-- The actual supremal variational pressure gap vanishes exactly at and
  below the Curie--Weiss threshold. -/
  ldVariationalPressureGapHasExactCriticalPoint :
    ∀ tlam : ℝ, cwVariationalPressureGap tlam = 0 ↔ tlam ≤ 1
  /-- The genomic LD pressure profile is globally half-Lipschitz, continuous,
  monotone, and convex in effective coupling. -/
  ldVariationalPressureGapHasGlobalRegularity :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal) cwVariationalPressureGap ∧
      Continuous cwVariationalPressureGap ∧
        Monotone cwVariationalPressureGap ∧
          ConvexOn ℝ Set.univ cwVariationalPressureGap
  /-- The sharp scalar-to-random-design ledger subtracts the sum of two
  independently certified comparison errors. -/
  matchedBayesRandomDesignAsymmetricReduction :
    ∀ scalarLeft scalarRight randomLeft randomRight leftError rightError delta : ℝ,
      |randomLeft - scalarLeft| ≤ leftError →
      |randomRight - scalarRight| ≤ rightError →
      scalarRight - scalarLeft = delta →
        delta - (leftError + rightError) ≤ randomRight - randomLeft
  /-- Scalar matched-channel separation transfers to random design with exactly two comparison
  errors and no hidden constant. -/
  matchedBayesRandomDesignReduction :
    ∀ scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ,
      |randomLeft - scalarLeft| ≤ epsilon →
      |randomRight - scalarRight| ≤ epsilon →
      scalarRight - scalarLeft = delta →
        delta - 2 * epsilon ≤ randomRight - randomLeft
  /-- Independent vanishing comparison bounds on the two designs suffice for
  eventual transfer of every positive scalar gap. -/
  matchedBayesRandomDesignEventuallySeparatesWithAsymmetricErrors :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta : ℝ)
      (randomLeft randomRight leftError rightError : Index → ℝ),
      (∀ index, |randomLeft index - scalarLeft| ≤ leftError index) →
      (∀ index, |randomRight index - scalarRight| ≤ rightError index) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto leftError regime (nhds 0) →
      Filter.Tendsto rightError regime (nhds 0) →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- Every positive scalar matched-channel gap eventually transfers along a
  regime whose random-design comparison error vanishes. -/
  matchedBayesRandomDesignEventuallySeparates :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta : ℝ)
      (randomLeft randomRight comparisonError : Index → ℝ),
      (∀ index, |randomLeft index - scalarLeft| ≤ comparisonError index) →
      (∀ index, |randomRight index - scalarRight| ≤ comparisonError index) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto comparisonError regime (nhds 0) →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- The explicit `constant / sqrt aspectRatio` comparison rate transfers a
  scalar gap once it is below half the gap. -/
  matchedBayesRandomDesignSeparatesAtLargeAspect :
    ∀ scalarLeft scalarRight randomLeft randomRight aspectRatio constant delta : ℝ,
      |randomLeft - scalarLeft| ≤ constant / Real.sqrt aspectRatio →
      |randomRight - scalarRight| ≤ constant / Real.sqrt aspectRatio →
      scalarRight - scalarLeft = delta →
      2 * (constant / Real.sqrt aspectRatio) < delta →
        randomLeft < randomRight
  /-- Every fixed positive scalar gap eventually transfers when aspect ratio
  tends to infinity at the inverse-square-root comparison rate. -/
  matchedBayesRandomDesignEventuallySeparatesAtDivergingAspect :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta constant : ℝ)
      (aspectRatio randomLeft randomRight : Index → ℝ),
      (∀ index,
        |randomLeft index - scalarLeft| ≤ constant / Real.sqrt (aspectRatio index)) →
      (∀ index,
        |randomRight index - scalarRight| ≤ constant / Real.sqrt (aspectRatio index)) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto aspectRatio regime Filter.atTop →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- Diverging aspect and vanishing reciprocal Wishart ratio are the same
  one-sided limit, with identical pointwise comparison-error formulas. -/
  matchedBayesAspectWishartRatioBridge :
    ∀ (Index : Type) (regime : Filter Index)
      (aspectRatio : Index → ℝ) (constant : ℝ),
      (Filter.Tendsto aspectRatio regime Filter.atTop ↔
        Filter.Tendsto (fun index ↦ (aspectRatio index)⁻¹) regime (𝓝[>] 0)) ∧
      (∀ index, constant / Real.sqrt (aspectRatio index) =
        constant * Real.sqrt ((aspectRatio index)⁻¹))
  /-- A genomic comparison error at Wishart scale vanishes with the adjusted
  dimension/sample ratio. -/
  matchedBayesWishartInformationErrorVanishes :
    ∀ (Index : Type) (regime : Filter Index)
      (informationError adjustedRatio : Index → ℝ) (constant : ℝ),
      Filter.Tendsto adjustedRatio regime (nhds 0) →
      (∀ index,
        |informationError index| ≤ constant * Real.sqrt (adjustedRatio index)) →
        Filter.Tendsto informationError regime (nhds 0)
  /-- The two genomic designs may use distinct Wishart constants and ratios;
  independent vanishing transfers the scalar gap. -/
  matchedBayesRandomDesignEventuallySeparatesAtAsymmetricWishartRatios :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta leftConstant rightConstant : ℝ)
      (leftRatio rightRatio randomLeft randomRight : Index → ℝ),
      (∀ index, |randomLeft index - scalarLeft| ≤
        leftConstant * Real.sqrt (leftRatio index)) →
      (∀ index, |randomRight index - scalarRight| ≤
        rightConstant * Real.sqrt (rightRatio index)) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto leftRatio regime (nhds 0) →
      Filter.Tendsto rightRatio regime (nhds 0) →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- Every fixed positive scalar genomic gap transfers at the Wishart rate
  when `(p+1)/n` tends to zero. -/
  matchedBayesRandomDesignEventuallySeparatesAtWishartRatio :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta constant : ℝ)
      (adjustedRatio randomLeft randomRight : Index → ℝ),
      (∀ index,
        |randomLeft index - scalarLeft| ≤
          constant * Real.sqrt (adjustedRatio index)) →
      (∀ index,
        |randomRight index - scalarRight| ≤
          constant * Real.sqrt (adjustedRatio index)) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto adjustedRatio regime (nhds 0) →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- Finite singular-value support, rank, and operator bounds derive the
  normalized genomic nuclear-distance inequality. -/
  matchedBayesSingularSpectrumHasNormalizedNuclearBound :
    ∀ (Coordinate : Type) [Fintype Coordinate] [DecidableEq Coordinate]
      (spectrum : FiniteLowRankSingularSpectrum Coordinate),
      0 < Fintype.card Coordinate →
        spectrum.normalizedNuclearDistance ≤
          spectrum.operatorBound * spectrum.rankFraction
  /-- A concrete bounded rank-one genomic covariance perturbation has
  vanishing certified matched-information effect. -/
  matchedBayesCertifiedRankOnePerturbationIsAsymptoticallyInvisible :
    ∀ (certificate : ℕ → MatchedInformationPathCertificate)
      (varianceBound spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength),
      (∀ population, (certificate population).variance ≤ varianceBound) →
      (∀ population,
        (certificate population).nuclearDistance =
          FiniteLowRankSingularSpectrum.normalizedNuclearDistance
            (finiteRankOneSingularSpectrum population spikeStrength hspike)) →
        Filter.Tendsto
          (fun population ↦ (certificate population).informationPath 1 -
            (certificate population).informationPath 0)
          Filter.atTop (nhds 0)
  /-- Matrix I--MMSE plus posterior-covariance trace control yields the matched
  genomic nuclear Lipschitz estimate. -/
  matchedBayesInformationPathHasNuclearBound :
    ∀ certificate : MatchedInformationPathCertificate,
      |certificate.informationPath 1 - certificate.informationPath 0| ≤
        certificate.variance / 2 * certificate.nuclearDistance
  /-- The I--MMSE, nuclear/Frobenius, and Wishart ledgers imply the exact
  normalized matched-information comparison rate. -/
  matchedBayesHasWishartFrobeniusComparisonRate :
    ∀ dimension sampleSize signal variance operatorBound informationError
      nuclearError frobeniusError : ℝ,
      0 < dimension → 0 < sampleSize → 0 ≤ signal → 0 ≤ variance →
      |informationError| ≤ signal * variance / (2 * dimension) * nuclearError →
      nuclearError ≤ Real.sqrt dimension * frobeniusError →
      frobeniusError ≤ operatorBound *
        Real.sqrt (dimension * ((dimension + 1) / sampleSize)) →
        |informationError| ≤ signal * variance * operatorBound / 2 *
          Real.sqrt ((dimension + 1) / sampleSize)
  /-- The exact Wishart moment identity and trace bounds imply the complete
  normalized matched-information comparison rate. -/
  matchedBayesHasWishartMomentIdentityComparisonRate :
    ∀ dimension sampleSize signal variance operatorBound covarianceTrace
      covarianceTraceSq frobeniusSecondMoment frobeniusError nuclearError
      informationError : ℝ,
      0 < dimension → 0 < sampleSize → 0 ≤ signal → 0 ≤ variance →
      0 ≤ operatorBound →
      |covarianceTrace| ≤ dimension * operatorBound →
      covarianceTraceSq ≤ dimension * operatorBound ^ 2 →
      frobeniusSecondMoment =
        (covarianceTrace ^ 2 + covarianceTraceSq) / sampleSize →
      frobeniusError ≤ Real.sqrt frobeniusSecondMoment →
      nuclearError ≤ Real.sqrt dimension * frobeniusError →
      |informationError| ≤ signal * variance / (2 * dimension) * nuclearError →
        |informationError| ≤ signal * variance * operatorBound / 2 *
          Real.sqrt ((dimension + 1) / sampleSize)
  /-- A certified matched-information family with uniformly bounded prior
  variance and vanishing rank fraction has vanishing information gap. -/
  matchedBayesCertifiedSublinearRankIsInvisibleUnderVarianceBound :
    ∀ (Index : Type) (regime : Filter Index)
      (certificate : Index → MatchedInformationPathCertificate)
      (varianceBound operatorBound : ℝ) (rankFraction : Index → ℝ),
      (∀ index, (certificate index).variance ≤ varianceBound) →
      Filter.Tendsto rankFraction regime (nhds 0) →
      (∀ index,
        (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) →
        MatchedInformationPathGapTendsToZero regime certificate
  /-- Exact common variance is a special case of the uniform-bound result. -/
  matchedBayesCertifiedSublinearRankIsInvisible :
    ∀ (Index : Type) (regime : Filter Index)
      (certificate : Index → MatchedInformationPathCertificate)
      (operatorBound : ℝ) (rankFraction : Index → ℝ),
      (∃ variance : ℝ, ∀ index, (certificate index).variance = variance) →
      Filter.Tendsto rankFraction regime (nhds 0) →
      (∀ index,
        (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) →
        MatchedInformationPathGapTendsToZero regime certificate
  /-- Under the nuclear estimate, a vanishing-rank-fraction genomic covariance
  perturbation has vanishing matched information-density effect. -/
  matchedBayesSublinearRankPerturbationsAreInvisible :
    ∀ (densityGap rankFraction : ℕ → ℝ) (constant : ℝ),
      Filter.Tendsto rankFraction Filter.atTop (nhds 0) →
      (∀ index, |densityGap index| ≤ constant * rankFraction index) →
        Filter.Tendsto densityGap Filter.atTop (nhds 0)
  /-- A positive finite matched-density gap forces a quantitatively extensive
  genomic covariance-rank fraction. -/
  matchedBayesPositiveGapForcesExtensiveRank :
    ∀ densityGap constant rankFraction delta : ℝ,
      0 < constant → 0 < delta → delta ≤ |densityGap| →
      |densityGap| ≤ constant * rankFraction →
        0 < rankFraction ∧ delta / constant ≤ rankFraction
  /-- A certified finite I--MMSE path gap forces the explicit extensive-rank
  lower bound without assuming the final nuclear information estimate. -/
  matchedBayesCertifiedPositiveGapForcesExtensiveRank :
    ∀ (certificate : MatchedInformationPathCertificate)
      (varianceBound operatorBound rankFraction delta : ℝ),
      certificate.variance ≤ varianceBound →
      0 < varianceBound → 0 < operatorBound → 0 < delta →
      delta ≤ |certificate.informationPath 1 - certificate.informationPath 0| →
      certificate.nuclearDistance ≤ operatorBound * rankFraction →
        0 < rankFraction ∧
          delta / (varianceBound * operatorBound / 2) ≤ rankFraction
  /-- Persistent certified I--MMSE path separation forces the exact eventual
  rank lower bound and excludes vanishing rank fraction. -/
  matchedBayesCertifiedPersistentGapRequiresExtensiveRank :
    ∀ (Index : Type) (regime : Filter Index) [regime.NeBot]
      (certificate : Index → MatchedInformationPathCertificate)
      (varianceBound operatorBound delta : ℝ) (rankFraction : Index → ℝ),
      0 < varianceBound → 0 < operatorBound → 0 < delta →
      (∀ index, (certificate index).variance ≤ varianceBound) →
      (∀ index,
        (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) →
      (∀ᶠ index in regime, delta ≤
        |(certificate index).informationPath 1 -
          (certificate index).informationPath 0|) →
        (∀ᶠ index in regime,
          delta / (varianceBound * operatorBound / 2) ≤ rankFraction index) ∧
          ¬ Filter.Tendsto rankFraction regime (nhds 0)
  /-- A persistent matched-density gap forces an eventual positive rank
  fraction and rules out sublinear-rank perturbations. -/
  matchedBayesPersistentGapRequiresExtensiveRank :
    ∀ (Index : Type) (regime : Filter Index) [regime.NeBot]
      (densityGap rankFraction : Index → ℝ) (constant delta : ℝ),
      0 < constant → 0 < delta →
      (∀ᶠ index in regime, delta ≤ |densityGap index|) →
      (∀ index, |densityGap index| ≤ constant * rankFraction index) →
        (∀ᶠ index in regime, delta / constant ≤ rankFraction index) ∧
          ¬ Filter.Tendsto rankFraction regime (nhds 0)
  /-- Every degree-limited genomic risk that factors through a common truncated traffic profile
  inherits the complete Bayes-risk gap on one shared design. -/
  degreeLimitedGenomicRiskHasFullGapHardness :
    ∀ (Algorithm : Type) (D : ℕ) (risk : Algorithm → TruncatedTrafficRisk D)
      (left right : Fin (D + 1) → ℝ), left = right →
      ∀ bayesLeft bayesRight : ℝ,
        (∀ algorithm, bayesRight ≤ (risk algorithm).evaluate right) →
          ∀ algorithm,
            bayesRight - bayesLeft ≤ (risk algorithm).evaluate left - bayesLeft
  /-- Stable low-degree passage is quantitative: traffic resolution is
  multiplied by the coefficient `ℓ¹` mass. -/
  stableDegreeLimitedGenomicRiskHasQuantitativeTrafficBound :
    ∀ (D : ℕ) (risk : TruncatedTrafficRisk D)
      (left right : Fin (D + 1) → ℝ) (epsilon : ℝ),
      (∀ graph, |left graph - right graph| ≤ epsilon) →
        |risk.evaluate left - risk.evaluate right| ≤
          (∑ graph, |risk.coefficient graph|) * epsilon
  /-- Uniform coefficient mass makes quantitative fixed-depth traffic
  convergence sufficient for stable polynomial convergence. -/
  stableDegreeLimitedGenomicRiskConvergesOfBoundedCoefficientMass :
    ∀ (D : ℕ) (risk : ℕ → TruncatedTrafficRisk D)
      (left right : ℕ → Fin (D + 1) → ℝ)
      (discrepancy coefficientBound : ℝ),
      (∀ index graph,
        |left index graph - right index graph| ≤
          discrepancy * (1 / 2 : ℝ) ^ index) →
      (∀ index,
        (∑ graph, |(risk index).coefficient graph|) ≤ coefficientBound) →
      0 ≤ discrepancy →
        Filter.Tendsto
          (fun index ↦ (risk index).evaluate (left index) -
            (risk index).evaluate (right index))
          Filter.atTop (nhds 0)
  /-- In the uniqueness regime, a certified common finite-traffic expansion
  with a geometric tail determines the limiting matched pressure. -/
  highTemperatureGenomicTrafficDeterminesCertifiedPressure :
    ∀ (leftLimit rightLimit C q : ℝ) (commonTruncation : ℕ → ℝ),
      0 ≤ q → q < 1 →
      (∀ depth,
        |leftLimit - commonTruncation depth| ≤
          C * q ^ (depth + 1) / (1 - q)) →
      (∀ depth,
        |rightLimit - commonTruncation depth| ≤
          C * q ^ (depth + 1) / (1 - q)) →
        leftLimit = rightLimit
  /-- The diagonal genomic traffic hierarchy is strictly increasing at every
  finite edge depth, witnessed by probability laws on `[1,2]`. -/
  genomicLDTrafficHierarchyIsStrictAtEveryDegree :
    ∀ D : ℕ,
      ∃ left right : Fin (D + 2) → ℝ,
        IsMomentMatchedProbabilityPair D left right ∧
          SeparatesAtNextDiagonalTraffic D left right
  /-- A single probability pair defeats every truncated graph-polynomial risk
  at each finite depth while differing at the next LD traffic coordinate. -/
  genomicLDTrafficHasCommonBlindPairAtEveryDegree :
    ∀ D : ℕ,
      ∃ left right : Fin (D + 2) → ℝ,
        IsBlindPairForEveryTruncatedTrafficRisk D left right
  /-- Permutation invariance itself, rather than an assumed orbit-constancy
  premise, yields exact finite graph-sum factorization. -/
  permutationInvariantGenomicPolynomialFactorsThroughLDGraphs :
    ∀ (Slot Locus Graph : Type) [Fintype Slot] [DecidableEq Slot]
      [Fintype Locus] [Fintype Graph] [DecidableEq Graph]
      (shape : (Slot → Locus) → Graph)
      (coefficient value : (Slot → Locus) → ℝ),
      (∀ left right, shape left = shape right → SameEqualityPattern left right) →
      (∀ (permutation : Equiv.Perm Locus) monomial,
        coefficient (permutation ∘ monomial) = coefficient monomial) →
        (∑ monomial, coefficient monomial * value monomial) =
          ∑ graph, graphShapeCoefficient shape coefficient graph *
            ∑ monomial, if shape monomial = graph then value monomial else 0
  /-- Canonical unrooted factorization through the quotient by endpoint
  equality pattern requires no caller-supplied graph encoding. -/
  permutationInvariantGenomicPolynomialFactorsThroughCanonicalLDGraphs :
    ∀ (Slot Locus : Type) [Fintype Slot] [DecidableEq Slot] [Fintype Locus]
      (coefficient value : (Slot → Locus) → ℝ),
      (∀ (permutation : Equiv.Perm Locus) monomial,
        coefficient (permutation ∘ monomial) = coefficient monomial) →
        CanonicalTrafficFactorizationStatement coefficient value
  /-- Canonical rooted factorization uses `none` as the output locus and
  `some slot` as matrix-entry endpoint slots. -/
  permutationEquivariantGenomicPolynomialFactorsThroughRootedLDGraphs :
    ∀ (Slot Locus : Type) [Fintype Slot] [DecidableEq Slot] [Fintype Locus]
      (coefficient value : (Option Slot → Locus) → ℝ),
      (∀ (permutation : Equiv.Perm Locus) monomial,
        coefficient (permutation ∘ monomial) = coefficient monomial) →
        RootedCanonicalTrafficFactorizationStatement coefficient value
  /-- The homogeneous decomposition proves exact traffic factorization for
  every scalar genomic polynomial of total degree at most `D`. -/
  degreeLimitedGenomicPolynomialFactorsThroughCanonicalLDGraphs :
    ∀ (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient value : (degree : Fin (D + 1)) →
        ((Fin (degree : ℕ) × Bool → Locus) → ℝ)),
      (∀ degree (permutation : Equiv.Perm Locus) monomial,
        coefficient degree (permutation ∘ monomial) = coefficient degree monomial) →
        DegreeAtMostTrafficFactorizationStatement coefficient value
  /-- The rooted homogeneous decomposition gives the corresponding exact
  degree-`D` statement for equivariant vector-polynomial coordinates. -/
  degreeLimitedGenomicEquivariantPolynomialFactorsThroughRootedLDGraphs :
    ∀ (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient value : (degree : Fin (D + 1)) →
        ((Option (Fin (degree : ℕ) × Bool) → Locus) → ℝ)),
      (∀ degree (permutation : Equiv.Perm Locus) monomial,
        coefficient degree (permutation ∘ monomial) = coefficient degree monomial) →
        DegreeAtMostRootedTrafficFactorizationStatement coefficient value
  /-- Equality of canonical profiles implies exact equality of every invariant
  scalar polynomial of degree at most `D`. -/
  degreeLimitedGenomicPolynomialIsDeterminedByCanonicalLDProfile :
    ∀ (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
        ((Fin (degree : ℕ) × Bool → Locus) → ℝ)),
      (∀ degree (permutation : Equiv.Perm Locus) monomial,
        coefficient degree (permutation ∘ monomial) = coefficient degree monomial) →
      degreeAtMostCanonicalTrafficProfile leftValue =
        degreeAtMostCanonicalTrafficProfile rightValue →
        (∑ degree : Fin (D + 1),
          ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
          ∑ degree : Fin (D + 1),
            ∑ monomial, coefficient degree monomial * rightValue degree monomial
  /-- Equality of rooted profiles determines every equivariant polynomial
  coordinate of degree at most `D`. -/
  degreeLimitedGenomicEquivariantPolynomialIsDeterminedByRootedLDProfile :
    ∀ (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
        ((Option (Fin (degree : ℕ) × Bool) → Locus) → ℝ)),
      (∀ degree (permutation : Equiv.Perm Locus) monomial,
        coefficient degree (permutation ∘ monomial) = coefficient degree monomial) →
      degreeAtMostRootedCanonicalTrafficProfile leftValue =
        degreeAtMostRootedCanonicalTrafficProfile rightValue →
        (∑ degree : Fin (D + 1),
          ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
          ∑ degree : Fin (D + 1),
            ∑ monomial, coefficient degree monomial * rightValue degree monomial
  /-- Direct invariant separation transfers the complete Bayes gap to every
  uniform invariant degree-limited genomic polynomial procedure. -/
  degreeLimitedGenomicPolynomialHasDirectFullGapHardness :
    ∀ (Algorithm : Type) (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient : Algorithm → (degree : Fin (D + 1)) →
        ((Fin (degree : ℕ) × Bool → Locus) → ℝ))
      (leftValue rightValue : (degree : Fin (D + 1)) →
        ((Fin (degree : ℕ) × Bool → Locus) → ℝ)),
      (∀ algorithm degree (permutation : Equiv.Perm Locus) monomial,
        coefficient algorithm degree (permutation ∘ monomial) =
          coefficient algorithm degree monomial) →
      degreeAtMostCanonicalTrafficProfile leftValue =
        degreeAtMostCanonicalTrafficProfile rightValue →
      ∀ bayesLeft bayesRight : ℝ,
        (∀ algorithm,
          bayesRight ≤ ∑ degree : Fin (D + 1),
            ∑ monomial,
              coefficient algorithm degree monomial * rightValue degree monomial) →
        ∀ algorithm,
          bayesRight - bayesLeft ≤
            (∑ degree : Fin (D + 1),
              ∑ monomial,
                coefficient algorithm degree monomial * leftValue degree monomial) -
              bayesLeft
  /-- A finite tilt net controls the complete Lipschitz genomic pressure
  profile with explicit error `2Kρ + ε`. -/
  genomicPressureProfilesHaveQuantitativeTiltNetControl :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter]
      (K : NNReal) (left right : Parameter → ℝ),
      LipschitzWith K left → LipschitzWith K right →
      ∀ (net : Set Parameter) (radius coordinateError : ℝ),
        (∀ parameter, ∃ representative ∈ net,
          dist parameter representative ≤ radius) →
        (∀ representative ∈ net,
          dist (left representative) (right representative) ≤ coordinateError) →
          ∀ parameter,
            dist (left parameter) (right parameter) ≤
              2 * (K : ℝ) * radius + coordinateError
  /-- Agreement on a dense rational tilt family determines the full uniformly
  Lipschitz genomic pressure profile. -/
  genomicDenseTiltCoordinatesDeterminePressureProfile :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter]
      (K : NNReal) (left right : Parameter → ℝ),
      LipschitzWith K left → LipschitzWith K right →
      ∀ parameters : Set Parameter, Dense parameters →
        Set.EqOn left right parameters → left = right
  /-- Pointwise convergence on a dense rational tilt family extends to every
  tilt for a uniformly Lipschitz genomic pressure sequence and limit. -/
  genomicDenseTiltConvergenceExtendsGlobally :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter]
      (K : NNReal) (profiles : ℕ → Parameter → ℝ) (limit : Parameter → ℝ),
      (∀ index, LipschitzWith K (profiles index)) →
      LipschitzWith K limit →
      ∀ parameters : Set Parameter, Dense parameters →
        (∀ parameter ∈ parameters,
          Filter.Tendsto (fun index ↦ profiles index parameter)
            Filter.atTop (nhds (limit parameter))) →
          ∀ parameter,
            Filter.Tendsto (fun index ↦ profiles index parameter)
              Filter.atTop (nhds (limit parameter))
  /-- On compact tilt domains, the same dense-family hypotheses yield uniform
  convergence of the complete genomic pressure profile. -/
  genomicDenseTiltConvergenceIsUniformOnCompactDomains :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter] [CompactSpace Parameter]
      (K : NNReal) (profiles : ℕ → Parameter → ℝ) (limit : Parameter → ℝ),
      (∀ index, LipschitzWith K (profiles index)) →
      LipschitzWith K limit →
      ∀ parameters : Set Parameter, Dense parameters →
        (∀ parameter ∈ parameters,
          Filter.Tendsto (fun index ↦ profiles index parameter)
            Filter.atTop (nhds (limit parameter))) →
          TendstoUniformly profiles limit Filter.atTop
  /-- Uniformly bounded, common-Lipschitz genomic pressure functions form a
  compact family on every compact tilt domain. -/
  genomicBoundedLipschitzPressureProfilesAreCompact :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter] [CompactSpace Parameter]
      (K : NNReal) (bound : ℝ),
      IsCompact (boundedLipschitzPressureFamily
        (Parameter := Parameter) K bound)
  /-- Every bounded equi-Lipschitz genomic pressure sequence has a uniformly
  convergent subsequence whose limit remains bounded and equi-Lipschitz. -/
  genomicBoundedLipschitzPressureProfilesHaveCompactSubsequences :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter] [CompactSpace Parameter]
      (K : NNReal) (bound : ℝ)
      (profiles : ℕ → BoundedContinuousFunction Parameter ℝ),
      (∀ index, profiles index ∈ boundedLipschitzPressureFamily K bound) →
        ∃ limit ∈ boundedLipschitzPressureFamily (Parameter := Parameter) K bound,
          ∃ subsequence : ℕ → ℕ,
            StrictMono subsequence ∧
              Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit)
  /-- Every uniformly bounded countable exponential/LD profile has one common
  coordinatewise-convergent subsequence. -/
  genomicExponentialProfileIsSequentiallyCompact :
    ∀ (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound),
      ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          ∀ coordinate : ℕ,
            Filter.Tendsto (fun n ↦ profiles (subsequence n) coordinate)
              Filter.atTop (nhds (limit coordinate))
  /-- The explicit weighted exponential-profile formula satisfies the metric
  laws on bounded genomic pressure profiles. -/
  genomicExponentialProfileDistanceSatisfiesMetricLaws :
    ∀ (bound : ℝ) (left middle right : BoundedExponentialProfile bound),
      0 ≤ exponentialProfileDistance left right ∧
        exponentialProfileDistance left right = exponentialProfileDistance right left ∧
        exponentialProfileDistance left right ≤
        exponentialProfileDistance left middle + exponentialProfileDistance middle right ∧
        (exponentialProfileDistance left right = 0 ↔ left = right)
  /-- The explicit genomic right-profile carrier has the installed weighted
  metric and is compact in its standard topology. -/
  genomicExponentialProfilePointIsCompactMetricSpace :
    ∀ bound : ℝ,
      IsCompact (Set.univ : Set (ExponentialProfilePoint bound))
  /-- Metric convergence of bundled genomic profiles is coordinatewise
  convergence of every enumerated pressure. -/
  genomicExponentialProfilePointConvergenceIsCoordinatewise :
    ∀ (bound : ℝ) (profiles : ℕ → ExponentialProfilePoint bound)
      (limit : ExponentialProfilePoint bound),
      Filter.Tendsto profiles Filter.atTop (nhds limit) ↔
        ∀ coordinate : ℕ,
          Filter.Tendsto (fun n ↦ profiles n coordinate)
            Filter.atTop (nhds (limit coordinate))
  /-- Convergence in the explicit genomic right-profile distance is equivalent
  to convergence of every enumerated pressure coordinate. -/
  genomicExponentialProfileDistanceCharacterizesConvergence :
    ∀ (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound)
      (limit : BoundedExponentialProfile bound),
      Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
          Filter.atTop (nhds 0) ↔
        ∀ coordinate : ℕ,
          Filter.Tendsto (fun n ↦ profiles n coordinate)
            Filter.atTop (nhds (limit coordinate))
  /-- A finite prefix of genomic pressure coordinates controls the complete
  right-profile distance by the exact remaining geometric tail. -/
  genomicExponentialProfileHasFiniteCoordinateApproximation :
    ∀ (bound : ℝ) (left right : BoundedExponentialProfile bound)
      (prefixLength : ℕ),
      (∀ coordinate < prefixLength, left coordinate = right coordinate) →
        exponentialProfileDistance left right ≤ 2 ∧
          exponentialProfileDistance left right ≤
            2 * (1 / 2 : ℝ) ^ prefixLength
  /-- Every bounded sequence has a subsequence converging in the explicit
  weighted exponential-profile distance. -/
  genomicExponentialProfileIsCompactInExplicitDistance :
    ∀ (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound),
      ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          Filter.Tendsto
            (fun n ↦ exponentialProfileDistance (profiles (subsequence n)) limit)
            Filter.atTop (nhds 0)
  /-- Equal unconditioned Bolthausen--Sznitman genealogy does not determine the conditioned
  family: the logarithmic and linear response marks already separate at three lineages. -/
  speedConditionedGenealogyRetainsResponseMark :
    MarkedBreakout.linearDisplacementTripleRate 1 ≠ speedTiltBetaMergerRate 1 3 3
  /-- The cubic genealogical clock belongs to pioneer susceptibility, not coalescent theory. -/
  pioneerSusceptibilitySetsClock :
    ∀ width : ℝ, genealogicalTimescale width 3 = width ^ 3
  /-- A cross-state criterion is not a function of the target context: it fails to descend along
  the label the target-only annotation descends along. -/
  crossStateDoesNotDescend :
    ¬ DescendsAlong (fun g : TransportPair ↦ g.2) binaryTransportFamily
      (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2))
  /-- Reportability along each margin separately does not give reportability along the pair, so a
  stability check run one covariate at a time certifies nothing jointly. -/
  marginalDescentDoesNotCompose :
    DescendsAlong (fun g : TwoLociTrait ↦ g.1) admissibleInteractionTraitLaw
        (conditionalSectionMean traitIndicator) ∧
      DescendsAlong (fun g : TwoLociTrait ↦ g.2.1) admissibleInteractionTraitLaw
        (conditionalSectionMean traitIndicator) ∧
      ¬ DescendsAlong (fun g : TwoLociTrait ↦ (g.1, g.2.1)) admissibleInteractionTraitLaw
        (conditionalSectionMean traitIndicator)
  /-- Dropping a stratum destroys reportability that both finer labels have: there is no coarsest
  honest reporting label. -/
  crudeReportingLosesDescent :
    DescendsAlong (fun g : ExposureStratum ↦ g.1) admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator) ∧
      DescendsAlong (fun g : ExposureStratum ↦ g.2) admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator) ∧
      ¬ DescendsAlong trivialLabel admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator)
  /-- Every functional descends along posterior ancestry, and the ancestry-weighted average of
  component values is still off by a full unit of trait: descent and the affine-in-ancestry
  ansatz are different claims. -/
  ancestryWeightedAnsatzFails : exampleComponentResidual = -1
  /-- Pooling is aggregate-calibrated but leaves the positive index-wise drift defect. -/
  conditionalDriftSurvivesPooling :
    calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch = 1 / 4
  /-- Removing a dynamics from posterior support seals the defect without making the two
  conditional fields equal. -/
  zeroSupportSealsConditionalDrift :
    calibrationDriftDefectSq binaryStateWeight persistentOnlyDynamicsPosterior
      binaryConditionalContextMatch = 0
  /-- Every finite uniform correction through the pooled observation erases the biological
  contrast, independently of dictionary order. -/
  uniformCorrectionCannotRecoverContrast :
    ∀ (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ)),
      C ∈ UniformCorrectionFamily dynamicsPoolingObservation k → C dynamicsContrast = 0
  /-- Target-dependent coefficients cannot recover a direction already annihilated by the
  observation. -/
  adaptiveCorrectionCannotRecoverContrast :
    ∀ (k : ℕ) (T : Fin k → ℝ →ₗ[ℝ] (Bool → ℝ)),
      adaptiveCorrectionSet dynamicsPoolingObservation T dynamicsContrast = {0}
  /-- The same one-term adaptive dictionary is exact on the observable common mode, exposing the
  thin-class phase change rather than a blanket failure of adaptivity. -/
  observableModeIsAdaptivelyExact :
    dynamicsCommonMode ∈ adaptiveCorrectionSet dynamicsPoolingObservation
      (fun _ : Fin 1 ↦ dynamicsBroadcast) dynamicsCommonMode
  /-- The correction-null contrast and the calibration drift are the same biological direction,
  with the normalization made explicit. -/
  correctionContrastIsCalibrationDrift :
    ∀ persists y, dynamicsContrast persists =
      2 * posteriorDrift binaryDynamicsPosterior binaryConditionalContextMatch persists y

/-- **The finite obstruction theorem.**  Dynamics, dependence, value allocation, and
local operator geometry each carry information invisible to a tempting scalar reduction.
The witnesses coexist; none is a fallback explanation for another. -/
theorem dynamicsContrast_obstructions : DynamicsObstructions := by
  refine
    { targetOnlyBlind := targetOnlyPerformance_blind_to_binary_dynamics
      crossStateSeparates := ?_
      marginalsLoseDependence := coordinateMarginalsDoNotDetermineJointLaw
      commutingAllocationConflict := commutingConflict_myopic_ne_transport
      sharedGeometryNotFree := tridiagonalABAB_pathExpression_pos 0 0 1 1 (by norm_num)
        (by norm_num)
      isospectralLDLosesOrientation :=
        ⟨localizedCovarianceBlock_isospectral_rotatedCovarianceBlock (3 / 2), by
          intro heq
          have hzero :
              blockEntryCubeMean (localizedCovarianceBlock (3 / 2)) -
                  blockEntryCubeMean (rotatedCovarianceBlock (3 / 2)) = 0 := by
            rw [heq, sub_self]
          rw [midpoint_blockEntryCubeMean_separation] at hzero
          norm_num at hzero⟩
      skewedLDChangesLowSNRCoefficient :=
        sparsePrior_lowSNRThirdCoefficient_rotated_sub_localized
      symmetricSparseLDLosesOrientation :=
        ⟨localizedCovarianceBlock_isospectral_rotatedCovarianceBlock (3 / 2),
          midpoint_blockEntryFourthMean_ne⟩
      symmetricLDChangesLowSNRCoefficient :=
        rademacher_fullLowSNRFourthCoefficient_rotated_sub_localized
      environmentMixtureClosesPopulationGap :=
        ancestryMixture_pure_gapped_balanced_ungapped
      sameSignEnvironmentPoolingDoesNotMoveGapParameter :=
        sameSignAncestryPooling_preservesActiveCorrelation
      fiveEpochDemographyIsSeverelyIllConditioned :=
        fiveEpochDemography_sampleRateExponent
      kingmanSpectrumHasIdentifiabilityBoundary :=
        kingmanSpectrum_identifiabilityBoundary
      speedConditionedGenealogyNeedsThreeLineages :=
        speedConditionedGenealogy_pairBlind_tripleRecovers
      markedSuccessfulFamilyMeasureDeterminesGenealogy :=
        markedSuccessfulFamilyMeasure_determinesGenealogy
      markedMassPartitionMeasureDeterminesXi :=
        markedMassPartitionMeasure_determinesXi
      frontTrajectoryDoesNotDetermineXi :=
        sweepTrajectory_does_not_determine_genealogy
      twoColourPioneerResponseIsExact :=
        twoColourPioneerResponse_exact
      branchingRandomWalkBoundaryTransformIsCritical :=
        branchingRandomWalkBoundaryTransform_isCritical
      selectedDerivativeFluxControlsBreakouts :=
        fun _Pioneer _ _ tailConstant threshold blockScale fluxConstant weight htail
          hthreshold hweight hflux ↦
            selectedDerivativeFlux_controlsBreakouts
              tailConstant threshold blockScale fluxConstant weight
              htail hthreshold hweight hflux
      selectedPioneerFluxFollowsFromNegligiblePruning :=
        selectedPioneerFlux_follows_from_fullTreeFlux_and_negligiblePruning
      uniquePioneerCommonProfileDeterminesMarkedResponse :=
        uniquePioneer_commonProfile_markedResponse
      selectedGenealogyHasMuntzRateDichotomy :=
        selectedGenealogy_muntzRateDichotomy
      genomicAlgorithmicRiskSignatureIsCoarsest :=
        fun _Algorithm _Design _Model _Loss risk ↦
          genomicAlgorithmicRiskSignature_isCoarsestSufficientInvariant risk
      genomicRankOneTrafficExpansionFollowsFromHandshake :=
        fun _Term _ coefficient hasOddDegree vertices edges degree hpositive heven hhandshake ↦
          genomicRankOneTrafficCorrection_vanishes_of_positiveEvenDegreeData
            coefficient hasOddDegree vertices edges degree hpositive heven hhandshake
      positiveLDBalancedRankOneCovarianceHasFullWitness :=
        fun _Term _ coefficient hasOddDegree vertices edges hconnected baseline
          spikeStrength temperature hbaseline hspike hcritical ↦
            positiveLDBalancedRankOneCovariance_fullWitness coefficient hasOddDegree
              vertices edges hconnected baseline spikeStrength temperature hbaseline
              hspike hcritical
      rareLDSubspaceEvadesFixedTrafficAtLogRuntime :=
        rareLDSubspace_fixedTrafficInvisible_logRuntimeVisible
      rareLDSubspaceEvadesLimitingTrafficAtDegreeOne :=
        rareLDSubspace_limitingTrafficInsufficientForDegreeOne
      rareLDSubspaceConcreteGFOMEvadesFixedTrafficAtLogRuntime :=
        concreteGFOM_fixedTrafficInvisible_logRuntimeVisible
      genomicBulkSpectralLawDoesNotDetermineExtremalSpectrumOrSDP :=
        genomicBulkSpectralLaw_invisible_extremalSpectrumAndSDP_visible
      positiveLDSpikeFixedTrafficInvisibleVariationalPressureVisible :=
        fun _Term _ coefficient hasOddDegree vertices edges hconnected tlam hcritical ↦
          positiveLDSpike_fixedTrafficInvisible_variationalPressureVisible
            coefficient hasOddDegree vertices edges hconnected tlam hcritical
      positiveLDSpikeFixedTrafficInvisibleFinitePressureVisible :=
        fun _Term _ coefficient hasOddDegree vertices edges hconnected tlam hcritical ↦
          positiveLDSpike_fixedTrafficInvisible_finitePressureVisible
            coefficient hasOddDegree vertices edges hconnected tlam hcritical
      genomicFiniteCWPressureDominatesVariationalObjective :=
        genomicFiniteCWPressure_dominatesVariationalObjective
      genomicFiniteCWTypeMassLeOneOfSubcritical :=
        genomicFiniteCWTypeMass_le_one_of_subcritical
      genomicFiniteCWPressureHasExactCriticalPoint :=
        genomicFiniteCWPressure_exactCriticalPoint
      genomicFiniteCWPressureConvergesToVariational :=
        genomicFiniteCWPressure_convergesToVariational
      genomicFiniteCWPressureConvergesUniformlyOnNonnegative :=
        genomicFiniteCWPressure_convergesUniformlyOnNonnegative
      genomicFiniteCWPressureIsHalfLipschitz :=
        genomicFiniteCWPressure_isHalfLipschitz
      genomicFiniteCWPressureIsMonotone :=
        genomicFiniteCWPressure_isMonotone
      positiveLDSpikeFinitePressureExceedsBaseline :=
        positiveLDSpike_finitePressureExceedsBaseline
      positiveLDSpikePressureDifferenceHasExactCriticalPoint :=
        positiveLDSpike_pressureDifference_exactCriticalPoint
      positiveLDSpikePressureConvergesToVariational :=
        positiveLDSpike_pressure_convergesToVariational
      positiveLDSpikePressureConvergesUniformlyOnNonnegativeStrength :=
        positiveLDSpike_pressure_convergesUniformlyOnNonnegativeStrength
      positiveLDSpikeRefutesTrafficAndGroundStateDichotomies :=
        fun _Term _Genotype _ coefficient hasOddDegree vertices edges hconnected alignment
          orthogonal aligned baseline spikeStrength population temperature hspike hpopulation
          horthogonal haligned hcritical ↦
            positiveLDSpike_refutesTrafficAndGroundStateDichotomies
              coefficient hasOddDegree vertices edges hconnected alignment orthogonal aligned
              baseline spikeStrength population temperature hspike hpopulation horthogonal
              haligned hcritical
      positiveLDSpikeGroundStateDoesNotFixPressure :=
        positiveLDSpike_groundStateDoesNotFixPressure
      ldOverlapPressureHasExactCriticalPoint :=
        ldOverlapPressure_exactCriticalPoint
      ldVariationalPressureGapHasExactCriticalPoint :=
        ldVariationalPressureGap_exactCriticalPoint
      ldVariationalPressureGapHasGlobalRegularity :=
        ldVariationalPressureGap_globalRegularity
      matchedBayesRandomDesignAsymmetricReduction :=
        matchedBayes_randomDesignGap_fromScalarGap_asymmetric
      matchedBayesRandomDesignReduction :=
        matchedBayes_randomDesignGap_from_scalarGap
      matchedBayesRandomDesignEventuallySeparatesWithAsymmetricErrors :=
        fun _Index regime scalarLeft scalarRight delta randomLeft randomRight
          leftError rightError hleft hright hgap hpositive hleftVanishing
          hrightVanishing ↦
            matchedBayes_randomDesignEventuallySeparates_fromAsymmetricErrors
              regime scalarLeft scalarRight delta randomLeft randomRight leftError
              rightError hleft hright hgap hpositive hleftVanishing hrightVanishing
      matchedBayesRandomDesignEventuallySeparates :=
        fun _Index regime scalarLeft scalarRight delta randomLeft randomRight
          comparisonError hleft hright hgap hpositive herrorVanishing ↦
            matchedBayes_randomDesignEventuallySeparates_fromScalarGap
              regime scalarLeft scalarRight delta randomLeft randomRight
              comparisonError hleft hright hgap hpositive herrorVanishing
      matchedBayesRandomDesignSeparatesAtLargeAspect :=
        matchedBayes_randomDesignSeparates_ofLargeAspect
      matchedBayesRandomDesignEventuallySeparatesAtDivergingAspect :=
        fun _Index regime scalarLeft scalarRight delta constant aspectRatio
          randomLeft randomRight hleft hright hgap hpositive haspectRatio ↦
            matchedBayes_randomDesignEventuallySeparates_ofAspectAtTop regime
              scalarLeft scalarRight delta constant aspectRatio randomLeft randomRight
              hleft hright hgap hpositive haspectRatio
      matchedBayesAspectWishartRatioBridge :=
        fun _Index regime aspectRatio constant ↦
          matchedBayes_aspectWishartRatioBridge regime aspectRatio constant
      matchedBayesWishartInformationErrorVanishes :=
        fun _Index regime informationError adjustedRatio constant hratio herror ↦
          matchedBayes_wishartInformationErrorVanishes regime informationError
            adjustedRatio constant hratio herror
      matchedBayesRandomDesignEventuallySeparatesAtAsymmetricWishartRatios :=
        fun _Index regime scalarLeft scalarRight delta leftConstant rightConstant
          leftRatio rightRatio randomLeft randomRight hleft hright hgap hpositive
          hleftRatio hrightRatio ↦
            matchedBayes_randomDesignEventuallySeparates_ofAsymmetricWishartRatios
              regime scalarLeft scalarRight delta leftConstant rightConstant leftRatio
              rightRatio randomLeft randomRight hleft hright hgap hpositive hleftRatio
              hrightRatio
      matchedBayesRandomDesignEventuallySeparatesAtWishartRatio :=
        fun _Index regime scalarLeft scalarRight delta constant adjustedRatio
          randomLeft randomRight hleft hright hgap hpositive hratio ↦
            matchedBayes_randomDesignEventuallySeparates_ofWishartRatio regime
              scalarLeft scalarRight delta constant adjustedRatio randomLeft randomRight
              hleft hright hgap hpositive hratio
      matchedBayesSingularSpectrumHasNormalizedNuclearBound :=
        fun _Coordinate _ _ spectrum hdimension ↦
          spectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction hdimension
      matchedBayesCertifiedRankOnePerturbationIsAsymptoticallyInvisible :=
        matchedBayes_certifiedRankOnePerturbation_isAsymptoticallyInvisible
      matchedBayesInformationPathHasNuclearBound :=
        matchedBayes_informationPath_nuclearBound
      matchedBayesHasWishartFrobeniusComparisonRate :=
        matchedBayes_wishartFrobeniusComparisonRate
      matchedBayesHasWishartMomentIdentityComparisonRate :=
        matchedBayes_wishartMomentIdentityComparisonRate
      matchedBayesCertifiedSublinearRankIsInvisibleUnderVarianceBound :=
        fun _Index regime certificate varianceBound operatorBound rankFraction
          hvarianceBound hrankVanishing hnuclearRank ↦
            matchedBayes_certifiedSublinearRank_isInvisible_ofVarianceBound
              regime certificate varianceBound operatorBound rankFraction
              hvarianceBound hrankVanishing hnuclearRank
      matchedBayesCertifiedSublinearRankIsInvisible :=
        fun _Index regime certificate operatorBound rankFraction hvariance
          hrankVanishing hnuclearRank ↦
            matchedBayes_certifiedSublinearRank_isInvisible regime certificate
              operatorBound rankFraction hvariance hrankVanishing hnuclearRank
      matchedBayesSublinearRankPerturbationsAreInvisible :=
        matchedBayes_sublinearRankPerturbation_isAsymptoticallyInvisible
      matchedBayesPositiveGapForcesExtensiveRank :=
        matchedBayes_positiveGap_forcesExtensiveRank
      matchedBayesCertifiedPositiveGapForcesExtensiveRank :=
        matchedBayes_certifiedPositiveGap_forcesExtensiveRank
      matchedBayesCertifiedPersistentGapRequiresExtensiveRank :=
        fun _Index regime _hregime certificate varianceBound operatorBound delta rankFraction
          hvariancePositive hoperator hdelta hvarianceBound hnuclearRank hgap ↦
            matchedBayes_certifiedPersistentGap_requiresExtensiveRank regime
              certificate varianceBound operatorBound delta rankFraction hvariancePositive
              hoperator hdelta hvarianceBound hnuclearRank hgap
      matchedBayesPersistentGapRequiresExtensiveRank :=
        fun _Index regime _hregime densityGap rankFraction constant delta hconstant hdelta
          hgap hnuclear ↦
            matchedBayes_persistentGap_requiresExtensiveRank regime densityGap
              rankFraction constant delta hconstant hdelta hgap hnuclear
      degreeLimitedGenomicRiskHasFullGapHardness :=
        fun _Algorithm _D risk left right htraffic bayesLeft bayesRight hoptimal algorithm ↦
          degreeLimitedGenomicRisk_fullGapHardness risk left right htraffic bayesLeft bayesRight
            hoptimal algorithm
      stableDegreeLimitedGenomicRiskHasQuantitativeTrafficBound :=
        fun _D risk left right epsilon hcoordinate ↦
          stableDegreeLimitedGenomicRisk_quantitativeTrafficBound
            risk left right epsilon hcoordinate
      stableDegreeLimitedGenomicRiskConvergesOfBoundedCoefficientMass :=
        fun _D risk left right discrepancy coefficientBound hdiscrepancy
          hcoefficient hdiscrepancyNonneg ↦
            stableDegreeLimitedGenomicRisk_convergesOfBoundedCoefficientMass
              risk left right discrepancy coefficientBound hdiscrepancy
              hcoefficient hdiscrepancyNonneg
      highTemperatureGenomicTrafficDeterminesCertifiedPressure :=
        highTemperatureTrafficLimitsAgree_ofGeometricCertificate
      genomicLDTrafficHierarchyIsStrictAtEveryDegree :=
        genomicLDTrafficHierarchy_strictAtEveryDegree
      genomicLDTrafficHasCommonBlindPairAtEveryDegree :=
        genomicLDTrafficBlindPair_existsAtEveryDegree
      permutationInvariantGenomicPolynomialFactorsThroughLDGraphs :=
        fun _Slot _Locus _Graph _ _ _ _ _ shape coefficient value hshape hinvariant ↦
          permutationInvariantGenomicPolynomial_factorsThroughLDGraphs
            shape coefficient value hshape hinvariant
      permutationInvariantGenomicPolynomialFactorsThroughCanonicalLDGraphs :=
        fun _Slot _Locus _ _ _ coefficient value hinvariant ↦
          permutationInvariantGenomicPolynomial_factorsThroughCanonicalLDGraphs
            coefficient value hinvariant
      permutationEquivariantGenomicPolynomialFactorsThroughRootedLDGraphs :=
        fun _Slot _Locus _ _ _ coefficient value hinvariant ↦
          permutationEquivariantGenomicPolynomial_factorsThroughRootedLDGraphs
            coefficient value hinvariant
      degreeLimitedGenomicPolynomialFactorsThroughCanonicalLDGraphs :=
        fun _D _Locus _ coefficient value hinvariant ↦
          degreeLimitedGenomicPolynomial_factorsThroughCanonicalLDGraphs
            coefficient value hinvariant
      degreeLimitedGenomicEquivariantPolynomialFactorsThroughRootedLDGraphs :=
        fun _D _Locus _ coefficient value hinvariant ↦
          degreeLimitedGenomicEquivariantPolynomial_factorsThroughRootedLDGraphs
            coefficient value hinvariant
      degreeLimitedGenomicPolynomialIsDeterminedByCanonicalLDProfile :=
        fun _D _Locus _ coefficient leftValue rightValue hinvariant htraffic ↦
          degreeLimitedGenomicPolynomial_eq_ofCanonicalLDProfileEq
            coefficient leftValue rightValue hinvariant htraffic
      degreeLimitedGenomicEquivariantPolynomialIsDeterminedByRootedLDProfile :=
        fun _D _Locus _ coefficient leftValue rightValue hinvariant htraffic ↦
          degreeLimitedGenomicEquivariantPolynomial_eq_ofRootedLDProfileEq
            coefficient leftValue rightValue hinvariant htraffic
      degreeLimitedGenomicPolynomialHasDirectFullGapHardness :=
        fun _Algorithm _D _Locus _ coefficient leftValue rightValue hinvariant
          htraffic bayesLeft bayesRight hoptimalRight algorithm ↦
            degreeLimitedGenomicPolynomial_fullGapHardness_fromCanonicalLDProfile
              coefficient leftValue rightValue hinvariant htraffic bayesLeft bayesRight
              hoptimalRight algorithm
      genomicPressureProfilesHaveQuantitativeTiltNetControl :=
        fun _Parameter _ K left right hleft hright net radius coordinateError hnet hagrees ↦
          genomicPressureProfiles_dist_le_of_tiltNet
            K left right hleft hright net radius coordinateError hnet hagrees
      genomicDenseTiltCoordinatesDeterminePressureProfile :=
        fun _Parameter _ K left right hleft hright parameters hdense hagrees ↦
          genomicPressureProfiles_eq_of_eqOn_denseTilts
            K left right hleft hright parameters hdense hagrees
      genomicDenseTiltConvergenceExtendsGlobally :=
        fun _Parameter _ K profiles limit hprofiles hlimit parameters hdense hconverges ↦
          lipschitzPressureProfiles_tendsto_of_tendstoOn_dense
            K profiles limit hprofiles hlimit parameters hdense hconverges
      genomicDenseTiltConvergenceIsUniformOnCompactDomains :=
        fun _Parameter _ _ K profiles limit hprofiles hlimit parameters hdense hconverges ↦
          lipschitzPressureProfiles_tendstoUniformly_of_tendstoOn_dense
            K profiles limit hprofiles hlimit parameters hdense hconverges
      genomicBoundedLipschitzPressureProfilesAreCompact :=
        fun _Parameter _ _ K bound ↦
          genomicBoundedLipschitzPressureFamily_isCompact K bound
      genomicBoundedLipschitzPressureProfilesHaveCompactSubsequences :=
        fun _Parameter _ _ K bound profiles hprofiles ↦
          genomicBoundedLipschitzPressureFamily_hasUniformlyConvergentSubsequence
            K bound profiles hprofiles
      genomicExponentialProfileIsSequentiallyCompact :=
        genomicExponentialProfile_hasCommonCoordinatewiseSubsequence
      genomicExponentialProfileDistanceSatisfiesMetricLaws :=
        fun _bound left middle right ↦
          genomicExponentialProfileDistance_metricLaws left middle right
      genomicExponentialProfilePointIsCompactMetricSpace :=
        genomicExponentialProfilePoint_isCompactMetricSpace
      genomicExponentialProfilePointConvergenceIsCoordinatewise :=
        fun _bound _profiles _limit ↦
          genomicExponentialProfilePoint_converges_iff_coordinatewise
      genomicExponentialProfileDistanceCharacterizesConvergence :=
        fun _bound _profiles _limit ↦
          genomicExponentialProfileDistance_converges_iff_coordinatewise
      genomicExponentialProfileHasFiniteCoordinateApproximation :=
        fun _bound left right prefixLength hprefix ↦
          genomicExponentialProfileDistance_finitePrefixControl
            left right prefixLength hprefix
      genomicExponentialProfileIsCompactInExplicitDistance :=
        genomicExponentialProfile_compactInExplicitDistance
      speedConditionedGenealogyRetainsResponseMark :=
        speedConditionedGenealogy_chart_not_universal
      pioneerSusceptibilitySetsClock :=
        pioneerSusceptibility_setsGenealogicalClock
      crossStateDoesNotDescend := not_descends_contextMatchQuality_along_targetState
      marginalDescentDoesNotCompose := admissible_interaction_join_obstruction
      crudeReportingLosesDescent := admissible_confounding_meet_obstruction
      ancestryWeightedAnsatzFails := exampleComponentResidual_eq_neg_one
      conditionalDriftSurvivesPooling := binaryContextMatch_calibrationDriftDefectSq_eq_quarter
      zeroSupportSealsConditionalDrift :=
        persistentOnly_contextMatch_calibrationDriftDefectSq_eq_zero
      uniformCorrectionCannotRecoverContrast :=
        every_uniform_pooled_correction_erases_dynamicsContrast
      adaptiveCorrectionCannotRecoverContrast :=
        adaptive_pooled_correctionSet_dynamicsContrast_eq_zero
      observableModeIsAdaptivelyExact :=
        dynamicsCommonMode_mem_adaptive_pooled_correctionSet
      correctionContrastIsCalibrationDrift := dynamicsContrast_eq_two_mul_contextMatchDrift }
  rw [crossStatePerformance_persistent_eq_one, crossStatePerformance_switching_eq_zero]
  norm_num

/-! ## Conditional descent is the portability gate before prediction

The same score bin or ancestry summary can support different conditional phenotype laws in
different cohorts.  `FunctionalDescent` separates two biologically distinct failures:
interaction can disappear in either margin and reappear after refinement, while confounding can
be controlled by either informative variable and reappear after marginalization.  Thus the
choice of retained covariate is part of the portability theorem, not preprocessing notation. -/

/-- **The conditional-descent boundary is present in the biological core.**  Both finite
probability-law witnesses retain their complete order-theoretic statements.  Moreover, each
failure is already pairwise: the exact finite gluing theorem rules out a hidden global-selection
explanation.  Biologically, two cohorts disagree on a charged conditional section; the failure is
effect modification or confounding, not an off-support choice of conditional version. -/
theorem conditionalDescent_biological_boundary :
    ((DescendsAlong (fun g : TwoLociTrait ↦ g.1) admissibleInteractionTraitLaw
          (conditionalSectionMean traitIndicator) ∧
        DescendsAlong (fun g : TwoLociTrait ↦ g.2.1) admissibleInteractionTraitLaw
          (conditionalSectionMean traitIndicator) ∧
        ¬ DescendsAlong (fun g : TwoLociTrait ↦ (g.1, g.2.1))
          admissibleInteractionTraitLaw (conditionalSectionMean traitIndicator)) ∧
      ¬ PairwiseConsistent (fun g : TwoLociTrait ↦ (g.1, g.2.1))
        admissibleInteractionTraitLaw (conditionalSectionMean traitIndicator)) ∧
    ((DescendsAlong (fun g : ExposureStratum ↦ g.1) admissibleConfoundedExposureLaw
          (conditionalSectionMean exposureIndicator) ∧
        DescendsAlong (fun g : ExposureStratum ↦ g.2) admissibleConfoundedExposureLaw
          (conditionalSectionMean exposureIndicator) ∧
        ¬ DescendsAlong trivialLabel admissibleConfoundedExposureLaw
          (conditionalSectionMean exposureIndicator)) ∧
      ¬ PairwiseConsistent trivialLabel admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator)) := by
  refine ⟨⟨admissible_interaction_join_obstruction, ?_⟩,
    ⟨admissible_confounding_meet_obstruction, ?_⟩⟩
  · intro hpair
    exact admissible_interaction_join_obstruction.2.2
      ((descendsAlong_iff_pairwiseConsistent_of_nonempty _ _ _).mpr hpair)
  · intro hpair
    exact admissible_confounding_meet_obstruction.2.2
      ((descendsAlong_iff_pairwiseConsistent_of_nonempty _ _ _).mpr hpair)

end Descent
