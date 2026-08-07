/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Conditionals.DynamicsContrast.CohortLandscapeSuperposition
import Descent.Blindness.TrafficInvariantSeparation.CurieWeissWindow
import Descent.Blindness.TrafficInvariantSeparation.MatchedBayesBoundary
import Descent.Blindness.XiFromMarkedBreakouts

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Portability`, `Descent.Program`:
--   Portability: reaches 13 module(s) -- `Descent.Portability.ContinuumCalibration`,
--   `Descent.Portability.CorrectionWidths`, `Descent.Portability.HorizonCurve` and 10 more
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.Conditionals

open Blindness.MarkedBreakout
open Blindness.XiFromMarks
open Blindness.TrafficInvariantSeparation
open scoped Matrix Topology
open scoped BigOperators

/-!
# `DynamicsContrast.StationarityRepair`

Part of the split of `Descent/Conditionals/DynamicsContrast.lean`, which was 3,590 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/


/-! ## Population overlap geometry under ancestry-environment mixing -/

/-- The active sparse-LD correlation after pooling two environments with correlations `rho`
and `-rho`.  This is the biological name for the landscape parameter itself.

    Empirical status: **VALIDATED AS ARITHMETIC**, and the modelling step it rests on
    is still untested (`simcov/battery_gap01.py`, `group_mixture`).

    What is measured: 1e5 pairs per block and 20 blocks per cell drawn from TWO
    environments with correlations `+rho` and `-rho` and pooled at mass `mix`, with the
    observable the realised Pearson correlation of the POOLED sample. Worst cell 2.06 sems
    at 0.27% relative over `(rho, mix)` = (0.8, 0.5), (0.8, 0.75), (0.4, 0.25), (0.6, 0.9)
    -- the balanced cell included because exact cancellation is the one prediction a reader
    will check by hand. Reading the positive environment's mass alone is FALSIFIED at 473
    sems and the negative environment's at 730. The same cells measure
    `LandscapeSuperposition.mixedEnvironmentCorrelation`, which this instantiates.

    What is NOT measured, and the sentence below is unchanged because it is still true: that
    an ancestry-environment mixture IS described by two correlations of equal size and
    opposite sign is a modelling step no simulation can settle, and no dataset here bears on
    it. The pooling formula is arithmetic on the two environment correlations; what was
    untested until now was that arithmetic, and what remains untested is the model it is
    arithmetic about. -/
noncomputable def ancestryMixtureCorrelation (rho positiveEnvironmentMass : ℝ) : ℝ :=
  Blindness.mixedEnvironmentCorrelation rho positiveEnvironmentMass

/-- A balanced ancestry-environment mixture cancels the active correlation exactly. -/
@[simp] theorem ancestryMixtureCorrelation_balanced (rho : ℝ) :
    ancestryMixtureCorrelation rho (1 / 2) = 0 := by
  exact Blindness.mixedEnvironmentCorrelation_half rho

/-- **Two individually gapped LD environments can pool to an ungapped population profile.**

At active correlation `4/5`, both signs lie beyond the golden threshold and have a negative
population gap certificate.  Equal environment mass cancels the active correlation, leaving
certificate one.  This is a population-landscape statement only: it does not infer a
polynomial-time algorithm from absence of the gap. -/
theorem ancestryMixture_pure_gapped_balanced_ungapped :
    Blindness.populationGapCertificate (4 / 5) < 0 ∧
      Blindness.populationGapCertificate (-(4 / 5)) < 0 ∧
      Blindness.populationGapCertificate (ancestryMixtureCorrelation (4 / 5) (1 / 2)) = 1 := by
  have hthreshold : Blindness.goldenCorrelationThreshold < (4 / 5 : ℝ) := by
    have hgold := Blindness.goldenCorrelationThreshold_sq_add_self
    have hpositive := Blindness.goldenCorrelationThreshold_mem_Ioo.1
    nlinarith
  have habsPositive : |(4 / 5 : ℝ)| = 4 / 5 := by norm_num
  have habsNegative : |(-(4 / 5) : ℝ)| = 4 / 5 := by norm_num
  have hpositive := Blindness.populationGapCertificate_neg_of_golden_lt_abs
    (4 / 5) (by norm_num) (by rw [habsPositive]; exact hthreshold)
  have hnegative := Blindness.populationGapCertificate_neg_of_golden_lt_abs
    (-(4 / 5)) (by norm_num) (by rw [habsNegative]; exact hthreshold)
  refine ⟨hpositive, hnegative, ?_⟩
  simp [ancestryMixtureCorrelation, Blindness.mixedEnvironmentCorrelation,
    Blindness.populationGapCertificate]

/-- **Scope of the explicit diversity mechanism.**  If the two ancestry environments carry
the same active LD correlation, pooling leaves that correlation unchanged at every mixture
weight.  The proven gap-closing construction therefore uses opposite-sign LD, not diversity
alone. -/
theorem sameSignAncestryPooling_preservesActiveCorrelation (rho mix : ℝ) :
    Blindness.pooledEnvironmentCorrelation rho rho mix = rho :=
  Blindness.pooledEnvironmentCorrelation_same rho mix

/-! ## Demographic resolution budget from the frequency spectrum -/

/-- **Exact fixed-epoch design budget.**  The first conjunct is the spectrum-precision
multiplier needed to halve reconstruction error; the second is the independent-genomic-data
multiplier under root-sample spectrum error.  These are algebraic consequences of the sharp
`1 / (2K - 3)` inverse exponent. -/
theorem fixedEpochDemography_halving_budget :
    (PopGen.spectrumPrecisionMultiplier 2 2 = 2 ∧
      PopGen.spectrumPrecisionMultiplier 3 2 = 8 ∧
      PopGen.spectrumPrecisionMultiplier 4 2 = 32 ∧
      PopGen.spectrumPrecisionMultiplier 5 2 = 128) ∧
    (PopGen.independentSampleMultiplier 2 2 = 4 ∧
      PopGen.independentSampleMultiplier 3 2 = 64 ∧
      PopGen.independentSampleMultiplier 4 2 = 1024 ∧
      PopGen.independentSampleMultiplier 5 2 = 16384) :=
  ⟨PopGen.spectrumPrecisionMultiplier_halving_table,
    PopGen.independentSampleMultiplier_halving_table⟩

/-- A five-epoch demographic sieve inherits the slow `sampleSize⁻¹ᐟ¹⁴` stability rate. -/
theorem fiveEpochDemography_sampleRateExponent :
    PopGen.fixedEpochSampleRateExponent 5 = 1 / 14 :=
  PopGen.fixedEpochSampleRateExponent_five

/-- **Kingman SFS identifiability boundary.**  The complete quadratic rate ladder has a
summable reciprocal, while every finite observation map has a nonzero direction on a sieve
with one additional coefficient.  The first fact is the Müntz obstruction's spectral input;
the second says finite-sample analyticity alone cannot restore identification. -/
theorem kingmanSpectrum_identifiabilityBoundary :
    Summable (fun k : ℕ ↦
      1 / Coalescent.deathRate (k + 2)) ∧
      ∀ n : ℕ, ∀ observation : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ),
        ∃ direction : Fin (n + 1) → ℝ,
          direction ≠ 0 ∧ observation direction = 0 :=
  ⟨Blindness.SpectrumIdentifiability.summable_one_div_coalescentRate,
    fun _ observation ↦ Blindness.SpectrumIdentifiability.exists_invisible_perturbation observation⟩

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
    PopGen.TargetIdentifiableUnderLinearObservation spectrumObservation target historyClass ↔
      PopGen.modelDifferenceSet historyClass ∩ LinearMap.ker spectrumObservation ⊆
        LinearMap.ker target :=
  PopGen.targetIdentifiableUnderLinearObservation_iff_differenceSet_inter_kernel_subset_ker
    spectrumObservation target historyClass

/-- At the stationary Cauchy root, the per-dimension inverse-conditioning base is the exact
ratio `(1 + θ²) / (1 - θ²)`. -/
theorem demographicSieveConditioning_exactBase
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hstationary : Blindness.SpectrumIdentifiability.CauchyConditioningStationary θ) :
    Real.exp (Blindness.SpectrumIdentifiability.cauchyConditioningProfile θ / 2) =
      (1 + θ ^ 2) / (1 - θ ^ 2) :=
  Blindness.SpectrumIdentifiability.exp_half_cauchyConditioningProfile_at_stationary
    θ hθ0 hθ1 hstationary

/-! ## Multiple-merger genealogy: pairwise blindness -/

/-- **Pairwise diversity cannot identify a normalized multiple-merger regime.**  Every
probability-normalized merger law has pair-merger rate one, whereas the three-lineage rate is
its first merger-fraction moment.  The displayed point-mass pair is the smallest exact
witness: identical at two lineages and separated at three. -/
theorem pairwiseGenealogy_blind_threeLineage_visible :
    Blindness.lambdaCoalescentMergerRate (MeasureTheory.Measure.dirac 0) 2 2 =
        Blindness.lambdaCoalescentMergerRate (MeasureTheory.Measure.dirac 1) 2 2 ∧
      Blindness.lambdaCoalescentMergerRate (MeasureTheory.Measure.dirac 0) 3 3 = 0 ∧
      Blindness.lambdaCoalescentMergerRate (MeasureTheory.Measure.dirac 1) 3 3 = 1 :=
  Blindness.pairwise_blind_three_lineage_separates_dirac

/-- **Speed-conditioned genealogy is identified at three lineages, not two.**  In the
normalized `Beta(1, β + 1)` chart the pair rate is identically one, while the inverse of the
three-lineage rate recovers `β` exactly.  This is the finite observable consequence of the
regular-variation speed-tilt theorem. -/
theorem speedConditionedGenealogy_pairBlind_tripleRecovers (β : ℝ) :
    Blindness.speedTiltBetaMergerRate β 2 2 = 1 ∧
      Blindness.speedBiasParameterFromTripleRate (Blindness.speedTiltBetaMergerRate β 3 3) = β :=
  ⟨Blindness.speedTiltBetaMergerRate_two_two β,
    Blindness.speedBiasParameterFromTripleRate_recovers β⟩

/-- **Why the regular-variation genealogy has no simultaneous disjoint mergers.**  At tail
scale `d`, a two-family pair-pair collision is smaller than a one-family pair collision by the
explicit factor `d (β + 1) / ((β + 2) (β + 3))`.  The factor is one order smaller in the
rare-family scale, not merely bounded by an unspecified error. -/
theorem speedConditionedGenealogy_twoFamilyToPairRatio
    {β d : ℝ} (hβ : -1 < β) (hd : d ≠ 0) :
    Blindness.speedTiltTwoFamilyCollisionScale β d / Blindness.speedTiltPairCollisionScale β d =
      d * (β + 1) / ((β + 2) * (β + 3)) :=
  Blindness.speedTiltTwoFamilyCollisionScale_div_pair hβ hd

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
  Blindness.tendsto_speedTiltTwoFamilyToPairRatio_comp β hscale

/-- **The biology core consumes the marked successful-family measure itself.**  At zero tilt its
weighted pushforward is exactly the unconditioned genealogy measure, and for every merger size
the Bernoulli family-participation rate is the corresponding `Λ`-rate.  This is the formal
replacement for treating a coalescent measure alone as the universal branching-front object. -/
theorem markedSuccessfulFamilyMeasure_determinesGenealogy
    (ν : MeasureTheory.Measure Blindness.MarkedBreakout.SuccessfulFamilyMark)
    (b k : ℕ) (hk : 2 ≤ k) :
    Blindness.MarkedBreakout.speedTiltedGenealogyMeasure 0 ν =
      Blindness.MarkedBreakout.genealogyMeasure ν ∧
      Blindness.MarkedBreakout.markedEventMergerRate ν b k =
        Blindness.MarkedBreakout.markedLambdaMergerRate ν b k :=
  ⟨Blindness.MarkedBreakout.speedTiltedGenealogyMeasure_zero ν,
    Blindness.MarkedBreakout.markedEventMergerRate_eq_lambda ν b k hk⟩

/-- The marked second-moment condition is exactly the finite-rate condition consumed by the
biology core: it makes the weighted genealogy projection a finite measure. -/
theorem markedSuccessfulFamilyMeasure_finiteGenealogy_of_finiteIntensity
    {ν : MeasureTheory.Measure Blindness.MarkedBreakout.SuccessfulFamilyMark}
    (hν : Blindness.MarkedBreakout.HasFiniteGenealogicalIntensity ν) :
    Blindness.MarkedBreakout.genealogyMeasure ν Set.univ < ⊤ :=
  Blindness.MarkedBreakout.genealogyMeasure_finite_of_secondMoment hν

/-- **The speed-conditioned genealogy retains the response mark.**  This measurable-set formula
is the biology-facing version of `Λθ(dx) = x² ∫ exp(-θr) ν(dx,dr)`: it exposes the full marked
intensity rather than silently replacing it by its unconditioned fraction marginal. -/
theorem speedConditionedGenealogy_markedMeasure_formula
    (theta : ℝ) (ν : MeasureTheory.Measure Blindness.MarkedBreakout.SuccessfulFamilyMark)
    {s : Set ℝ} (hs : MeasurableSet s) :
    Blindness.MarkedBreakout.speedTiltedGenealogyMeasure theta ν s =
      ∫⁻ mark in Blindness.MarkedBreakout.familyFraction ⁻¹' s,
        ENNReal.ofReal
          (Blindness.MarkedBreakout.familyFraction mark ^ 2 *
            Real.exp (-(theta * Blindness.MarkedBreakout.frontDisplacement mark))) ∂ν :=
  Blindness.MarkedBreakout.speedTiltedGenealogyMeasure_apply theta ν hs

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
    Blindness.MarkedBreakout.linearDisplacementTripleRate 1 ≠ Blindness.speedTiltBetaMergerRate 1 3
      3 :=
  Blindness.MarkedBreakout.tripleRate_separates_at_unit_tilt

/-- **And what the chart does rest on, exactly.**  The logarithmic displacement law is what
makes the tilt factor a power of the surviving fraction, and additive displacement noise
independent of the family fraction is absorbed by normalization.  These two identities are the
forward calculation; the following theorem supplies the exact transform-level converse. -/
theorem speedConditionedGenealogy_chart_invariant
    (gamma theta x noise : ℝ) (hgamma : gamma ≠ 0) (hx : x < 1) :
    Real.exp (-(theta * Blindness.MarkedBreakout.logDisplacement gamma x))
        = (1 - x) ^ (theta / gamma) ∧
      Real.exp (-(theta * (Blindness.MarkedBreakout.logDisplacement gamma x + noise)))
        = (1 - x) ^ (theta / gamma) * Real.exp (-(theta * noise)) :=
  ⟨Blindness.MarkedBreakout.logDisplacement_laplace_factors gamma theta x hgamma hx,
    Blindness.MarkedBreakout.displacementNoise_factors gamma theta x noise hgamma hx⟩

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
    Blindness.XiFromMarks.paintboxWeight ![finalFrequency]
        ≠ Blindness.XiFromMarks.paintboxWeight ![finalFrequency / 2, finalFrequency / 2] ∧
      Blindness.XiFromMarks.disjointPairMergeProbability ![finalFrequency] = 0 ∧
      0 < Blindness.XiFromMarks.disjointPairMergeProbability
        ![finalFrequency / 2, finalFrequency / 2] :=
  Blindness.XiFromMarks.front_does_not_determine_genealogy finalFrequency hpolymorphic

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
    Blindness.speedTiltBetaMergerRate β 2 2 = 1 ∧
      Blindness.speedBiasParameterFromTripleRate (Blindness.speedTiltBetaMergerRate β 3 3) = β ∧
      Blindness.XiFromMarks.disjointPairMergeProbability ![finalFrequency] = 0 ∧
      0 < Blindness.XiFromMarks.disjointPairMergeProbability
        ![finalFrequency / 2, finalFrequency / 2] :=
  ⟨Blindness.speedTiltBetaMergerRate_two_two β,
    Blindness.speedBiasParameterFromTripleRate_recovers β,
    Blindness.XiFromMarks.disjointPairMerge_single_zero finalFrequency,
    (Blindness.XiFromMarks.front_does_not_determine_genealogy finalFrequency hpolymorphic).2.2⟩

/-- **The sweep-origin count a frequency trajectory would have to supply, and cannot.**

The pioneer change of variables turns a reproductive-weight tail into the population-fraction
intensity and the frequency response into the logarithmic displacement law, so the whole
reduction rests on those two maps and nothing else.  Recording it here is what makes the
previous theorem a statement about a mechanism rather than about two arbitrary partitions. -/
theorem sweepResponse_is_logarithmic (gamma reproductiveWeight : ℝ)
    (hweight : 0 < reproductiveWeight) :
    Blindness.XiFromMarks.pioneerWeightDisplacement gamma reproductiveWeight
      = Blindness.MarkedBreakout.logDisplacement gamma
        (Blindness.XiFromMarks.pioneerWeightFraction reproductiveWeight) :=
  Blindness.XiFromMarks.pioneerDisplacement_eq_logDisplacement gamma reproductiveWeight hweight

/-- **The biology core consumes the complete mass-partition mark.**  Collision integrability
simultaneously makes every fixed-sample event rate finite and makes zero speed tilt recover the
unconditioned `Ξ` measure.  Thus the successful-event object is not merely an allele-frequency
measure with an informal multiplicity annotation: the mass partition is part of its type. -/
theorem markedMassPartitionMeasure_determinesXi
    (n : ℕ) (ν : MeasureTheory.Measure Blindness.XiFromMarks.MarkedMassPartition)
    (hν : Blindness.XiFromMarks.HasFiniteCollisionIntensity ν) :
    Blindness.XiFromMarks.speedTiltedXiMeasure 0 ν = Blindness.XiFromMarks.xiMeasure ν ∧
      Blindness.XiFromMarks.samplePartitionChangeRateBound n ν < ⊤ :=
  ⟨Blindness.XiFromMarks.speedTiltedXiMeasure_zero ν,
    Blindness.XiFromMarks.samplePartitionChangeRateBound_lt_top_of_finiteCollision n hν⟩

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
          Blindness.XiFromMarks.pioneerWeightFraction reproductiveWeight ∧
      Real.exp (-(gamma * Blindness.XiFromMarks.pioneerWeightDisplacement gamma reproductiveWeight))
        *
          (1 + reproductiveWeight) = 1 := by
  refine ⟨Blindness.XiFromMarks.spectralResponse_pioneerFraction conversion reproductiveWeight
    hconversion ?_,
    Blindness.XiFromMarks.spectralResponse_shift_restoresAmplitude gamma reproductiveWeight hgamma
      hweight⟩
  linarith

/-- **The light-tailed BRW boundary transform is an algebraic identity.**  The critical
log-mgf equation normalizes additive mass, while choosing speed equal to the log-mgf derivative
centers the derivative mass.  What remains model-specific is passage through rightmost-`N`
selection, not this transformation. -/
theorem branchingRandomWalkBoundaryTransform_isCritical
    (logMgf logMgfDerivative criticalParameter criticalSpeed : ℝ)
    (hboundary : criticalParameter * criticalSpeed - logMgf = Real.log 2)
    (hspeed : criticalSpeed = logMgfDerivative) :
    Blindness.XiFromMarks.boundaryTiltMass logMgf criticalParameter criticalSpeed = 1 ∧
      Blindness.XiFromMarks.boundaryTiltCenteredFirstMoment
        logMgf logMgfDerivative criticalParameter criticalSpeed = 0 :=
  ⟨Blindness.XiFromMarks.boundaryTiltMass_eq_one logMgf criticalParameter criticalSpeed hboundary,
    Blindness.XiFromMarks.boundaryTiltCenteredFirstMoment_eq_zero
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
    (hflux : Blindness.XiFromMarks.selectedPioneerFlux weight = blockScale * fluxConstant) :
    (∑ pioneer,
        paretoExceedanceMass tailConstant threshold (weight pioneer)) =
        blockScale * (tailConstant * fluxConstant / threshold) ∧
      Blindness.XiFromMarks.distinctPairExceedanceMass
          (fun pioneer ↦ paretoExceedanceMass
            tailConstant threshold (weight pioneer)) ≤
        (blockScale * (tailConstant * fluxConstant / threshold)) ^ 2 := by
  constructor
  · rw [Blindness.XiFromMarks.weightedParetoExceedanceMass_eq_flux, hflux]
    ring
  · exact Blindness.XiFromMarks.distinctPairParetoExceedanceMass_le_blockScale_sq
      tailConstant threshold blockScale fluxConstant weight
      htail hthreshold hweight hflux

/-- **Potential-pioneer survival is precisely the pruning gap.**  An exogenous full-tree flux
law transfers to the selected system once the reproductive-value flux removed by intermediate
rightmost-`N` pruning vanishes on the same scale.

Assumes: `IsSelectedFluxDecomposition fullTreeFlux selectedFlux prunedFlux`. -/
theorem selectedPioneerFlux_follows_from_fullTreeFlux_and_negligiblePruning
    (fullTreeFlux selectedFlux prunedFlux : ℕ → ℝ) (fluxConstant : ℝ)
    (hdecomposition :
      Blindness.XiFromMarks.IsSelectedFluxDecomposition fullTreeFlux selectedFlux prunedFlux)
    (hfull : Filter.Tendsto fullTreeFlux Filter.atTop (nhds fluxConstant))
    (hpruned : Filter.Tendsto prunedFlux Filter.atTop (nhds 0)) :
    Filter.Tendsto selectedFlux Filter.atTop (nhds fluxConstant) :=
  Blindness.XiFromMarks.selectedFlux_tendsto_of_exogenous_of_pruned
    fullTreeFlux selectedFlux prunedFlux fluxConstant hdecomposition hfull hpruned

/-- **One pioneer gives one atom, but its sample fraction still needs common-profile
relaxation.**  The first conjunct is pathwise ancestry bookkeeping.  The second consumes the
separate two-colour profile hypothesis, and the third uses the real-valued amplitude front.

Assumes: `HasCommonProfileRelaxation conversion 1 w backgroundCount pioneerCount`. -/
theorem uniquePioneer_commonProfile_markedResponse
    (conversion gamma w backgroundCount pioneerCount : ℝ)
    (hconversion : conversion ≠ 0)
    (hcount : backgroundCount + pioneerCount ≠ 0)
    (hprofile : Blindness.XiFromMarks.HasCommonProfileRelaxation conversion 1 w
      backgroundCount pioneerCount) :
    (Blindness.XiFromMarks.totalFamilyFraction ![Blindness.XiFromMarks.pioneerWeightFraction w] =
      Blindness.XiFromMarks.pioneerWeightFraction w ∧
      Blindness.XiFromMarks.paintboxWeight ![Blindness.XiFromMarks.pioneerWeightFraction w] =
        Blindness.XiFromMarks.pioneerWeightFraction w ^ 2 ∧
        Blindness.XiFromMarks.disjointPairMergeProbability
          ![Blindness.XiFromMarks.pioneerWeightFraction w] = 0) ∧
      pioneerCount / (backgroundCount + pioneerCount) = Blindness.XiFromMarks.pioneerWeightFraction
        w ∧
        Blindness.XiFromMarks.amplitudeFront gamma (1 + w) - Blindness.XiFromMarks.amplitudeFront
          gamma 1 =
          Blindness.XiFromMarks.pioneerWeightDisplacement gamma w :=
  ⟨Blindness.XiFromMarks.oneSuccessfulAncestor_produces_onePaintboxAtom
    (Blindness.XiFromMarks.pioneerWeightFraction w),
    Blindness.XiFromMarks.pioneerCountFraction_eq_of_commonProfile
      conversion w backgroundCount pioneerCount hconversion hcount hprofile,
    Blindness.XiFromMarks.amplitudeFront_pioneerShift gamma w⟩

/-- **The reciprocal-rate inversion is localized at the pulled boundary.**  Linear pulled
clocks have divergent reciprocals; every stable exponent above one, including the quadratic
Kingman order, has summable reciprocals.  This removes one Müntz obstruction only after the
demographic observation operator is proved to use this exponential rate ladder. -/
theorem selectedGenealogy_muntzRateDichotomy
    (coefficient alpha : ℝ) (hcoefficient : 0 < coefficient) (halpha : 1 < alpha) :
    (¬Summable fun n : ℕ ↦
        1 / Blindness.criticallyPulledLinearRateLadder coefficient n) ∧
      Summable (fun n : ℕ ↦ 1 / Blindness.stablePowerRateLadder alpha n) ∧
        Summable (fun n : ℕ ↦ 1 / Blindness.stablePowerRateLadder 2 n) :=
  ⟨Blindness.not_summable_one_div_criticallyPulledLinearRateLadder coefficient hcoefficient,
    Blindness.summable_one_div_stablePowerRateLadder alpha halpha,
    Blindness.summable_one_div_quadraticRateLadder⟩

/-! ## Traffic depth, mesoscopic LD structure, and iterative genomic procedures -/

/-- **The complete genomic procedure-risk signature is the canonical coarsest
sufficient design invariant.**  It reconstructs every model/loss risk directly,
while equality under any other sufficient invariant forces equality of the
complete signature.  Uniformity is encoded by the single reconstruction map
shared across all designs. -/
theorem genomicAlgorithmicRiskSignature_isCoarsestSufficientInvariant
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) :
    Blindness.TrafficInvariantSeparation.RiskSignaturesFactorThrough risk
      (Blindness.TrafficInvariantSeparation.algorithmicRiskSignature risk) ∧
      ∀ (Invariant : Type*) (invariant : Design → Invariant),
        Blindness.TrafficInvariantSeparation.RiskSignaturesFactorThrough risk invariant →
          ∀ left right, invariant left = invariant right →
            Blindness.TrafficInvariantSeparation.algorithmicRiskSignature risk left =
              Blindness.TrafficInvariantSeparation.algorithmicRiskSignature risk right :=
  Blindness.TrafficInvariantSeparation.algorithmicRiskSignature_isCoarsestSufficientInvariant risk

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
        Blindness.TrafficInvariantSeparation.finiteRankOneTrafficCorrection coefficient hasOddDegree
          vertices edges
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
    Blindness.TrafficInvariantSeparation.ConcreteBalancedPSDPressureWitness coefficient hasOddDegree
      vertices edges
      baseline spikeStrength temperature :=
  Blindness.TrafficInvariantSeparation.concreteBalancedPSDPressureWitness coefficient hasOddDegree
    vertices edges
    hconnected baseline spikeStrength temperature hbaseline hspike hcritical

/-- **A rare LD subspace is invisible to every fixed traffic coordinate but survives a
logarithmic number of power iterations.**  The exceptional fraction is `4⁻ᵏ`; each fixed graph
sum loses it, while `k` iterations amplify its squared output by `4ᵏ`. -/
theorem rareLDSubspace_fixedTrafficInvisible_logRuntimeVisible :
    FixedTrafficLogRuntimeSeparation :=
  Blindness.TrafficInvariantSeparation.fixedTraffic_invisible_logRuntime_visible

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
        Blindness.TrafficInvariantSeparation.amplifiedDegreeOneTrafficDifference baseline iteration
          = 2 :=
  Blindness.TrafficInvariantSeparation.limitingTraffic_insufficient_for_unstableDegreeOne baseline

/-- **Bulk LD spectrum does not determine extremal spectral or SDP behavior.**
A single positive LD outlier vanishes from every normalized spectral test
average, while changing both the exact spectral maximum and the full
trace-one positive-semidefinite SDP optimum by its complete strength. -/
theorem genomicBulkSpectralLaw_invisible_extremalSpectrumAndSDP_visible
    (baseline spikeStrength : ℝ) (hspike : 0 < spikeStrength) :
    Blindness.TrafficInvariantSeparation.BulkSpectralLawExtremalSDPSeparation baseline spikeStrength
      :=
  Blindness.TrafficInvariantSeparation.bulkSpectralLaw_invisible_extremalSpectrumAndSDP_visible
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
          Blindness.TrafficInvariantSeparation.finiteRankOneTrafficCorrection coefficient
            hasOddDegree vertices edges
            (population + 1))
        Filter.atTop (nhds 0) ∧
      0 < Blindness.TrafficInvariantSeparation.cwVariationalPressureGap tlam :=
  Blindness.TrafficInvariantSeparation.finiteRankOneTraffic_invisible_variationalPressure_visible
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
    Blindness.TrafficInvariantSeparation.RankOneSpikeInvisibleWithFinitePressure coefficient
      hasOddDegree vertices edges tlam :=
  Blindness.TrafficInvariantSeparation.finiteRankOneTraffic_invisible_finitePressure_visible
    coefficient hasOddDegree vertices edges hconnected tlam hcritical

/-- **Finite genomic Gibbs lower bound.**  At every nonempty population, each
interior LD magnetisation objective lower-bounds the genuine Rademacher
pressure.  This is the exact finite change-of-measure theorem behind the sharp
counterexample. -/
theorem genomicFiniteCWPressure_dominatesVariationalObjective
    (population : ℕ) (tlam m : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) (hm : |m| < 1) :
    Blindness.TrafficInvariantSeparation.cwObjective tlam m ≤
      Blindness.TrafficInvariantSeparation.finiteCWPressureGap population tlam :=
  Blindness.TrafficInvariantSeparation.finiteCWPressureGap_ge_cwObjective
    population tlam m hpopulation htlam hm

/-- Every admissible genomic magnetisation class has normalized Gibbs mass
at most one at and below the Curie--Weiss threshold.  This is the finite
typewise estimate that controls the full partition function without an LDP. -/
theorem genomicFiniteCWTypeMass_le_one_of_subcritical
    (population upSpins : ℕ) (tlam : ℝ) (hcritical : tlam ≤ 1)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    Blindness.TrafficInvariantSeparation.finiteCWTypeMass population tlam upSpins ≤ 1 :=
  Blindness.TrafficInvariantSeparation.finiteCWTypeMass_le_one_of_subcritical population upSpins
    tlam
    hcritical hupSpins

/-- **Exact finite genomic pressure phase boundary.**  For nonnegative LD
coupling, the genuine normalized finite-population Rademacher pressure tends
to its unspiked value exactly when `tλ ≤ 1`; throughout `tλ > 1` a uniform
interior genotype-frequency witness prevents convergence to zero. -/
theorem genomicFiniteCWPressure_exactCriticalPoint
    (tlam : ℝ) (htlam : 0 ≤ tlam) :
    Filter.Tendsto
        (fun population : ℕ ↦ Blindness.TrafficInvariantSeparation.finiteCWPressureGap (population +
          1) tlam)
        Filter.atTop (nhds 0) ↔
      tlam ≤ 1 :=
  Blindness.TrafficInvariantSeparation.finiteCWPressureGap_tendsto_zero_iff tlam htlam

/-- The genuine finite genomic Curie--Weiss pressure converges to the complete
variational LD pressure for every nonnegative coupling, with no asymptotic
principle assumed beyond the proved finite type-count squeeze. -/
theorem genomicFiniteCWPressure_convergesToVariational
    (tlam : ℝ) (htlam : 0 ≤ tlam) :
    Filter.Tendsto
      (fun population : ℕ ↦ Blindness.TrafficInvariantSeparation.finiteCWPressureGap (population +
        1) tlam)
      Filter.atTop (nhds (Blindness.TrafficInvariantSeparation.cwVariationalPressureGap tlam)) :=
  Blindness.TrafficInvariantSeparation.finiteCWPressureGap_tendsto_variationalPressure tlam htlam

/-- Finite genomic Curie--Weiss pressure converges uniformly to its
variational LD pressure over the entire nonnegative coupling half-line. -/
theorem genomicFiniteCWPressure_convergesUniformlyOnNonnegative :
    TendstoUniformlyOn
      (fun population : ℕ ↦ fun tlam : ℝ ↦
        Blindness.TrafficInvariantSeparation.finiteCWPressureGap (population + 1) tlam)
      Blindness.TrafficInvariantSeparation.cwVariationalPressureGap Filter.atTop (Set.Ici 0) :=
  Blindness.TrafficInvariantSeparation.finiteCWPressureGap_tendstoUniformlyOn_nonnegative

/-- Every positive finite genomic population already has the same sharp
half-Lipschitz pressure stability as the thermodynamic limit. -/
theorem genomicFiniteCWPressure_isHalfLipschitz
    (population : ℕ) (hpopulation : 0 < population) :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal)
      (Blindness.TrafficInvariantSeparation.finiteCWPressureGap population) :=
  Blindness.TrafficInvariantSeparation.finiteCWPressureGap_lipschitzWith population hpopulation

/-- Every positive finite genomic population has pressure monotone in
effective LD coupling. -/
theorem genomicFiniteCWPressure_isMonotone
    (population : ℕ) (hpopulation : 0 < population) :
    Monotone (Blindness.TrafficInvariantSeparation.finiteCWPressureGap population) :=
  Blindness.TrafficInvariantSeparation.monotone_finiteCWPressureGap population hpopulation

/-- The same finite-volume statement in direct pressure language: the
rank-one LD-spiked genomic pressure is strictly larger than the unspiked
baseline at every nonempty population throughout `tλ > 1`. -/
theorem positiveLDSpike_finitePressureExceedsBaseline
    (baseline : ℝ) (population : ℕ)
    (temperature spikeStrength : ℝ) (hpopulation : 0 < population)
    (hcritical : 1 < temperature * spikeStrength) :
    Blindness.TrafficInvariantSeparation.finiteBaselineRademacherPressure baseline temperature <
      Blindness.TrafficInvariantSeparation.finiteRankOneRademacherPressure
        baseline population temperature spikeStrength :=
  Blindness.TrafficInvariantSeparation.finiteRankOneRademacherPressure_gt_baseline
    baseline population temperature spikeStrength hpopulation hcritical

/-- The direct spiked-minus-baseline genomic pressure converges to zero
exactly when the nonnegative effective LD coupling is at most one. -/
theorem positiveLDSpike_pressureDifference_exactCriticalPoint
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    Blindness.TrafficInvariantSeparation.FiniteRankOnePressureCriticalStatement baseline temperature
      spikeStrength :=
  Blindness.TrafficInvariantSeparation.finiteRankOneRademacherPressure_difference_tendsto_zero_iff
    baseline temperature spikeStrength hcoupling

/-- The full finite LD-spiked genomic pressure converges to baseline plus the
exact Curie--Weiss variational pressure. -/
theorem positiveLDSpike_pressure_convergesToVariational
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    Blindness.TrafficInvariantSeparation.FiniteRankOnePressureVariationalLimitStatement
      baseline temperature spikeStrength :=
  Blindness.TrafficInvariantSeparation.finiteRankOneRademacherPressure_tendsto_variational
    baseline temperature spikeStrength hcoupling

/-- At fixed nonnegative temperature, the finite LD-spiked genomic pressure
converges uniformly over every nonnegative spike strength. -/
theorem positiveLDSpike_pressure_convergesUniformlyOnNonnegativeStrength
    (baseline temperature : ℝ) (htemperature : 0 ≤ temperature) :
    Blindness.TrafficInvariantSeparation.FiniteRankOnePressureUniformLimitStatement baseline
      temperature :=
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
    Blindness.TrafficInvariantSeparation.RankOneSpikeRefutesBothDichotomies coefficient hasOddDegree
      vertices edges
      alignment orthogonal aligned baseline spikeStrength population temperature :=
  Blindness.TrafficInvariantSeparation.rankOneTraffic_groundState_pressure_counterexample
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
        Blindness.TrafficInvariantSeparation.rankOneEnergyDensity baseline spikeStrength population
          (if state = true then population else 0)) ∧
      Blindness.TrafficInvariantSeparation.rankOneEnergyDensity baseline spikeStrength population
        (if false = true then population else 0) = baseline) ∧
      0 < Blindness.TrafficInvariantSeparation.cwObjective tlam 1 := by
  refine ⟨Blindness.TrafficInvariantSeparation.rankOne_groundState_certificate
    (fun state : Bool ↦ if state = true then population else 0) false
    baseline spikeStrength population hspike ?_,
      Blindness.TrafficInvariantSeparation.curieWeiss_supercritical_witness tlam hlarge⟩
  simp

/-- **The positive LD-spike pressure has its exact Curie–Weiss critical point.**  The pressure
objective is nonpositive for every admissible overlap when `tλ ≤ 1`, and an explicit interior
overlap has positive objective as soon as `tλ > 1`. -/
theorem ldOverlapPressure_exactCriticalPoint (tlam : ℝ) :
    (tlam ≤ 1 → ∀ m : ℝ, |m| ≤ 1 → Blindness.TrafficInvariantSeparation.cwObjective tlam m ≤ 0) ∧
      (1 < tlam → ∃ m : ℝ, |m| < 1 ∧ 0 < Blindness.TrafficInvariantSeparation.cwObjective tlam m) :=
  Blindness.TrafficInvariantSeparation.curieWeiss_critical_dichotomy tlam

/-- **The supremal LD pressure, not merely its pointwise objective, has exact
critical point `tλ = 1`.**  The pressure gap is zero precisely on the
subcritical side and strictly positive above it. -/
theorem ldVariationalPressureGap_exactCriticalPoint (tlam : ℝ) :
    Blindness.TrafficInvariantSeparation.cwVariationalPressureGap tlam = 0 ↔ tlam ≤ 1 :=
  Blindness.TrafficInvariantSeparation.cwVariationalPressureGap_eq_zero_iff tlam

/-- The limiting LD pressure is globally stable under coupling changes: it is
`1/2`-Lipschitz, continuous, monotone, and convex. -/
theorem ldVariationalPressureGap_globalRegularity :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal)
      Blindness.TrafficInvariantSeparation.cwVariationalPressureGap ∧
      Continuous Blindness.TrafficInvariantSeparation.cwVariationalPressureGap ∧
        Monotone Blindness.TrafficInvariantSeparation.cwVariationalPressureGap ∧
          ConvexOn ℝ Set.univ Blindness.TrafficInvariantSeparation.cwVariationalPressureGap :=
  ⟨Blindness.TrafficInvariantSeparation.cwVariationalPressureGap_lipschitzWith,
    Blindness.TrafficInvariantSeparation.continuous_cwVariationalPressureGap,
    Blindness.TrafficInvariantSeparation.monotone_cwVariationalPressureGap,
    Blindness.TrafficInvariantSeparation.convexOn_cwVariationalPressureGap⟩

/-- **The matched-Bayes random-design question reduces to its scalar channel
with the sharp two-error ledger.**  A scalar mutual-information gap `Δ` loses
at most the sum of the independently certified left and right errors. -/
theorem matchedBayes_randomDesignGap_fromScalarGap_asymmetric
    (scalarLeft scalarRight randomLeft randomRight leftError rightError delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ leftError)
    (hright : |randomRight - scalarRight| ≤ rightError)
    (hgap : scalarRight - scalarLeft = delta) :
    delta - (leftError + rightError) ≤ randomRight - randomLeft :=
  Blindness.TrafficInvariantSeparation.randomDesign_gap_of_scalarGap_asymmetric scalarLeft
    scalarRight randomLeft randomRight
    leftError rightError delta hleft hright hgap

/-- The equal-error specialization loses at most `2ε`. -/
theorem matchedBayes_randomDesignGap_from_scalarGap
    (scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ epsilon)
    (hright : |randomRight - scalarRight| ≤ epsilon)
    (hgap : scalarRight - scalarLeft = delta) :
    delta - 2 * epsilon ≤ randomRight - randomLeft :=
  Blindness.TrafficInvariantSeparation.randomDesign_gap_of_scalarGap scalarLeft scalarRight
    randomLeft randomRight epsilon delta
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
  Blindness.TrafficInvariantSeparation.randomDesign_eventually_separates_of_scalarGap_asymmetric
    regime
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
  Blindness.TrafficInvariantSeparation.randomDesign_eventually_separates_of_scalarGap regime
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
  Blindness.TrafficInvariantSeparation.randomDesign_separates_of_scalarGap_of_inverseSqrtAspect
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
  · exact Blindness.TrafficInvariantSeparation.aspectAtTop_iff_inverseTendstoNhdsGTZero regime
      aspectRatio
  · intro index
    exact Blindness.TrafficInvariantSeparation.div_sqrt_eq_mul_sqrt_inv constant (aspectRatio index)

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
  Blindness.TrafficInvariantSeparation.randomDesign_eventually_separates_of_scalarGap_of_aspectAtTop
    regime
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
  Blindness.TrafficInvariantSeparation.matchedInformationError_tendsto_zero_of_wishartRatio
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
    (certificate : ℕ → Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
    (varianceBound spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength)
    (hvarianceBound : ∀ population,
      (certificate population).variance ≤ varianceBound)
    (hnuclear : ∀ population,
      (certificate population).nuclearDistance =
        (Blindness.TrafficInvariantSeparation.finiteRankOneSingularSpectrum population spikeStrength
          hspike).normalizedNuclearDistance) :
    Filter.Tendsto
      (fun population ↦ (certificate population).informationPath 1 -
        (certificate population).informationPath 0)
      Filter.atTop (nhds 0) :=
  Blindness.TrafficInvariantSeparation.matchedInformationPath_rankOne_tendsto_zero_of_varianceBound
    certificate varianceBound spikeStrength hspike hvarianceBound hnuclear

/-- The genomic matched-information nuclear estimate follows from a certified
matrix I--MMSE interpolation path and its posterior-covariance trace bound. -/
theorem matchedBayes_informationPath_nuclearBound
    (certificate : Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      certificate.variance / 2 * certificate.nuclearDistance :=
  Blindness.TrafficInvariantSeparation.matchedInformationPath_nuclear_bound certificate

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
  Blindness.TrafficInvariantSeparation.matchedInformationError_le_of_wishartFrobenius
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
  Blindness.TrafficInvariantSeparation.matchedInformationError_le_of_wishartMomentIdentity
    dimension sampleSize signal variance operatorBound covarianceTrace
    covarianceTraceSq frobeniusSecondMoment frobeniusError nuclearError
    informationError hdimension hsampleSize hsignal hvariance hoperator htrace
    htraceSq hmoment hfrobenius hnuclear hinformation

/-- Certified genomic matched-information paths become asymptotically
indistinguishable whenever their covariance perturbations have vanishing rank
fraction and their prior variances admit one uniform bound. -/
theorem matchedBayes_certifiedSublinearRank_isInvisible_ofVarianceBound
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
    (varianceBound operatorBound : ℝ) (rankFraction : Index → ℝ)
    (hvarianceBound : ∀ index, (certificate index).variance ≤ varianceBound)
    (hrankVanishing : Filter.Tendsto rankFraction regime (nhds 0))
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) :
    Blindness.TrafficInvariantSeparation.MatchedInformationPathGapTendsToZero regime certificate :=
  Blindness.TrafficInvariantSeparation.matchedInformationPath_lowRank_tendsto_zero_of_varianceBound
    regime certificate
    varianceBound operatorBound rankFraction hvarianceBound
    hrankVanishing hnuclearRank

/-- Exact common variance is only a specialization of uniform boundedness. -/
theorem matchedBayes_certifiedSublinearRank_isInvisible
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
    (operatorBound : ℝ) (rankFraction : Index → ℝ)
    (hvariance : ∃ variance : ℝ, ∀ index, (certificate index).variance = variance)
    (hrankVanishing : Filter.Tendsto rankFraction regime (nhds 0))
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) :
    Blindness.TrafficInvariantSeparation.MatchedInformationPathGapTendsToZero regime certificate :=
  Blindness.TrafficInvariantSeparation.matchedInformationPath_lowRank_tendsto_zero regime
    certificate operatorBound
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
  Blindness.TrafficInvariantSeparation.matchedDensity_lowRank_tendsto_zero_of_nuclearEstimate
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
  Blindness.TrafficInvariantSeparation.matchedDensity_positiveGap_forces_rankFraction
    densityGap constant rankFraction delta hconstant hdelta hgap hnuclear

/-- A finite genomic information gap certified directly by an I--MMSE path
forces an explicit rank fraction under only a prior-variance upper bound. -/
theorem matchedBayes_certifiedPositiveGap_forcesExtensiveRank
    (certificate : Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
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
    (certificate : Index → Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
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
  Blindness.TrafficInvariantSeparation.matchedInformationPath_persistentGap_requires_extensiveRank
    regime certificate
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
  ⟨Blindness.TrafficInvariantSeparation.matchedDensity_eventualGap_forces_eventualRankFraction
      regime densityGap rankFraction constant delta hconstant hdelta hgap hnuclear,
    Blindness.TrafficInvariantSeparation.matchedDensity_eventualGap_not_sublinearRank
      regime densityGap rankFraction constant delta hconstant hdelta hgap hnuclear⟩

/-- A degree-limited genomic risk functional cannot distinguish designs with the same truncated
traffic profile, so the complete Bayes gap transfers to every procedure in the class. -/
theorem degreeLimitedGenomicRisk_fullGapHardness
    {Algorithm : Type*} {D : ℕ} (risk : Algorithm →
      Blindness.TrafficInvariantSeparation.TruncatedTrafficRisk D)
    (left right : Fin (D + 1) → ℝ) (htraffic : left = right)
    (bayesLeft bayesRight : ℝ)
    (hoptimalRight : ∀ algorithm, bayesRight ≤ (risk algorithm).evaluate right)
    (algorithm : Algorithm) :
    bayesRight - bayesLeft ≤ (risk algorithm).evaluate left - bayesLeft :=
  Blindness.TrafficInvariantSeparation.truncatedTraffic_hardness risk left right htraffic bayesLeft
    bayesRight hoptimalRight algorithm

/-- **The corrected stable low-degree theorem.**  A degree-`D` genomic graph
polynomial is quantitatively controlled by the maximum retained LD-traffic
error times its coefficient `ℓ¹` mass.  Thus exact finite factorization
passes to limiting traffic only with a coefficient-growth/resolution bound. -/
theorem stableDegreeLimitedGenomicRisk_quantitativeTrafficBound
    {D : ℕ} (risk : Blindness.TrafficInvariantSeparation.TruncatedTrafficRisk D)
    (left right : Fin (D + 1) → ℝ) (epsilon : ℝ)
    (hcoordinate : ∀ graph, |left graph - right graph| ≤ epsilon) :
    |risk.evaluate left - risk.evaluate right| ≤
      (∑ graph, |risk.coefficient graph|) * epsilon :=
  Blindness.TrafficInvariantSeparation.truncatedTrafficRisk_abs_sub_le_coefficientMass_mul
    risk left right epsilon hcoordinate

/-- Uniformly bounded coefficient mass turns quantitative LD-traffic
convergence into convergence of the corresponding stable low-degree genomic
procedure. -/
theorem stableDegreeLimitedGenomicRisk_convergesOfBoundedCoefficientMass
    {D : ℕ} (risk : ℕ → Blindness.TrafficInvariantSeparation.TruncatedTrafficRisk D)
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
  Blindness.TrafficInvariantSeparation.truncatedTrafficRisk_tendsto_zero_of_boundedCoefficientMass
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
  Blindness.TrafficInvariantSeparation.highTemperatureTrafficLimit_eq_of_geometricTruncation
    leftLimit rightLimit C q commonTruncation hqNonneg hq hleft hright

/-- **Every finite LD-traffic depth is strictly weaker than the next.**  For
each `D`, two genuine probability laws on uniformly conditioned diagonal LD
values in `[1,2]` agree on every connected diagonal traffic coordinate with at
most `D` edges and differ at `D+1` edges. -/
theorem genomicLDTrafficHierarchy_strictAtEveryDegree (D : ℕ) :
    ∃ left right : Fin (D + 2) → ℝ,
      Blindness.TrafficInvariantSeparation.IsMomentMatchedProbabilityPair D left right ∧
        Blindness.TrafficInvariantSeparation.SeparatesAtNextDiagonalTraffic D left right :=
  Blindness.TrafficInvariantSeparation.exists_probabilityWeights_matchingMoments_through_degree D

/-- **At every finite LD-traffic depth there is one probability pair blind to
the entire graph-polynomial risk class.**  This is stronger than pairwise
moment matching: the same pair equalizes every truncated risk functional while
its next traffic coordinate remains different. -/
theorem genomicLDTrafficBlindPair_existsAtEveryDegree (D : ℕ) :
    ∃ left right : Fin (D + 2) → ℝ,
      Blindness.TrafficInvariantSeparation.IsBlindPairForEveryTruncatedTrafficRisk D left right :=
  Blindness.TrafficInvariantSeparation.exists_probabilityPair_blindToEveryTruncatedTrafficRisk D

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
      Blindness.TrafficInvariantSeparation.SameEqualityPattern left right)
    (hinvariant : ∀ (permutation : Equiv.Perm Locus) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    (∑ monomial, coefficient monomial * value monomial) =
      ∑ graph, Blindness.TrafficInvariantSeparation.graphShapeCoefficient shape coefficient graph *
        ∑ monomial, if shape monomial = graph then value monomial else 0 :=
  Blindness.TrafficInvariantSeparation.invariantPolynomial_graphSum_factorization shape coefficient
    value hshape hinvariant

/-- **Canonical finite genomic traffic factorization.**  The graph index is
the quotient of endpoint assignments by equality pattern, so callers need not
provide or validate a separate graph-shape encoding. -/
theorem permutationInvariantGenomicPolynomial_factorsThroughCanonicalLDGraphs
    {Slot Locus : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Locus]
    (coefficient value : (Slot → Locus) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Locus) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    Blindness.TrafficInvariantSeparation.CanonicalTrafficFactorizationStatement coefficient value :=
  Blindness.TrafficInvariantSeparation.invariantPolynomial_canonicalTraffic_factorization
    coefficient value hinvariant

/-- **Canonical rooted genomic traffic factorization.**  The distinguished
`none` slot records the output locus, formally supplying the rooted graph
version needed for permutation-equivariant vector estimators. -/
theorem permutationEquivariantGenomicPolynomial_factorsThroughRootedLDGraphs
    {Slot Locus : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Locus]
    (coefficient value : (Option Slot → Locus) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Locus) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    Blindness.TrafficInvariantSeparation.RootedCanonicalTrafficFactorizationStatement coefficient
      value :=
  Blindness.TrafficInvariantSeparation.rootedInvariantPolynomial_canonicalTraffic_factorization
    coefficient value hinvariant

/-- A genomic polynomial of total degree at most `D`, decomposed into its
homogeneous degrees, factors exactly through canonical LD traffic graphs with at most `D` ordered
edges. -/
theorem degreeLimitedGenomicPolynomial_factorsThroughCanonicalLDGraphs
    {D : ℕ} {Locus : Type*} [Fintype Locus]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Locus) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Locus) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial) :
    Blindness.TrafficInvariantSeparation.DegreeAtMostTrafficFactorizationStatement coefficient value
      :=
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
    Blindness.TrafficInvariantSeparation.DegreeAtMostRootedTrafficFactorizationStatement coefficient
      value :=
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
    (htraffic : Blindness.TrafficInvariantSeparation.degreeAtMostCanonicalTrafficProfile leftValue =
      Blindness.TrafficInvariantSeparation.degreeAtMostCanonicalTrafficProfile rightValue) :
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
    (htraffic : Blindness.TrafficInvariantSeparation.degreeAtMostRootedCanonicalTrafficProfile
      leftValue =
      Blindness.TrafficInvariantSeparation.degreeAtMostRootedCanonicalTrafficProfile rightValue) :
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
    (htraffic : Blindness.TrafficInvariantSeparation.degreeAtMostCanonicalTrafficProfile leftValue =
      Blindness.TrafficInvariantSeparation.degreeAtMostCanonicalTrafficProfile rightValue)
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
  Blindness.TrafficInvariantSeparation.lipschitzPressureProfiles_dist_le_of_net
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
  Blindness.TrafficInvariantSeparation.lipschitzPressureProfiles_eq_of_eqOn_dense
    K left right hleft hright parameters hdense hagrees

/-- **Functional genomic right-profile compactness.**  On a compact tilt
domain, the uniformly bounded pressure functions sharing one Lipschitz constant
form a compact family in the uniform metric. -/
theorem genomicBoundedLipschitzPressureFamily_isCompact
    {Parameter : Type*} [PseudoMetricSpace Parameter] [CompactSpace Parameter]
    (K : NNReal) (bound : ℝ) :
    IsCompact (boundedLipschitzPressureFamily
      (Parameter := Parameter) K bound) :=
  Blindness.TrafficInvariantSeparation.isCompact_boundedLipschitzPressureFamily K bound

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
  Blindness.TrafficInvariantSeparation.boundedLipschitzPressureFamily_tendsto_subseq K bound
    profiles hprofiles

/-- **The nonperturbative genomic LD profile has a genuine compact state space.**
Uniformly bounded countable pressure coordinates admit one common subsequence
on which every prior/replica/tilt coordinate converges.  This is the exact
diagonal compactness statement needed before any model-specific identification
of the limiting right-convergence profile. -/
theorem genomicExponentialProfile_hasCommonCoordinatewiseSubsequence
    (bound : ℝ) (profiles : ℕ → Blindness.TrafficInvariantSeparation.BoundedExponentialProfile
      bound) :
    ∃ limit : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound, ∃ subsequence :
      ℕ → ℕ,
      StrictMono subsequence ∧
        ∀ coordinate : ℕ,
          Filter.Tendsto (fun n ↦ profiles (subsequence n) coordinate)
            Filter.atTop (nhds (limit coordinate)) :=
  Blindness.TrafficInvariantSeparation.boundedExponentialProfile_common_coordinatewise_subsequence
    bound profiles

/-- **The explicit exponential-profile formula is a genuine separating
distance.**  It is nonnegative, symmetric, triangular, and vanishes exactly on
identical genomic LD pressure profiles. -/
theorem genomicExponentialProfileDistance_metricLaws
    {bound : ℝ} (left middle right : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile
      bound) :
    0 ≤ exponentialProfileDistance left right ∧
      exponentialProfileDistance left right = exponentialProfileDistance right left ∧
      exponentialProfileDistance left right ≤
        exponentialProfileDistance left middle + exponentialProfileDistance middle right ∧
      (exponentialProfileDistance left right = 0 ↔ left = right) :=
  ⟨Blindness.TrafficInvariantSeparation.exponentialProfileDistance_nonneg left right,
    Blindness.TrafficInvariantSeparation.exponentialProfileDistance_comm left right,
    Blindness.TrafficInvariantSeparation.exponentialProfileDistance_triangle left middle right,
    Blindness.TrafficInvariantSeparation.exponentialProfileDistance_eq_zero_iff left right⟩

/-- **The genomic right-profile formula is an actual compact metric space.**
The installed metric is exactly the weighted capped-coordinate distance, and
its complete carrier is compact in the ordinary topological sense. -/
theorem genomicExponentialProfilePoint_isCompactMetricSpace (bound : ℝ) :
    IsCompact (Set.univ : Set (Blindness.TrafficInvariantSeparation.ExponentialProfilePoint bound))
      :=
  isCompact_univ

/-- Standard convergence in the bundled genomic right-profile metric is
exactly simultaneous convergence of every prior/replica/tilt coordinate. -/
theorem genomicExponentialProfilePoint_converges_iff_coordinatewise
    {bound : ℝ} {profiles : ℕ → Blindness.TrafficInvariantSeparation.ExponentialProfilePoint bound}
    {limit : Blindness.TrafficInvariantSeparation.ExponentialProfilePoint bound} :
    Filter.Tendsto profiles Filter.atTop (nhds limit) ↔
      ∀ coordinate : ℕ,
        Filter.Tendsto (fun n ↦ profiles n coordinate)
          Filter.atTop (nhds (limit coordinate)) :=
  Blindness.TrafficInvariantSeparation.exponentialProfilePoint_tendsto_iff_coordinatewise

/-- **The explicit genomic right-profile distance induces exactly coordinatewise
pressure convergence.**  Thus convergence in the metric is neither weaker nor
stronger than simultaneous convergence of every enumerated prior/replica/tilt
coordinate. -/
theorem genomicExponentialProfileDistance_converges_iff_coordinatewise
    {bound : ℝ} {profiles : ℕ → Blindness.TrafficInvariantSeparation.BoundedExponentialProfile
      bound}
    {limit : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound} :
    Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
        Filter.atTop (nhds 0) ↔
      ∀ coordinate : ℕ,
        Filter.Tendsto (fun n ↦ profiles n coordinate)
          Filter.atTop (nhds (limit coordinate)) :=
  Blindness.TrafficInvariantSeparation.exponentialProfileDistance_tendsto_zero_iff_coordinatewise

/-- **Finite genomic pressure data approximate the full right profile with an
explicit modulus.**  The profile space has diameter at most two, and agreement
on coordinates `0,…,K-1` leaves distance at most the geometric tail `2·2⁻ᴷ`. -/
theorem genomicExponentialProfileDistance_finitePrefixControl
    {bound : ℝ} (left right : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound)
    (prefixLength : ℕ)
    (hprefix : ∀ coordinate < prefixLength, left coordinate = right coordinate) :
    exponentialProfileDistance left right ≤ 2 ∧
      exponentialProfileDistance left right ≤
        2 * (1 / 2 : ℝ) ^ prefixLength :=
  ⟨Blindness.TrafficInvariantSeparation.exponentialProfileDistance_le_two left right,
    Blindness.TrafficInvariantSeparation.exponentialProfileDistance_le_geometricTail_of_prefix_eq
      left right prefixLength hprefix⟩

/-- **Bounded genomic exponential profiles are sequentially compact in the
explicit weighted distance.**  The same subsequence works simultaneously for
every enumerated prior/replica/tilt coordinate. -/
theorem genomicExponentialProfile_compactInExplicitDistance
    (bound : ℝ) (profiles : ℕ → Blindness.TrafficInvariantSeparation.BoundedExponentialProfile
      bound) :
    ∃ limit : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound, ∃ subsequence :
      ℕ → ℕ,
      StrictMono subsequence ∧
        Filter.Tendsto
          (fun n ↦ exponentialProfileDistance (profiles (subsequence n)) limit)
          Filter.atTop (nhds 0) :=
  Blindness.TrafficInvariantSeparation.boundedExponentialProfile_compact_subsequence_in_distance
    bound profiles


/-- **Exact criterion for the Beta curve.**  At conditional-Laplace-transform level the Beta
power profile is equivalent to an `x`-independent transform after subtracting the logarithmic
front response.  When the transforms determine the laws, this is the claimed common-noise
representation and is both necessary and sufficient. -/
theorem speedConditionedGenealogy_beta_iff_logResponse
    (gamma : ℝ) (conditionalLaplace : ℝ → ℝ → ℝ) :
    Blindness.MarkedBreakout.HasBetaTiltInvariant gamma conditionalLaplace ↔
      Blindness.MarkedBreakout.HasFractionIndependentCenteredTransform gamma conditionalLaplace :=
  Blindness.MarkedBreakout.hasBetaTiltInvariant_iff_centeredTransformIndependent gamma
    conditionalLaplace

/-- **The `log³ N` clock is a front-response statement.**  At susceptibility exponent three the
genealogical clock is the cube of the front width; the coalescent rate law contributes no cube. -/
theorem pioneerSusceptibility_setsGenealogicalClock (width : ℝ) :
    Blindness.MarkedBreakout.genealogicalTimescale width 3 = width ^ 3 :=
  Blindness.MarkedBreakout.genealogicalTimescale_three width

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

end Descent.Conditionals
