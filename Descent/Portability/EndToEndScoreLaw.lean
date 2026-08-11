/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StructuredPresentDay
import Descent.PopGen.GeneticArchitectureDiscovery
import Descent.PopGen.Shrinkage
import Descent.Portability.PGSCalibrationTheory.CalibrationDefinitions
import Descent.Portability.PGSCalibrationTheory.PopulationCalibrationDrift
import Descent.Portability.PhenomeWidePortability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

/-!
# End-to-end selected-score and calibration law

This file is the score-construction layer between a demographic moment law and the metric
charts.  Clumping cutoff, physical window, threshold family, discovery sample size, marker
count and GWAS sampling law are all inputs.  No study layout and no global retention scalar
appears in the law.  The output is a score mean and a `Core.ScoreMoments` tuple in each deme,
which is exactly what the existing metric and calibration layers consume.
-/

/-! ## B1. The P+T selection law -/

/-- A real quantity known to be strictly positive. -/
structure PositiveScale where
  value : ℝ
  value_pos : 0 < value

/-- A probability strictly inside the unit interval. -/
structure InteriorProbability where
  value : ℝ
  value_pos : 0 < value
  value_lt_one : value < 1

/-- Parameters of a P+T construction.  They are supplied by a study instance, never selected
inside the law. -/
structure PTParameters where
  clumpR2Cutoff : ℝ
  clumpWindowBp : ℕ
  discoverySampleSize : ℕ
  clumpR2Cutoff_nonneg : 0 ≤ clumpR2Cutoff
  clumpR2Cutoff_lt_one : clumpR2Cutoff < 1
  discoverySampleSize_pos : 0 < discoverySampleSize

/-- The fixed part of a P+T analysis.  LD geometry and the threshold family do not change
with a realised GWAS draw. -/
structure PTProtocol (thresholdCount m : ℕ) where
  parameters : PTParameters
  positionBp : Fin m → ℕ
  sourceR2 : Fin m → Fin m → ℝ
  sourceR2_nonnegative : ∀ i j, 0 ≤ sourceR2 i j
  sourceR2_le_one : ∀ i j, sourceR2 i j ≤ 1
  sourceR2_symmetric : ∀ i j, sourceR2 i j = sourceR2 j i
  pThreshold : Fin thresholdCount → ℝ
  pThreshold_nonnegative : ∀ q, 0 ≤ pThreshold q
  pThreshold_le_one : ∀ q, pThreshold q ≤ 1

/-- Two markers conflict when they lie inside the supplied clumping window and their source
LD reaches the supplied exclusion cutoff.  Equality is excluded, matching retention by a
strict `r² < cutoff` rule. -/
noncomputable def ptConflict {m : ℕ} (parameters : PTParameters) (positionBp : Fin m → ℕ)
    (sourceR2 : Fin m → Fin m → ℝ) (i j : Fin m) : Bool :=
  decide (((positionBp i : ℤ) - (positionBp j : ℤ)).natAbs ≤ parameters.clumpWindowBp ∧
    parameters.clumpR2Cutoff ≤ sourceR2 i j)

/-- Greedy clumping in the supplied significance order.  A marker is kept exactly when no
already-kept marker conflicts with it.  This recursion, rather than an independence
approximation, is the clumping-under-LD law. -/
def greedyClumpAux {α : Type*} (conflict : α → α → Bool) : List α → List α → List α
  | [], kept => kept.reverse
  | x :: xs, kept =>
      if kept.any (fun y ↦ conflict x y) then greedyClumpAux conflict xs kept
      else greedyClumpAux conflict xs (x :: kept)

/-- Run greedy clumping from an empty retained set. -/
def greedyClump {α : Type*} (conflict : α → α → Bool) (ordered : List α) : List α :=
  greedyClumpAux conflict ordered []

/-- A complete P+T design with an arbitrary finite threshold family.  `orderedMarkers` is the
deterministic order used by the clumper; `coversMarkers` prevents silently dropping a marker. -/
structure PTDesign (thresholdCount m : ℕ) where
  protocol : PTProtocol thresholdCount m
  pValue : Fin m → ℝ
  pValue_nonnegative : ∀ i, 0 ≤ pValue i
  pValue_le_one : ∀ i, pValue i ≤ 1
  orderedMarkers : List (Fin m)
  orderedMarkers_nodup : orderedMarkers.Nodup
  orderedMarkers_by_significance :
    orderedMarkers.Pairwise (fun earlier later ↦ pValue earlier ≤ pValue later)
  coversMarkers : ∀ i, i ∈ orderedMarkers

/-- Ordered threshold-eligible markers. -/
noncomputable def PTDesign.eligible {thresholdCount m : ℕ} (d : PTDesign thresholdCount m)
    (q : Fin thresholdCount) : List (Fin m) :=
  d.orderedMarkers.filter fun i ↦ decide (d.pValue i ≤ d.protocol.pThreshold q)

/-- The exact retained marker list at threshold `q`. -/
noncomputable def PTDesign.selected {thresholdCount m : ℕ} (d : PTDesign thresholdCount m)
    (q : Fin thresholdCount) : List (Fin m) :=
  greedyClump
    (ptConflict d.protocol.parameters d.protocol.positionBp d.protocol.sourceR2) (d.eligible q)

/-- A threshold winner is the index whose analytically predicted objective dominates all
other candidates.  Ties are allowed and must be resolved by the caller's declared
ordering, not by an unrecorded search. -/
structure PTWinner {thresholdCount m : ℕ} (d : PTDesign thresholdCount m)
    (objective : Fin thresholdCount → ℝ) where
  index : Fin thresholdCount
  optimal : ∀ q, objective q ≤ objective index

/-- A normalized law over threshold choices.  This is the analytic alternative to selecting
one winner when threshold uncertainty must be propagated. -/
structure PTThresholdMixture (thresholdCount : ℕ) where
  probability : Fin thresholdCount → ℝ
  probability_nonneg : ∀ q, 0 ≤ probability q
  probability_sum_one : ∑ q, probability q = 1

/-- Exact marginalization of any threshold-indexed functional. -/
noncomputable def PTThresholdMixture.expectation {thresholdCount : ℕ}
    (mixture : PTThresholdMixture thresholdCount) (functional : Fin thresholdCount → ℝ) : ℝ :=
  ∑ q, mixture.probability q * functional q

/-- Additive effect-variance mass retained after clumping and thresholding. -/
noncomputable def PTDesign.selectedEffectMass {thresholdCount m : ℕ}
    (d : PTDesign thresholdCount m) (q : Fin thresholdCount)
    (alleleFrequency effect : Fin m → ℝ) : ℝ :=
  (d.selected q).map (fun i ↦
    2 * alleleFrequency i * (1 - alleleFrequency i) * effect i ^ 2) |>.sum

/-- Fraction of total additive effect mass retained by P+T. -/
noncomputable def PTDesign.selectedEffectMassFraction {thresholdCount m : ℕ}
    (d : PTDesign thresholdCount m) (q : Fin thresholdCount)
    (alleleFrequency effect : Fin m → ℝ)
    (_ : (∑ i, 2 * alleleFrequency i * (1 - alleleFrequency i) * effect i ^ 2) ≠ 0) : ℝ :=
  d.selectedEffectMass q alleleFrequency effect /
    (∑ i, 2 * alleleFrequency i * (1 - alleleFrequency i) * effect i ^ 2)

/-- Effect mass surviving the analytically predicted winner. -/
noncomputable def PTWinner.selectedEffectMass {thresholdCount m : ℕ}
    {d : PTDesign thresholdCount m} {objective : Fin thresholdCount → ℝ}
    (winner : PTWinner d objective) (alleleFrequency effect : Fin m → ℝ) : ℝ :=
  d.selectedEffectMass winner.index alleleFrequency effect

/-- Effect mass with threshold uncertainty marginalized rather than optimized away. -/
noncomputable def PTDesign.marginalSelectedEffectMass {thresholdCount m : ℕ}
    (d : PTDesign thresholdCount m) (mixture : PTThresholdMixture thresholdCount)
    (alleleFrequency effect : Fin m → ℝ) : ℝ :=
  mixture.expectation fun q ↦ d.selectedEffectMass q alleleFrequency effect

/-! ## B2. GWAS estimation noise and its composition with selection -/

/-- Inputs to the one-locus OLS noise law.  Every denominator constraint is carried by the
type. -/
structure GWASNoiseMarginal where
  discoverySampleSize : ℕ
  discoverySampleSize_pos : 0 < discoverySampleSize
  residualVariance : PositiveScale
  alleleFrequency : InteriorProbability

/-- The one-locus OLS variance.  The genotype variance is diploid HWE `2p(1-p)`. -/
noncomputable def GWASNoiseMarginal.variance (noise : GWASNoiseMarginal) : ℝ :=
  noise.residualVariance.value /
    (noise.discoverySampleSize *
      (2 * noise.alleleFrequency.value * (1 - noise.alleleFrequency.value)))

/-- GWAS noise evaluated at the discovery sample size fixed by a P+T protocol. -/
noncomputable def PTProtocol.effectNoiseVariance {thresholdCount m : ℕ}
    (protocol : PTProtocol thresholdCount m) (residualVariance : PositiveScale)
    (alleleFrequency : InteriorProbability) : ℝ :=
  GWASNoiseMarginal.variance
    { discoverySampleSize := protocol.parameters.discoverySampleSize
      discoverySampleSize_pos := protocol.parameters.discoverySampleSize_pos
      residualVariance := residualVariance
      alleleFrequency := alleleFrequency }

/-- An exact finite representation of the sampling law of the GWAS output.  Continuous
Gaussian sampling may be approximated by quadrature, but no independence between linked
markers is assumed: each atom carries the whole estimated-effect and p-value vector, so
clumping is performed jointly inside the atom before averaging. -/
structure PTGWASSamplingLaw (omega m : ℕ) where
  probability : Fin omega → ℝ
  probability_nonneg : ∀ w, 0 ≤ probability w
  probability_sum_one : ∑ w, probability w = 1
  trueEffect : Fin m → ℝ
  estimatedEffect : Fin omega → Fin m → ℝ
  pValue : Fin omega → Fin m → ℝ

/-- Expected value under the exact joint GWAS sampling law. -/
noncomputable def PTGWASSamplingLaw.expectation {omega m : ℕ}
    (law : PTGWASSamplingLaw omega m) (f : Fin omega → ℝ) : ℝ :=
  ∑ w, law.probability w * f w

/-- A joint GWAS sampling law certified to have the declared OLS marginal moments.  Linkage
and cross-marker estimation dependence remain arbitrary in the joint atoms. -/
structure PTGWASNoiseModel {omega thresholdCount m : ℕ}
    (protocol : PTProtocol thresholdCount m) (law : PTGWASSamplingLaw omega m) where
  residualVariance : PositiveScale
  alleleFrequency : Fin m → InteriorProbability
  estimationErrorMeanZero : ∀ marker,
    law.expectation (fun draw ↦ law.estimatedEffect draw marker - law.trueEffect marker) = 0
  estimationErrorVariance : ∀ marker,
    law.expectation (fun draw ↦
      (law.estimatedEffect draw marker - law.trueEffect marker) ^ 2) =
      protocol.effectNoiseVariance residualVariance (alleleFrequency marker)

/-- Selection and estimation noise composed in the correct order: select with the realised
joint GWAS output, construct the selected score, and only then average over GWAS samples. -/
noncomputable def expectedSelectedFunctional {omega thresholdCount m : ℕ}
    (law : PTGWASSamplingLaw omega m)
    (designAt : Fin omega → PTDesign thresholdCount m) (q : Fin thresholdCount)
    (functional : Fin omega → List (Fin m) → ℝ) : ℝ :=
  law.expectation fun w ↦ functional w ((designAt w).selected q)

/-- The composition really is selection inside expectation, a useful guard against replacing
the random retained set by a list selected from mean p-values. -/
theorem expectedSelectedFunctional_eq {omega thresholdCount m : ℕ}
    (law : PTGWASSamplingLaw omega m)
    (designAt : Fin omega → PTDesign thresholdCount m) (q : Fin thresholdCount)
    (functional : Fin omega → List (Fin m) → ℝ) :
    expectedSelectedFunctional law designAt q functional =
      ∑ w, law.probability w * functional w ((designAt w).selected q) := rfl

/-! ## C. Within-deme accuracy from the selected score moments -/

/-- Exact genotype/outcome primitives in one deme.  Allele-frequency moments from A1 supply
`genotypeMean`; one- and two-locus moments from A1/A2 supply `genotypeCovariance`; the genetic
architecture supplies the score/outcome cross-covariance. -/
structure DemeGeneticMomentPrimitive (markerCount : ℕ) where
  genotypeMean : Fin markerCount → ℝ
  genotypeCovariance : Matrix (Fin markerCount) (Fin markerCount) ℝ
  outcomeCrossCovariance : Fin markerCount → ℝ
  outcomeVariance : ℝ
  prevalence : ℝ
  covariance_symmetric : ∀ i j, genotypeCovariance i j = genotypeCovariance j i
  outcomeVariance_pos : 0 < outcomeVariance
  prevalence_pos : 0 < prevalence
  prevalence_lt_one : prevalence < 1
  cauchy_schwarz : ∀ weight : Fin markerCount → ℝ,
    (∑ i, weight i * outcomeCrossCovariance i) ^ 2 ≤
      (∑ i, ∑ j, weight i * genotypeCovariance i j * weight j) * outcomeVariance

/-- Score mean from weights and genotype means. -/
noncomputable def DemeGeneticMomentPrimitive.scoreMean {markerCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount)
    (weight : Fin markerCount → ℝ) : ℝ :=
  ∑ i, weight i * primitive.genotypeMean i

/-- Exact quadratic score variance `w' Sigma w`. -/
noncomputable def DemeGeneticMomentPrimitive.scoreVariance {markerCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount)
    (weight : Fin markerCount → ℝ) : ℝ :=
  ∑ i, ∑ j, weight i * primitive.genotypeCovariance i j * weight j

/-- Exact score/outcome covariance `w' Cov(G,Y)`. -/
noncomputable def DemeGeneticMomentPrimitive.predictiveCovariance {markerCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount)
    (weight : Fin markerCount → ℝ) : ℝ :=
  ∑ i, weight i * primitive.outcomeCrossCovariance i

/-- A selected score whose variance is genuinely positive.  Cauchy--Schwarz is inherited
from the primitive for this weight vector. -/
structure AdmissibleScoreWeights {markerCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount) where
  weight : Fin markerCount → ℝ
  scoreVariance_pos : 0 < primitive.scoreVariance weight
  predictiveCovariance_nonneg : 0 ≤ primitive.predictiveCovariance weight

/-- Zero unselected weights and retain the realised GWAS effect at selected markers. -/
noncomputable def PTDesign.selectedWeight {thresholdCount markerCount : ℕ}
    (design : PTDesign thresholdCount markerCount) (threshold : Fin thresholdCount)
    (estimatedEffect : Fin markerCount → ℝ) : Fin markerCount → ℝ :=
  fun marker ↦ if marker ∈ design.selected threshold then estimatedEffect marker else 0

/-- The per-deme output of A+B.  `scoreMean` is required for calibration and pooling;
second moments alone are insufficient for either. -/
structure DemeScoreLaw where
  scoreMean : ℝ
  moments : Descent.Core.ScoreMoments
  moments_admissible : Descent.Core.ScoreMoments.Admissible moments
  predictiveCovariance_nonneg : 0 ≤ moments.predictiveCovariance
  prevalence : ℝ
  prevalence_pos : 0 < prevalence
  prevalence_lt_one : prevalence < 1

/-- The prevalence carried by a deme score law, with its domain evidence. -/
def DemeScoreLaw.prevalenceProbability (law : DemeScoreLaw) : InteriorProbability where
  value := law.prevalence
  value_pos := law.prevalence_pos
  value_lt_one := law.prevalence_lt_one

/-- The exact A+B-to-C constructor. -/
noncomputable def AdmissibleScoreWeights.toDemeScoreLaw {markerCount : ℕ}
    {primitive : DemeGeneticMomentPrimitive markerCount}
    (score : AdmissibleScoreWeights primitive) : DemeScoreLaw where
  scoreMean := primitive.scoreMean score.weight
  moments :=
    { scoreVariance := primitive.scoreVariance score.weight
      predictiveCovariance := primitive.predictiveCovariance score.weight
      outcomeVariance := primitive.outcomeVariance }
  moments_admissible :=
    { scoreVariance_pos := score.scoreVariance_pos
      outcomeVariance_pos := primitive.outcomeVariance_pos
      cauchy_schwarz := primitive.cauchy_schwarz score.weight }
  predictiveCovariance_nonneg := score.predictiveCovariance_nonneg
  prevalence := primitive.prevalence
  prevalence_pos := primitive.prevalence_pos
  prevalence_lt_one := primitive.prevalence_lt_one

/-- Distance-resolved output for a train deme and every target deme. -/
structure DistanceResolvedScoreLaw (D : ℕ) where
  train : Fin D
  atDeme : Fin D → DemeScoreLaw

/-! ### B1+B2 composed into the distance-resolved moment law -/

/-- A complete family of candidate score laws under the joint GWAS sampling distribution.
Each realised GWAS atom performs its own clumping and threshold comparison; selection never
uses mean p-values or a mean retained set. -/
structure PTGWASDistanceLaw (omega thresholdCount markerCount D : ℕ) where
  protocol : PTProtocol thresholdCount markerCount
  sampling : PTGWASSamplingLaw omega markerCount
  noiseModel : PTGWASNoiseModel protocol sampling
  designAt : Fin omega → PTDesign thresholdCount markerCount
  design_protocol_eq : ∀ draw, (designAt draw).protocol = protocol
  design_pValue_eq : ∀ draw, (designAt draw).pValue = sampling.pValue draw
  scoreLawAt : Fin omega → Fin thresholdCount → DistanceResolvedScoreLaw D
  validationDeme : Fin D
  winnerAt : ∀ draw,
    PTWinner (designAt draw)
      (fun threshold ↦ ((scoreLawAt draw threshold).atDeme validationDeme).moments.r2)

/-- Candidate selected in one realised GWAS draw. -/
noncomputable def PTGWASDistanceLaw.winningScoreLaw
    {omega thresholdCount markerCount D : ℕ}
    (law : PTGWASDistanceLaw omega thresholdCount markerCount D)
    (draw : Fin omega) : DistanceResolvedScoreLaw D :=
  law.scoreLawAt draw (law.winnerAt draw).index

/-- Exact expected downstream metric after GWAS noise, clumping, and threshold choice. -/
noncomputable def PTGWASDistanceLaw.expectedWinningMetric
    {omega thresholdCount markerCount D : ℕ}
    (law : PTGWASDistanceLaw omega thresholdCount markerCount D)
    (target : Fin D) (metric : DemeScoreLaw → ℝ) : ℝ :=
  law.sampling.expectation fun draw ↦ metric ((law.winningScoreLaw draw).atDeme target)

/-- Threshold uncertainty marginalized inside each GWAS draw. -/
noncomputable def PTGWASDistanceLaw.expectedMarginalMetric
    {omega thresholdCount markerCount D : ℕ}
    (law : PTGWASDistanceLaw omega thresholdCount markerCount D)
    (thresholdLaw : Fin omega → PTThresholdMixture thresholdCount)
    (target : Fin D) (metric : DemeScoreLaw → ℝ) : ℝ :=
  law.sampling.expectation fun draw ↦
    (thresholdLaw draw).expectation fun threshold ↦
      metric ((law.scoreLawAt draw threshold).atDeme target)

/-- Concrete composition of realised GWAS weights with per-deme genetic moment primitives. -/
structure PTGWASMomentComposition (omega thresholdCount markerCount D : ℕ) where
  protocol : PTProtocol thresholdCount markerCount
  sampling : PTGWASSamplingLaw omega markerCount
  noiseModel : PTGWASNoiseModel protocol sampling
  designAt : Fin omega → PTDesign thresholdCount markerCount
  design_protocol_eq : ∀ draw, (designAt draw).protocol = protocol
  design_pValue_eq : ∀ draw, (designAt draw).pValue = sampling.pValue draw
  primitiveAt : Fin omega → Fin D → DemeGeneticMomentPrimitive markerCount
  train : Fin D
  validationDeme : Fin D
  selectedScoreAt : ∀ draw threshold deme,
    AdmissibleScoreWeights (primitiveAt draw deme)
  selectedWeight_eq : ∀ draw threshold deme,
    (selectedScoreAt draw threshold deme).weight =
      (designAt draw).selectedWeight threshold (sampling.estimatedEffect draw)
  winnerAt : ∀ draw,
    PTWinner (designAt draw) (fun threshold ↦
      ((selectedScoreAt draw threshold validationDeme).toDemeScoreLaw).moments.r2)

/-- Distance-resolved score law generated by one GWAS draw and threshold. -/
noncomputable def PTGWASMomentComposition.distanceLawAt
    {omega thresholdCount markerCount D : ℕ}
    (composition : PTGWASMomentComposition omega thresholdCount markerCount D)
    (draw : Fin omega) (threshold : Fin thresholdCount) : DistanceResolvedScoreLaw D where
  train := composition.train
  atDeme := fun deme ↦ (composition.selectedScoreAt draw threshold deme).toDemeScoreLaw

/-- Forget the construction details only after the exact quadratic moment law has built every
candidate score. -/
noncomputable def PTGWASMomentComposition.toDistanceLaw
    {omega thresholdCount markerCount D : ℕ}
    (composition : PTGWASMomentComposition omega thresholdCount markerCount D) :
    PTGWASDistanceLaw omega thresholdCount markerCount D where
  protocol := composition.protocol
  sampling := composition.sampling
  noiseModel := composition.noiseModel
  designAt := composition.designAt
  design_protocol_eq := composition.design_protocol_eq
  design_pValue_eq := composition.design_pValue_eq
  scoreLawAt := composition.distanceLawAt
  validationDeme := composition.validationDeme
  winnerAt := composition.winnerAt

/-- C1: true within-deme squared accuracy. -/
noncomputable def DemeScoreLaw.r2True (law : DemeScoreLaw) : ℝ := law.moments.r2

/-- Certificate that an A+B moment construction composes with the validated clean-split
portability law.  The score moments remain the primary object; this equality is the independent
clean-split reduction they must satisfy. -/
structure CleanSplitMomentCertificate (law : DemeScoreLaw) (markerCount : ℕ) where
  ancestralR2 : ℝ
  effectMass : Fin markerCount → ℝ
  sourceFrequency : Fin markerCount → ℝ
  sourceEffectiveSize : ℝ
  targetEffectiveSize : ℝ
  generations : ℕ
  ldFactor : ℝ
  r2_reduction : law.r2True =
    cleanSplitTargetR2' ancestralR2 effectMass sourceFrequency
      sourceEffectiveSize targetEffectiveSize generations ldFactor

/-- C2: calibration slope from the same two score moments. -/
noncomputable def DemeScoreLaw.calibrationSlope (law : DemeScoreLaw) : ℝ :=
  law.moments.calibrationSlope

/-- Domain for charts that divide by unexplained variance. -/
structure DemeScoreLaw.ResidualVariation (law : DemeScoreLaw) : Prop where
  r2_lt_one : law.r2True < 1

/-- C2: probit index spread relative to residual spread,
`sqrt(R^2/(1-R^2))`. -/
noncomputable def DemeScoreLaw.probitRiskSpreadRatio
    (law : DemeScoreLaw) (_ : law.ResidualVariation) : ℝ :=
  Real.sqrt (law.r2True / (1 - law.r2True))

/-- Spearman correlation for a bivariate Gaussian with Pearson correlation `r`. -/
noncomputable def gaussianSpearman (r : ℝ) : ℝ :=
  6 / Real.pi * Real.arcsin (r / 2)

/-- Oriented Pearson correlation, retaining information that `R²` squares away. -/
noncomputable def DemeScoreLaw.pearson (law : DemeScoreLaw) : ℝ :=
  law.moments.predictiveCovariance /
    (Real.sqrt law.moments.scoreVariance * Real.sqrt law.moments.outcomeVariance)

/-- C3: within-deme Spearman accuracy under the bivariate-normal score/liability chart. -/
noncomputable def DemeScoreLaw.spearman (law : DemeScoreLaw) : ℝ :=
  gaussianSpearman law.pearson

/-- Gaussian mean absolute error from its error variance. -/
noncomputable def gaussianMAE (errorVariance : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * Real.sqrt errorVariance

/-- Error variance of the optimally linearly rescaled score. -/
noncomputable def DemeScoreLaw.linearErrorVariance (law : DemeScoreLaw) : ℝ :=
  law.moments.outcomeVariance * (1 - law.r2True)

/-- C3: MAE under the Gaussian residual chart. -/
noncomputable def DemeScoreLaw.mae (law : DemeScoreLaw) : ℝ :=
  gaussianMAE law.linearErrorVariance

/-- Standard normal density. -/
noncomputable def standardNormalDensity (z : ℝ) : ℝ :=
  Real.exp (-(z ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- A standardized Gaussian upper tail with its probability tied to its boundary. -/
structure GaussianUpperTail where
  boundary : ℝ
  mass : ℝ
  mass_pos : 0 < mass
  mass_eq : mass = 1 - Foundations.Phi boundary

/-- A top-decile Gaussian tail. -/
structure GaussianTopDecile extends GaussianUpperTail where
  is_decile : mass = 1 / 10

/-- Conditional RMSE when `(error,Z)` is jointly Gaussian and `Z` is standardized.  The
conditional second moment is
`Var(error) + Cov(error,Z)^2 * a*phi(a)/P(Z>=a)`. -/
noncomputable def gaussianTailRMSE
    (errorVariance errorTailCovariance : ℝ) (tail : GaussianUpperTail) : ℝ :=
  Real.sqrt (errorVariance + errorTailCovariance ^ 2 *
    tail.boundary * standardNormalDensity tail.boundary / tail.mass)

/-- C3: general Gaussian tail-RMSE chart with error/tail covariance explicit. -/
noncomputable def DemeScoreLaw.tailRMSE (law : DemeScoreLaw)
    (errorTailCovariance : ℝ) (tail : GaussianUpperTail) : ℝ :=
  gaussianTailRMSE law.linearErrorVariance errorTailCovariance tail

/-- C3: top-score-decile RMSE after optimal linear rescaling.  The Gaussian residual is
orthogonal, hence independent, of the score, so selecting on the score leaves RMSE unchanged. -/
noncomputable def DemeScoreLaw.topDecileRMSE (law : DemeScoreLaw)
    (tail : GaussianTopDecile) : ℝ :=
  law.tailRMSE 0 tail.toGaussianUpperTail

theorem DemeScoreLaw.topDecileRMSE_eq_residualRMSE (law : DemeScoreLaw)
    (tail : GaussianTopDecile) :
    law.topDecileRMSE tail = Real.sqrt law.linearErrorVariance := by
  simp [DemeScoreLaw.topDecileRMSE, DemeScoreLaw.tailRMSE, gaussianTailRMSE]

/-- Mean liability-model risk in the score tail `z >= q`, divided by prevalence.  This is
the exact Gaussian integral chart for the top-decile risk ratio. -/
noncomputable def topTailRiskRatio
    (r2 : ℝ) (prevalence : InteriorProbability) (tail : GaussianUpperTail) : ℝ :=
  ((∫ z in Set.Ici tail.boundary,
      liabilityRiskAtScore r2 prevalence.value z * standardNormalDensity z) / tail.mass) /
    prevalence.value

/-- C3: top-decile risk ratio at the law's own `R^2` and prevalence. -/
noncomputable def DemeScoreLaw.topDecileRiskRatio (law : DemeScoreLaw)
    (_ : law.ResidualVariation) (tail : GaussianTopDecile) : ℝ :=
  topTailRiskRatio law.r2True law.prevalenceProbability tail.toGaussianUpperTail

/-- C3: OR per SD, using the already validated liability chart. -/
noncomputable def DemeScoreLaw.orPerSD
    (law : DemeScoreLaw) (_ : law.ResidualVariation) : ℝ :=
  orPerSDFromLiability law.r2True law.prevalence

/-- C3: exact liability Brier chart. -/
noncomputable def DemeScoreLaw.brier (law : DemeScoreLaw) : ℝ :=
  PopGen.TransportedMetrics.liabilityBrierExact law.prevalence law.r2True

/-- A strictly positive reference Brier risk. -/
structure ReferenceBrier where
  value : ℝ
  value_pos : 0 < value

/-- C3: Brier skill against an explicitly supplied reference risk. -/
noncomputable def DemeScoreLaw.brierSkill
    (law : DemeScoreLaw) (referenceBrier : ReferenceBrier) : ℝ :=
  1 - law.brier / referenceBrier.value

/-! ## D. Calibration and the phenotype ladder -/

/-- D1--D2: identity-scale per-deme calibration from the score mean, observed outcome mean,
and the same variance/covariance pair used by `r2True`. -/
noncomputable def DemeScoreLaw.identityCalibration (law : DemeScoreLaw)
    (observedMean predictedReferenceMean : ℝ) : CalibrationProfile :=
  identityCalibrationProfile observedMean
    (predictedReferenceMean + law.scoreMean) law.calibrationSlope

/-- Drifted prevalence generated by a liability mean shift.  The threshold is pinned by the
source prevalence; a zero residual scale cannot be supplied. -/
noncomputable def emergentPrevalenceFromLiabilityMean
    (sourcePrevalence : InteriorProbability) (liabilityMean : ℝ)
    (residualSD : PositiveScale) : InteriorProbability where
  value := Foundations.Phi
    (liabilityMean / residualSD.value - liabilityThreshold sourcePrevalence.value)
  value_pos := Foundations.Phi_pos _
  value_lt_one := Foundations.Phi_lt_one _

/-- With no liability-mean shift, the emergent prevalence is exactly the source prevalence
at every positive residual scale. -/
theorem emergentPrevalenceFromLiabilityMean_zero
    (sourcePrevalence : InteriorProbability) (residualSD : PositiveScale) :
    (emergentPrevalenceFromLiabilityMean sourcePrevalence 0 residualSD).value =
      sourcePrevalence.value := by
  unfold emergentPrevalenceFromLiabilityMean
  have h := liabilityRiskAtScore_at_zero_r2_eq_prevalence
    sourcePrevalence.value 0 sourcePrevalence.value_pos sourcePrevalence.value_lt_one
  unfold liabilityRiskAtScore at h
  norm_num at h ⊢
  exact h

/-- The four phenotype rungs. -/
inductive PhenotypeRung where
  | phenoC
  | phenoA
  | phenoR
  | phenoB
deriving DecidableEq, Repr

/-- Inputs whose provenance distinguishes imposed baselines from the emergent genetic mean.
`affineBaseline` and `randomBaseline` are used only on their named rungs; phenoB uses the
genetic-liability mean generated upstream. -/
structure PhenotypeLadderInput where
  sourcePrevalence : InteriorProbability
  residualSD : PositiveScale
  affineBaseline : ℝ
  randomBaseline : ℝ
  geneticLiabilityMean : ℝ

/-- Explicit affine coordinate map from deployed score mean to genetic-liability mean. -/
structure ScoreLiabilityScale where
  intercept : ℝ
  loading : ℝ

noncomputable def ScoreLiabilityScale.mean
    (scale : ScoreLiabilityScale) (scoreMean : ℝ) : ℝ :=
  scale.intercept + scale.loading * scoreMean

/-- Identity scale for a score already measured as genetic liability. -/
def ScoreLiabilityScale.identity : ScoreLiabilityScale where
  intercept := 0
  loading := 1

/-- Build the phenotype ladder from the demographic score law.  This is the A1-to-phenoB
edge: the emergent rung receives the genetic-liability mean and no target prevalence. -/
noncomputable def PhenotypeLadderInput.ofScoreLaw
    (sourcePrevalence : InteriorProbability) (residualSD : PositiveScale)
    (affineBaseline randomBaseline : ℝ) (scale : ScoreLiabilityScale)
    (law : DemeScoreLaw) : PhenotypeLadderInput where
  sourcePrevalence := sourcePrevalence
  residualSD := residualSD
  affineBaseline := affineBaseline
  randomBaseline := randomBaseline
  geneticLiabilityMean := scale.mean law.scoreMean

/-- D3: per-rung prevalence.  phenoC is the clean floor; phenoA/R apply their imposed
baselines; phenoB obtains its prevalence from the upstream genetic-liability mean and is not
told a target prevalence. -/
noncomputable def phenotypePrevalence (input : PhenotypeLadderInput)
    (rung : PhenotypeRung) : InteriorProbability :=
  match rung with
  | .phenoC => input.sourcePrevalence
  | .phenoA => emergentPrevalenceFromLiabilityMean input.sourcePrevalence
      input.affineBaseline input.residualSD
  | .phenoR => emergentPrevalenceFromLiabilityMean input.sourcePrevalence
      input.randomBaseline input.residualSD
  | .phenoB => emergentPrevalenceFromLiabilityMean input.sourcePrevalence
      input.geneticLiabilityMean input.residualSD

/-- Replace only the prevalence axis of a score law by a phenotype rung.  Score moments stay
fixed, so discrimination and calibration consume phenoB's emergent prevalence without being
told it independently. -/
noncomputable def DemeScoreLaw.atPhenotypeRung (law : DemeScoreLaw)
    (input : PhenotypeLadderInput) (rung : PhenotypeRung) : DemeScoreLaw :=
  let rungPrevalence := phenotypePrevalence input rung
  { law with
    prevalence := rungPrevalence.value
    prevalence_pos := rungPrevalence.value_pos
    prevalence_lt_one := rungPrevalence.value_lt_one }

/-- D1--D3: logistic CITL at every rung, using the validated prevalence-shift algebra. -/
noncomputable def phenotypeCITL (input : PhenotypeLadderInput)
    (predictedPrevalence : InteriorProbability) (rung : PhenotypeRung) : ℝ :=
  prevalenceCITLShift predictedPrevalence.value (phenotypePrevalence input rung).value

/-- The complete per-rung calibration profile: rung-specific CITL and the single slope fixed
by the selected score moments. -/
noncomputable def phenotypeCalibrationProfile (law : DemeScoreLaw)
    (input : PhenotypeLadderInput) (predictedPrevalence : InteriorProbability)
    (rung : PhenotypeRung) : CalibrationProfile where
  citl := phenotypeCITL input predictedPrevalence rung
  slope := law.calibrationSlope
  link := CalibrationLink.logistic

/-- The clean rung has no intercept shift when predicted at its source prevalence. -/
theorem phenotypeCITL_phenoC_zero (input : PhenotypeLadderInput) :
    phenotypeCITL input input.sourcePrevalence PhenotypeRung.phenoC = 0 := by
  exact no_citl_shift_same_prevalence input.sourcePrevalence.value

/-- D2 is shared by all rungs: changing a baseline changes the intercept/prevalence but not
the variance-attenuation slope supplied by the score law. -/
theorem phenotype_ladder_slope_is_score_slope (law : DemeScoreLaw)
    (input : PhenotypeLadderInput) (rung : PhenotypeRung) :
    law.calibrationSlope = law.moments.calibrationSlope := rfl

end Descent.Portability
