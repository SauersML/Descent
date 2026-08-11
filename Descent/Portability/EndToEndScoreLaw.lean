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

/-- Parameters of a P+T construction.  They are supplied by a study instance, never selected
inside the law. -/
structure PTParameters where
  clumpR2Cutoff : ℝ
  clumpWindowBp : ℕ
  discoverySampleSize : ℕ

/-- Two markers conflict when they lie inside the clumping window and their source LD reaches
the exclusion cutoff.  Equality is excluded, matching the pipeline's retained condition
`r^2 < 0.1`. -/
def ptConflict {m : ℕ} (parameters : PTParameters) (positionBp : Fin m → ℕ)
    (sourceR2 : Fin m → Fin m → ℝ) (i j : Fin m) : Bool :=
  decide (Nat.dist (positionBp i) (positionBp j) ≤ parameters.clumpWindowBp ∧
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
  parameters : PTParameters
  positionBp : Fin m → ℕ
  sourceR2 : Fin m → Fin m → ℝ
  pValue : Fin m → ℝ
  pThreshold : Fin thresholdCount → ℝ
  orderedMarkers : List (Fin m)
  orderedMarkers_nodup : orderedMarkers.Nodup
  coversMarkers : ∀ i, i ∈ orderedMarkers

/-- Ordered threshold-eligible markers. -/
def PTDesign.eligible {thresholdCount m : ℕ} (d : PTDesign thresholdCount m)
    (q : Fin thresholdCount) : List (Fin m) :=
  d.orderedMarkers.filter fun i ↦ decide (d.pValue i ≤ d.pThreshold q)

/-- The exact retained marker list at threshold `q`. -/
def PTDesign.selected {thresholdCount m : ℕ} (d : PTDesign thresholdCount m)
    (q : Fin thresholdCount) : List (Fin m) :=
  greedyClump (ptConflict d.parameters d.positionBp d.sourceR2) (d.eligible q)

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
    (alleleFrequency effect : Fin m → ℝ) : ℝ :=
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

/-- The one-locus OLS variance at a supplied discovery sample size.  The genotype variance is
diploid HWE `2p(1-p)`. -/
noncomputable def gwasEffectNoiseVariance
    (discoverySampleSize : ℕ) (residualVariance p : ℝ) : ℝ :=
  residualVariance / (discoverySampleSize * (2 * p * (1 - p)))

/-- GWAS noise evaluated at the discovery sample size carried by a P+T design. -/
noncomputable def PTDesign.effectNoiseVariance {thresholdCount m : ℕ}
    (d : PTDesign thresholdCount m) (residualVariance p : ℝ) : ℝ :=
  gwasEffectNoiseVariance d.parameters.discoverySampleSize residualVariance p

/-- An exact finite representation of the sampling law of the GWAS output.  Continuous
Gaussian sampling may be approximated by quadrature, but no independence between linked
markers is assumed: each atom carries the whole estimated-effect and p-value vector, so
clumping is performed jointly inside the atom before averaging. -/
structure PTGWASSamplingLaw (omega m : ℕ) where
  probability : Fin omega → ℝ
  probability_nonneg : ∀ w, 0 ≤ probability w
  probability_sum_one : ∑ w, probability w = 1
  estimatedEffect : Fin omega → Fin m → ℝ
  pValue : Fin omega → Fin m → ℝ

/-- Expected value under the exact joint GWAS sampling law. -/
noncomputable def PTGWASSamplingLaw.expectation {omega m : ℕ}
    (law : PTGWASSamplingLaw omega m) (f : Fin omega → ℝ) : ℝ :=
  ∑ w, law.probability w * f w

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

/-- The per-deme output of A+B.  `scoreMean` is required for calibration and pooling;
second moments alone are insufficient for either. -/
structure DemeScoreLaw where
  scoreMean : ℝ
  moments : Descent.Core.ScoreMoments
  prevalence : ℝ

/-- Distance-resolved output for a train deme and every target deme. -/
structure DistanceResolvedScoreLaw (D : ℕ) where
  train : Fin D
  atDeme : Fin D → DemeScoreLaw

/-- C1: true within-deme squared accuracy. -/
noncomputable def DemeScoreLaw.r2True (law : DemeScoreLaw) : ℝ := law.moments.r2

/-- C2: calibration slope from the same two score moments. -/
noncomputable def DemeScoreLaw.calibrationSlope (law : DemeScoreLaw) : ℝ :=
  law.moments.calibrationSlope

/-- C2: probit index spread relative to residual spread,
`sqrt(R^2/(1-R^2))`. -/
noncomputable def DemeScoreLaw.probitRiskSpreadRatio (law : DemeScoreLaw) : ℝ :=
  Real.sqrt (law.r2True / (1 - law.r2True))

/-- Spearman correlation for a bivariate Gaussian with Pearson correlation `r`. -/
noncomputable def gaussianSpearman (r : ℝ) : ℝ :=
  6 / Real.pi * Real.arcsin (r / 2)

/-- C3: within-deme Spearman accuracy under the bivariate-normal score/liability chart. -/
noncomputable def DemeScoreLaw.spearman (law : DemeScoreLaw) : ℝ :=
  gaussianSpearman (Real.sqrt law.r2True)

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

/-- Conditional RMSE above a standardized Gaussian tail threshold `a`.  The second moment
of a standard normal truncated above `a` is `1 + a phi(a)/(1-Phi(a))`. -/
noncomputable def gaussianTailRMSE (errorVariance a : ℝ) : ℝ :=
  Real.sqrt (errorVariance *
    (1 + a * standardNormalDensity a / (1 - Foundations.Phi a)))

/-- C3: top-decile tail RMSE, with the top-decile boundary supplied explicitly so its
quantile convention cannot change inside the chart. -/
noncomputable def DemeScoreLaw.topDecileRMSE (law : DemeScoreLaw)
    (topDecileBoundary : ℝ) : ℝ :=
  gaussianTailRMSE law.linearErrorVariance topDecileBoundary

/-- Mean liability-model risk in the score tail `z >= q`, divided by prevalence.  This is
the exact Gaussian integral chart for the top-decile risk ratio. -/
noncomputable def topTailRiskRatio (r2 prevalence q tailMass : ℝ) : ℝ :=
  ((∫ z in Set.Ici q,
      liabilityRiskAtScore r2 prevalence z * standardNormalDensity z) / tailMass) /
    prevalence

/-- C3: top-decile risk ratio at the law's own `R^2` and prevalence. -/
noncomputable def DemeScoreLaw.topDecileRiskRatio (law : DemeScoreLaw)
    (topDecileBoundary : ℝ) : ℝ :=
  topTailRiskRatio law.r2True law.prevalence topDecileBoundary (1 / 10)

/-- C3: OR per SD, using the already validated liability chart. -/
noncomputable def DemeScoreLaw.orPerSD (law : DemeScoreLaw) : ℝ :=
  orPerSDFromLiability law.r2True law.prevalence

/-- C3: exact liability Brier chart. -/
noncomputable def DemeScoreLaw.brier (law : DemeScoreLaw) : ℝ :=
  PopGen.liabilityBrierExact law.prevalence law.r2True

/-- C3: Brier skill against an explicitly supplied reference risk.  The reference is an
argument because its definition belongs to the comparison instance, not to the metric law. -/
noncomputable def DemeScoreLaw.brierSkill
    (law : DemeScoreLaw) (referenceBrier : ℝ) : ℝ :=
  1 - law.brier / referenceBrier

/-! ## D. Calibration and the phenotype ladder -/

/-- D1--D2: identity-scale per-deme calibration from the score mean, observed outcome mean,
and the same variance/covariance pair used by `r2True`. -/
noncomputable def DemeScoreLaw.identityCalibration (law : DemeScoreLaw)
    (observedMean predictedReferenceMean : ℝ) : CalibrationProfile :=
  identityCalibrationProfile observedMean
    (predictedReferenceMean + law.scoreMean) law.calibrationSlope

/-- Drifted prevalence generated by a liability mean shift.  The threshold is pinned by the
source prevalence and the residual scale is explicit. -/
noncomputable def emergentPrevalenceFromLiabilityMean
    (sourcePrevalence liabilityMean residualSD : ℝ) : ℝ :=
  Foundations.Phi
    ((liabilityMean - liabilityThreshold sourcePrevalence) / residualSD)

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
  sourcePrevalence : ℝ
  residualSD : ℝ
  affineBaseline : ℝ
  randomBaseline : ℝ
  geneticLiabilityMean : ℝ

/-- Build the phenotype ladder from the demographic score law.  This is the A1-to-phenoB
edge: the emergent rung receives the genetic-liability mean and no target prevalence. -/
noncomputable def PhenotypeLadderInput.ofScoreLaw (sourcePrevalence residualSD
    affineBaseline randomBaseline : ℝ) (scoreMeanToLiabilityMean : ℝ → ℝ)
    (law : DemeScoreLaw) : PhenotypeLadderInput where
  sourcePrevalence := sourcePrevalence
  residualSD := residualSD
  affineBaseline := affineBaseline
  randomBaseline := randomBaseline
  geneticLiabilityMean := scoreMeanToLiabilityMean law.scoreMean

/-- D3: per-rung prevalence.  phenoC is the clean floor; phenoA/R apply their imposed
baselines; phenoB obtains its prevalence from the upstream genetic-liability mean and is not
told a target prevalence. -/
noncomputable def phenotypePrevalence (input : PhenotypeLadderInput)
    (rung : PhenotypeRung) : ℝ :=
  match rung with
  | .phenoC => input.sourcePrevalence
  | .phenoA => emergentPrevalenceFromLiabilityMean input.sourcePrevalence
      input.affineBaseline input.residualSD
  | .phenoR => emergentPrevalenceFromLiabilityMean input.sourcePrevalence
      input.randomBaseline input.residualSD
  | .phenoB => emergentPrevalenceFromLiabilityMean input.sourcePrevalence
      input.geneticLiabilityMean input.residualSD

/-- D1--D3: logistic CITL at every rung, using the validated prevalence-shift algebra. -/
noncomputable def phenotypeCITL (input : PhenotypeLadderInput)
    (predictedPrevalence : ℝ) (rung : PhenotypeRung) : ℝ :=
  prevalenceCITLShift predictedPrevalence (phenotypePrevalence input rung)

/-- The complete per-rung calibration profile: rung-specific CITL and the single slope fixed
by the selected score moments. -/
noncomputable def phenotypeCalibrationProfile (law : DemeScoreLaw)
    (input : PhenotypeLadderInput) (predictedPrevalence : ℝ)
    (rung : PhenotypeRung) : CalibrationProfile where
  citl := phenotypeCITL input predictedPrevalence rung
  slope := law.calibrationSlope
  link := CalibrationLink.logistic

/-- The clean rung has no intercept shift when predicted at its source prevalence. -/
theorem phenotypeCITL_phenoC_zero (input : PhenotypeLadderInput) :
    phenotypeCITL input input.sourcePrevalence PhenotypeRung.phenoC = 0 := by
  exact no_citl_shift_same_prevalence input.sourcePrevalence

/-- D2 is shared by all rungs: changing a baseline changes the intercept/prevalence but not
the variance-attenuation slope supplied by the score law. -/
theorem phenotype_ladder_slope_is_score_slope (law : DemeScoreLaw)
    (input : PhenotypeLadderInput) (rung : PhenotypeRung) :
    law.calibrationSlope = law.moments.calibrationSlope := rfl

end Descent.Portability
