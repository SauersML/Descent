/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DiscriminationLaw
import Descent.PopGen.MigrationCorrespondence

namespace Descent.Validation

/-!
# Portability estimator correspondence

This is validation infrastructure, not a production mathematical dependency.  It pins
reported columns to library declarations, keeps mixture rows distinct from atomic rows, and
owns rival estimator gates used by validation batteries.
-/

/-- An estimator constructor and its exact mathematical form. -/
structure EstimatorConstructor (Input : Type) where
  value : Input → ℝ
  name : String
  exactForm : String

/-- Provenance for one reported column. -/
structure CorrespondenceRow (Column : Type) where
  column : Column
  corpusDeclaration : String
  estimatorForm : String
  sourceQuotation : String

/-- A complete correspondence table. -/
structure CorrespondenceTable (Column : Type) where
  row : Column → CorrespondenceRow Column

/-- The complete family of portability outputs checked by the validation battery. -/
inductive PortabilityMetricColumn where
  | finiteSampleF
  | r2True
  | calibrationSlope
  | calibrationInTheLarge
  | probitRiskSpread
  | spearman
  | meanAbsoluteError
  | tailRootMeanSquaredError
  | topTailRiskRatio
  | oddsRatioPerScoreSD
  | brierScore
  | brierSkillScore
  | withinDemeAUC
  | pooledAUC
  | harrellC
deriving DecidableEq, Repr

/-- Total correspondence for every output in the portability validation chain. -/
def portabilityMetricCorrespondence : CorrespondenceTable PortabilityMetricColumn where
  row
    | .finiteSampleF =>
        ⟨.finiteSampleF, "Core.bhatiaHudsonRatioOfSums",
          "sum finite-sample-corrected Hudson numerators / sum between-population denominators",
          "Hudson finite-sample ratio-of-averages estimator"⟩
    | .r2True =>
        ⟨.r2True, "DemeScoreLaw.r2True", "Cov(S,Y)^2 / (Var(S) Var(Y))",
          "within-population liability_r2"⟩
    | .calibrationSlope =>
        ⟨.calibrationSlope, "DemeScoreLaw.calibrationSlope", "Cov(S,Y) / Var(S)",
          "within-population calibration slope"⟩
    | .calibrationInTheLarge =>
        ⟨.calibrationInTheLarge, "phenotypeCITL",
          "logit(observed prevalence) - logit(predicted prevalence)",
          "calibration-in-the-large on the declared phenotype rung"⟩
    | .probitRiskSpread =>
        ⟨.probitRiskSpread, "DemeScoreLaw.probitRiskSpreadRatio",
          "sqrt(R2 / (1 - R2))", "within-population probit risk-spread ratio"⟩
    | .spearman =>
        ⟨.spearman, "DemeScoreLaw.spearman", "6 / pi * asin(Pearson / 2)",
          "Gaussian-copula Spearman correlation"⟩
    | .meanAbsoluteError =>
        ⟨.meanAbsoluteError, "DemeScoreLaw.mae",
          "sqrt(2 / pi) * sqrt(Var(Y-S))", "within-population absolute error"⟩
    | .tailRootMeanSquaredError =>
        ⟨.tailRootMeanSquaredError, "DemeScoreLaw.tailRMSE",
          "sqrt(Var(Y-S) + Cov(Y-S,S)^2/Var(S) * a*phi(a)/(1-Phi(a)))",
          "Gaussian conditional error above a declared score boundary"⟩
    | .topTailRiskRatio =>
        ⟨.topTailRiskRatio, "DemeScoreLaw.topDecileRiskRatio",
          "mean liability risk in the upper score tail / deme prevalence",
          "upper-tail risk enrichment within population"⟩
    | .oddsRatioPerScoreSD =>
        ⟨.oddsRatioPerScoreSD, "DemeScoreLaw.orPerSD",
          "liability-threshold odds ratio for a one-score-SD contrast",
          "odds ratio per score standard deviation"⟩
    | .brierScore =>
        ⟨.brierScore, "DemeScoreLaw.brier", "exact liability-model Brier expectation",
          "within-population binary Brier score"⟩
    | .brierSkillScore =>
        ⟨.brierSkillScore, "DemeScoreLaw.brierSkill",
          "1 - model Brier / declared reference Brier",
          "Brier skill relative to an explicit reference"⟩
    | .withinDemeAUC =>
        ⟨.withinDemeAUC, "DemeScoreLaw.withinAUC",
          "liability-threshold case-control exceedance probability",
          "within-population binary AUC"⟩
    | .pooledAUC =>
        ⟨.pooledAUC, "DemeMixture.pooledAUC",
          "sum_i sum_j P(i|case) P(j|control) P(S_i^+ > S_j^-)",
          "pooled case-control AUC"⟩
    | .harrellC =>
        ⟨.harrellC, "administrativeHarrellC",
          "concordant comparable-pair mass / comparable-pair mass",
          "Harrell concordance under administrative censoring"⟩

/-- Inference keys keep demography as a typed coordinate. -/
structure InferenceKey (Demography Phenotype Method Replicate : Type) where
  demography : Demography
  phenotype : Phenotype
  method : Method
  replicate : Replicate

/-- A reported row is an atomic population or an explicitly weighted probability mixture. -/
inductive PopulationRow (Population : Type) [Fintype Population] where
  | atomic (population : Population)
  | mixture (weight : Population → ℝ)
      (weightNonnegative : ∀ population, 0 ≤ weight population)
      (weightSumOne : ∑ population, weight population = 1)

/-- Estimator dictated by the validation row subtype. -/
noncomputable def PopulationRow.estimate {Population : Type} [Fintype Population]
    (value : Population → ℝ) : PopulationRow Population → ℝ
  | .atomic population => value population
  | .mixture weight _ _ => ∑ population, weight population * value population

/-- A validation gate owns one estimator and a nonempty family of rivals. -/
structure EstimatorGate (Input : Type) where
  estimator : EstimatorConstructor Input
  rivals : List (String × (Input → ℝ))
  rivals_nonempty : rivals ≠ []
  tolerance : ℝ
  tolerance_nonnegative : 0 ≤ tolerance

def EstimatorGate.accepts {Input : Type} (gate : EstimatorGate Input)
    (input : Input) (observed : ℝ) : Prop :=
  |gate.estimator.value input - observed| ≤ gate.tolerance

def EstimatorGate.rejectsRivals {Input : Type} (gate : EstimatorGate Input)
    (input : Input) (observed : ℝ) : Prop :=
  ∀ rival ∈ gate.rivals, gate.tolerance < |rival.2 input - observed|

noncomputable def bhatiaHudsonEstimator {L : ℕ} :
    EstimatorConstructor (Descent.Core.BhatiaHudsonPanel L) where
  value := Descent.Core.bhatiaHudsonRatioOfSums
  name := "Bhatia-Hudson finite-sample ratio of sums"
  exactForm := "sum corrected numerators / sum between-population denominators"

noncomputable def bhatiaHudsonGate {L : ℕ}
    (parametricHudson meanPerLocusHudson neiGST weirCockerhamTheta :
      Descent.Core.BhatiaHudsonPanel L → ℝ)
    (tolerance : ℝ) (tolerance_nonnegative : 0 ≤ tolerance) :
    EstimatorGate (Descent.Core.BhatiaHudsonPanel L) where
  estimator := bhatiaHudsonEstimator
  rivals :=
    [("parametric Hudson F", parametricHudson),
     ("mean per-locus Hudson ratios", meanPerLocusHudson),
     ("Nei G_ST ratio of sums", neiGST),
     ("Weir-Cockerham theta", weirCockerhamTheta)]
  rivals_nonempty := by simp
  tolerance := tolerance
  tolerance_nonnegative := tolerance_nonnegative

end Descent.Validation
