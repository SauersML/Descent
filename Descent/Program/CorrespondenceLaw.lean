/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DiscriminationLaw
import Descent.PopGen.MigrationCorrespondence

namespace Descent.Program

/-!
# General estimator correspondence and validation doctrine

The declarations in this file do not know any study's number of demes, thresholds,
replicates, or sample sizes.  A concrete analysis supplies those facts in its correspondence
instance.  Completeness is a total function from a closed column type, and mixed strata
remain typed probability mixtures rather than being coerced to atomic populations.
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

/-- A complete correspondence table.  `row` is total, so every inhabitant of `Column` has
exactly one declared meaning. -/
structure CorrespondenceTable (Column : Type) where
  row : Column → CorrespondenceRow Column

/-- The complete family of portability outputs owned by the mathematical chain. -/
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

/-- Machine-total correspondence for every output in the portability chain.  Source text is
quoted by a concrete corpus instance; the mathematical estimator names remain general. -/
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

/-- Inference keys keep demography as a typed coordinate.  An analysis may use arbitrary
types for demography, phenotype, method, and replicate identifiers. -/
structure InferenceKey (Demography Phenotype Method Replicate : Type) where
  demography : Demography
  phenotype : Phenotype
  method : Method
  replicate : Replicate

/-- The population-row subtype pair: an atomic population or an explicitly weighted
probability mixture.  A mixture cannot masquerade as a representative atomic population. -/
inductive PopulationRow (Population : Type) [Fintype Population] where
  | atomic (population : Population)
  | mixture (weight : Population → ℝ)
      (weightNonnegative : ∀ population, 0 ≤ weight population)
      (weightSumOne : ∑ population, weight population = 1)

/-- Estimator dictated by the row subtype. -/
noncomputable def PopulationRow.estimate {Population : Type} [Fintype Population]
    (value : Population → ℝ) : PopulationRow Population → ℝ
  | .atomic population => value population
  | .mixture weight _ _ => ∑ population, weight population * value population

/-- A gate owns the constructor it checks.  Its rival family is necessarily nonempty and
there is no fallback constructor. -/
structure EstimatorGate (Input : Type) where
  estimator : EstimatorConstructor Input
  rivals : List (String × (Input → ℝ))
  rivals_nonempty : rivals ≠ []
  tolerance : ℝ
  tolerance_nonnegative : 0 ≤ tolerance

/-- The preferred estimator is inside its preregistered numerical tolerance. -/
def EstimatorGate.accepts {Input : Type} (gate : EstimatorGate Input)
    (input : Input) (observed : ℝ) : Prop :=
  |gate.estimator.value input - observed| ≤ gate.tolerance

/-- Every preregistered rival is outside the preferred estimator's tolerance. -/
def EstimatorGate.rejectsRivals {Input : Type} (gate : EstimatorGate Input)
    (input : Input) (observed : ℝ) : Prop :=
  ∀ rival ∈ gate.rivals, gate.tolerance < |rival.2 input - observed|

/-- The typed constructor for Bhatia's finite-sample Hudson ratio of sums. -/
noncomputable def bhatiaHudsonEstimator {L : ℕ} :
    EstimatorConstructor (Fin L → Descent.Core.BhatiaHudsonLocus) where
  value := Descent.Core.bhatiaHudsonRatioOfSums
  name := "Bhatia-Hudson finite-sample ratio of sums"
  exactForm := "sum corrected numerators / sum between-population denominators"

/-- The complete finite-sample F gate.  The four comparison conventions are explicit
functions on the same locus panel; none can be selected as a fallback. -/
noncomputable def bhatiaHudsonGate {L : ℕ}
    (parametricHudson meanPerLocusHudson neiGST weirCockerhamTheta :
      (Fin L → Descent.Core.BhatiaHudsonLocus) → ℝ)
    (tolerance : ℝ) (tolerance_nonnegative : 0 ≤ tolerance) :
    EstimatorGate (Fin L → Descent.Core.BhatiaHudsonLocus) where
  estimator := bhatiaHudsonEstimator
  rivals :=
    [("parametric Hudson F", parametricHudson),
     ("mean per-locus Hudson ratios", meanPerLocusHudson),
     ("Nei G_ST ratio of sums", neiGST),
     ("Weir-Cockerham theta", weirCockerhamTheta)]
  rivals_nonempty := by simp
  tolerance := tolerance
  tolerance_nonnegative := tolerance_nonnegative

/-! ## Literature-to-ledger doctrine -/

/-- The only three failure diagnoses. -/
inductive MissClass where
  | badAssumption | badMath | badCorrespondence
deriving DecidableEq, Repr

/-- Ordered process stages. -/
inductive DoctrineStage where
  | literature | symbolicDerivation | leanBody | analyticSelfCheck
  | blindBatteryPreregistered | blindBatteryRun | ledgered
deriving DecidableEq, Repr

/-- Literature ownership precedes every derivation and contains at least one source. -/
structure LiteratureRecord where
  scope : String
  sources : List String
  sources_nonempty : sources ≠ []

/-- A symbolic derivation is linked to its literature record and exposes its equations. -/
structure SymbolicDerivationRecord where
  literature : LiteratureRecord
  identifier : String
  equations : List String
  equations_nonempty : equations ≠ []

/-- A Lean body is owned by one prior symbolic derivation.  Mathematical constraints are
reported as type-level fields, not prose assumptions. -/
structure LeanBodyRecord where
  symbolicDerivation : SymbolicDerivationRecord
  declaration : String
  typedConstraints : List String

/-- Analytic self-checks precede any blind battery and cannot contain simulated outcomes. -/
structure AnalyticSelfCheckRecord where
  leanBody : LeanBodyRecord
  exactLimits : List String
  exactLimits_nonempty : exactLimits ≠ []

/-- A blind link from a general law to an observable. -/
structure BlindGap where
  identifier : String
  selfCheck : AnalyticSelfCheckRecord
  observable : String
  rivals : List String
  rivals_nonempty : rivals ≠ []
  informativeZero : String

/-- A repair is admissible after a miss only if its trigger and action were frozen before
the blind outcomes existed. -/
structure MandatoryRepair where
  gapIdentifier : String
  trigger : MissClass
  action : String
deriving DecidableEq, Repr

/-- A preregistration deliberately has no observation or verdict field. -/
structure BlindBatteryPreregistration (Demography : Type) where
  identifier : String
  freshDemographies : List Demography
  freshDemographies_nonempty : freshDemographies ≠ []
  gaps : List BlindGap
  gaps_nonempty : gaps ≠ []
  inferenceUnit : String
  acceptanceRule : String
  rivalRejectionRule : String
  informativeZeroRule : String
  mandatoryRepairs : List MandatoryRepair

/-- Exact authorization test for a proposed post-miss repair. -/
def BlindBatteryPreregistration.authorizesRepair {Demography : Type}
    (registration : BlindBatteryPreregistration Demography)
    (repair : MandatoryRepair) : Prop :=
  repair ∈ registration.mandatoryRepairs

/-- Evidence required before the word `validated` can enter the ledger. -/
structure BlindBatteryEvidence where
  registrationIdentifier : String
  batteryIdentifier : String
  frozenBeforeObservation : Prop
  frozenBeforeObservation_proof : frozenBeforeObservation
  freshSimulations : Prop
  freshSimulations_proof : freshSimulations
  preferredAccepted : Prop
  preferredAccepted_proof : preferredAccepted
  allRivalsRejected : Prop
  allRivalsRejected_proof : allRivalsRejected
  informativeZerosRetained : Prop
  informativeZerosRetained_proof : informativeZerosRetained

/-- Ledger state never equates a derived or preregistered law with a validated one. -/
inductive LedgerStatus where
  | derived
  | preregistered
  | validated (evidence : BlindBatteryEvidence)
  | falsified (cause : MissClass)

/-- The ledger stage is determined by status and cannot contradict it. -/
def LedgerStatus.lastCompletedStage : LedgerStatus → DoctrineStage
  | .derived => .analyticSelfCheck
  | .preregistered => .blindBatteryPreregistered
  | .validated _ => .ledgered
  | .falsified _ => .ledgered

/-- One auditable ledger row. -/
structure LedgerRow where
  gap : BlindGap
  status : LedgerStatus

/-- Authoring a preregistration enters every gap as preregistered, never validated. -/
def BlindBatteryPreregistration.initialLedger {Demography : Type}
    (registration : BlindBatteryPreregistration Demography) : List LedgerRow :=
  registration.gaps.map fun gap =>
    ⟨gap, .preregistered⟩

end Descent.Program
