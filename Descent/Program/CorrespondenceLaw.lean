/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DiscriminationLaw
import Descent.PopGen.MigrationCorrespondence

namespace Descent.Program

/-!
# General estimator correspondence and validation doctrine

These types do not know any study's number of demes, thresholds, seeds, sample sizes, or
metric names.  A concrete analysis supplies an instance.  Completeness is expressed by a
total function from its column type, and mixed strata remain typed mixtures rather than
being coerced to atomic populations.
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

/-- Inference keys keep demography as a typed coordinate.  An analysis may use arbitrary
types for demography, phenotype, method, and replicate identifiers. -/
structure InferenceKey (Demography Phenotype Method Replicate : Type) where
  demography : Demography
  phenotype : Phenotype
  method : Method
  replicate : Replicate

/-- The population-row subtype pair: an atomic population or an explicitly weighted mixture.
A mixture is not allowed to masquerade as a representative atomic population. -/
inductive PopulationRow (Population : Type) [Fintype Population] where
  | atomic (population : Population)
  | mixture (weight : Population → ℝ) (weightSumOne : ∑ p, weight p = 1)

/-- Estimator dictated by the row subtype. -/
noncomputable def PopulationRow.estimate {Population : Type} [Fintype Population]
    (value : Population → ℝ) : PopulationRow Population → ℝ
  | .atomic p => value p
  | .mixture weight _ => ∑ p, weight p * value p

/-- A gate owns the constructor it checks.  Rivals are named functions on the same input;
there is no fallback constructor. -/
structure EstimatorGate (Input : Type) where
  estimator : EstimatorConstructor Input
  rivals : List (String × (Input → ℝ))
  tolerance : ℝ
  tolerance_nonneg : 0 ≤ tolerance

/-- The typed gate for Bhatia's finite-sample Hudson ratio of sums.  Concrete analyses add
their rival constructors and tolerance without changing the estimator law. -/
noncomputable def bhatiaHudsonEstimator {L : ℕ} :
    EstimatorConstructor (Fin L → Descent.Core.BhatiaHudsonLocus) where
  value := Descent.Core.bhatiaHudsonRatioOfSums
  name := "Bhatia-Hudson finite-sample ratio of sums"
  exactForm := "sum corrected numerators / sum between-population denominators"

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

/-- A blind link from a general law to an observable. -/
structure BlindGap where
  identifier : String
  lawDeclaration : String
  observable : String
  analyticLimits : List String
  rivals : List String
  informativeZero : String

/-- A preregistration deliberately has no observation, verdict, or repair field. -/
structure BlindBatteryPreregistration (Demography : Type) where
  freshDemographies : List Demography
  gaps : List BlindGap
  inferenceUnit : String
  acceptanceRule : String
  rivalRejectionRule : String
  informativeZeroRule : String
  mandatoryRepairRule : String

/-- Ledger state never equates a derived or preregistered law with a validated one. -/
inductive LedgerStatus where
  | derived | preregistered | validated | falsified (cause : MissClass)
deriving DecidableEq, Repr

/-- One auditable ledger row. -/
structure LedgerRow where
  gap : BlindGap
  status : LedgerStatus
  lastCompletedStage : DoctrineStage

/-- Authoring a preregistration enters every gap as preregistered, never validated. -/
def BlindBatteryPreregistration.initialLedger {Demography : Type}
    (registration : BlindBatteryPreregistration Demography) : List LedgerRow :=
  registration.gaps.map fun gap =>
    ⟨gap, .preregistered, .blindBatteryPreregistered⟩

end Descent.Program
