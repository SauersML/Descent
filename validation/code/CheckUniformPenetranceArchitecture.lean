/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniformPenetranceArchitecture

/-! Axiom audit of UniformPenetranceArchitecture. -/

open Descent.Portability.UniformPenetranceArchitecture

#print axioms sum_cells
#print axioms penetrance_nonneg
#print axioms penetrance_le_one
#print axioms penetrance_eq_self
#print axioms penetranceLaw_mass
#print axioms expectation_penetranceLaw
#print axioms expectation_cellScore_penetranceLaw
#print axioms expectation_cellOutcome_penetranceLaw
#print axioms variance_cellScore_penetranceLaw
#print axioms variance_cellOutcome_penetranceLaw
#print axioms covariance_penetranceLaw
#print axioms squaredCorrelation_penetranceLaw
#print axioms squaredCorrelation_penetranceLaw_zero
#print axioms calibrationSlope_penetranceLaw
#print axioms calibrationIntercept_penetranceLaw
#print axioms meanSquaredError_penetranceLaw
#print axioms binaryCaseMass_penetranceLaw
#print axioms binaryAUCNumerator_penetranceLaw
#print axioms binaryAUC_penetranceLaw
#print axioms scoreGroupMass_penetranceLaw_true
#print axioms scoreGroupMass_penetranceLaw_false
#print axioms scoreSuccessMass_penetranceLaw_true
#print axioms scoreSuccessMass_penetranceLaw_false
#print axioms discreteECE_penetranceLaw
#print axioms repairedBrier_penetranceLaw
#print axioms accuracyRate_penetranceLaw
#print axioms repairedLogLoss_penetranceLaw
#print axioms rawLogLoss_penetranceLaw
#print axioms pooledPenetranceLaw_mass
#print axioms expectation_pooledPenetranceLaw
#print axioms squaredCorrelation_pooledPenetranceLaw
