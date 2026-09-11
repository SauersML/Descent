/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaMetricInstances

/-! Axiom audit of ReplicaMetricInstances. -/

open Descent.Portability.ReplicaMetricInstances

#print axioms getD_guardedRatio
#print axioms conditionalMetric_guardedRatio
#print axioms expectation_guardedRatio_eq_tsum
#print axioms guardedRatio_certificate
#print axioms variance_le_quarter
#print axioms correlationNumerator_nonneg
#print axioms correlationNumerator_le_denominator
#print axioms correlationDenominator_le_one
#print axioms correlationDenominator_pos_iff
#print axioms squaredCorrelation_eq_guardedRatio
#print axioms expectation_squaredCorrelation_eq_tsum
#print axioms squaredCorrelation_certificate
#print axioms replicaCohortLaw_mass
#print axioms empiricalAUCComparison_mem_unit
#print axioms rankingCredit_bounds
#print axioms binaryAUCNumerator_eq_twoReplica
#print axioms binaryCaseMass_mem_unit
#print axioms aucNumerator_nonneg
#print axioms aucNumerator_le_denominator
#print axioms aucDenominator_le_one
#print axioms aucDenominator_pos_iff
#print axioms binaryAUC_eq_guardedRatio
#print axioms expectation_aucNumerator_eq_twoReplica
#print axioms expectation_binaryAUC_eq_tsum
#print axioms binaryAUC_certificate
