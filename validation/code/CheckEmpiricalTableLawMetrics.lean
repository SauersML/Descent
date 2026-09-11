/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalTableLawMetrics

/-! Axiom audit of EmpiricalTableLawMetrics. -/

open Descent.Portability.EmpiricalTableLawMetrics

#print axioms scoreGroupSize_add
#print axioms scoreCount_mul_pos_iff
#print axioms tableLaw_binaryAUC
#print axioms sum_outcomeOf_split
#print axioms tableLaw_calibrationSlope
#print axioms conditional_tableLaw_binaryAUC
#print axioms conditional_tableLaw_calibrationSlope
#print axioms tableLaw_linearIntercept
#print axioms intercept_numerator_identity
#print axioms linearIntercept_cleared
#print axioms conditional_empiricalIntercept
#print axioms conditional_tableLaw_linearIntercept
#print axioms conditional_tableLaw_linearIntercept_chronologyLaw
#print axioms expectation_tableLaw_expectation
#print axioms tableLaw_thresholdAccuracy
#print axioms expectation_tableLaw_thresholdAccuracy
#print axioms expectation_tableLaw_thresholdAccuracy_chronologyLaw
#print axioms tableLaw_meanSquaredError
#print axioms expectation_tableLaw_meanSquaredError
