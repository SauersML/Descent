/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalTableLawMetrics

/-! Axiom audit of EmpiricalTableLawMetrics. -/

open Descent.Portability.EmpiricalTableLawMetrics

#print axioms scoreGroupSize_add
#print axioms scoreCount_mul_pos_iff
#print axioms tableLaw_binaryAUC
#print axioms tableLaw_calibrationSlope
#print axioms conditional_tableLaw_binaryAUC
#print axioms conditional_tableLaw_calibrationSlope
