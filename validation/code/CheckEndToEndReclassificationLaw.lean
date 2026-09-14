/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndReclassificationLaw

/-! Axiom audit of EndToEndReclassificationLaw. -/

open Descent.Portability.EndToEndReclassificationLaw

#print axioms jointCallReport
#print axioms tableNRI
#print axioms tableNRI_eq_tableYouden_sub
#print axioms jointMass_add_old
#print axioms jointMass_add_new
#print axioms expectedJointTable
#print axioms expectedJointTable_eq_dotProduct
#print axioms oldTable_newTable_expectedJointTable
#print axioms tableNRI_expectedJointTable
#print axioms expectedForecastMass
#print axioms expectedDiscriminationSlope
#print axioms expectedIDI
#print axioms ReclassificationReport
#print axioms reclassificationReport
#print axioms reclassificationReport_eq_of_polynomialsAgreeAt_one
#print axioms reclassificationReport_historyEvent_eq_rateHistory
#print axioms witnessSourceJoint
#print axioms witnessTargetJoint
#print axioms nriShift_witness
