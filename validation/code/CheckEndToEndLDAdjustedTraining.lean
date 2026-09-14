/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndLDAdjustedTraining

/-! Axiom audit of EndToEndLDAdjustedTraining. -/

open Descent.Portability.EndToEndLDAdjustedTraining

#print axioms adjustedWeights
#print axioms adjugateWeights
#print axioms ridgeWeights_eq_of_mulVec_eq
#print axioms isUnit_det_add_penalty
#print axioms adjustedWeights_eq_trainedWeights_of_tagCovariance_eq
#print axioms adjustedWeights_self
#print axioms r2_eq_dot
#print axioms r2_smul_weights
#print axioms det_smul_adjustedWeights
#print axioms r2_adjustedWeights_eq_adjugate
#print axioms predictiveCovariance_adjustedWeights_source
#print axioms calibrationSlope_adjustedWeights_source
#print axioms penalty_sq_mul_dot_le
#print axioms abs_le_of_penalty_sq_mul_dot_le
#print axioms tendsto_penalty_smul_adjustedWeights
#print axioms adjustedReport_historyEventKernel
#print axioms adjustedReport_eq_of_moments_eq
#print axioms witnessSource
#print axioms witnessPanel
#print axioms witnessArchitecture
#print axioms witnessCovariance_nonneg
#print axioms witnessMatchedWeights
#print axioms witnessPanelWeights
#print axioms witnessMatchedR2
#print axioms witnessPanelR2
#print axioms r2_mismatchedPanel_lt_matched
