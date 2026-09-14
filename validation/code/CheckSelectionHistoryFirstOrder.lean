/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SelectionHistoryFirstOrder

/-! Axiom audit of SelectionHistoryFirstOrder. -/

open Descent.Portability.SelectionHistoryFirstOrder

#print axioms norm_sub_firstOrder_step_le
#print axioms continuous_correctionIntegrand
#print axioms selectionCorrection_sub
#print axioms norm_selectionCorrection_le
#print axioms historyCorrection
#print axioms historyCorrection_sub
#print axioms norm_historyCorrection_le
#print axioms norm_selectedHistory_sub_firstOrder_le
#print axioms scaledModel
#print axioms selectionTerms_scaledModel
#print axioms selectionMatrix_scaledModel
#print axioms selectionCorrection_scaledModel
#print axioms historyCorrection_scaledModel
#print axioms norm_scaledHistory_sub_firstOrder_le
#print axioms hasDerivWithinAt_of_norm_sub_le_sq
#print axioms hasDerivWithinAt_selectedHistory_firstOrder
#print axioms abs_product_le
#print axioms abs_mul_sub_firstOrder_le
#print axioms crossRatio_sub_firstOrder_eq
#print axioms abs_crossRatio_sub_firstOrder_le
#print axioms crossRatioDerivative_pos_iff_of_pos
#print axioms abs_dotProduct_le_mass_mul_norm
#print axioms dotProduct_firstOrder_bounds
#print axioms norm_expectedMomentVector_le_one
#print axioms coefficientMass
#print axioms crossRatioRemainder
#print axioms portabilityFirstOrder
#print axioms portabilityFirstOrder_pos_iff
#print axioms abs_selectedPortability_sub_firstOrder_le
#print axioms hasDerivWithinAt_selectedPortability_firstOrder
