/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityLaw

/-! Axiom audit of EndToEndSensitivityLaw. -/

open Descent.Portability.EndToEndSensitivityLaw

#print axioms continuous_exp_smul_mul_exp_smul
#print axioms hasDerivAt_exp_smul_mul_exp_smul
#print axioms exp_smul_sub_exp_smul_eq_integral
#print axioms continuous_duhamelIntegral
#print axioms continuous_duhamelIntegral_apply
#print axioms tendsto_coordinates_slope
#print axioms slope_exp_smul_eq_integral
#print axioms hasDerivAt_exp_smul_apply
#print axioms hasDerivAt_of_hasDerivAt_apply
#print axioms hasDerivAt_apply
#print axioms hasDerivAt_matrixExponential_of_hasDerivAt
#print axioms hasDerivAt_matrixExponential_apply
#print axioms dotProduct_duhamelDerivative_mulVec
#print axioms duhamelDerivative_of_commute
#print axioms matrixExponential_neg_smul_one
#print axioms hasDerivAt_portabilityDecay_rate
#print axioms backValue_succ_eq
#print axioms backValue_congr
#print axioms hasDerivAt_historyStage
#print axioms historyEventPropagator_mulVec_eq_backValue
#print axioms hasDerivAt_dotProduct_historyEventPropagator
#print axioms hasDerivAt_eventPropagator_epoch
#print axioms hasDerivAt_eventPropagator_pulse
