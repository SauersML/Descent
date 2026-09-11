/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderExponentialDraw

/-! Axiom audit of CylinderExponentialDraw. -/

open Descent.Portability.CylinderExponentialDraw

#print axioms tendsto_truncatedDraw
#print axioms curve_truncatedDraw_eq
#print axioms integral_truncatedDraw_curve
#print axioms integral_uniformDraw_of_antitoneOn
#print axioms exp_neg_one_le_one
#print axioms max_exp_neg_one_pos
#print axioms exponentialCap_continuous
#print axioms exponentialCap_antitone
#print axioms exponentialCap_le_one
#print axioms exponentialCap_nonneg
#print axioms exponentialCap_eq_min
#print axioms integral_exponentialCap
#print axioms cast_logLower
#print axioms cast_logUpper
#print axioms logLower_le_neg_log
#print axioms neg_log_le_logUpper
#print axioms logLower_antitone_rate
#print axioms logLower_le_succ
#print axioms logUpper_succ_le
#print axioms logUpper_antitone_rate
#print axioms capLower_le
#print axioms le_capUpper
#print axioms min_one_sub_min_one_le
#print axioms tail_le
#print axioms exponentialWidth_le
#print axioms placeValue_le_truncatedDraw
#print axioms exponentialEvaluator
#print axioms integral_exponentialCap_uniformDraw
#print axioms exponential_certificate
#print axioms tendsto_exponential_certificate
#print axioms integral_min_exponentialDraw
