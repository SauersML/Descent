/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndPortabilityLipschitz

/-! Axiom audit of EndToEndPortabilityLipschitz. -/

open Descent.Portability.EndToEndPortabilityLipschitz

#print axioms abs_mul_sub_mul_le
#print axioms abs_div_sub_div_le_of_le_one
#print axioms rateHistoryDualPropagator_eq_caratheodory
#print axioms norm_rateHistoryDualPropagator_sub_le
#print axioms abs_integral_correlationNumerator_sub_le
#print axioms abs_integral_correlationDenominator_sub_le
#print axioms integrable_correlationNumerator
#print axioms integrable_correlationDenominator
#print axioms integral_correlationNumerator_nonneg
#print axioms integral_correlationNumerator_le_denominator
#print axioms integral_correlationDenominator_le_one
#print axioms abs_expectedPortability_sub_le
