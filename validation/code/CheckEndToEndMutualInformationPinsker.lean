/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndMutualInformationPinsker

/-! Axiom audit of EndToEndMutualInformationPinsker. -/

open Descent.Portability.EndToEndMutualInformationPinsker

#print axioms logFactor
#print axioms hasDerivAt_logFactor
#print axioms logFactor_sign
#print axioms padeGap
#print axioms hasDerivAt_padeGap
#print axioms padeGap_nonneg
#print axioms quadraticFactor_ge
#print axioms sq_sub_le_mul_divergenceTerm
#print axioms pinsker_finite
#print axioms sum_productMarginals
#print axioms productMarginalLaw
#print axioms productMarginalLaw_mass
#print axioms independenceGap
#print axioms independenceGap_eq_two_mul_totalVariation
#print axioms half_sq_independenceGap_le_mutualInformation
#print axioms two_mul_sq_totalVariation_le_mutualInformation
#print axioms sq_independenceGap_div_le_pseudoRSquared
#print axioms continuous_independenceGap
#print axioms half_integral_sq_independenceGap_le_expectedMutualInformation
#print axioms half_sq_integral_independenceGap_le_expectedMutualInformation
#print axioms sq_integral_independenceGap_div_le_expectedPseudoRSquared
#print axioms pinsker_historyEventKernel
#print axioms pinsker_rateHistoryKernel
