/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadderDispersion

/-! Axiom audit of PortabilityMomentLadderDispersion. -/

open Descent.Portability.PortabilityMomentLadderDispersion

#print axioms DecisionDispersion
#print axioms decisionDispersion
#print axioms memLp_two_polynomialFunction
#print axioms variance_polynomialFunction_eq
#print axioms variance_polynomialFunction_eq_of_polynomialsAgreeAt_two_mul
#print axioms decisionDispersion_eq_of_polynomialsAgreeAt_two
#print axioms covarianceDispersion_eq_of_polynomialsAgreeAt_four
#print axioms deviation_le_of_polynomialsAgreeAt_two_mul
#print axioms confusionDeviation_le_of_polynomialsAgreeAt_two
#print axioms decisionDispersion_historyEvent_eq_rateHistory
