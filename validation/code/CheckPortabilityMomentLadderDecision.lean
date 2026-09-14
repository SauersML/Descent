/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadderDecision

/-! Axiom audit of PortabilityMomentLadderDecision. -/

open Descent.Portability.PortabilityMomentLadderDecision

#print axioms DecisionReport
#print axioms decisionReport
#print axioms decisionReport_eq_of_polynomialsAgreeAt_one
#print axioms portabilityReport_and_decisionReport_eq_of_polynomialsAgreeAt_four
#print axioms expectedRecallPrecision_eq_of_polynomialsAgreeAt_all
#print axioms decisionReport_historyEvent_eq_rateHistory
#print axioms expectedRecallPrecision_historyEvent_eq_rateHistory
