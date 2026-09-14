/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder

/-! Axiom audit of PortabilityMomentLadder. -/

open Descent.Portability.PortabilityMomentLadder

#print axioms MomentsAgreeAt
#print axioms momentsAgreeAt_refl
#print axioms MomentsAgreeAt.mono
#print axioms PortabilityReport
#print axioms portabilityReport
#print axioms portabilityReport_eq_of_momentsAgreeAt_four
#print axioms portabilityReport_and_training_eq_of_momentsAgreeAt_eight
#print axioms expectedMetrics_eq_of_momentsAgreeAt_all
#print axioms PolynomialsAgreeAt
#print axioms polynomialsAgreeAt_refl
#print axioms PolynomialsAgreeAt.mono
#print axioms polynomialsAgreeAt_of_hasDualMoments
#print axioms MomentsAgreeAt.polynomialsAgreeAt
#print axioms portabilityReport_eq_of_polynomialsAgreeAt_four
#print axioms portabilityReport_historyEvent_eq_rateHistory
