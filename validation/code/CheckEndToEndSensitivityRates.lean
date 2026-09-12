/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityRates

/-! Axiom audit of EndToEndSensitivityRates. -/

open Descent.Portability.EndToEndSensitivityRates

#print axioms hasDerivAt_dualGenerator_apply
#print axioms hasDerivAt_eventPropagator_ratePath
#print axioms dualGenerator_rateSegment
#print axioms hasDerivAt_dualGenerator_rateSegment
#print axioms hasDerivAt_eventPropagator_segmentEvent
#print axioms deriv_eventPropagator_segmentEvent
#print axioms hasDerivAt_familyDerivative_segmentHistory
#print axioms hasDerivAt_dotProduct_segmentHistory
#print axioms hasDerivAt_expectedPortability_segmentHistory
#print axioms hasDerivAt_expectedCalibrationPortability_segmentHistory
#print axioms hasDerivAt_expectedAUCPortability_segmentHistory
