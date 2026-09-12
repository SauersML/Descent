/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityRatePath

/-! Axiom audit of EndToEndSensitivityRatePath. -/

open Descent.Portability.EndToEndSensitivityRatePath

#print axioms continuousOn_dualGenerator_rateSegment
#print axioms dualGeneratorPath_rateSegment
#print axioms hasDerivAt_rateHistoryDualPropagator_segment
#print axioms hasDerivAt_dotProduct_rateHistoryDualPropagator_segment
#print axioms hasDerivAt_of_eq_dotProduct_rateSegment
#print axioms hasDerivAt_integral_correlationNumerator_rateSegment
#print axioms hasDerivAt_integral_correlationDenominator_rateSegment
#print axioms hasDerivAt_expectedPortability_rateSegment
