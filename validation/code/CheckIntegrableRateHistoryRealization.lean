/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntegrableRateHistoryRealization

/-! Axiom audit of locus-exchangeable realizability under time-varying rate histories. -/

open Descent.Portability.IntegrableRateHistoryRealization

#print axioms generatorPath
#print axioms generatorPath_of_mem
#print axioms continuous_generatorPath
#print axioms exists_generatorPath_bound
#print axioms rateHistoryPropagator
#print axioms fundamentalMatrix_generatorPath_zero
#print axioms hasDerivWithinAt_rateHistory
#print axioms sampledRateEvents
#print axioms propagate_sampledRateEvents
#print axioms exchangeableStates
#print axioms isClosed_exchangeableStates
#print axioms mem_exchangeableStates_iff
#print axioms rateHistory_preserves_locusExchangeable_realization
#print axioms rateHistoryPropagator_mulVec_mem_realizationBody
#print axioms rateHistoryPropagator_dd_quadraticForm_nonneg
#print axioms norm_rateHistoryPropagator_sub_le
#print axioms eventually_integral_norm_sampledGenerator_sub_le
