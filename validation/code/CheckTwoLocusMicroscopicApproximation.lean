/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoLocusMicroscopicApproximation

/-! Axiom audit of the hypothesis-free two-locus microscopic approximation and NOTE1 Theorem 2. -/

open Descent.Portability.TwoLocusMicroscopicApproximation

#print axioms enlargedMicroscopicApproximation
#print axioms enlargedLowOrderLDGenerator_zeroDeme
#print axioms zeroDemeMicroscopicApproximation
#print axioms enlargedLowOrderLDFeature_eq
#print axioms enlargedPropagator_mulVec_mem_realizationBody
#print axioms rateEpoch_preserves_locusExchangeable_realization
#print axioms RateHistoryEvent.instruction
#print axioms propagate_preserves_locusExchangeable_realization
#print axioms history_present_locusExchangeable_realization
#print axioms locusExchangeableSplit_haplotype
#print axioms history_present_mem_realizationBody_of_events
#print axioms history_present_dd_quadraticForm_nonneg
#print axioms history_present_dd_cauchySchwarz
#print axioms history_present_dd_diagonal_nonneg
#print axioms history_LDPairDomain
