/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralRateHistoryRealization

/-! Axiom audit of NeutralRateHistoryRealization. -/

open Descent.Portability.NeutralRateHistoryRealization

#print axioms dualGeneratorPath
#print axioms continuous_dualGeneratorPath
#print axioms exists_dualGeneratorPath_bound
#print axioms rateHistoryDualPropagator
#print axioms sampledEpochs
#print axioms historyPropagator_append
#print axioms historyPropagator_sampledEpochs
#print axioms tendsto_historyPropagator_sampledEpochs
#print axioms historyPropagator_mulVec_mem_realizationBody
#print axioms rateHistoryDualPropagator_mulVec_mem_realizationBody
#print axioms exists_rateHistoryLaw
#print axioms tendsto_integral_momentPolynomial_sampledEpochs
#print axioms tendsto_integral_panelReport_sampledEpochs
