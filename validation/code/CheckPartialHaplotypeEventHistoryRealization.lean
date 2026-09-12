/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeEventHistoryRealization

/-! Axiom audit of PartialHaplotypeEventHistoryRealization. -/

open Descent.Portability.PartialHaplotypeEventHistoryRealization

#print axioms HaplotypeHistoryEvent.duration
#print axioms HaplotypeHistoryEvent.ofEpoch
#print axioms HaplotypeHistoryEvent.demeSplit
#print axioms splitParent
#print axioms split_weight
#print axioms pulseKernel_split_mulVec
#print axioms pulsedState
#print axioms stateLaw_pulsedState
#print axioms budgetMomentFeature_pulsedState
#print axioms pulseKernel_mulVec_mem_realizationBody
#print axioms eventMatrix
#print axioms eventPropagator
#print axioms eventPulseCount
#print axioms eventHistoryDuration
#print axioms eventPropagator_ofEpoch
#print axioms eventMatrix_mulVec_mem_realizationBody
#print axioms eventPropagator_mulVec_mem_realizationBody
#print axioms exists_eventHistoryLaw
#print axioms ForwardOnEventHistory
#print axioms forwardOnEventHistory_nil
#print axioms expectedMomentVector_eventHistory
#print axioms realizableLaw
#print axioms realizableLaw_spec
#print axioms realizableExpectation
#print axioms expectedMoments_realizableExpectation
#print axioms eventMoments
#print axioms eventMoments_ofEpoch
#print axioms eventMoments_zero
#print axioms eventMoments_mem_realizationBody
#print axioms eventRealizedExpectation
#print axioms expectedMomentVector_eventRealizedExpectation
#print axioms forwardOnEventHistory_of_moments
#print axioms forwardOnEventHistory_eventRealizedExpectation
#print axioms expectedMomentVector_eventHistory_realized
