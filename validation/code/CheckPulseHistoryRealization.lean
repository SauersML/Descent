/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PulseHistoryRealization

/-! Axiom audit of realizability under histories with admixture pulses. -/

open Descent.Portability.PulseHistoryRealization

#print axioms slotAverage
#print axioms contrastStencil
#print axioms pulseMoment
#print axioms slotAverage_add
#print axioms slotAverage_smul
#print axioms contrastStencil_add
#print axioms contrastStencil_smul
#print axioms pulseMomentMap
#print axioms lowOrderLDPulseTransform
#print axioms lowOrderLDPulseTransform_mulVec
#print axioms pulseMoment_lowOrderLDFeature
#print axioms mulVec_expectation
#print axioms realization_state_eq_expectation
#print axioms lowOrderLDPulseTransform_mulVec_eq_pulseState
#print axioms pulseRealization
#print axioms expectation_slotAverage
#print axioms rightHeterozygosity_pulseHaplotype
#print axioms lowOrderLDPulseTransform_mulVec_rightHeterozygosity
#print axioms locusExchangeablePulse
#print axioms PulseHistoryEvent.instruction
#print axioms PulseHistoryEvent.identityPulse
#print axioms PulseHistoryEvent.preserves_locusExchangeable_realization
#print axioms propagate_pulseHistory_preserves_locusExchangeable_realization
#print axioms pulseHistory_present_locusExchangeable_realization
#print axioms pulseHistory_present_mem_realizationBody
#print axioms pulseHistory_present_dd_quadraticForm_nonneg
#print axioms pulseHistory_present_dd_cauchySchwarz
#print axioms pulseHistory_present_dd_diagonal_nonneg
#print axioms pulseHistory_LDPairDomain
