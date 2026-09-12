/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralPulseHistoryKernel

/-! Axiom audit of NeutralPulseHistoryKernel. -/

open Descent.Portability.NeutralPulseHistoryKernel

#print axioms pulsedState
#print axioms stateLaw_pulsedState
#print axioms continuous_pulsedState
#print axioms pulseStateKernel
#print axioms integral_momentPolynomial_pulseStateKernel
#print axioms integral_momentPolynomial_comp
#print axioms eventKernel
#print axioms eventPropagator
#print axioms isMarkovKernel_eventKernel
#print axioms integral_momentPolynomial_eventKernel
#print axioms historyEventKernel
#print axioms historyEventPropagator
#print axioms isMarkovKernel_historyEventKernel
#print axioms integral_momentPolynomial_historyEventKernel
