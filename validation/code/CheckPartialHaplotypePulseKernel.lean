/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypePulseKernel

/-! Axiom audit of PartialHaplotypePulseKernel. -/

open Descent.Portability.PartialHaplotypePulseKernel

#print axioms marginalFrequency_pulsedLaw
#print axioms carriers_eq_map_get
#print axioms load_relabelCarriers
#print axioms withinBudget_relabelCarriers
#print axioms choiceWeight_nonneg
#print axioms sum_choiceWeight
#print axioms configurationMoment_pulsedLaw
#print axioms pulseKernel_mulVec
#print axioms pulseKernel_rowSum
#print axioms pulseKernel_substochastic
#print axioms pulseKernel_mulVec_configurationMoment
#print axioms pulseKernel_mulVec_expectedMoment
