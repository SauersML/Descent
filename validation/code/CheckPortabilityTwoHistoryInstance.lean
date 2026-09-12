/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityTwoHistoryInstance

/-! Axiom audit of PortabilityTwoHistoryInstance. -/

open Descent.Portability.PortabilityTwoHistoryInstance

#print axioms terminalMass_twoPointHistory
#print axioms terminalTable_nonneg
#print axioms terminalTable_sum
#print axioms experimentMass_nonneg
#print axioms sum_experimentMass_terminal
#print axioms sum_experimentMass
#print axioms sourcePanelLaw_toReal
#print axioms sourcePanelLaw_false_eq_true
#print axioms totalVariation_sourcePanelLaw
#print axioms half_separation_le_worstRisk
#print axioms lt_worstRisk_of_lt_half_separation
#print axioms worstRisk_midpoint
#print axioms isLeast_worstRisk
#print axioms panelMass_sum
#print axioms atomMass_eq_sum_panelMass
#print axioms half_separation_r2
#print axioms half_separation_r2Portability
#print axioms half_separation_r2_zero_one
#print axioms half_separation_r2_one_zero
#print axioms half_separation_r2Portability_zero_one
#print axioms minimax_floor_r2
#print axioms minimax_floor_r2Portability
#print axioms minimax_floor_r2_zero_one
#print axioms minimax_floor_r2_one_zero
#print axioms minimax_floor_r2Portability_zero_one
