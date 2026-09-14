/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SelectionHistoryVaryingFitness

/-! Axiom audit of SelectionHistoryVaryingFitness. -/

open Descent.Portability.SelectionHistoryVaryingFitness

#print axioms weightedSelection
#print axioms weightedSelection_const
#print axioms weightedSelection_le
#print axioms VaryingSelectedOnHistory
#print axioms varyingSelectedOnHistory_nil
#print axioms varyingSelectedOnHistory_const_iff
#print axioms norm_event_sub_propagator_le
#print axioms norm_varyingHistory_sub_propagator_le
#print axioms norm_selectedHistory_sub_propagator_le_of_const
#print axioms abs_varyingPortability_sub_neutral_le
