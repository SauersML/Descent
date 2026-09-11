/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.Conservation

/-! Axiom audit of Conservation. -/

open Descent.Pangenome.GraphCoalescent

#print axioms hiddenExcess_add_reportBlocks
#print axioms sum_hiddenLoad_sub_one
#print axioms hiddenExcess_of_invisible
#print axioms hiddenExcess_of_visible
#print axioms hiddenExcess_bot
#print axioms hiddenExcess_top
#print axioms hiddenExcess_path_eq
#print axioms reportBlocks_path_eq
#print axioms card_silentSteps_visibleSteps
#print axioms graphKer_le_graphKer_comp
#print axioms observed_le_observed_of_graphKer_le
#print axioms observed_eq_top_of_graphKer_le
#print axioms connectedTimes_subset
