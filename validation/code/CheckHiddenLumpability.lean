/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLumpability

/-! Axiom audit of HiddenLumpability. -/

open Descent.Pangenome.GraphCoalescent

#print axioms invisibleTarget_eq_of_rel
#print axioms visibleTarget_eq_of_rel
#print axioms hiddenState_merge_of_rel
#print axioms hiddenState_merge_of_not_rel
#print axioms hiddenState_of_covers
#print axioms covers_hiddenState_eq_invisibleTarget_iff
#print axioms covers_hiddenState_eq_visibleTarget_iff
#print axioms card_covers_invisibleTarget
#print axioms card_covers_visibleTarget
#print axioms card_covers_hiddenState_eq
#print axioms exampleInterface_fiberCard_zero
#print axioms exampleInterface_fiberCard_two
#print axioms example_rel_zero_one
#print axioms example_not_rel_zero_two
#print axioms example_ne_zero_one
#print axioms example_loads_bot
#print axioms example_invisible_rate
#print axioms example_visible_rate
#print axioms example_total_rate
#print axioms example_loads_after_invisible
#print axioms example_visible_rate_after
#print axioms example_mean_connection_time
