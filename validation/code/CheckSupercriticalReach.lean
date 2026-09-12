/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalReach

/-! Axiom audit of SupercriticalReach. -/

open Descent.Pangenome.AncestralLocality

#print axioms graphExpect_add
#print axioms graphExpect_div_const
#print axioms graphProb_add_not
#print axioms graphProb_le_one
#print axioms graphProb_mono
#print axioms reach_mono
#print axioms reach_singleton_eq_of_mem
#print axioms sq_card_reach_le_sum
#print axioms giantEvent_zero_of_forall_card_le
#print axioms indicator_not_giantEvent_zero_le
#print axioms graphProb_not_giantEvent_zero_le
#print axioms giantComponentLaw_of_lt_one
#print axioms giantComponentLaw_half
#print axioms card_reach_le_of_forall_not_mem
#print axioms abs_card_reach_div_sub_le_of_mem
#print axioms giantEvent_card_reach_dichotomy
#print axioms tendsto_graphProb_reach_near_zero_or_giant
