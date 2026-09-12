/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalBranches

/-! Axiom audit of SupercriticalBranches. -/

open Descent.Pangenome.AncestralLocality

#print axioms graphExpect_const
#print axioms graphExpect_sub
#print axioms abs_graphExpect_le
#print axioms bigSet_eq_reach_of_giantEvent
#print axioms tendsto_graphExpect_choose_div_choose
#print axioms tendsto_graphProb_disjoint_bigSet
#print axioms tendsto_graphProb_sub_of_eq_on_giantEvent
#print axioms tendsto_graphProb_reach_small
#print axioms tendsto_graphProb_reach_giant
