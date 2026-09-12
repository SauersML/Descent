/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.GiantComponentAssembly

/-! Axiom audit of GiantComponentAssembly. -/

open Descent.Pangenome.AncestralLocality

#print axioms continuousAt_giantFraction
#print axioms GiantEvent.mono
#print axioms eventually_graphExpect_card_bigSet_le
#print axioms tendsto_graphProb_card_bigSet_gt
#print axioms giantComponentLaw_of_lower
#print axioms largeCount_floor_add_one
#print axioms tendsto_graphProb_exists_card_reach_ge_giantFraction
#print axioms giantComponentLaw_of_largeCountConcentration
