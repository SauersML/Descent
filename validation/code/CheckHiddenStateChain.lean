/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenStateChain

/-! Axiom audit of HiddenStateChain. -/

open Descent.Pangenome.GraphCoalescent

#print axioms hiddenJumpLaw_apply
#print axioms hiddenJumpLaw_of_absorbed
#print axioms blocks_eq_sum_hiddenState
#print axioms blocks_eq_of_hiddenState_eq
#print axioms hiddenJumpLaw_eq_of_hiddenState_eq
#print axioms hiddenKernel_hiddenState
#print axioms hiddenKernel_invisibleTarget
#print axioms hiddenKernel_visibleTarget
#print axioms hiddenKernel_invisibleTarget_toReal
#print axioms hiddenKernel_visibleTarget_toReal
#print axioms hiddenChainLaw_zero
#print axioms hiddenChainLaw_succ
#print axioms blockLaw_map_hiddenState_succ
