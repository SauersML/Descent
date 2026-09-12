/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.FiniteJumpProcess

/-! Axiom audit of FiniteJumpProcess. -/

open Descent.Pangenome.GraphCoalescent.FiniteJumpProcess

#print axioms stateAt_eq_some_iff
#print axioms stateAt_eq_of_mem_Ico
#print axioms map_consSeq_infinitePi
#print axioms infinitePi_eq_lintegral_consSeq
#print axioms lintegral_stepMeasure_eval
#print axioms fuelProb_succ
#print axioms pathMeasure_jumpHold_cylinder
#print axioms sum_holdJumpGenerator
#print axioms sum_exp_smul_holdJumpGenerator
#print axioms exp_smul_apply_eq_firstJump
#print axioms ofReal_exp_smul_apply_eq_firstJump
#print axioms canonicalKernel_apply_of_ne
#print axioms holdJumpGenerator_canonical
#print axioms fuelProb_le_exp
#print axioms fuelProb_none_le
#print axioms fuelProb_none_add_sum
#print axioms pathMeasure_stateAt_eq
#print axioms stateProb_eq
#print axioms stateProb_eq_matrixExponential
#print axioms pathMeasure_stateAt_none
#print axioms hasDerivAt_stateProb_forward
#print axioms hasDerivAt_stateProb_backward
#print axioms stateProb_add
#print axioms stateProb_canonical_eq
