/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ShortTimeConnectionLaw

/-! Axiom audit of the short-time law of the connection time. -/

open Descent.Pangenome.GraphCoalescent.ShortTimeConnectionLaw

#print axioms abs_pow_apply_le
#print axioms summable_pow_apply
#print axioms exp_smul_apply
#print axioms tsum_sub_leading_isBigO
#print axioms exp_smul_apply_sub_isBigO
#print axioms pow_apply_eq_zero_of_level
#print axioms descentMatrix
#print axioms descentMatrix_apply
#print axioms pow_apply_eq_descentMatrix_pow_apply
#print axioms targetProbability
#print axioms targetProbability_sub_isBigO
#print axioms kingmanMatrix
#print axioms kingmanMatrix_mulVec
#print axioms kingmanMatrix_step
#print axioms descentMatrix_kingmanMatrix_apply
#print axioms connectedStates
#print axioms reportConnectedProbability
#print axioms minimalHistoryCount
#print axioms reportConnectedProbability_sub_isBigO
