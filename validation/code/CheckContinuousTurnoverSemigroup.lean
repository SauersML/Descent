/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ContinuousTurnoverSemigroup

/-! Axiom audit of ContinuousTurnoverSemigroup. -/

open Descent.Portability.ContinuousTurnoverSemigroup

#print axioms exp_mulVec_le_of_euler
#print axioms gridEmbed_coe
#print axioms gridEmbed_succ
#print axioms gridEmbed_pred
#print axioms nearestDriftMatrix_mulVec
#print axioms nearestDriftMatrix_mulVec_le
#print axioms step_mulVec_eq
#print axioms gridEmbed_step
#print axioms gridEmbed_step_gridConvex
#print axioms pow_mulVec_succ
#print axioms gridEmbed_pow_gridConvex
#print axioms step_mulVec_mono
#print axioms euler_iterate_le
#print axioms diag_nonpos
#print axioms exp_nearestDriftMatrix_mulVec_le
#print axioms mulVec_smul_comm
#print axioms euler_pow_mulVec_eigen
#print axioms exp_mulVec_eigen
#print axioms linearDeathMatrix_mulVec
#print axioms linearDeathMatrix_eigen_id
#print axioms linearDeathMatrix_eigen_quad
#print axioms exp_linearDeath_sq
#print axioms exp_linearDeath_lower_endpoint
#print axioms fallingFactorial_succ_right
#print axioms fallingFactorial_down_diff
#print axioms fallingFactorial_zero
#print axioms linearDeathMatrix_eigen_falling
#print axioms exp_linearDeath_falling
#print axioms fallingFactorial_shift
#print axioms binMoment_falling
#print axioms exp_linearDeath_falling_eq_binomial
