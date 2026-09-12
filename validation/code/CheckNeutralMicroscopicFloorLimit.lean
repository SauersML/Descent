/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralMicroscopicFloorLimit

/-! Axiom audit of NeutralMicroscopicFloorLimit. -/

open Descent.Portability.NeutralMicroscopicFloorLimit

#print axioms varying_euler_tends_exp
#print axioms tendsto_floor_div
#print axioms tendsto_floor_div_mul
#print axioms tendsto_norm_euler_floor_sub
#print axioms norm_kernelPower_sub_euler_le_floor
#print axioms abs_kernelPower_dotProduct_sub_le
#print axioms tendstoUniformly_kernelPower_floor_dotProduct
#print axioms coe_polynomialSubspace_eq_dotProduct
#print axioms coe_neutralPolynomialSemigroup_eq_dotProduct
#print axioms tendstoUniformly_neutralPolynomialSemigroup_floor
#print axioms neutralPolynomialSemigroup_markov_of_euler
#print axioms tendstoUniformly_integral_neutralMarkovKernel_floor
