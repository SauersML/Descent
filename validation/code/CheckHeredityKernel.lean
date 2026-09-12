/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.HeredityKernel

/-! Axiom audit of HeredityKernel. -/

open Descent.Pangenome.AncestralLocality

#print axioms kernelMass_symm
#print axioms reproduce_mem_stdSimplex
#print axioms mem_fiber_iff
#print axioms pushforward_eq_sum_fiber
#print axioms mem_block_iff
#print axioms block_ker
#print axioms blockMass_symm
#print axioms hereditarilyAutonomous_id
#print axioms kernelMass_fiber_congr
#print axioms hereditarilyAutonomous_iff
#print axioms isHeredityKernel_of_kernelMass_fiber_eq
#print axioms kernelMass_childKernel
#print axioms isHeredityKernel_childKernel
#print axioms pushforward_reproduce
#print axioms sum_mul_comp_eq_sum_pushforward
#print axioms sum_sum_mul_comp_eq_sum_sum_pushforward
#print axioms pointMass_mem_stdSimplex
#print axioms sum_pointMass_mul
#print axioms sum_pairMidpoint_mul
#print axioms pairMidpoint_mem_stdSimplex
#print axioms sum_sum_pointMass
#print axioms sum_sum_pairMidpoint
#print axioms pushforward_pointMass
#print axioms pushforward_pairMidpoint
