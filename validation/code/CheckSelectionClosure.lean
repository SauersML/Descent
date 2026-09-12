/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SelectionClosure

/-! Axiom audit of SelectionClosure. -/

open Descent.Pangenome.AncestralLocality

#print axioms selectedKernel_eq
#print axioms hereditaryClosure_selectedKernel
#print axioms selectedReproduce_eq
#print axioms sum_mul_pos_of_mem_stdSimplex
#print axioms sizeBias_mem_stdSimplex
#print axioms sizeBias_sizeBias_inv
#print axioms pushforward_sizeBias_of_factor
#print axioms selectionAutonomous_iff_of_factor
#print axioms isGreatest_selectionClosure
#print axioms selectionClosure_le_inf
#print axioms selectionClosure_eq_hereditaryClosure_iff
#print axioms selectionAutonomous_closureMap
#print axioms halfMix_symm
#print axioms hereditarilyAutonomous_halfMix
#print axioms reproduce_halfMix_eq
#print axioms pushforward_sizeBias_pairMidpoint
#print axioms fitness_eq_of_selectionAutonomous_halfMix
#print axioms selectionAutonomous_halfMix_iff
#print axioms sum_sum_mul_const
#print axioms selectionAutonomous_of_kernelMass_eq
#print axioms selectionAutonomous_parentFree
#print axioms ker_observeA_inf_ker_bFitness
#print axioms selectionClosure_ne_inf_gated
