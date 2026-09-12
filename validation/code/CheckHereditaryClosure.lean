/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.HereditaryClosure

/-! Axiom audit of HereditaryClosure. -/

open Descent.Pangenome.AncestralLocality

#print axioms card_quotient_le
#print axioms card_quotient_le_of_le
#print axioms card_quotient_lt_of_lt
#print axioms iterate_add_eq_of_fixed
#print axioms iterate_fixed_of_card_le
#print axioms refinement_rel_iff
#print axioms refinement_le
#print axioms refinement_eq_self_iff
#print axioms isAutonomous_of_refinement_eq
#print axioms sum_block_eq_of_le
#print axioms le_refinement_of_isAutonomous
#print axioms iterate_refinement_le
#print axioms hereditaryClosure_le
#print axioms refinement_hereditaryClosure
#print axioms hereditaryClosure_eq_iterate
#print axioms blocks_le_blocks_hereditaryClosure
#print axioms isAutonomous_hereditaryClosure
#print axioms le_iterate_refinement_of_isAutonomous
#print axioms le_hereditaryClosure_of_isAutonomous
#print axioms isGreatest_hereditaryClosure
#print axioms hereditarilyAutonomous_closureMap
#print axioms ker_le_hereditaryClosure_of_hereditarilyAutonomous
#print axioms isHeredityKernel_transportKernel
#print axioms blockMass_transportKernel
#print axioms refinement_transportKernel
#print axioms iterate_refinement_transportKernel
#print axioms hereditaryClosure_transportKernel
#print axioms isAutonomous_transportKernel_iff
#print axioms hereditaryClosure_ker_comp_symm
#print axioms kernelMass_gatedKernel_observeA
#print axioms kernelMass_gatedKernel_observeB
#print axioms hereditarilyAutonomous_observeA
#print axioms hereditarilyAutonomous_observeB
#print axioms not_hereditarilyAutonomous_observeAB
#print axioms exists_autonomous_pair_not_autonomous_join
