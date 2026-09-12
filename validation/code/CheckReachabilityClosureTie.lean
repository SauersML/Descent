/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.ReachabilityClosureTie

/-! Axiom audit of ReachabilityClosureTie. -/

open Descent.Pangenome.AncestralLocality

#print axioms block_eq_filter
#print axioms refinementStep_eq_refinement
#print axioms iterate_refinementStep_eq_iterate_refinement
#print axioms autonomous_iff_hereditarilyAutonomous
#print axioms card_le_card_genomes
#print axioms ker_observeOn
#print axioms hereditaryClosure_checkKernel_agreeOn
#print axioms hereditaryClosure_checkKernel_agreeOn_of_card_le_one
#print axioms hereditaryClosure_ker_observeOn
#print axioms isHeredityKernel_checkKernel
#print axioms isGreatest_agreeOn_directedReach
#print axioms hereditarilyAutonomous_observeOn_directedReach
#print axioms ker_le_agreeOn_directedReach_of_hereditarilyAutonomous
#print axioms not_hereditarilyAutonomous_pair
