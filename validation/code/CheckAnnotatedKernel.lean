/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.AnnotatedKernel

/-! Axiom audit of AnnotatedKernel. -/

open Descent.Pangenome.AncestralLocality

#print axioms isHeredityKernel_stateMarginal
#print axioms sum_witnessLaw
#print axioms sum_annotatedReproduce
#print axioms sum_annotatedReproduce_pointMass
#print axioms annotatedMass_eq_kernelMass
#print axioms hereditarilyAutonomous_stateMarginal_iff
#print axioms sum_annotatedReproduce_congr
#print axioms hereditarilyAutonomous_stateMarginal_congr
#print axioms hereditaryClosure_stateMarginal_congr
#print axioms isAnnotatedKernel_swapParents
#print axioms stateMarginal_swapParents
#print axioms stateMarginal_donorAnnotation
#print axioms isAnnotatedKernel_donorAnnotation
#print axioms donorAnnotation_self
#print axioms donorAnnotation_ne_swapParents
#print axioms orderedChild_ne_swap
#print axioms stateMarginal_donorAnnotation_orderedChild
#print axioms donorAnnotation_orderedChild_ne_swapParents
#print axioms stateMarginal_flagAnnotation
#print axioms witnessLaw_flagAnnotation
#print axioms isAnnotatedKernel_flagAnnotation
#print axioms exchangePerformed_comm
#print axioms exchangeVisible_comm
#print axioms witnessLaw_exchangePerformed_self
#print axioms witnessLaw_exchangeVisible_self
#print axioms performed_visible_same_closure_different_witnessLaw
