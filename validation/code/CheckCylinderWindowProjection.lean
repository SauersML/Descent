/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CylinderWindowProjection

/-! Axiom audit of CylinderWindowProjection. -/

open Descent.Pangenome.AncestralLocality.CylinderWindowProjection

#print axioms continuous_windowRestrict
#print axioms shrinkWindow
#print axioms continuous_shrinkWindow
#print axioms shrinkWindow_comp_restrict
#print axioms windowLaw
#print axioms shrinkLaw
#print axioms continuous_windowLaw
#print axioms continuous_shrinkLaw
#print axioms shrinkLaw_windowLaw
#print axioms extendWindow
#print axioms continuous_extendWindow
#print axioms restrict_extendWindow
#print axioms windowLaw_surjective
#print axioms windowPullback
#print axioms shrinkPullback
#print axioms windowPullback_apply
#print axioms shrinkPullback_apply
#print axioms windowPullback_shrinkPullback
#print axioms norm_windowPullback
#print axioms windowPullback_injective
#print axioms windowMonomial
#print axioms windowAlgebra
#print axioms windowMonomial_mem_windowAlgebra
#print axioms windowPullback_windowMonomial
#print axioms shrinkPullback_windowMonomial
#print axioms windowPolynomial
#print axioms windowPolynomial_mem_windowAlgebra
#print axioms windowPullback_windowPolynomial
#print axioms windowPullback_mem_samplingAlgebra
#print axioms shrinkPullback_mem_windowAlgebra
#print axioms exists_windowPullback
#print axioms WindowOperatorFamily
#print axioms identityWindowOperators
#print axioms windowPullback_operator_agree
#print axioms gluedValue
#print axioms gluedValue_eq
#print axioms gluedOperator
#print axioms gluedOperator_windowPullback
#print axioms norm_gluedOperator_le
#print axioms continuousGluedOperator
#print axioms denseRange_samplingAlgebra_subtypeL
#print axioms norm_le_subtypeL
#print axioms extendedOperator
#print axioms extendedOperator_apply
#print axioms norm_extendedOperator_le
