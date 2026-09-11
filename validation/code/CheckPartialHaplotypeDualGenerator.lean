/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeDualGenerator

/-! Axiom audit of PartialHaplotypeDualGenerator. -/

open Descent.Portability.PartialHaplotypeDualGenerator

#print axioms demeSecondOrder_mul
#print axioms neutralGenerator_mul
#print axioms neutralGenerator_mul_eq_carreDuChamp
#print axioms neutralGenerator_one
#print axioms halfCovariance_one_left
#print axioms halfCovariance_one_right
#print axioms halfCovariance_mul_right
#print axioms halfCovariance_mul_left
#print axioms momentPolynomial_cons
#print axioms leibniz_momentPolynomial
#print axioms neutralGenerator_momentPolynomial
#print axioms pderiv_assignmentPolynomial
#print axioms pderiv_pderiv_assignmentPolynomial
#print axioms neutralGenerator_assignmentPolynomial
#print axioms demeCovarianceForm_assignmentPolynomial
#print axioms halfCovariance_assignmentPolynomial
#print axioms eval_assignmentPolynomial
#print axioms eval_marginalPolynomial
#print axioms eval_momentPolynomial
#print axioms satisfies_coalesce_iff
#print axioms not_satisfies_of_not_compatible
#print axioms jointFrequency_eq_coalesce
#print axioms eval_halfCovariance_joint
#print axioms eval_carreDuChamp_compatible
#print axioms eval_carreDuChamp_incompatible
