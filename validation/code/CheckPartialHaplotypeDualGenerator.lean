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
#print axioms apply_eq_of_satisfies
#print axioms satisfies_update_of_none
#print axioms sum_migrationDrift
#print axioms mutationDrift_unassigned
#print axioms sum_update_of_some
#print axioms mutationDrift_retained
#print axioms sum_mutationDrift
#print axioms satisfies_restrict_full_iff
#print axioms satisfies_mixHaplotype_iff
#print axioms sum_recombinantProduct
#print axioms sum_satisfies_none
#print axioms recombinantDrift_selector
#print axioms sum_recombinationDrift
#print axioms momentPolynomial_singleton
#print axioms momentPolynomial_pair
#print axioms sum_migrationMoves
#print axioms sum_mutationMoves
#print axioms sum_recombinationMoves
#print axioms eval_neutralGenerator_marginal
#print axioms neutralGenerator_configurationMoment
#print axioms dualTransitions_rate_nonneg
#print axioms dualTransitions_withinBudget
