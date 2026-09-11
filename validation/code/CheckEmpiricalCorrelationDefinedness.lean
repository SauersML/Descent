/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalCorrelationDefinedness

/-! Axiom audit of EmpiricalCorrelationDefinedness. -/

open Descent.Portability.EmpiricalCorrelationDefinedness

#print axioms sum_count_eq
#print axioms expectation_tableLaw
#print axioms sum_eq_sum_cellCount
#print axioms expectation_tableLaw_cellCount
#print axioms table_total_ne_zero
#print axioms tableLaw_variance_scoreValue
#print axioms tableLaw_variance_outcomeValue
#print axioms tableLaw_covariance
#print axioms cast_add_pos
#print axioms mul_pos_iff_of_nonneg
#print axioms tableLaw_squaredCorrelation
#print axioms expectation_scoreIndicator
#print axioms expectation_outcomeIndicator
#print axioms expectation_cellIndicator
#print axioms cellIndicator_mul
#print axioms cohort_expectation_prod
#print axioms sum_mass_all_score
#print axioms sum_mass_all_outcome
#print axioms cellCount_score_pos
#print axioms cellCount_outcome_pos
#print axioms defined_iff_not_constant
#print axioms prod_member_indicator
#print axioms inclusion_exclusion_two_pairs
#print axioms definedIndicator_expand
#print axioms definedness_probability
#print axioms definedness_probability_of_equal_marginals
