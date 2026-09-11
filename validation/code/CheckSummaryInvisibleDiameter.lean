/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SummaryInvisibleDiameter

/-! Axiom audit of SummaryInvisibleDiameter. -/

open Descent.Portability.SummaryInvisibleDiameter

#print axioms summaryGap_nonneg
#print axioms exists_best_approximation
#print axioms abs_expectation_le_norm
#print axioms expectation_sub_metric
#print axioms abs_expectation_sub_le_two_summaryGap
#print axioms max_sub_max_neg
#print axioms max_add_max_neg
#print axioms sum_max_eq_half
#print axioms half_expectation_sub
#print axioms exists_dual_direction
#print axioms exists_attaining_pair
#print axioms linear_estimator_error_le_summaryGap
#print axioms summary_estimator_error_ge_summaryGap
#print axioms identified_iff_mem_features
