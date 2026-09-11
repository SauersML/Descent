/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SmallCohortConditionalMeans

/-! Axiom audit of SmallCohortConditionalMeans. -/

open Descent.Portability.SmallCohortConditionalMeans

#print axioms sum_census_cells
#print axioms censusOf_counts
#print axioms counts_mem_censusIndex
#print axioms censusOf_mem_piAntidiag
#print axioms censusOf_index
#print axioms cohort_expectation_censusIndex
#print axioms cohortCorrelation_mul_definedIndicator_eq
#print axioms expectation_cohortCorrelation_three
#print axioms expectation_cohortCorrelation_four
#print axioms expectation_cohortCorrelation_three_half
#print axioms conditional_cohortCorrelation_three_half
#print axioms conditional_cohortCorrelation_halvedCoupling_three
#print axioms expectation_cohortCorrelation_halvedCoupling_four
#print axioms conditional_cohortCorrelation_halvedCoupling_four
#print axioms conditional_empiricalAUC_halvedCoupling
