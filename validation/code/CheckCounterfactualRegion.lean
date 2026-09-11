/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CounterfactualRegion

/-! Axiom audit of CounterfactualRegion. -/

open Descent.Portability.CounterfactualRegion

#print axioms counterfactualOutcome_consistent
#print axioms counterfactualOutcome_split
#print axioms expectation_counterfactualOutcome
#print axioms expectation_offIndicator_nonneg
#print axioms counterfactual_mean_mem_interval
#print axioms counterfactual_mean_attains
#print axioms signOf_eq_sign
#print axioms signOf_true
#print axioms signOf_false
#print axioms observational_laws_agree
#print axioms intervened_mean_first_model
#print axioms intervened_mean_second_model
