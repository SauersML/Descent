/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalAUCUnbiasedness

/-! Axiom audit of EmpiricalAUCUnbiasedness. -/

open Descent.Portability.EmpiricalAUCUnbiasedness

#print axioms scoreValue_eq_scoreOf
#print axioms outcomeValue_eq_outcomeOf
#print axioms scoreMass_eq_scoreCellMass
#print axioms binaryCaseMass_eq_outcomeMass
#print axioms outcomeMass_add_eq_one
#print axioms caseControl_iff
#print axioms empiricalPairMass_eq_sum
#print axioms outcomeCount_pos
#print axioms outcomeCount_nonneg
#print axioms empiricalPairMass_pos_iff
#print axioms aucDefinedIndicator_expand
#print axioms auc_definedness_probability
#print axioms expectation_empiricalBrier
#print axioms outcomeMass_chronologyLaw
#print axioms auc_definedness_probability_chronologyLaw
#print axioms expectation_empiricalBrier_chronologyLaw
#print axioms sum_mass_eq_outcomeMass
#print axioms binaryAUCNumerator_eq_pairSum
#print axioms cohort_expectation_split
#print axioms sum_prod_mass
#print axioms prod_split_two
#print axioms prod_exchange_two
#print axioms prod_pinMarker
#print axioms sum_prod_pinned
#print axioms sum_prod_pair
#print axioms empiricalPairMass_eq_outcomePairMass
#print axioms aucDefinedIndicator_eq_outcomeDefinedIndicator
#print axioms outcomePairMass_pos_iff
#print axioms outcome_fiber_numerator
#print axioms outcome_fiber_identity
#print axioms auc_numerator_identity
#print axioms conditional_empiricalAUC
#print axioms conditional_empiricalAUC_chronologyLaw
#print axioms prod_split_one
#print axioms prod_exchange_one
#print axioms prod_singleMarker
#print axioms sum_prod_pinned_one
#print axioms cohort_expectation_split_score
#print axioms sum_mass_eq_scoreMass
#print axioms sum_prod_mass_score
#print axioms scoreCount_split
#print axioms slopeDefinedIndicator_split
#print axioms scoreGroupSize_pos
#print axioms scoreGroupSize_pos_of_defined
#print axioms score_fiber_total
#print axioms score_fiber_mean
#print axioms score_fiber_slope
#print axioms slope_numerator_identity
#print axioms linearSlope_cleared
#print axioms conditional_empiricalSlope
#print axioms scoreMass_chronologyLaw
#print axioms conditional_empiricalSlope_chronologyLaw
