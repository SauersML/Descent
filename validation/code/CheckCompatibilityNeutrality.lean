/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality

/-! Axiom audit of CompatibilityNeutrality. -/

open Descent.Pangenome.AncestralLocality

#print axioms sum_block_reproduce
#print axioms sum_reproduce
#print axioms reproduce_nonneg
#print axioms sum_prod_filter_card_eq_choose
#print axioms halfMix_nonneg
#print axioms sum_halfMix_mul
#print axioms sum_filter_halfMix
#print axioms sum_halfMix
#print axioms reproduce_halfMix
#print axioms sum_reproduce_halfMix_mul
#print axioms CheckingGraph.totalRate_pos
#print axioms orderedChild_indicator_add
#print axioms featureMass_eq_pushforward
#print axioms exchangeKernel_marginal
#print axioms compatibilityKernel_of_eq_empty
#print axioms compatibilityKernel_of_ne_empty
#print axioms compatibilityKernel_singleEdge
#print axioms compatibilityKernel_marginal
#print axioms featureMass_reproduce_of_marginal
#print axioms featureMass_reproduce_compatibilityKernel
#print axioms featureMass_nonneg
#print axioms featureMass_le_one
#print axioms featureMass_finitePopulationLaw
#print axioms finitePopulationLaw_nonneg
#print axioms sum_finitePopulationLaw
#print axioms sum_offspringCount
#print axioms binomial_toReal
#print axioms offspringCount_eq_binomial
#print axioms witness_pushforward_eq
#print axioms pushforward_observeAB_true_true
#print axioms witness_observed
#print axioms witness_checker_values
#print axioms witness_expected
#print axioms witness_drift
#print axioms witness_no_observed_transition_law
#print axioms witness_not_autonomous
