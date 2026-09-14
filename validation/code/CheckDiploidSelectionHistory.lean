/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DiploidSelectionHistory

/-! Axiom audit of DiploidSelectionHistory. -/

open Descent.Portability.DiploidSelectionHistory

#print axioms DiploidSelectionModel
#print axioms DiploidSelectionModel.neutral
#print axioms partnerModel
#print axioms haploidDiploidModel
#print axioms marginalFitnessPolynomial
#print axioms eval_marginalFitnessPolynomial
#print axioms diploidMeanFitnessPolynomial
#print axioms diploidDrift
#print axioms diploidSelectionGenerator
#print axioms diploidSelectedGenerator
#print axioms diploidSelectionGenerator_neutral
#print axioms frozenHaploidModel
#print axioms eval_diploidDrift
#print axioms eval_diploidSelectionGenerator
#print axioms frozenHaploidModel_fitness_mem
#print axioms abs_eval_diploidSelectionGenerator_momentPolynomial_le
#print axioms eval_diploidSelectionGenerator_marginal_branching
#print axioms sum_eval_singleLocusType_eq_one
#print axioms eval_diploidDrift_haploidDiploidModel
#print axioms eval_diploidSelectionGenerator_haploidDiploidModel
#print axioms expectedDiploidSelection
#print axioms abs_expectedDiploidSelection_le
#print axioms expectedDiploidSelectedGenerator_eq
#print axioms norm_expectedMomentVector_sub_propagator_le_diploid
#print axioms DiploidSelectedOnHistory
#print axioms diploidSelectedOnHistory_nil
#print axioms norm_diploidHistory_sub_propagator_le
#print axioms abs_diploidPortability_sub_neutral_le
