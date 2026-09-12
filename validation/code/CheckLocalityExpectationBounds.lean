/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.LocalityExpectationBounds

/-! Axiom audit of the expectation and escape bounds of the genomic light cone. -/

open Descent.Pangenome.AncestralLocality

#print axioms Descent.Pangenome.AncestralLocality.DriftExpectation.mean_le
#print axioms Descent.Pangenome.AncestralLocality.supportMean_le
#print axioms Descent.Pangenome.AncestralLocality.BranchingExpectation.branchingMean_le
#print axioms Descent.Pangenome.AncestralLocality.sum_law_mul_le_of_generator_le
#print axioms Descent.Pangenome.AncestralLocality.sum_law_mul_supportGenerator_le
#print axioms Descent.Pangenome.AncestralLocality.sum_law_mul_supportGenerator_lightWeight_le
#print axioms Descent.Pangenome.AncestralLocality.sum_law_mul_decisionRate_le
#print axioms Descent.Pangenome.AncestralLocality.sum_filter_weight_le_div
#print axioms Descent.Pangenome.AncestralLocality.escapeProbability_le_min
#print axioms Descent.Pangenome.AncestralLocality.exp_div_pow_at_lightConeBase
#print axioms Descent.Pangenome.AncestralLocality.escapeProbability_le_lightCone
#print axioms Descent.Pangenome.AncestralLocality.escapeProbability_eq_zero_of_mul_eq_zero
#print axioms Descent.Pangenome.AncestralLocality.totalVariation_le_lightCone
