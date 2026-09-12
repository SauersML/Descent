/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.DecisionDualMoments

/-! Axiom audit of DecisionDualMoments. -/

open Descent.Pangenome.AncestralLocality

#print axioms norm_coalesceArguments_le
#print axioms norm_decisionBranch_le
#print axioms norm_coalescenceGain_le
#print axioms norm_branchingGain_le
#print axioms momentGenerator_samplingFunctional
#print axioms momentGenerator_eq
#print axioms momentGenerator_sub
#print axioms gainSemigroup_zero
#print axioms hasDerivAt_gainSemigroup_apply
#print axioms norm_gainSemigroup_le
#print axioms hasDerivAt_duhamel
#print axioms abs_moment_le_choose_mul_pow
#print axioms moment_eq_zero_of_mul_lt_one
#print axioms moment_eq_zero
#print axioms moments_eq_of_momentEquation
