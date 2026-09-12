/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.DecisionDualProcess

/-! Axiom audit of DecisionDualProcess. -/

open Descent.Pangenome.AncestralLocality

#print axioms norm_decisionSubstitution_le
#print axioms holdingSemigroup_neg_mul
#print axioms hasDerivAt_holdingSemigroup_apply
#print axioms norm_holdingSemigroup_apply_le
#print axioms abs_samplingObservable_le
#print axioms continuous_dysonMoment_apply
#print axioms hasDerivAt_dysonMoment_succ
#print axioms dysonMoment_succ_eq_integral
#print axioms sum_range_yuleWeight_le_one
#print axioms mul_one_sub_sum_range_yuleWeight_le
#print axioms tsum_yuleWeight_eq_one
#print axioms abs_dysonMoment_le
#print axioms tendsto_truncatedDual
#print axioms abs_decisionDual_le
#print axioms abs_decisionDual_sub_truncatedDual_le_exp
#print axioms decisionDual_zero_time
#print axioms hasDerivAt_truncatedDual
#print axioms decisionDual_sub_eq_integral
#print axioms continuousOn_decisionDual
#print axioms hasDerivAt_decisionDual
#print axioms decisionDual_add
#print axioms decisionDual_smul
#print axioms decisionDual_holdingGenerator_add
#print axioms decisionDual_moment_equation
#print axioms hasDerivAt_decisionDual_moment_equation
#print axioms continuousOn_decisionDual_Ici
#print axioms hasDerivWithinAt_decisionDual_moment_equation
#print axioms decisionDualMap_apply
#print axioms decisionDualMap_zero_time
#print axioms abs_decisionDualMap_le
#print axioms hasDerivWithinAt_decisionDualMap
