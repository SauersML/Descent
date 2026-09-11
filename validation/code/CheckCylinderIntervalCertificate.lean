/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderIntervalCertificate

/-! Axiom audit of CylinderIntervalCertificate. -/

open Descent.Portability.CylinderIntervalCertificate

#print axioms fairBit_singleton
#print axioms length_prefixOf
#print axioms getD_prefixOf
#print axioms take_prefixOf
#print axioms measurableSet_cylinder
#print axioms mem_cylinder_iff
#print axioms mem_cylinder_prefixOf
#print axioms mem_cylinder_iff_prefixOf_eq
#print axioms cylinder_prefixOf_subset
#print axioms bitMeasure_cylinder
#print axioms bitMeasure_real_cylinder
#print axioms mem_wordsOfLength
#print axioms prefix_eq_sum_indicator
#print axioms measurable_prefix
#print axioms integral_prefix
#print axioms CylinderEvaluator.lowerEvaluation_le
#print axioms CylinderEvaluator.le_upperEvaluation
#print axioms CylinderEvaluator.lowerEvaluation_le_succ
#print axioms CylinderEvaluator.upperEvaluation_succ_le
#print axioms CylinderEvaluator.monotone_lowerEvaluation
#print axioms CylinderEvaluator.antitone_upperEvaluation
#print axioms CylinderEvaluator.abs_evaluations_le
#print axioms CylinderEvaluator.tendsto_evaluations_ae
#print axioms CylinderEvaluator.integrable_lowerEvaluation
#print axioms CylinderEvaluator.integrable_upperEvaluation
#print axioms CylinderEvaluator.integrable_integrand
#print axioms CylinderEvaluator.tendsto_integral_lowerEvaluation
#print axioms CylinderEvaluator.tendsto_integral_upperEvaluation
#print axioms CylinderEvaluator.lowerSum_cast
#print axioms CylinderEvaluator.upperSum_cast
#print axioms CylinderEvaluator.lowerSum_le_succ
#print axioms CylinderEvaluator.upperSum_succ_le
#print axioms CylinderEvaluator.monotone_lowerSum
#print axioms CylinderEvaluator.antitone_upperSum
#print axioms CylinderEvaluator.tendsto_lowerSum
#print axioms CylinderEvaluator.tendsto_upperSum
#print axioms CylinderEvaluator.lowerSum_le_integral
#print axioms CylinderEvaluator.integral_le_upperSum
#print axioms CylinderEvaluator.tendsto_upperSum_sub_lowerSum
#print axioms CylinderEvaluator.toIntervalEvaluator
#print axioms CylinderEvaluator.integral_toIntervalEvaluator_lower
#print axioms ae_exists_true
#print axioms hasTrueBit_eq_one
#print axioms hasTrueBit_mem_unitInterval
#print axioms hasTrueBitEvaluator
#print axioms coupled_ratio_bracket
#print axioms integral_add_of_split
#print axioms conditionalMean_mem_coupledBracket
#print axioms tendsto_coupledBracket
