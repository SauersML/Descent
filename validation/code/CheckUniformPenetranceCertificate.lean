/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniformPenetranceCertificate

/-! Axiom audit of UniformPenetranceCertificate. -/

open Descent.Portability.UniformPenetranceCertificate

#print axioms wordDraw_nonneg
#print axioms wordDraw_add_le_one
#print axioms wordDraw_cons
#print axioms wordDraw_cons_false
#print axioms wordDraw_cons_true
#print axioms wordsOfLength_zero
#print axioms wordsOfLength_succ
#print axioms sum_wordsOfLength_succ
#print axioms sum_wordsOfLength_wordDraw
#print axioms draw_bracket
#print axioms metricEvaluator
#print axioms lowerSum_metricEvaluator
#print axioms upperSum_metricEvaluator
#print axioms integral_unit_eq_sum_dyadic
#print axioms integral_dyadic_bracket
#print axioms riemannSums_bracket_integral
#print axioms riemannSums_gap
#print axioms tendsto_riemannSums
#print axioms metricEvaluator_certificate
#print axioms squaredCorrelationFormula_eq_thetaReport
#print axioms cast_squaredCorrelationFormula
#print axioms cast_aucFormula
#print axioms squaredCorrelationFormula_increase
#print axioms aucFormula_increase
#print axioms squaredCorrelationEvaluator
#print axioms aucEvaluator
#print axioms squaredCorrelation_certificate
#print axioms tendsto_squaredCorrelation_certificate
#print axioms auc_certificate
#print axioms tendsto_auc_certificate
#print axioms uniformDraw_pos
#print axioms uniformDraw_le_one
#print axioms integral_squaredCorrelation_penetranceLaw_uniformDraw
#print axioms integral_binaryAUC_penetranceLaw_uniformDraw
