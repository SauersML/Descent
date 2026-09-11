/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntervalEvaluatorCertificate

/-! Axiom audit of IntervalEvaluatorCertificate. -/

open Descent.Portability.IntervalEvaluatorCertificate

#print axioms slack_pos
#print axioms slack_le_one
#print axioms tendsto_slack
#print axioms integrable_of_abs_le_const
#print axioms IntervalEvaluator.integrable_lower
#print axioms IntervalEvaluator.integrable_upper
#print axioms IntervalEvaluator.integrable_integrand
#print axioms IntervalEvaluator.integral_lower_le
#print axioms IntervalEvaluator.integral_le_upper
#print axioms IntervalEvaluator.tendsto_lower
#print axioms IntervalEvaluator.tendsto_upper
#print axioms IntervalEvaluator.tendsto_integral_lower
#print axioms IntervalEvaluator.tendsto_integral_upper
#print axioms bracketed_ratio_bounds
#print axioms conditionalMean_bracket
#print axioms prefixFree_singleton_nil
#print axioms dyadic_sum_le_one_of_subset_nil
#print axioms dyadic_sum_le_one_of_length_le
#print axioms kraft_sum_le_one
#print axioms haltingSublaw_missingMass
