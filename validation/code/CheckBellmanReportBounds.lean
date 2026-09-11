/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BellmanReportBounds

/-! Axiom audit of BellmanReportBounds. -/

open Descent.Portability.BellmanReportBounds

#print axioms expectation_mono
#print axioms abs_expectation_sub_le
#print axioms abs_inf'_sub_le
#print axioms abs_sup'_sub_le
#print axioms lowerValue_succ
#print axioms upperValue_succ
#print axioms policyValue_succ_eq_bind
#print axioms lowerValue_le_policyValue
#print axioms policyValue_le_upperValue
#print axioms policyValue_eq_of_step
#print axioms lowerPolicy_attains
#print axioms upperPolicy_attains
#print axioms policyValue_lowerPolicy
#print axioms policyValue_upperPolicy
#print axioms exists_lower_optimal_policy
#print axioms exists_upper_optimal_policy
#print axioms lowerValue_mem_range
#print axioms abs_lowerStep_sub_le
#print axioms abs_upperStep_sub_le
#print axioms abs_approx_sub_lowerValue_le
#print axioms accumulated_defect_eq
