/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialRemainderEveryDegree

/-! Axiom audit of MultinomialRemainderEveryDegree. -/

open Descent.Portability.MultinomialRemainderEveryDegree

#print axioms descFactorial_div_pow_succ
#print axioms descFactorial_div_pow_bounds
#print axioms abs_descFactorial_div_pow_sub_le_choose_sq
#print axioms abs_descFactorial_pred_div_pow_sub_le_choose
#print axioms abs_expectation_monomial_sub_le_every
#print axioms abs_expectation_eval_sub_le_every
#print axioms sum_stirlingSecond_le_factorial
#print axioms totalStirlingWeight_le_factorial
#print axioms abs_expectation_eval_sub_le_of_totalDegree_le
