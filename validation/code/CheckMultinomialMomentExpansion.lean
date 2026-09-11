/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialMomentExpansion

/-! Axiom audit of MultinomialMomentExpansion. -/

open Descent.Portability.MultinomialMomentExpansion

namespace Descent.Portability.MultinomialMomentExpansion

#print axioms multinomial_mul_prod_descFactorial
#print axioms sum_piAntidiag_prod_descFactorial
#print axioms expectation_prod_descFactorial
#print axioms pow_eq_sum_stirlingSecond_mul_descFactorial
#print axioms expectation_prod_pow
#print axioms cast_descFactorial_succ
#print axioms cast_descFactorial_three
#print axioms cast_descFactorial_four
#print axioms abs_descFactorial_div_pow_sub_le
#print axioms abs_descFactorial_pred_div_pow_sub_le
#print axioms subIndices
#print axioms stirlingWeight
#print axioms totalStirlingWeight
#print axioms firstOrderStirlingSum
#print axioms lowOrderStirlingSum
#print axioms monomialFirstOrder
#print axioms subIndices_le
#print axioms mem_subIndices_self
#print axioms stirlingWeight_nonneg
#print axioms stirlingWeight_self
#print axioms categoryMonomial_nonneg
#print axioms categoryMonomial_le_one
#print axioms firstOrderStirlingSum_nonneg
#print axioms firstOrderStirlingSum_le
#print axioms firstOrderStirlingSum_of_sum_eq_zero
#print axioms lowOrderStirlingSum_nonneg
#print axioms lowOrderStirlingSum_mul_sq_le
#print axioms expectation_monomial_eq
#print axioms sum_subIndices_split
#print axioms abs_expectation_monomial_sub_le
#print axioms firstOrderStirlingSum_eq_sum_choose
#print axioms monomialFirstOrder_eq_sum_choose

end Descent.Portability.MultinomialMomentExpansion
