/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RationalParameterReports

/-! Axiom audit of RationalParameterReports. -/

open Descent.Portability.RationalParameterReports

#print axioms PolynomialQuotient.eval_ofPolynomial
#print axioms PolynomialQuotient.denominator_ofPolynomial_ne_zero
#print axioms PolynomialQuotient.eval_mul
#print axioms PolynomialQuotient.denominator_mul_ne_zero
#print axioms PolynomialQuotient.eval_div
#print axioms PolynomialQuotient.denominator_div_ne_zero
#print axioms PolynomialQuotient.denominator_sum_ne_zero
#print axioms PolynomialQuotient.eval_sum
#print axioms mem_signCell_signPattern
#print axioms disjoint_signCell
#print axioms iUnion_signCell
#print axioms finite_range_signCell
#print axioms ParametricTree.traceWeight_eq_eval_weightQuotient
#print axioms ParametricTree.denominator_weightQuotient_ne_zero
#print axioms ParametricTree.denominator_accumulationQuotient_ne_zero
#print axioms ParametricTree.accumulation_eq_eval_accumulationQuotient
#print axioms ParametricTree.conditionalMean_eq_eval_div
#print axioms ParametricTree.trace_experimentAt
#print axioms ParametricTree.backwardValue_experimentAt
#print axioms ParametricTree.definedMass_experimentAt
#print axioms ParametricTree.weightedDefinedMetric_experimentAt
#print axioms ParametricTree.conditionalMetric_experimentAt_eq_eval
#print axioms attainableRegion_eq_image
#print axioms attainableRegion_eq_iUnion_image_cells
#print axioms eval_indicatorQuotient_true
#print axioms eval_indicatorQuotient_false
#print axioms regularAt_architectureTree
#print axioms validAt_architectureTree
#print axioms accumulation_architectureTree
#print axioms attainableRegion_architectureTree_eq_jointRegion
