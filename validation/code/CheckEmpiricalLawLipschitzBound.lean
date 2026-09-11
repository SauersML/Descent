/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalLawLipschitzBound

/-! Axiom audit of EmpiricalLawLipschitzBound. -/

open Descent.Portability.EmpiricalLawLipschitzBound

#print axioms expectation_indicator_affine
#print axioms singletonMetric_sq
#print axioms expectation_centeredIndicator
#print axioms expectation_sq_centeredIndicator
#print axioms empiricalMass_sub_eq_sum
#print axioms expectation_sq_deviation
#print axioms expectation_abs_deviation_le
#print axioms expectation_deviation_sum_le
#print axioms lipschitzInL1_coordinate
#print axioms abs_expectation_le_expectation_abs
#print axioms abs_expectation_functional_sub_le
#print axioms abs_mixed_expectation_functional_sub_le
