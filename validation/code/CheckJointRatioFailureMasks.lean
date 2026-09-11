/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.JointRatioFailureMasks

/-! Axiom audit of JointRatioFailureMasks. -/

open Descent.Portability.JointRatioFailureMasks

#print axioms jointNumerator_ratio
#print axioms jointDenominator_nonneg
#print axioms jointDenominator_le_one
#print axioms jointNumerator_nonneg
#print axioms jointNumerator_le_jointDenominator
#print axioms multiIndexNumerator_ratio
#print axioms multiIndexNumerator_nonneg
#print axioms multiIndexDenominator_le_one
#print axioms multiIndexNumerator_le_multiIndexDenominator
#print axioms maskStatistic_eq_one
#print axioms maskStatistic_eq_zero_of_mem
#print axioms maskStatistic_eq_zero_of_not_mem
#print axioms prod_mask_expansion
#print axioms expectation_mask_expansion
