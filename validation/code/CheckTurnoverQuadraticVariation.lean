/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TurnoverQuadraticVariation

/-! Axiom audit of TurnoverQuadraticVariation. -/

open Descent.Portability.TurnoverQuadraticVariation

#print axioms sum_sq_le_sq_sum
#print axioms flipWeight_nonneg
#print axioms flipWeight_le_total
#print axioms flipWeight_sq_le
#print axioms flipWeight_sq_ge
#print axioms sum_kernel_flipWeight
#print axioms kernel_signValue_drift
#print axioms kernel_alignment_drift
#print axioms kernel_alignment_quadratic_variation
#print axioms quadraticVariation_nonneg
#print axioms pathExp_alignment
#print axioms pathExp_mse_invariant
#print axioms pathExp_alignment_sq_ge
#print axioms alignment_diff_allTrue
#print axioms quadraticVariation_le
#print axioms quadraticVariation_ge
