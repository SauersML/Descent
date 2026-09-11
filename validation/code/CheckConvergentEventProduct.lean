/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ConvergentEventProduct

/-! Axiom audit of realizability at the limit of a convergent event product. -/

open Descent.Portability.ConvergentEventProduct

#print axioms InterleavedSegment.matrix
#print axioms InterleavedSegment.apply_eq_mulVec
#print axioms productMatrix
#print axioms foldl_matrix_mulVec
#print axioms productMatrix_mulVec
#print axioms convergentHistory_limit_locusExchangeable_realization
#print axioms convergentOperator_locusExchangeable_realization
#print axioms convergentMatrix_locusExchangeable_realization
#print axioms convergentHistory_limit_dd_quadraticForm_nonneg
#print axioms convergentHistory_limit_dd_cauchySchwarz
#print axioms convergentHistory_limit_dd_diagonal_nonneg
