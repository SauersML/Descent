/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.LinearFundamentalMatrix

/-! Axiom audit of the fundamental matrix of a time-varying linear moment system. -/

open Descent.Portability.LinearFundamentalMatrix

#print axioms clampTime
#print axioms clampTime_mem
#print axioms clampTime_of_mem
#print axioms continuous_clampTime
#print axioms norm_identityMatrix_le_one
#print axioms norm_exp_matrix_le
#print axioms picardIterate
#print axioms continuous_picardIterate
#print axioms norm_picardIterate_le
#print axioms norm_picardIterate_le_majorant
#print axioms fundamentalMatrix
#print axioms summable_picardIterate
#print axioms continuous_fundamentalMatrix
#print axioms fundamentalMatrix_zero
#print axioms fundamentalMatrix_eq_integral
#print axioms fundamentalMatrix_hasDerivWithinAt
#print axioms norm_fundamentalMatrix_le
