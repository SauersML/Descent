/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoTimeRatePropagator

/-! Axiom audit of TwoTimeRatePropagator. -/

open Descent.Portability.TwoTimeRatePropagator

#print axioms transposeMap
#print axioms mulLeftMap
#print axioms eq_of_hasDerivWithinAt_zero
#print axioms continuous_neg_transpose
#print axioms adjointFundamentalMatrix
#print axioms adjointFundamentalMatrix_zero
#print axioms continuous_adjointFundamentalMatrix
#print axioms hasDerivWithinAt_adjointFundamentalMatrix
#print axioms adjointFundamentalMatrix_mul_fundamentalMatrix
#print axioms fundamentalMatrix_mul_adjointFundamentalMatrix
#print axioms twoTimePropagator
#print axioms twoTimePropagator_self
#print axioms twoTimePropagator_mul
#print axioms twoTimePropagator_zero_right
#print axioms hasDerivWithinAt_twoTimePropagator_left
#print axioms hasDerivWithinAt_twoTimePropagator_right
#print axioms hasDerivWithinAt_toBlocks₂₁_fundamentalMatrix_blockPath
#print axioms toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral_twoTimePropagator
#print axioms hasDerivAt_twoTimePropagator_affinePath
#print axioms twoTimePropagator_rateHistory
#print axioms ratePathSensitivity_eq_integral
