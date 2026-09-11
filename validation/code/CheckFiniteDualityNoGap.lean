/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteDualityNoGap

/-! Axiom audit of FiniteDualityNoGap. -/

open Descent.Portability.FiniteDualityNoGap

#print axioms le_dual_at_law
#print axioms le_dualValue
#print axioms pointVector_mem_stdSimplex
#print axioms pairing_pointVector
#print axioms sum_pointVector
#print axioms sum_option_option
#print axioms continuous_dualityCoords
#print axioms convex_dualityImage
#print axioms isCompact_dualityImage
#print axioms target_not_mem_dualityImage
#print axioms exists_dual_certificate_near
#print axioms isGLB_dualValue
#print axioms isGLB_dualValue_reportRegion
#print axioms neg_sum_abs_le_pairing
#print axioms abs_potential_le
#print axioms continuous_dualExpr
#print axioms continuous_dualValueProd
#print axioms isClosed_boundedDualSet
#print axioms isCompact_boundedDualSet
#print axioms exists_optimal_dual_certificate
#print axioms slater_witness
