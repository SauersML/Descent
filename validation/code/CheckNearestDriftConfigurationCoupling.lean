/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NearestDriftConfigurationCoupling

/-! Axiom audit of NearestDriftConfigurationCoupling. -/

open Descent.Portability.NearestDriftConfigurationCoupling

#print axioms max_eq_min_add_parts
#print axioms upRate_eq_excess
#print axioms downRate_eq_excess
#print axioms oneRateTotal_nonneg
#print axioms zeroRateTotal_nonneg
#print axioms count_mul_singleOneProb
#print axioms countCompl_mul_singleZeroProb
#print axioms pairs_mul_pairProb
#print axioms sum_dirac
#print axioms nearestDriftKernel_apply
#print axioms nearestDriftKernel_sum
#print axioms nearestDriftKernel_nonneg
