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
#print axioms occupiedCount_flipCoord_true
#print axioms occupiedCount_flipCoord_false
#print axioms occupiedCount_flipPair
#print axioms nearestDriftKernel_count
#print axioms pathExp_nearestDriftKernel
#print axioms nearestDrift_pathExp_le_synchronous
#print axioms max_sub_add_min
#print axioms min_add_max_sub
#print axioms count_ne_zero_of_true
#print axioms countCompl_ne_zero_of_false
#print axioms count_mul_pairProb
#print axioms countCompl_mul_pairProb
#print axioms flip_indicator_single
#print axioms nearestDriftKernel_flip
