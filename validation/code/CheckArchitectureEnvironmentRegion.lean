/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchitectureEnvironmentRegion

/-! Axiom audit of ArchitectureEnvironmentRegion. -/

open Descent.Portability.ArchitectureEnvironmentRegion

#print axioms cellWeight_sum
#print axioms cellWeight_nonneg
#print axioms architectureLaw_mass
#print axioms mixtureDenominator_pos
#print axioms cornerWeight_nonneg
#print axioms cornerWeight_sum
#print axioms conditionalMean_eq_corner_combination
#print axioms conditionalMean_le
#print axioms le_conditionalMean
#print axioms conditionalMean_corner
#print axioms cellWeight_det
#print axioms cellWeight_marginals
#print axioms det_zero_iff_eq_cellWeight
#print axioms marginal_mem_unitInterval
#print axioms jointRegion_eq_image
