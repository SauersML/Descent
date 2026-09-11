/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.JointMetricMomentDeterminacy

/-! Axiom audit of JointMetricMomentDeterminacy. -/

open Descent.Portability.JointMetricMomentDeterminacy

#print axioms integrable_continuousReadout
#print axioms abs_integral_sub_le_norm_mul_mass
#print axioms integral_eq_of_mem_span
#print axioms measure_eq_of_separating_subalgebra
#print axioms cubeMonomial_apply
#print axioms cubeMonomial_zero
#print axioms cubeMonomial_add
#print axioms cubeMonomial_single
#print axioms cubeAlgebra_toSubmodule
#print axioms cubeAlgebra_separatesPoints
#print axioms measure_eq_of_cube_moments_eq
#print axioms measurable_metricVector
#print axioms measurableSet_definedDomain
#print axioms measurableSet_maskEvent
#print axioms integral_cubeMonomial_map
#print axioms integral_multiIndexRatio_eq_moment
#print axioms measurable_multiIndexNumerator
#print axioms measurable_multiIndexDenominator
#print axioms moment_eq_tsum_expansion
#print axioms conditional_map_eq_of_restricted_map_eq
#print axioms jointMetricLaw_eq_of_expansion_eq
#print axioms definedDomain_subfamilyDenominator
#print axioms subfamily_moment_eq_tsum
#print axioms maskStatistic_definedIndicators
#print axioms prod_definedIndicators
#print axioms masked_moment_expansion
#print axioms maskProbability_expansion
#print axioms masked_moment_eq_zero
#print axioms maskMetricLaw_eq_of_masked_moments_eq
#print axioms maskMetricLaw_eq_of_subfamily_moments_eq
