/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMetricCompilation

/-! Axiom audit of PortabilityMetricCompilation. -/

open Descent.Portability.PortabilityMetricCompilation

#print axioms scoreVariance_momentsOf
#print axioms outcomeVariance_momentsOf
#print axioms scoreOutcomeCovariance_momentsOf
#print axioms squaredCorrelation_eq_compiled
#print axioms calibrationSlope_eq_compiled
#print axioms compiledPortabilityRatio_eq_portabilityRatio
#print axioms continuous_scoreVariance
#print axioms continuous_outcomeVariance
#print axioms continuous_scoreOutcomeCovariance
#print axioms isOpen_definedRegion
#print axioms continuousOn_compiledSquaredCorrelation
#print axioms continuousOn_compiledSlope
#print axioms continuousOn_compiledPortabilityRatio
#print axioms abs_div_sub_div_le
#print axioms abs_guardedRatio_sub_le
#print axioms abs_correlationNumerator_le_denominator
#print axioms momentDistance_eq
#print axioms abs_scoreOutcomeCovariance_le_one
#print axioms scoreVariance_le_one
#print axioms outcomeVariance_le_one
#print axioms abs_scoreVariance_sub_le
#print axioms abs_outcomeVariance_sub_le
#print axioms abs_scoreOutcomeCovariance_sub_le
#print axioms abs_compiledSlope_sub_le
#print axioms compiledSquaredCorrelation_nonneg
#print axioms compiledSquaredCorrelation_le_inv_sq
#print axioms abs_compiledSquaredCorrelation_sub_le
#print axioms abs_compiledPortabilityRatio_sub_le
#print axioms momentDistance_readout_le
#print axioms convex_readoutCube
#print axioms readout_mem_cube_of_mem_realizationBody
#print axioms abs_compiledSquaredCorrelation_readout_sub_le
#print axioms abs_compiledSlope_readout_sub_le
#print axioms abs_dotProduct_le
#print axioms abs_dotProduct_sub_le
#print axioms convex_box
#print axioms abs_apply_le_of_mem_realizationBody
#print axioms crossRatio_eq_portabilityRatio
#print axioms abs_crossRatio_sub_le
