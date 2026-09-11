/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderThresholdCertificate

/-! Axiom audit of CylinderThresholdCertificate. -/

open Descent.Portability.CylinderThresholdCertificate

#print axioms measurableSet_prefix
#print axioms bitMeasure_real_prefix
#print axioms cast_lowerValue
#print axioms cast_upperValue
#print axioms resolvedMass_cast
#print axioms unresolvedMass_cast
#print axioms resolvedMass_le_and_le_add
#print axioms resolvedMass_add_unresolvedMass_cast
#print axioms resolvedMass_le_succ
#print axioms resolvedMass_add_unresolvedMass_succ_le
#print axioms unresolvedMass_integral
#print axioms tendsto_unresolvedMass
#print axioms tendsto_resolvedMass
#print axioms tieEvaluator
#print axioms unresolvedMass_tieEvaluator
#print axioms resolvedMass_tieEvaluator
#print axioms bitMeasure_singleton
#print axioms discretization_event_gap
#print axioms measurable_roundToResolution
#print axioms roundToResolution_mem_cylinder_iff
#print axioms roundedLaw_cylinder
#print axioms countable_range_roundToResolution
#print axioms roundedLaw_range_gap
