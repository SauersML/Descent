/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaMeasureCertificate

/-! Axiom audit of ReplicaMeasureCertificate. -/

open Descent.Portability.ReplicaMeasureCertificate

#print axioms measurable_ratioOnDefined
#print axioms integrable_of_unit_bounds
#print axioms integrable_expansion_term
#print axioms integrable_retainedWeight
#print axioms integrable_dampedRatio
#print axioms integrable_unresolvedWeight
#print axioms integral_ratioOnDefined_partition
#print axioms definedProbability_partition
#print axioms retainedNumerator_nonneg
#print axioms retainedNumerator_le_retainedMass
#print axioms unresolvedNumerator_nonneg
#print axioms unresolvedMass_nonneg
#print axioms unresolvedNumerator_le_unresolvedMass
#print axioms unresolvedMass_le_one_sub_retainedMass
#print axioms coupled_residuals
#print axioms conditional_integral_ratioOnDefined
#print axioms measure_replica_certificate
#print axioms measure_certificate_width
#print axioms replica_certificate_min_tolerance
#print axioms tendsto_unresolvedMass
#print axioms certificate_endpoints_tendsto
#print axioms unresolvedMass_le_pow
#print axioms retained_measure_eq
#print axioms unresolvedMass_measure_eq
