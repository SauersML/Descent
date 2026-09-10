/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityRatioGeometry

/-! Audit of covariance cancellation and derived ratio-integrability conditions. -/

open Descent.Portability.PortabilityRatioGeometry

#print axioms crossForm_eq_dot
#print axioms crossForm_aligned
#print axioms formRatio_some_domain
#print axioms formRatio_aligned_value
#print axioms formRatio_aligned_le
#print axioms varianceForm_nonneg
#print axioms trait_domination_iff
#print axioms AlignmentCertificate.bound_nonneg
#print axioms AlignmentCertificate.ratio_le_bound
#print axioms outcomeBound_nonneg
#print axioms report_le_outcomeBound
#print axioms certified_innerValue_integrable
#print axioms certified_extendedNumerator_finite
#print axioms certified_expected_ratio
#print axioms binReport_le_sum
#print axioms binInner_le_sum
#print axioms certified_bin_integrable
#print axioms certified_bin_extended_finite
#print axioms certified_bin_expectation
