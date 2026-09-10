/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DistanceBinnedPortabilityLaw

/-! Axiom audit of joint acceptance, distance averaging, and expectation limits. -/

open Descent.Portability.DistanceBinnedPortabilityLaw

#print axioms target_labelKernel
#print axioms allValid_measurable
#print axioms clippedBinReport_defined
#print axioms clippedBinReport_bounds
#print axioms clippedBinReport_measurable
#print axioms binReport_defined_measurable
#print axioms clipped_bin_expectation
#print axioms binReport_nonneg
#print axioms binReport_measurable
#print axioms binInner_eq_iSup_clipped
#print axioms binExtendedNumerator_eq_iSup
#print axioms binInner_integrable_iff
#print axioms finite_bin_expectation
