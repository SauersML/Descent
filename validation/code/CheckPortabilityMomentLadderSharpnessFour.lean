/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadderSharpnessFour

/-! Axiom audit of PortabilityMomentLadderSharpnessFour. -/

open Descent.Portability.PortabilityMomentLadderSharpnessFour

#print axioms sum_triallelicHaplotype
#print axioms lineMass_nonneg
#print axioms lineState_apply
#print axioms stateLaw_lineState
#print axioms mass_lineLaw
#print axioms expectations_alleles
#print axioms correlationNumerator_alleles
#print axioms correlationDenominator_alleles
#print axioms correlationNumerator_target
#print axioms correlationDenominator_target
#print axioms correlationNumerator_source
#print axioms correlationDenominator_source
#print axioms integral_firstLaw
#print axioms integral_secondLaw
#print axioms polynomialFunction_lineState
#print axioms natDegree_linePolynomial_le
#print axioms polynomialsAgreeAt_three
#print axioms integrals_firstKernel
#print axioms integrals_secondKernel
#print axioms expectedPortability_firstKernel
#print axioms expectedPortability_secondKernel
#print axioms polynomialsAgreeAt_three_and_expectedPortability_ne
#print axioms portabilityReport_ne
#print axioms not_forall_portabilityReport_eq_of_polynomialsAgreeAt_three
