/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ConditionalErrorCertificate

/-! Axiom audit of finite numerical and conditioning certificates. -/

open Descent.Portability.ConditionalErrorCertificate

#print axioms eventMass
#print axioms eventMass_nonneg
#print axioms eventMass_le_one
#print axioms condition
#print axioms totalVariation_overlap
#print axioms conditional_totalVariation
#print axioms conditional_mean_interval
#print axioms sharpSource
#print axioms sharpTarget
#print axioms sharpSource_acceptance
#print axioms sharpTarget_acceptance
#print axioms sharp_amplification
