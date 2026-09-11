/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialJetCertificate

/-! Axiom audit of MultinomialJetCertificate. -/

open Descent.Portability.MultinomialJetCertificate

namespace Descent.Portability.MultinomialJetCertificate

#print axioms coefficientMass
#print axioms coefficientMass_nonneg
#print axioms coefficientMass_eq_sum_of_subset
#print axioms coefficientMass_add_le
#print axioms coefficientMass_smul
#print axioms coefficientMass_monomial
#print axioms coefficientMass_sum_le
#print axioms coefficientMass_mul_le
#print axioms totalStirlingWeight_eq_prod
#print axioms totalStirlingWeight_le
#print axioms sum_coeff_remainder_le
#print axioms JetPolynomialCertificate
#print axioms JetPolynomialCertificate.const
#print axioms JetPolynomialCertificate.add
#print axioms JetPolynomialCertificate.eval_smul
#print axioms JetPolynomialCertificate.smul

end Descent.Portability.MultinomialJetCertificate
