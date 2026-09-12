/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralWitnessDrift

/-! Axiom audit of the witness drifts (5.5) as time derivatives. -/

open Descent.Portability.AncestralWitnessDrift

#print axioms observedProductPolynomial
#print axioms eval_observedProductPolynomial
#print axioms eval_pderiv_observedProductPolynomial
#print axioms resamplingOperator_observedProductPolynomial
#print axioms forwardGenerator_observedProductPolynomial
#print axioms witness_generator
#print axioms witnessLawP
#print axioms witnessLawQ
#print axioms tendsto_witnessP_nextGenerationMean
#print axioms tendsto_witnessQ_nextGenerationMean
