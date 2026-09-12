/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralSamplingLimit

/-! Axiom audit of AncestralSamplingLimit. -/

open Descent.Portability.AncestralSamplingLimit

#print axioms Descent.Portability.AncestralSamplingLimit.hasDerivAt_eval_line
#print axioms Descent.Portability.AncestralSamplingLimit.lineDeriv_eval
#print axioms Descent.Portability.AncestralSamplingLimit.firstPartial_eval
#print axioms Descent.Portability.AncestralSamplingLimit.secondPartial_eval
#print axioms Descent.Portability.AncestralSamplingLimit.edgeRate
#print axioms Descent.Portability.AncestralSamplingLimit.forwardGenerator_eq_samplingDuality
#print axioms Descent.Portability.AncestralSamplingLimit.samplingPolynomial
#print axioms Descent.Portability.AncestralSamplingLimit.eval_samplingPolynomial
#print axioms
  Descent.Portability.AncestralSamplingLimit.tendsto_nextGenerationMean_samplingPolynomial
