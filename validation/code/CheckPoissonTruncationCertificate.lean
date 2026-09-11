/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PoissonTruncationCertificate

/-! Axiom audit of PoissonTruncationCertificate. -/

open Descent.Portability.PoissonTruncationCertificate

#print axioms matrixExponential_smul_matrix
#print axioms matrixExponential_eq_poissonMixture
#print axioms partialSum_apply
#print axioms expSeries_entry_summable
#print axioms exponential_apply_tsum
#print axioms rowSum_expSeries_term
#print axioms scaled_uniformization_nonneg
#print axioms poissonTruncation_nonneg
#print axioms poissonTruncation_le_exponential
#print axioms rowSum_deficit_le
