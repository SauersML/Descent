/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralIntegrableRateRealization

/-! Axiom audit of NeutralIntegrableRateRealization. -/

open Descent.Portability.NeutralIntegrableRateRealization

namespace Descent.Portability.NeutralIntegrableRateRealization

#print axioms continuous_coordinates_positivePartNeutralRates
#print axioms norm_coordinates_positivePartNeutralRates_sub_le
#print axioms exists_continuous_neutralRates_near
#print axioms dualGenerator_comp_eq_linearMap
#print axioms continuousOn_dualGenerator_of_continuous
#print axioms intervalIntegrable_dualGenerator
#print axioms exists_neutralIntegrablePropagator
#print axioms neutralIntegrablePropagator_mulVec_mem_realizationBody
#print axioms exists_neutralIntegrableLaw

end Descent.Portability.NeutralIntegrableRateRealization
