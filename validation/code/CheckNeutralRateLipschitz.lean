/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralRateLipschitz

/-! Axiom audit of NeutralRateLipschitz. -/

open Descent.Portability.NeutralRateLipschitz

namespace Descent.Portability.NeutralRateLipschitz

#print axioms addNeutralRates
#print axioms scaleNeutralRates
#print axioms sum_map_bind_eq_add
#print axioms sum_map_bind_eq_mul
#print axioms ite_add_zero_eq
#print axioms ite_mul_zero_eq
#print axioms sum_map_migrationMoves_add
#print axioms sum_map_mutationMoves_add
#print axioms sum_map_recombinationMoves_add
#print axioms sum_map_carrierMoves_add
#print axioms sum_map_migrationMoves_scale
#print axioms sum_map_mutationMoves_scale
#print axioms sum_map_recombinationMoves_scale
#print axioms sum_map_carrierMoves_scale
#print axioms sum_map_dualTransitions_add
#print axioms sum_map_dualTransitions_scale
#print axioms jumpRate_eq_sum_map
#print axioms exitRate_eq_sum_map
#print axioms jumpRate_addNeutralRates
#print axioms exitRate_addNeutralRates
#print axioms jumpRate_scaleNeutralRates
#print axioms exitRate_scaleNeutralRates
#print axioms dualGenerator_addNeutralRates
#print axioms dualGenerator_scaleNeutralRates
#print axioms neutralRateCoordinates
#print axioms neutralRates_eq_of_fields
#print axioms symmetrizeMutation
#print axioms symmetrizeMutation_add
#print axioms symmetrizeMutation_neg
#print axioms symmetrizeMutation_smul
#print axioms positivePartNeutralRates
#print axioms addNeutralRates_positivePart_add
#print axioms addNeutralRates_positivePart_smul
#print axioms dualGenerator_sub_eq_of_add_eq
#print axioms signedDualGenerator
#print axioms signedDualGenerator_add
#print axioms signedDualGenerator_neg
#print axioms signedDualGenerator_smul_of_pos
#print axioms signedDualGenerator_smul
#print axioms dualGeneratorLinearMap
#print axioms positivePartNeutralRates_coordinates
#print axioms positivePartNeutralRates_neg_coordinates
#print axioms dualGenerator_eq_dualGeneratorLinearMap
#print axioms exists_dualGenerator_lipschitz

end Descent.Portability.NeutralRateLipschitz
