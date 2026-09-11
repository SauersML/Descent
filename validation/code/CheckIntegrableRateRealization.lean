/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntegrableRateRealization

/-! Axiom audit of IntegrableRateRealization. -/

open Descent.Portability.IntegrableRateRealization

#print axioms floorRates
#print axioms positivePartRates_eq_floorRates
#print axioms norm_rateCoordinates_floorRates_sub_le
#print axioms continuous_rateCoordinates_floorRates
#print axioms continuous_augmentedLowOrderLDGenerator
#print axioms intervalIntegrable_augmentedLowOrderLDGenerator
#print axioms exists_continuous_rates_integral_norm_sub_le
#print axioms eq_of_integral_eq
#print axioms exists_integral_solution_of_continuous_approximation
#print axioms integrableRateHistory_preserves_locusExchangeable_realization
