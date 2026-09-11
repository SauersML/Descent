/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RateGeneratorLipschitz

/-! Axiom audit of RateGeneratorLipschitz. -/

open Descent.Portability.RateGeneratorLipschitz

#print axioms addRates
#print axioms scaleRates
#print axioms rates_eq_of_coordinates
#print axioms augmentedLowOrderLDGenerator_addRates
#print axioms generator_sub_eq_of_addRates_eq
#print axioms augmentedLowOrderLDGenerator_scaleRates
#print axioms rateCoordinates
#print axioms positivePartRates
#print axioms addRates_positivePartRates_add
#print axioms addRates_positivePartRates_smul
#print axioms addRates_positivePartRates_neg_rateCoordinates
#print axioms signedGenerator
#print axioms signedGenerator_add
#print axioms signedGenerator_neg
#print axioms signedGenerator_smul
#print axioms generatorLinearMap
#print axioms augmentedLowOrderLDGenerator_eq_generatorLinearMap
#print axioms exists_generator_lipschitz
