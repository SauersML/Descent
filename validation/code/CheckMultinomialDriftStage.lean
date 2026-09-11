/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialDriftStage

/-! Axiom audit of MultinomialDriftStage. -/

open Descent.Portability.MultinomialDriftStage

namespace Descent.Portability.MultinomialDriftStage

#print axioms haplotypeDrawLaw
#print axioms censusFrequencies
#print axioms haplotypeCoordinate_censusFrequencies
#print axioms multinomialDriftKernel
#print axioms DegreeFourObservable
#print axioms apply_multinomialDriftKernel_expansion
#print axioms multinomialChromosomeCount
#print axioms one_le_multinomialChromosomeCount
#print axioms one_div_multinomialChromosomeCount_le
#print axioms abs_one_div_multinomialChromosomeCount_sub_le
#print axioms abs_sub_mul_le_of_rounding
#print axioms apply_multinomialDriftStage_expansion
#print axioms pderiv_pderiv_X
#print axioms resamplingOperator_X
#print axioms leftFrequencyObservable

end Descent.Portability.MultinomialDriftStage
