/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ResamplingJetExpansion

/-! Axiom audit of the second-order resampling expansion of the corpus diffusion jets. -/

open Descent.Portability.ResamplingJetExpansion

#print axioms ResamplingExpansion.bound_nonneg
#print axioms ResamplingExpansion.remainder_nonneg
#print axioms abs_mul_le_of_abs_le_of_abs_le
#print axioms abs_add_four_le
#print axioms abs_centeredGradient_le
#print axioms abs_expansionResidual_le_of_eq_zero
#print axioms expansionResidual_eq_zero_of_ne
#print axioms expansionResidual_mul
#print axioms resamplingExpansionConst
#print axioms ResamplingExpansion.add
#print axioms ResamplingExpansion.smul
#print axioms ResamplingExpansion.mul
#print axioms resamplingExpansionLeftFrequencyJet
#print axioms resamplingExpansionRightFrequencyJet
#print axioms resamplingExpansionLinkageJet
#print axioms resamplingExpansionLeftContrastJet
#print axioms resamplingExpansionRightContrastJet
#print axioms resamplingExpansionHJet
#print axioms resamplingExpansionRightHJet
#print axioms resamplingExpansionDDJet
#print axioms resamplingExpansionDzJet
#print axioms resamplingExpansionPi2Jet
#print axioms resamplingExpansionCoordinateJet
#print axioms resampleExpectation_jet_expansion
