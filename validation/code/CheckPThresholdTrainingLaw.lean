/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PThresholdTrainingLaw

/-!
Kernel axiom audit for ordered threshold selection, score cleanup and the finite learner.
-/

#print axioms Descent.Portability.PThresholdTrainingLaw.scan_append
#print axioms Descent.Portability.PThresholdTrainingLaw.advance_tie_keeps_first
#print axioms Descent.Portability.PThresholdTrainingLaw.scan_mem
#print axioms Descent.Portability.PThresholdTrainingLaw.select_mem
#print axioms Descent.Portability.PThresholdTrainingLaw.scan_some
#print axioms Descent.Portability.PThresholdTrainingLaw.select_none_iff
#print axioms Descent.Portability.PThresholdTrainingLaw.scan_keeps_maximum
#print axioms Descent.Portability.PThresholdTrainingLaw.select_first_maximum
#print axioms Descent.Portability.PThresholdTrainingLaw.scan_quality_ge_incumbent
#print axioms Descent.Portability.PThresholdTrainingLaw.scan_quality_ge_member
#print axioms Descent.Portability.PThresholdTrainingLaw.select_quality_maximal
#print axioms Descent.Portability.PThresholdTrainingLaw.comparison_bounds
#print axioms Descent.Portability.PThresholdTrainingLaw.comparison_affine_positive
#print axioms Descent.Portability.PThresholdTrainingLaw.binaryAUC_affine_positive
#print axioms Descent.Portability.PThresholdTrainingLaw.oriented_auc_lower_bound
#print axioms Descent.Portability.PThresholdTrainingLaw.evaluate_spec
#print axioms Descent.Portability.PThresholdTrainingLaw.chooseThreshold_valid
#print axioms Descent.Portability.PThresholdTrainingLaw.chooseThreshold_maximal
#print axioms Descent.Portability.PThresholdTrainingLaw.sign_ne_zero
#print axioms Descent.Portability.PThresholdTrainingLaw.cleanedScore_eq_affine
#print axioms Descent.Portability.PThresholdTrainingLaw.cleanedScore_nonfinite_zero
#print axioms Descent.Portability.PThresholdTrainingLaw.learnScore_of_selected
#print axioms Descent.Portability.PThresholdTrainingLaw.learnScore_insufficient_clumps
#print axioms Descent.Portability.PThresholdTrainingLaw.sign_nonfinite_fit
#print axioms Descent.Portability.PThresholdTrainingLaw.flipSign_iff_negative_correlation
#print axioms Descent.Portability.PThresholdTrainingLaw.cleanedScore_squaredCorrelation
#print axioms Descent.Portability.PThresholdTrainingLaw.candidatesFromTable_mem
#print axioms Descent.Portability.PThresholdTrainingLaw.chosen_from_table
#print axioms Descent.Portability.PThresholdTrainingLaw.linearScore_rowSelectors
#print axioms Descent.Portability.PThresholdTrainingLaw.selected_score_behavior
#print axioms Descent.Portability.PThresholdTrainingLaw.linearScoreFiles_values
#print axioms Descent.Portability.PThresholdTrainingLaw.evaluate
#print axioms Descent.Portability.PThresholdTrainingLaw.learnScore
#print axioms Descent.Portability.PThresholdTrainingLaw.learnerFromTables
