/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.KilledSurvivalMean

/-! Axiom audit of the mean connection time as the integral of the killed survival function. -/

open Descent.Pangenome.GraphCoalescent.KilledSurvivalMean

#print axioms pow_apply_nonneg
#print axioms exp_smul_one_apply
#print axioms exp_smul_apply_nonneg
#print axioms loadGenerator_eq_zero_of_not_pos
#print axioms pow_loadGenerator_eq_zero_of_not_pos
#print axioms exp_smul_loadGenerator_eq_zero_of_not_pos
#print axioms loadGenerator_nonneg_of_ne
#print axioms gridSurvival_nonneg
#print axioms hasDerivAt_gridSurvival_forward
#print axioms gridSurvival_le_exp_neg
#print axioms tendsto_gridSurvival_atTop
#print axioms continuous_gridSurvival
#print axioms integrableOn_gridSurvival
#print axioms sum_loadGenerator_mul_integral
#print axioms loadMean
#print axioms loadMean_one_one
#print axioms loadMean_two_one
#print axioms integral_gridSurvival_eq_loadMean_aux
#print axioms integral_gridSurvival_eq_loadMean
#print axioms integral_survival_eq_loadMean
#print axioms sum_loadGenerator_mul_loadMean
#print axioms integral_survival_two_one
#print axioms integral_survival_two_one_eq_integral_exampleSurvival
#print axioms three_clocks_differ_survival
