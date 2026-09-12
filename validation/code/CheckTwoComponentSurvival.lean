/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent
import Descent.Pangenome.GraphCoalescent.TwoComponentSurvival

/-! Axiom audit of TwoComponentSurvival, imported beside the GraphCoalescent head. -/

open Descent.Pangenome.GraphCoalescent.TwoComponentSurvival

#print axioms sum_loadGenerator_mul
#print axioms sum_loadGenerator
#print axioms sum_loadGenerator_sq
#print axioms exp_add_smul_loadGenerator
#print axioms gridSurvival_zero
#print axioms gridSurvival_add
#print axioms survival_add
#print axioms hasDerivAt_sum_mul_exp_smul
#print axioms hasDerivAt_gridSurvival
#print axioms hasDerivAt_gridSurvival_eq_generator
#print axioms hasDerivAt_deriv_gridSurvival
#print axioms hasDerivAt_survival_generator_one
#print axioms hasDerivAt_deriv_survival_generator_twice
#print axioms hasDerivAt_survival_zero
#print axioms hasDerivAt_deriv_survival_zero
#print axioms deriv_survival_zero
#print axioms deriv_deriv_survival_zero
#print axioms unorderedPair_of_survival_eq
#print axioms loadGenerator_swap
#print axioms exp_smul_loadGenerator_swap
#print axioms survival_swap
#print axioms survival_eq_iff
