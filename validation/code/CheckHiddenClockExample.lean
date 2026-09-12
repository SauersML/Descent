/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenClockExample

/-! Axiom audit of HiddenClockExample. -/

open Descent.Pangenome.GraphCoalescent

#print axioms exampleGenerator_eq_rates
#print axioms exp_apply_fin_two
#print axioms exampleEigenvectors_inv
#print axioms isUnit_exampleEigenvectors
#print axioms smul_exampleGenerator_eq_conj
#print axioms exp_smul_exampleGenerator
#print axioms exampleSurvival_eq
#print axioms integral_exampleSurvival
#print axioms neg_exampleGenerator_inv
#print axioms integral_exampleSurvival_eq_phaseType
#print axioms integral_exampleSurvival_eq_mean_connection_time
#print axioms exampleInterface_width
#print axioms example_graphKer_rate
#print axioms example_graphMeanTransitTime
#print axioms example_labeled_meanTransitTime
#print axioms three_clocks_differ
