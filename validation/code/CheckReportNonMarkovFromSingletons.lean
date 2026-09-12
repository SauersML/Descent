/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ReportNonMarkovFromSingletons

/-! Axiom audit of ReportNonMarkovFromSingletons. -/

open Descent.Pangenome.GraphCoalescent.ReportNonMarkovFromSingletons

#print axioms chainLaw_succ_apply
#print axioms reportLaw_zero
#print axioms isReportMarkovFromBot_of_injective
#print axioms isReportMarkovFromBot_id
#print axioms reportLaw_one_ne_zero
#print axioms reportLaw_replicate_eq_zero
#print axioms not_isReportMarkovFromBot
#print axioms example_width
#print axioms example_eq_of_covers_observed
#print axioms example_reportLaw_one
#print axioms example_reportLaw_two
#print axioms example_stay_given_one
#print axioms example_stay_given_two
#print axioms example_not_isReportMarkovFromBot
