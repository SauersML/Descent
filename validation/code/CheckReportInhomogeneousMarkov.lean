/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ReportInhomogeneousMarkov

/-! Axiom audit of ReportInhomogeneousMarkov. -/

open Descent.Pangenome.GraphCoalescent.ReportInhomogeneousMarkov

#print axioms reportLaw_apply
#print axioms reportLaw_succ_apply
#print axioms reportLaw_succ_eq_zero
#print axioms reportLaw_succ_eq_mul
#print axioms isReportInhomogeneousMarkov_of_isReportMarkovFromBot
#print axioms isReportInhomogeneousMarkov_id
#print axioms blocks_eq_of_chainLaw_ne_zero
#print axioms isReportInhomogeneousMarkov_of_blocks
#print axioms reportJumpLaw_eq_of_hiddenState_eq
#print axioms atMostOneHeavy_id
#print axioms atMostOneHeavy_example
#print axioms hiddenLoad_eq_one_of_not_heavy
#print axioms hiddenLoad_heavy
#print axioms hiddenState_eq_of_atMostOneHeavy
#print axioms isReportInhomogeneousMarkov_of_atMostOneHeavy
#print axioms le_of_mem_tail
#print axioms eq_replicate_of_reportLaw_ne_zero
#print axioms reportJumpLaw_eq_pure
#print axioms reportLaw_succ_eq_widthTwoLaw
#print axioms isReportInhomogeneousMarkov_of_width_eq_two
#print axioms example_widthTwoLaw_zero
#print axioms example_widthTwoLaw_one
#print axioms example_isReportInhomogeneousMarkov
