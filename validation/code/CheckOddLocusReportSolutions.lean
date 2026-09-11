/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.OddLocusReportSolutions

/-! Axiom audit of OddLocusReportSolutions. -/

open Descent.Portability.OddLocusReportSolutions

#print axioms dexp_zero
#print axioms dexp_succ
#print axioms dexp_lt_succ
#print axioms dexp_one
#print axioms dexp_two
#print axioms oddRow_zero
#print axioms oddRow_succ_of_lt
#print axioms oddRow_succ_self
#print axioms oddShift_mul
#print axioms sum_oddRow
#print axioms oddSolution_level_zero
#print axioms oddSolution_initial
#print axioms hasDerivAt_expLin
#print axioms hasDerivAt_expTerm
#print axioms hasDerivAt_oddSolution
#print axioms oddSolution_ode
#print axioms oddRow_one_zero
#print axioms oddRow_one_one
#print axioms oddRow_two_zero
#print axioms oddRow_two_one
#print axioms oddRow_two_two
#print axioms oddSolution_one
#print axioms oddSolution_two
#print axioms oddSystem_unique
#print axioms oddLevelMatrix_mulVec
#print axioms oddRow_eq_zero_of_lt
#print axioms oddLevelMatrix_eigen
#print axioms mulVec_sum
#print axioms sum_oddRow_columns
#print axioms exp_oddLevelMatrix_square_report
#print axioms oddAggregate_cases
#print axioms oddAggregate_succ_of_lt
#print axioms oddAggregate_pred_of_gt
#print axioms nearestDriftGen_lump
#print axioms driftStep_lump
#print axioms driftStep_iterate_lump
#print axioms aggLevel_of_le
#print axioms aggLevel_of_gt
#print axioms aggLevel_gridSucc
#print axioms aggLevel_gridPred
#print axioms pullbackMatrix_mulVec
#print axioms nearestDriftMatrix_mulVec_grid
#print axioms countDrift_grid
#print axioms upRate_grid_le
#print axioms downRate_grid_le
#print axioms downRate_grid_gt
#print axioms upRate_grid_gt
#print axioms nearestDrift_lump_mulVec
#print axioms nearestDrift_pullback_intertwine
#print axioms pow_intertwine
#print axioms euler_intertwine
#print axioms exp_intertwine
#print axioms exp_nearestDrift_square_report
