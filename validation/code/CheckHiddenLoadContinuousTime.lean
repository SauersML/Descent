/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLoadContinuousTime

/-! Axiom audit of HiddenLoadContinuousTime. -/

open Descent.Pangenome.GraphCoalescent

#print axioms lintegral_Icc_rate_exp
#print axioms measurable_sojourn_indicator
#print axioms lintegral_holdMeasure_window
#print axioms lintegral_rate_mul_measure_between
#print axioms descentTime_clockHold_eq_sum
#print axioms descentTime_clockHold_succ
#print axioms indepFun_descentTime_clockHold
#print axioms blockCountAt_clockHold_eq_iff
#print axioms kingmanClock_descentTime_le
