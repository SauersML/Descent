/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.PartitionLatticeMobius

/-! Axiom audit of PartitionLatticeMobius. -/

open Descent.Pangenome.GraphCoalescent

#print axioms instLocallyFiniteOrderFinpartition
#print axioms mu_finpartition_top
#print axioms card_filter_card_parts_eq_stirlingSecond
#print axioms sum_stirlingSecond_mul_mobiusCoefficient
#print axioms topMobius_eq_mobiusCoefficient
#print axioms sum_mobiusCoefficient_eq_sum_stirlingSecond
