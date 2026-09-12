/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup

/-! Axiom audit of DecisionWindowSemigroup. -/

open Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup

#print axioms
  Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup.sum_samplingObservable_dysonDeriv
#print axioms Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup.summable_dualTerm
#print axioms
  Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup.norm_jumpOperator_sub_partialDual_le
#print axioms
  Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup.norm_jumpOperator_sub_dualSeries_le
#print axioms
  Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup.decisionLightConeApproximation
#print axioms Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup.decisionWindowSemigroup
#print axioms decisionWindowSemigroup_samplingFunction
#print axioms Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup.backwardFunction_apply
#print axioms
  Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup.tendsto_decisionWindowSemigroup_slope
