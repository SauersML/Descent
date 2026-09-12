/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.DecisionDysonDual

/-! Axiom audit of DecisionDysonDual. -/

open Descent.Pangenome.AncestralLocality.DecisionDysonDual

#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.hasDerivAt_integral_from_zero
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.yuleWeight
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.continuous_yuleWeight
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.hasDerivAt_yuleWeight
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.yuleWeight_nonneg
#print axioms
  Descent.Pangenome.AncestralLocality.DecisionDysonDual.sum_yuleMoment_mul_yuleDeriv_le
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.sum_yuleMoment_mul_le
#print axioms
  Descent.Pangenome.AncestralLocality.DecisionDysonDual.yuleMoment_mul_yuleWeight_le
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.gainSemigroup_add
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.killedSemigroup_add
#print axioms
  Descent.Pangenome.AncestralLocality.DecisionDysonDual.hasDerivAt_killedSemigroup_apply
#print axioms
  Descent.Pangenome.AncestralLocality.DecisionDysonDual.norm_killedSemigroup_apply_le
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.dysonTerm
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.continuous_dysonTerm
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.hasDerivAt_dysonTerm_zero
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.hasDerivAt_dysonTerm_succ
#print axioms Descent.Pangenome.AncestralLocality.DecisionDysonDual.norm_dysonTerm_le
#print axioms
  Descent.Pangenome.AncestralLocality.DecisionDysonDual.samplingObservable_generator
