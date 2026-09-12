/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeCoupling

/-! Kernel audit of the uniformized coupling of the report with the multiplicative coalescent. -/

#print axioms
  Descent.Pangenome.GraphCoalescent.sum_kingmanStep
#print axioms
  Descent.Pangenome.GraphCoalescent.kingmanStep_nonneg
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_multiplicativeStep
#print axioms
  Descent.Pangenome.GraphCoalescent.multiplicativeStep_nonneg
#print axioms
  Descent.Pangenome.GraphCoalescent.multiplicativeStep_merge
#print axioms
  Descent.Pangenome.GraphCoalescent.multiplicativeStep_merge_eq_multiplicativeCoverRate
#print axioms
  Descent.Pangenome.GraphCoalescent.hiddenLoad_le_componentSize
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_loadDeficit_scaled
#print axioms
  Descent.Pangenome.GraphCoalescent.covers_observed_eq_merge_iff
#print axioms
  Descent.Pangenome.GraphCoalescent.card_covers_observed_eq_div
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_excessStep
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_excessStep_le
