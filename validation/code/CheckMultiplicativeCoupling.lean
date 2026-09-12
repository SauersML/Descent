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
  Descent.Pangenome.GraphCoalescent.hiddenLoad_le_card_component
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
#print axioms
  Descent.Pangenome.GraphCoalescent.coupledStep_nonneg
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_coupledStep
#print axioms
  Descent.Pangenome.GraphCoalescent.coupledStep_absorb
#print axioms
  Descent.Pangenome.GraphCoalescent.observed_eq_of_not_coupledSep
#print axioms
  Descent.Pangenome.GraphCoalescent.coupledStep_hazard
#print axioms
  Descent.Pangenome.GraphCoalescent.coupledStep_drift
#print axioms
  Descent.Pangenome.GraphCoalescent.coupled_separationMass_le
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_coupledStep_fst
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_coupledStep_snd
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_filter_path_comp_eq
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_filter_coupled_report_eq
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_filter_coupled_multiplicative_eq
#print axioms
  Descent.Pangenome.GraphCoalescent.report_multiplicative_pathTotalVariation_le
#print axioms
  Descent.Pangenome.GraphCoalescent.report_multiplicative_pathTotalVariation_le_one
#print axioms
  Descent.Pangenome.GraphCoalescent.report_multiplicative_poissonTotalVariation_le
