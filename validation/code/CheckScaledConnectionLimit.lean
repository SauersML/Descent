/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ScaledConnectionLimit

/-! Kernel audit of the limit law of the scaled connection clock and of (F2) for path
functionals. -/

#print axioms
  Descent.Pangenome.GraphCoalescent.crossingRate_eq_pairProductSum
#print axioms
  Descent.Pangenome.GraphCoalescent.crossingRate_top
#print axioms
  Descent.Pangenome.GraphCoalescent.connectionProbability_mem_Icc
#print axioms
  Descent.Pangenome.GraphCoalescent.connectionProbability_zero
#print axioms
  Descent.Pangenome.GraphCoalescent.tendsto_connectionProbability_atTop
#print axioms
  Descent.Pangenome.GraphCoalescent.abs_sum_mul_sub_sum_mul_le
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_mul_mem_unit
#print axioms
  Descent.Pangenome.GraphCoalescent.abs_poissonMixture_sub_le
#print axioms
  Descent.Pangenome.GraphCoalescent.abs_poissonMixture_report_sub_spread_le
#print axioms
  Descent.Pangenome.GraphCoalescent.mk_graphKer_labelInterface_eq_iff
#print axioms
  Descent.Pangenome.GraphCoalescent.fiberLabel_bijective
#print axioms
  Descent.Pangenome.GraphCoalescent.fiberSize_labelInterface
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_spreadMass_mul_comp
#print axioms
  Descent.Pangenome.GraphCoalescent.pairProductSum_blockMass_comap_of_marginal
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_topMobius_graphKer_spread_eq_connectionProbability
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_reportPathLaw_mul_last_top
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_massPathLaw_mul_last_top
#print axioms
  Descent.Pangenome.GraphCoalescent.abs_reportConnectionProbability_sub_le_min
#print axioms
  Descent.Pangenome.GraphCoalescent.configMass_eq_prod_edgeMass
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_configMass
#print axioms
  Descent.Pangenome.GraphCoalescent.configMass_nonneg
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_configMass_add_mul
#print axioms
  Descent.Pangenome.GraphCoalescent.componentPartition_mono
#print axioms
  Descent.Pangenome.GraphCoalescent.connectionProbability_le_add
#print axioms
  Descent.Pangenome.GraphCoalescent.monotoneOn_connectionProbability
