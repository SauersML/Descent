/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ScaledConnectionLimit

/-! Kernel audit of the limit law of the scaled connection clock and of (F2) for path
functionals. -/

#print axioms
  Descent.Pangenome.GraphCoalescent.two_mul_pairProductSum_blockMass
#print axioms
  Descent.Pangenome.GraphCoalescent.crossingRate_eq_pairProductSum
#print axioms
  Descent.Pangenome.GraphCoalescent.continuous_connectionProbability_time
#print axioms
  Descent.Pangenome.GraphCoalescent.crossingRate_top
#print axioms
  Descent.Pangenome.GraphCoalescent.connectionProbability_mem_Icc
#print axioms
  Descent.Pangenome.GraphCoalescent.connectionProbability_zero
#print axioms
  Descent.Pangenome.GraphCoalescent.crossingRate_pos
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
  Descent.Pangenome.GraphCoalescent.ite_blockMap_mul_blockMass_eq
#print axioms
  Descent.Pangenome.GraphCoalescent.two_mul_sum_crossing_eq_mass
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_filter_le_massStep
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_filter_le_massStep_of_not_le
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_filter_le_massLaw
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_massLaw_mul_top
#print axioms
  Descent.Pangenome.GraphCoalescent.hasSum_poissonPMFReal_mul_massTop
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
