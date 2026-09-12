/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.EdgeClockConnectionLaw

/-! Kernel audit of the connection time `T_p` as a function of exponential edge clocks. -/

#print axioms
  Descent.Pangenome.GraphCoalescent.componentPartition_all_true
#print axioms
  Descent.Pangenome.GraphCoalescent.edgeConnectionTime_nonneg
#print axioms
  Descent.Pangenome.GraphCoalescent.edgeConnectionTime_le_iff
#print axioms
  Descent.Pangenome.GraphCoalescent.preimage_rungEdges_eq_pi
#print axioms
  Descent.Pangenome.GraphCoalescent.measurableSet_ite_Iic_Ioi
#print axioms
  Descent.Pangenome.GraphCoalescent.measurableSet_preimage_rungEdges
#print axioms
  Descent.Pangenome.GraphCoalescent.preimage_Iic_edgeConnectionTime
#print axioms
  Descent.Pangenome.GraphCoalescent.measurable_edgeConnectionTime
#print axioms
  Descent.Pangenome.GraphCoalescent.expMeasure_Iic_eq
#print axioms
  Descent.Pangenome.GraphCoalescent.expMeasure_Ioi_eq
#print axioms
  Descent.Pangenome.GraphCoalescent.isProbabilityMeasure_edgeClockLaw
#print axioms
  Descent.Pangenome.GraphCoalescent.edgeClockLaw_preimage_Iic
#print axioms
  Descent.Pangenome.GraphCoalescent.cdf_map_edgeConnectionTime
#print axioms
  Descent.Pangenome.GraphCoalescent.map_edgeConnectionTime_edgeClockLaw
