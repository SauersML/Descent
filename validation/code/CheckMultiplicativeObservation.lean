/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeObservation

/-! Kernel audit of the multiplicative-coalescent observation bound (Theorem F, (F1)). -/

#print axioms
  Descent.Pangenome.GraphCoalescent.two_mul_pairProductSum
#print axioms
  Descent.Pangenome.GraphCoalescent.pairProductSum_sub_eq
#print axioms
  Descent.Pangenome.GraphCoalescent.pairProductSum_sub_le
#print axioms
  Descent.Pangenome.GraphCoalescent.pairProductSum_sub_div_sq_le
#print axioms
  Descent.Pangenome.GraphCoalescent.load_mul_load_le
#print axioms
  Descent.Pangenome.GraphCoalescent.deathRate_div_sq_le_half
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_blockMass
#print axioms
  Descent.Pangenome.GraphCoalescent.coverPair_merge
#print axioms
  Descent.Pangenome.GraphCoalescent.multiplicativeCoverRate_merge
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_multiplicativeCoverRate
#print axioms
  Descent.Pangenome.GraphCoalescent.blockMass_merge
#print axioms
  Descent.Pangenome.GraphCoalescent.two_mul_sum_multiplicativeCoverRate
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_multiplicativeCoverRate_le_half
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_skeletonLaw
#print axioms
  Descent.Pangenome.GraphCoalescent.deficitMass_le
#print axioms
  Descent.Pangenome.GraphCoalescent.separationMass_le
#print axioms
  Descent.Pangenome.GraphCoalescent.hasSum_poissonPMFReal_mul_descFactorial
#print axioms
  Descent.Pangenome.GraphCoalescent.poissonMixture_le
#print axioms
  Descent.Pangenome.GraphCoalescent.poissonMixture_le_min
#print axioms
  Descent.Pangenome.GraphCoalescent.skeletonPathWeight_snoc
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_skeletonPathWeight_mul
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_abs_sub_fiber_le
#print axioms
  Descent.Pangenome.GraphCoalescent.sep_last_of_skeletonPathWeight_ne_zero
#print axioms
  Descent.Pangenome.GraphCoalescent.sum_filter_path_ne_le_separationMass
#print axioms
  Descent.Pangenome.GraphCoalescent.pathTotalVariation_le_separationMass
