/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupportChainDynkin

/-! Axiom audit of SupportChainDynkin. -/

open Descent.Pangenome.AncestralLocality

#print axioms jumpRateGenerator_mulVec
#print axioms sum_jumpRateGenerator
#print axioms jumpChainLaw_nonneg
#print axioms hasDerivAt_sum_jumpChainLaw_mul
#print axioms sum_jumpChainLaw
#print axioms sum_jumpChainLaw_mul_le_exp
#print axioms sum_jumpChainLaw_mul_sub_eq_integral
#print axioms tagWeight_update
#print axioms tagWeight_supportChainStart
#print axioms tagWeight_supportChainBranch_le
#print axioms supportChainGenerator_mulVec
#print axioms supportChainGenerator_tagWeight_le
#print axioms supportChainGenerator_count_le
#print axioms hasDerivAt_sum_supportChainLaw_mul
#print axioms supportChainLaw_nonneg
#print axioms sum_supportChainLaw
#print axioms sum_supportChainLaw_mul_tagCount_le
#print axioms sum_supportChainLaw_mul_count_le
#print axioms sum_supportChainLaw_mul_lightWeight_le
#print axioms sum_supportChainLaw_escape_le
#print axioms sum_supportChainLaw_escape_le_radius
#print axioms sum_supportChainLaw_escape_eq_zero
