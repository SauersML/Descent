/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.InfiniteGenomeRate

/-! Axiom audit of InfiniteGenomeRate. -/

open Descent.Pangenome.AncestralLocality.InfiniteGenomeRate

#print axioms radiusEscape
#print axioms radiusEscape_nonneg
#print axioms radiusEscape_mono_time
#print axioms radiusEscape_le_exp_neg
#print axioms radiusEscape_le_of_radius
#print axioms sum_supportChainLaw_escape_le_radiusEscape
#print axioms abs_sum_supportChainLaw_sub_le
#print axioms norm_operator_sub_le_radiusEscape
#print axioms norm_sub_limit_le_of_tail
#print axioms norm_operator_sub_limitValue_le_radiusEscape
#print axioms norm_operator_sub_infiniteGenomeSemigroup_le
#print axioms norm_windowPullback_operator_sub_infiniteGenomeSemigroup_le
