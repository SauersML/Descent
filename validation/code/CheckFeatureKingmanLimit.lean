/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.FeatureKingmanLimit

/-! Axiom audit of FeatureKingmanLimit. -/

open Descent.Pangenome.AncestralLocality

#print axioms halfMix_self
#print axioms sum_halfMix_fst
#print axioms sum_halfMix_snd
#print axioms sum_sum_halfMix
#print axioms sum_prod_mul_pair
#print axioms orderedChild_apply_eq_source
#print axioms orderedSource_indicator_add
#print axioms sum_empiricalLaw_mul
#print axioms sum_empiricalLaw
#print axioms sum_copyAnnotation_fst
#print axioms sum_copyAnnotation_snd
#print axioms sum_annotatedExchange_fst
#print axioms sum_annotatedExchange_snd
#print axioms sum_exchangeAnnotation_fst
#print axioms sum_exchangeAnnotation_snd
#print axioms sum_annotatedLaw_fst
#print axioms sum_annotatedLaw_snd
#print axioms sum_annotatedLaw
#print axioms sum_offspringCount_annotatedLaw
#print axioms sum_sum_annotatedLaw_mul
#print axioms sum_prod_annotatedLaw_source_eq
#print axioms featurePairSurvival_eq
#print axioms tendsto_one_sub_inv_pow_floor
#print axioms tendsto_featurePairSurvival
#print axioms tendsto_one_sub_featurePairSurvival
