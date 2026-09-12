/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MarkovCompressions

/-! Axiom audit of MarkovCompressions. -/

open Descent.Pangenome.GraphCoalescent.MarkovCompressions

#print axioms injective_iff_width_eq
#print axioms hiddenLoad_graphKer
#print axioms card_covers_bot_merge
#print axioms card_covers_graphKer_merge
#print axioms not_isReportLumping_of_width
#print axioms isReportLumping_of_injective
#print axioms isReportLumping_of_width_le_one
#print axioms isReportLumping_id
#print axioms isReportLumping_iff
#print axioms observablyMarkov_iff_injective
#print axioms componentSize_bot
#print axioms componentWidth_bot
#print axioms filter_merge_rel_of_rel
#print axioms filter_merge_rel_of_not_rel
#print axioms hiddenLoad_add_componentWidth_le
