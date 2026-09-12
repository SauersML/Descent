/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.RandomClosure

/-! Axiom audit of RandomClosure. -/

open Descent.Pangenome.AncestralLocality

#print axioms directedReach_eq_reach
#print axioms degreeRate_nonneg
#print axioms degreeRate_pos_iff
#print axioms directedReach_degreeRate
#print axioms iterate_refinementStep_degreeRate
#print axioms graphExpect_card_directedReach_le
