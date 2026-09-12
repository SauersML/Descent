/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MinimalHistoryLumping

/-! Axiom audit of the lumping of the minimal connecting histories. -/

open Descent.Pangenome.GraphCoalescent.MinimalHistoryLumping

#print axioms historyWeight_congr
#print axioms visibleTarget_comm
#print axioms IsRepresentativeSet
#print axioms representatives
#print axioms representatives_isRepresentativeSet
#print axioms IsRepresentativeSet.card_eq
#print axioms IsRepresentativeSet.erase
#print axioms connectingCount
#print axioms minimalHistoryCount_eq_connectingCount
#print axioms connectingCount_zero
#print axioms connectingCount_succ
#print axioms exists_visibleTarget_of_visible
#print axioms visibleTarget_eq_iff
