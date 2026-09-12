/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SelectionTies

/-! Axiom audit of SelectionTies. -/

open Descent.Pangenome.AncestralLocality

#print axioms sum_mul_eq_meanFitness
#print axioms sizeBias_eq_div_meanFitness
#print axioms reproduce_halfMix_sizeBias_sub
#print axioms selectionKernel_drift_eq_sizeBias_drift
