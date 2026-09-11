/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteGeneticTransition

/-! Axiom audit of FiniteGeneticTransition. -/

open Descent.Portability.FiniteGeneticTransition

#print axioms piLaw_mass
#print axioms selectionLaw_mass
#print axioms pathMass_nonneg
#print axioms geneticKernel_mass
#print axioms geneticKernel_row_sum_one
#print axioms expectation_endToEndReportLaw
#print axioms endToEndReportLaw_mass
#print axioms endToEndReportLaw_unique
#print axioms genetic_endToEndReportLaw_sum_one
