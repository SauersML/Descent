/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.ClosureReachability
import Descent.Pangenome.AncestralLocality.CylinderSamplingAlgebra
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Descent.Pangenome.AncestralLocality.JointNonautonomy
import Descent.Pangenome.AncestralLocality.LocalityBounds
import Descent.Pangenome.AncestralLocality.LocalityTransition
import Descent.Pangenome.AncestralLocality.SupercriticalReach

/-! Import audit of the AncestralLocality head: the registered modules load together, with no
declaration declared twice. -/

open Descent.Pangenome.AncestralLocality

#print axioms refinementStep_agreeOn
#print axioms iterate_refinementStep_agreeOn_eq_reach
#print axioms checkKernel_edgeRates
