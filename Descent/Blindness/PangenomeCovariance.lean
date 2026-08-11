/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.ObservationalCeiling
import Descent.Pangenome.Presentation

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness

open CategoryTheory Descent.Pangenome.Presentation

/-!
# A statistic is readable from the pangenome exactly when the chopping cannot move it

`Descent.Pangenome.Presentation` builds the storage layer: a `GraphPresentation` is a
semantic homology presentation together with a choice of storage nodes covering it, two of
them are `GraphEquivalent` when their semantic layers agree, and a `PangenomeObject` is the
equivalence class — the pangenome with node identifiers and segmentation quotiented away. It
proves the descent theorem, that a storage statistic survives every lossless node rewrite
exactly when it factors through semantic homology, and it exhibits the witness: two atomic
nodes merged into one, same semantics, different node count.

This file says what that costs an observer, in the corpus's identifiability vocabulary.

## The two halves

`identifiedBy_classOf_iff_isGraphInvariant` is the positive half, and it is a translation
rather than a new theorem: `IdentifiedBy classOf F` and `IsGraphInvariant F` are the same
predicate written twice. Composing it with the descent theorem gives
`identifiedBy_classOf_iff_factorsThroughSemantic` — **a storage-graph statistic is pinned by
the pangenome object exactly when it factors through semantic homology.** That is the
precise form of "this allele statistic does not depend on how we chopped the graph": not a
convention, not a modelling choice, but a biconditional whose two sides are checkable.

`rechoppingSymmetry` is the negative half. The transformation is atomic re-chopping — replace
a graph's storage by one node per semantic coordinate — which preserves the pangenome object
at EVERY graph, since it does not touch the semantic layer, and moves the node count at the
merged witness. So no procedure reading the pangenome decides how many storage nodes the
graph had, which is what it means for node count to be an artefact of the file rather than a
fact about the organism.

## Why the transformation is global

`ObservationalSymmetry` demands invariance at every parameter, and atomic re-chopping
supplies it: `atomicRechopping` is defined on all graphs and its invariance is definitional,
because `atomicGraph` copies the semantic field. A transformation defined only at the
witness would give the same blindness conclusion and would be a coincidence rather than a
symmetry — the whole point of the structure is that the invariance is a law about the
observation, and the witness only shows the law is not vacuous.
-/

/-- **Atomic re-chopping**: keep the semantics, replace the storage by one node per semantic
coordinate. This is the canonical representative of a graph's rewrite class. -/
def atomicRechopping {Pos : Type*} (graph : GraphPresentation Pos) : GraphPresentation Pos :=
  atomicGraph graph.semantic

/-- Re-chopping does not move the pangenome object, at any graph: it leaves the semantic
layer alone, so the two graphs are equivalent by the identity isomorphism. -/
theorem classOf_atomicRechopping {Pos : Type*} (graph : GraphPresentation Pos) :
    classOf (atomicRechopping graph) = classOf graph :=
  (classOf_eq_iff _ _).mpr ⟨Iso.refl _⟩

/-- **Identification by the pangenome object IS graph invariance.** The corpus's
identifiability vocabulary and the storage layer's invariance vocabulary are one predicate;
neither development needs its own. -/
theorem identifiedBy_classOf_iff_isGraphInvariant {Pos : Type*} {Value : Type*}
    (statistic : GraphPresentation Pos → Value) :
    IdentifiedBy (fun graph : GraphPresentation Pos ↦ classOf graph) statistic ↔
      IsGraphInvariant statistic := by
  constructor
  · intro hidentified first second hequivalent
    exact hidentified first second ((classOf_eq_iff first second).mpr hequivalent)
  · intro hinvariant first second hclass
    exact hinvariant first second ((classOf_eq_iff first second).mp hclass)

/-- **The statement the storage layer was built for.** A storage-graph statistic is pinned by
the pangenome object exactly when it factors through semantic homology — so an allele
statistic that reads only homology is independent of how the graph was chopped, and one that
does not is not merely hard to compare across builds but unpinned by the pangenome at all. -/
theorem identifiedBy_classOf_iff_factorsThroughSemantic {Pos : Type*} {Value : Type*}
    (statistic : GraphPresentation Pos → Value) :
    IdentifiedBy (fun graph : GraphPresentation Pos ↦ classOf graph) statistic ↔
      FactorsThroughSemantic statistic :=
  (identifiedBy_classOf_iff_isGraphInvariant statistic).trans
    (graphInvariant_iff_factorsThroughSemantic statistic)

/-- **Re-chopping is an observational symmetry of the pangenome, with the node count as its
moved target.** -/
noncomputable def rechoppingSymmetry :
    ObservationalSymmetry (fun graph : GraphPresentation (Fin 2) ↦ classOf graph)
      (fun graph : GraphPresentation (Fin 2) ↦ graphNodeCount graph) where
  transform := atomicRechopping
  observation_invariant := classOf_atomicRechopping
  moved := mergedNodeWitness
  target_moved := by
    intro hcount
    norm_num [atomicRechopping, graphNodeCount, splitNodeWitness, mergedNodeWitness,
      atomicGraph, discretePresentation] at hcount

/-- **The storage node count is not identified by the pangenome.** -/
theorem graphNodeCount_not_identifiedBy_classOf :
    ¬ IdentifiedBy (fun graph : GraphPresentation (Fin 2) ↦ classOf graph)
      (fun graph : GraphPresentation (Fin 2) ↦ graphNodeCount graph) :=
  not_identifiedBy_of_observationalSymmetry rechoppingSymmetry

/-- **No procedure reading the pangenome decides the storage node count.** Any statistic, any
post-processing, any hierarchy of tests folded into a verdict: each is a function of the
pangenome object, and the object is the same at a graph and at its atomic re-chopping while
the count is not. The node count is a fact about the file, not about the organism. -/
theorem no_pangenome_criterion_for_graphNodeCount :
    ¬ ∃ decideValue : Descent.Pangenome.Presentation.PangenomeObject (Fin 2) → Prop,
      ∀ graph : GraphPresentation (Fin 2),
        graphNodeCount graph = graphNodeCount (atomicRechopping mergedNodeWitness)
          ↔ decideValue (classOf graph) :=
  rechoppingSymmetry.no_target_criterion

end Descent.Blindness
