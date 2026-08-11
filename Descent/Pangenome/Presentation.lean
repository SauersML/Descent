/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Descent.Pangenome.Construction
import Descent.Layer

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The category of pangenome presentations

`Descent.Pangenome.Construction` proves that an alignment relation generates a quotient of
panel positions.  It does not distinguish that quotient from the particular node identifiers
used to present it, and therefore cannot yet state what it means for a statistic to be
independent of a presentation.  This file supplies that missing level.

## Objects and arrows

Fix the panel positions `Pos`.  A `Presentation Pos` is a surjection from those positions to
a type of presented coordinates.  Surjectivity rules out dead coordinates: every coordinate
must be visited by the panel.  A morphism `P ⟶ Q` is a map of coordinates commuting with
the two presentation maps.  It can only merge coordinates, never move a panel position to an
unrelated one.  Composition is ordinary function composition, making presentations a
category.

This category is thin.  Because every coordinate is hit by a panel position, two commuting
coordinate maps are equal.  More importantly, its order has an exact biological reading:
there is an arrow `P ⟶ Q` exactly when every pair identified by `P` is also identified by
`Q`.  Thus arrows are coarsenings of represented homology.

## Isomorphism and descent

The central theorem is `nonempty_iso_iff_kernel_eq`: two presentations are isomorphic exactly
when their maps have the same kernel relation on panel positions.  Node names and all other
carrier-level choices disappear; the relation saying which observed positions share a
coordinate is complete for presentation equivalence.

`invariant_iff_factorsThroughKernel` is the corresponding theorem for statistics.  A
functional on presentations is invariant under every presentation isomorphism exactly when
it factors through the kernel setoid.  This is the promised descent criterion: it does not
merely list some safe statistics, but characterises all of them.

## Semantic coordinates are not storage nodes

A split of one GFA node into two changes the storage segmentation but not the atomic homology
coordinates carried by its sequence.  `GraphPresentation` therefore adds a surjective block
map from semantic coordinates to storage nodes without confusing its fibers with homology.
Two graph presentations are equivalent when their semantic presentations are isomorphic;
their block maps may differ.  `graphInvariant_iff_factorsThroughSemantic` proves the second
descent theorem: a graph statistic survives all lossless segmentation changes exactly when it
factors through an invariant statistic of the semantic presentation.

`graphNodeCount_not_invariant` is the two-position witness.  The same discrete semantic
pangenome can be stored as two one-coordinate nodes or one two-coordinate node, so raw node
count is not a pangenome invariant.  This is why `coordinateCount_invariant` counts semantic
coordinates and must not be read as a GFA node-count theorem.

## The universal pangenome

For an aligner relation `A`, `closurePresentation A` presents positions by the equivalence
closure from `Construction`.  `closurePresentation_universal` proves its universal property:
a presentation coequalises every reported alignment exactly when it receives a unique arrow
from `closurePresentation A`.  So the construction is a coequalizer, equivalently the colimit
of the relation-shaped alignment diagram.  Calling an arbitrary sequence graph a colimit
would be too strong; this theorem states the precise sense in which the generated pangenome
is universal.

## Empirical status

None.  The declarations are theorems about surjections, equivalence relations and a reported
binary relation.  Whether a real graph builder preserves the position-level kernel, and which
statistics used by a real analysis factor through it, are empirical questions not settled
here.

## Main results

- `hom_subsingleton`: the presentation category is thin.
- `nonempty_hom_iff_kernel_le`: arrows are exactly coarsenings of represented homology.
- `nonempty_iso_iff_kernel_eq`: isomorphism classes are exactly kernel relations.
- `support_eq_of_iso`, `collapseFree_iff_of_iso`: the existing construction-level
  biological quantities transport across categorical presentation equivalence.
- `invariant_iff_factorsThroughKernel`: the complete descent criterion for statistics.
- `reindexIso`: relabelling coordinates is an isomorphism, not a new pangenome.
- `coordinateCount_invariant`: a concrete statistic that passes the descent criterion.
- `graphInvariant_iff_factorsThroughSemantic`: the complete descent criterion after node
  splitting, merging and relabelling.
- `PangenomeObject`, `classOf_eq_iff`: the coarse pangenome is literally the quotient of
  graph presentations by lossless presentation equivalence.
- `graphNodeCount_not_invariant`: raw storage-node count fails that criterion.
- `closurePresentation_universal`: generated alignment closure has the coequalizer universal
  property.
-/

namespace Descent.Pangenome

open CategoryTheory Function

universe u v

/-! ### The category -/

/-- **A presentation of a fixed panel of positions.**  `encode` assigns every observed
position a presented coordinate, and `onto` excludes coordinates unsupported by the panel.

The coordinate type is deliberately abstract.  It may be graph nodes at base resolution,
columns of an alignment, or any lossless renaming of either.  The kernel of `encode`, not the
carrier's names, records which positions the presentation identifies.

Empirical status: NOT AN EMPIRICAL CLAIM. -/
structure Presentation (Pos : Type u) where
  /-- The coordinate carrier chosen by this presentation. -/
  Coord : Type u
  /-- The coordinate occupied by each panel position. -/
  encode : Pos → Coord
  /-- Every presented coordinate is supported by an observed position. -/
  onto : Surjective encode

namespace Presentation

/-- **A map of presentations** is a coordinate map commuting with the panel encodings.
It witnesses that the target makes every identification made by the source. -/
structure Hom {Pos : Type u} (P Q : Presentation Pos) where
  /-- The map between presented coordinates. -/
  toFun : P.Coord → Q.Coord
  /-- Mapping after presentation agrees with presenting directly. -/
  comm : ∀ x, toFun (P.encode x) = Q.encode x

/-- A morphism is determined by its values on the panel, and the panel reaches every
coordinate.  Hence the presentation category has at most one arrow between two objects. -/
theorem hom_ext {Pos : Type u} {P Q : Presentation Pos} (f g : Hom P Q) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          congr
          funext y
          obtain ⟨x, rfl⟩ := P.onto y
          exact (hf x).trans (hg x).symm

/-- Identity map of a presentation. -/
def Hom.id {Pos : Type u} (P : Presentation Pos) : Hom P P where
  toFun := fun x ↦ x
  comm := fun _ ↦ rfl

/-- Composition of commuting coordinate maps. -/
def Hom.comp {Pos : Type u} {P Q R : Presentation Pos} (f : Hom P Q) (g : Hom Q R) :
    Hom P R where
  toFun := g.toFun ∘ f.toFun
  comm := fun x ↦ by rw [Function.comp_apply, f.comm, g.comm]

/-- Presentations of one panel form a category.  Its arrows point from a finer presentation
to a coarser one. -/
instance {Pos : Type u} : Category (Presentation Pos) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := fun _ ↦ hom_ext _ _
  comp_id := fun _ ↦ hom_ext _ _
  assoc := fun _ _ _ ↦ hom_ext _ _

/-- The presentation category is thin: a coarsening map, when it exists, is unique. -/
instance hom_subsingleton {Pos : Type u} (P Q : Presentation Pos) : Subsingleton (P ⟶ Q) :=
  ⟨hom_ext⟩

/-- The relation on panel positions represented by a presentation. -/
def kernel {Pos : Type u} (P : Presentation Pos) : Setoid Pos :=
  Setoid.ker P.encode

/-- A presentation identifies two positions exactly when their presented coordinates agree. -/
theorem kernel_rel_iff {Pos : Type u} (P : Presentation Pos) (x y : Pos) :
    P.kernel x y ↔ P.encode x = P.encode y :=
  Iff.rfl

/-! ### Arrows are coarsenings -/

/-- A commuting map can only add identifications: the source kernel is below the target
kernel in the lattice of equivalence relations. -/
theorem kernel_le_of_hom {Pos : Type u} {P Q : Presentation Pos} (f : P ⟶ Q) :
    P.kernel ≤ Q.kernel := by
  intro x y hxy
  change P.encode x = P.encode y at hxy
  change Q.encode x = Q.encode y
  rw [← f.comm x, ← f.comm y, hxy]

/-- A containment of kernel relations induces the unique commuting coordinate map.

The definition chooses one panel position above each source coordinate.  Kernel containment
makes the target coordinate independent of that choice. -/
noncomputable def homOfKernelLE {Pos : Type u} {P Q : Presentation Pos}
    (h : P.kernel ≤ Q.kernel) : P ⟶ Q where
  toFun y := Q.encode (Classical.choose (P.onto y))
  comm := fun x ↦ by
    let hx := Classical.choose_spec (P.onto (P.encode x))
    apply h at hx
    exact hx

/-- **Arrows are exactly coarsenings of represented homology.**  This identifies the
categorical preorder with the refinement order on equivalence relations. -/
theorem nonempty_hom_iff_kernel_le {Pos : Type u} (P Q : Presentation Pos) :
    Nonempty (P ⟶ Q) ↔ P.kernel ≤ Q.kernel :=
  ⟨fun ⟨f⟩ ↦ kernel_le_of_hom f, fun h ↦ ⟨homOfKernelLE h⟩⟩

/-- Any map from panel positions becomes a presentation after restricting its codomain to
the coordinates it actually uses.  The restriction removes dead graph states. -/
def ofMap {Pos Coord : Type u} (f : Pos → Coord) : Presentation Pos where
  Coord := Set.range f
  encode x := ⟨f x, x, rfl⟩
  onto y := by
    obtain ⟨_, x, rfl⟩ := y
    exact ⟨x, rfl⟩

/-- Restricting a map to its occupied range changes no position-level identifications. -/
@[simp]
theorem kernel_ofMap {Pos Coord : Type u} (f : Pos → Coord) :
    (ofMap f).kernel = Setoid.ker f := by
  apply Setoid.ext
  intro x y
  exact Subtype.ext_iff

/-! ### Canonical quotient presentations -/

/-- Every setoid gives a canonical presentation by its quotient map. -/
def ofSetoid {Pos : Type u} (r : Setoid Pos) : Presentation Pos where
  Coord := Quotient r
  encode := Quotient.mk r
  onto q := Quotient.inductionOn q fun x ↦ ⟨x, rfl⟩

/-- The canonical quotient presents exactly the relation it quotients by. -/
@[simp]
theorem kernel_ofSetoid {Pos : Type u} (r : Setoid Pos) :
    (ofSetoid r).kernel = r :=
  Setoid.ker_mk_eq r

/-! ### Isomorphism is equality of represented homology -/

/-- Isomorphic presentations identify the same pairs of panel positions. -/
theorem kernel_eq_of_iso {Pos : Type u} {P Q : Presentation Pos} (i : P ≅ Q) :
    P.kernel = Q.kernel := by
  apply le_antisymm
  · exact kernel_le_of_hom i.hom
  · exact kernel_le_of_hom i.inv

/-- Equal kernel relations construct an isomorphism of presentations.  The inverse laws need
no coordinate calculation: thinness makes every pair of parallel arrows equal. -/
noncomputable def isoOfKernelEq {Pos : Type u} {P Q : Presentation Pos}
    (h : P.kernel = Q.kernel) : P ≅ Q where
  hom := homOfKernelLE h.le
  inv := homOfKernelLE h.ge

/-- An isomorphism of presentations induces an equivalence of their coordinate carriers.
This is stated explicitly because `Presentation` is not made a concrete category merely to
obtain the carrier map. -/
def coordEquivOfIso {Pos : Type u} {P Q : Presentation Pos} (i : P ≅ Q) :
    P.Coord ≃ Q.Coord where
  toFun := i.hom.toFun
  invFun := i.inv.toFun
  left_inv y := by
    have h := congrArg Hom.toFun i.hom_inv_id
    exact congrFun h y
  right_inv y := by
    have h := congrArg Hom.toFun i.inv_hom_id
    exact congrFun h y

/-- **Classification of presentation equivalence.**  Two presentation objects are
isomorphic if and only if they encode exactly the same homology relation on the panel. -/
theorem nonempty_iso_iff_kernel_eq {Pos : Type u} (P Q : Presentation Pos) :
    Nonempty (P ≅ Q) ↔ P.kernel = Q.kernel :=
  ⟨fun ⟨i⟩ ↦ kernel_eq_of_iso i, fun h ↦ ⟨isoOfKernelEq h⟩⟩

/-- Haplotype support, the basis of the node-frequency spectrum, is unchanged by an
isomorphism of presentations. -/
theorem support_eq_of_iso {Pos Hap : Type u} (hap : Pos → Hap)
    {P Q : Presentation Pos} (i : P ≅ Q) (x : Pos) :
    Construction.support hap P.kernel x = Construction.support hap Q.kernel x := by
  rw [kernel_eq_of_iso i]

/-- Within-haplotype collapse is a property of the semantic kernel, so an isomorphic change
of presentation cannot create or remove it. -/
theorem collapseFree_iff_of_iso {Pos Hap : Type u} (hap : Pos → Hap)
    {P Q : Presentation Pos} (i : P ≅ Q) :
    Construction.CollapseFree hap P.kernel ↔ Construction.CollapseFree hap Q.kernel := by
  rw [kernel_eq_of_iso i]

/-- Every presentation is isomorphic to the canonical quotient by its kernel.  This is the
normal form behind the classification theorem. -/
noncomputable def canonicalIso {Pos : Type u} (P : Presentation Pos) :
    P ≅ ofSetoid P.kernel :=
  isoOfKernelEq (kernel_ofSetoid P.kernel).symm

/-- Relabel a presentation's coordinates through a bijection. -/
def reindex {Pos : Type u} (P : Presentation Pos) {Coord : Type u}
    (e : P.Coord ≃ Coord) : Presentation Pos where
  Coord := Coord
  encode := e ∘ P.encode
  onto := e.surjective.comp P.onto

/-- Relabelling coordinates preserves the represented kernel. -/
@[simp]
theorem kernel_reindex {Pos : Type u} (P : Presentation Pos) {Coord : Type u}
    (e : P.Coord ≃ Coord) :
    (reindex P e).kernel = P.kernel := by
  apply Setoid.ext
  intro x y
  exact e.injective.eq_iff

/-- **A relabelled coordinate carrier is the same pangenome presentation.**  This covers
identifier permutations, canonical renumberings and orientation conventions whenever they
act bijectively on the represented coordinates. -/
noncomputable def reindexIso {Pos : Type u} (P : Presentation Pos) {Coord : Type u}
    (e : P.Coord ≃ Coord) : P ≅ reindex P e :=
  isoOfKernelEq (kernel_reindex P e).symm

/-! ### The descent criterion for statistics -/

/-- A statistic is **representation-invariant** when isomorphic presentations give the same
answer. -/
def IsInvariant {Pos : Type u} {Value : Type v} (F : Presentation Pos → Value) : Prop :=
  ∀ P Q, Nonempty (P ≅ Q) → F P = F Q

/-- A statistic **factors through represented homology** when it is a function of the kernel
setoid alone. -/
def FactorsThroughKernel {Pos : Type u} {Value : Type v}
    (F : Presentation Pos → Value) : Prop :=
  ∃ f : Setoid Pos → Value, ∀ P, F P = f P.kernel

/-- Anything defined on kernel relations is automatically invariant under a change of
presentation. -/
theorem invariant_of_factorsThroughKernel {Pos : Type u} {Value : Type v}
    {F : Presentation Pos → Value} (hF : FactorsThroughKernel F) : IsInvariant F := by
  obtain ⟨f, hf⟩ := hF
  intro P Q hi
  rw [hf P, hf Q]
  exact congrArg f ((nonempty_iso_iff_kernel_eq P Q).mp hi)

/-- An invariant statistic factors through the canonical quotient presentation. -/
theorem factorsThroughKernel_of_invariant {Pos : Type u} {Value : Type v}
    {F : Presentation Pos → Value} (hF : IsInvariant F) : FactorsThroughKernel F := by
  refine ⟨fun r ↦ F (ofSetoid r), fun P ↦ ?_⟩
  exact hF P (ofSetoid P.kernel) ⟨canonicalIso P⟩

/-- **The complete descent criterion.**  A statistic is invariant under all changes of
presentation exactly when it is a function of the induced homology relation on positions. -/
theorem invariant_iff_factorsThroughKernel {Pos : Type u} {Value : Type v}
    (F : Presentation Pos → Value) :
    IsInvariant F ↔ FactorsThroughKernel F :=
  ⟨factorsThroughKernel_of_invariant, invariant_of_factorsThroughKernel⟩

/-- The number of occupied SEMANTIC coordinates in a presentation.  `Nat.card` makes the
definition independent of a chosen enumeration.  This is deliberately not the number of
storage nodes in one graph serialization; `graphNodeCount_not_invariant` below separates the
two quantities. -/
noncomputable def coordinateCount {Pos : Type u} (P : Presentation Pos) : ℕ :=
  Nat.card P.Coord

/-- Coordinate count factors through the kernel: it is the cardinality of the canonical
quotient by represented homology. -/
theorem coordinateCount_eq_kernel {Pos : Type u} (P : Presentation Pos) :
    coordinateCount P = Nat.card (Quotient P.kernel) := by
  exact Nat.card_congr (coordEquivOfIso (canonicalIso P))

/-- **Occupied coordinate count is representation-invariant.**  Relabelling or replacing a
presentation by any isomorphic carrier cannot change the count. -/
theorem coordinateCount_invariant {Pos : Type u} :
    IsInvariant (coordinateCount : Presentation Pos → ℕ) := by
  apply invariant_of_factorsThroughKernel
  exact ⟨fun r ↦ Nat.card (Quotient r), coordinateCount_eq_kernel⟩

/-! ### Storage-node presentations and lossless rewrites -/

/-- The discrete presentation, in which every panel position is its own semantic coordinate. -/
def discretePresentation (Pos : Type u) : Presentation Pos where
  Coord := Pos
  encode := id
  onto := surjective_id

/-- **A graph presentation has two levels.**  `semantic` records which panel positions are
homologous.  `block` groups those semantic coordinates into storage nodes.  Its surjectivity
again excludes dead nodes.

The definition deliberately does not yet impose an order or contiguity predicate on blocks;
it isolates the partition component of node splitting and merging.  Sequence-labelled path
constraints are additional structure, not silently assumed here.

Empirical status: NOT AN EMPIRICAL CLAIM. -/
structure GraphPresentation (Pos : Type u) where
  /-- The biological homology presentation. -/
  semantic : Presentation Pos
  /-- The graph's storage-node carrier. -/
  Node : Type u
  /-- The storage node containing each semantic coordinate. -/
  block : semantic.Coord → Node
  /-- Every storage node contains an observed semantic coordinate. -/
  block_onto : Surjective block

/-- The atomic storage of a semantic presentation: one node per semantic coordinate. -/
def atomicGraph {Pos : Type u} (P : Presentation Pos) : GraphPresentation Pos where
  semantic := P
  Node := P.Coord
  block := id
  block_onto := surjective_id

/-- **Lossless graph-presentation equivalence.**  Storage nodes may be split, merged or
renamed; the semantic presentations must remain isomorphic. -/
def GraphEquivalent {Pos : Type u} (G H : GraphPresentation Pos) : Prop :=
  Nonempty (G.semantic ≅ H.semantic)

/-- Graph-presentation equivalence is reflexive. -/
theorem graphEquivalent_refl {Pos : Type u} (G : GraphPresentation Pos) :
    GraphEquivalent G G :=
  ⟨Iso.refl _⟩

/-- Graph-presentation equivalence is symmetric. -/
theorem graphEquivalent_symm {Pos : Type u} {G H : GraphPresentation Pos}
    (h : GraphEquivalent G H) : GraphEquivalent H G := by
  obtain ⟨i⟩ := h
  exact ⟨i.symm⟩

/-- Graph-presentation equivalence is transitive. -/
theorem graphEquivalent_trans {Pos : Type u} {G H K : GraphPresentation Pos}
    (hGH : GraphEquivalent G H) (hHK : GraphEquivalent H K) : GraphEquivalent G K := by
  obtain ⟨i⟩ := hGH
  obtain ⟨j⟩ := hHK
  exact ⟨i.trans j⟩

/-- Presentation equivalence as a setoid on storage graphs. -/
def graphSetoid (Pos : Type u) : Setoid (GraphPresentation Pos) where
  r := GraphEquivalent
  iseqv := ⟨graphEquivalent_refl, graphEquivalent_symm, graphEquivalent_trans⟩

/-- **A pangenome object is an equivalence class of graph presentations.**  Node identifiers,
segmentations and semantic carrier names have been quotiented out. -/
abbrev PangenomeObject (Pos : Type u) := Quotient (graphSetoid Pos)

/-- The presentation-equivalence class represented by a storage graph. -/
def classOf {Pos : Type u} (G : GraphPresentation Pos) : PangenomeObject Pos :=
  Quotient.mk (graphSetoid Pos) G

/-- Two storage graphs name the same pangenome object exactly when their semantic
presentations are isomorphic. -/
theorem classOf_eq_iff {Pos : Type u} (G H : GraphPresentation Pos) :
    classOf G = classOf H ↔ GraphEquivalent G H :=
  Quotient.eq

/-- A statistic of storage graphs is invariant when it is constant under lossless graph
presentation equivalence. -/
def IsGraphInvariant {Pos : Type u} {Value : Type v}
    (F : GraphPresentation Pos → Value) : Prop :=
  ∀ G H, GraphEquivalent G H → F G = F H

/-- A storage-graph statistic factors through semantic content when it comes from an
isomorphism-invariant statistic of semantic presentations. -/
def FactorsThroughSemantic {Pos : Type u} {Value : Type v}
    (F : GraphPresentation Pos → Value) : Prop :=
  ∃ f : Presentation Pos → Value, IsInvariant f ∧ ∀ G, F G = f G.semantic

/-- Factoring through an invariant semantic statistic makes a storage-graph statistic
invariant under lossless rewrites. -/
theorem graphInvariant_of_factorsThroughSemantic {Pos : Type u} {Value : Type v}
    {F : GraphPresentation Pos → Value} (hF : FactorsThroughSemantic F) :
    IsGraphInvariant F := by
  obtain ⟨f, hf, hfactor⟩ := hF
  intro G H hGH
  rw [hfactor G, hfactor H]
  exact hf G.semantic H.semantic hGH

/-- A graph-invariant statistic is recovered by evaluating it on atomic storage. -/
theorem factorsThroughSemantic_of_graphInvariant {Pos : Type u} {Value : Type v}
    {F : GraphPresentation Pos → Value} (hF : IsGraphInvariant F) :
    FactorsThroughSemantic F := by
  refine ⟨fun P ↦ F (atomicGraph P), ?_, ?_⟩
  · intro P Q hPQ
    exact hF (atomicGraph P) (atomicGraph Q) hPQ
  · intro G
    exact hF G (atomicGraph G.semantic) (graphEquivalent_refl G)

/-- **The storage-graph descent theorem.**  A statistic survives every lossless node
rewrite exactly when it is a statistic of semantic homology rather than segmentation. -/
theorem graphInvariant_iff_factorsThroughSemantic {Pos : Type u} {Value : Type v}
    (F : GraphPresentation Pos → Value) :
    IsGraphInvariant F ↔ FactorsThroughSemantic F :=
  ⟨factorsThroughSemantic_of_graphInvariant, graphInvariant_of_factorsThroughSemantic⟩

/-- The raw number of occupied storage nodes. -/
noncomputable def graphNodeCount {Pos : Type u} (G : GraphPresentation Pos) : ℕ :=
  Nat.card G.Node

/-- Two atomic nodes over the discrete two-position semantic pangenome. -/
def splitNodeWitness : GraphPresentation (Fin 2) :=
  atomicGraph (discretePresentation (Fin 2))

/-- One merged node over exactly the same discrete two-position semantic pangenome. -/
def mergedNodeWitness : GraphPresentation (Fin 2) where
  semantic := discretePresentation (Fin 2)
  Node := Unit
  block := fun _ ↦ ()
  block_onto := fun y ↦ by
    cases y
    exact ⟨(discretePresentation (Fin 2)).encode 0, rfl⟩

/-- The split and merged witnesses are equivalent because their semantic layer is identical. -/
theorem split_merged_equivalent : GraphEquivalent splitNodeWitness mergedNodeWitness :=
  ⟨Iso.refl _⟩

/-- **Raw graph-node count is not representation-invariant.**  A lossless merge takes the
same two semantic coordinates from two storage nodes to one. -/
theorem graphNodeCount_not_invariant :
    ¬ IsGraphInvariant (graphNodeCount : GraphPresentation (Fin 2) → ℕ) := by
  intro h
  have hcount := h splitNodeWitness mergedNodeWitness split_merged_equivalent
  norm_num [graphNodeCount, splitNodeWitness, mergedNodeWitness, atomicGraph,
    discretePresentation] at hcount

/-! ### The generated pangenome as a universal object -/

/-- The canonical presentation generated by an alignment relation. -/
def closurePresentation {Pos : Type u} (A : Pos → Pos → Prop) : Presentation Pos :=
  ofSetoid (Construction.closure A)

/-- A presentation coequalises an alignment relation when every reported aligned pair is
assigned one coordinate. -/
def Coequalizes {Pos : Type u} (A : Pos → Pos → Prop) (P : Presentation Pos) : Prop :=
  Construction.Honors A P.kernel

/-- The generated presentation coequalises every reported alignment. -/
theorem closurePresentation_coequalizes {Pos : Type u} (A : Pos → Pos → Prop) :
    Coequalizes A (closurePresentation A) := by
  rw [Coequalizes, closurePresentation, kernel_ofSetoid]
  exact Construction.closure_honors A

/-- **The coequalizer universal property of pangenome construction.**

A presentation identifies every pair reported by the aligner exactly when there is a map
from the generated closure presentation into it.  The map is unique by `hom_subsingleton`.
This is the rigorous colimit statement: closure is the initial coequalising presentation,
not merely one graph assembled from the input. -/
theorem closurePresentation_universal {Pos : Type u} (A : Pos → Pos → Prop)
    (P : Presentation Pos) :
    Coequalizes A P ↔ Nonempty (closurePresentation A ⟶ P) := by
  rw [Coequalizes, Construction.honors_iff_closure_le,
    nonempty_hom_iff_kernel_le, closurePresentation, kernel_ofSetoid]

end Presentation

end Descent.Pangenome
