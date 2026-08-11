/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.FiniteGroupoidFunctor
import Descent.Pangenome.PartialBijectionSandwich
import Mathlib.Algebra.Order.BigOperators.Group.Finset

assert_below Descent.Coalescent Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# Pangenome charts and their biological groupoid

This is the shared core of the symmetry theory.

A `PangenomeChart` is a finite set of genomic anchors or blocks together with a nonnegative
mass.  It contains no graph-builder annotations and no speculative biological features.
A chart arrow is a `FinitePartialBijection`: an honest bijection between the homologous
subsets that are actually supported.  Deletions, duplications and unresolved regions remain
outside its source or target rather than being forced into a total coordinate map.

`ChartGroupoidRelation` is the one semantic input.  It says when two finite representatives
encode the same biological correspondence and requires the category laws only modulo that
relation.  `ChartGroupoidRelation.toPresentation` then invokes the generic quotient engine
from `FiniteGroupoidPresentation`: messy finite representatives become an exact Mathlib
groupoid.

Finally, `BridgeFunctorData` specializes functor descent to the sandwich construction.
Bridges `u_X : X ⇸ F(X)` transport an arrow `f : X ⇸ Y` to
`u_X⁻¹ · f · u_Y`.  Once the quantitative sandwich bounds establish the three stated
relation facts, `toFunctor` gives an honest functor of pangenome groupoids, and reflection of
the relation gives faithfulness.
-/

namespace Descent.Pangenome

open CategoryTheory

universe u

/-- A finite genomic chart with a nonnegative mass on every anchor or block.  Counting mass,
base-pair length and information weight are instances of the same field. -/
structure PangenomeChart where
  carrier : FiniteModel
  mass : carrier → ℝ
  mass_nonnegative : ∀ x, 0 ≤ mass x

instance chartCoeSort : CoeSort PangenomeChart Type := ⟨fun X ↦ X.carrier⟩

@[reducible, instance]
def chartFintype (X : PangenomeChart) : Fintype X := X.carrier.fintype

@[reducible, instance]
def chartDecidableEq (X : PangenomeChart) : DecidableEq X := X.carrier.decidableEq

/-- Total genomic mass carried by a finite set of chart points. -/
noncomputable def PangenomeChart.massOf (X : PangenomeChart) (s : Finset X) : ℝ :=
  ∑ x ∈ s, X.mass x

/-- The counting-mass chart on a finite carrier. -/
def PangenomeChart.counting (X : FiniteModel) : PangenomeChart where
  carrier := X
  mass := fun _ ↦ 1
  mass_nonnegative := fun _ ↦ zero_le_one

/-- A correspondence between charts is a bijection between explicitly supported subsets. -/
abbrev ChartMap (X Y : PangenomeChart) := FinitePartialBijection X.carrier Y.carrier

namespace ChartMap

variable {X Y Z : PangenomeChart}

/-- A chart map preserves genomic mass on every matched point. -/
def MassPreserving (f : ChartMap X Y) : Prop :=
  ∀ x (hx : x ∈ f.source), Y.mass (f.apply x hx) = X.mass x

/-- Mass missing from the source of a partial genomic correspondence. -/
noncomputable def sourceDefectMass (f : ChartMap X Y) : ℝ :=
  X.massOf (Finset.univ \ f.source)

/-- Mass missing from the target of a partial genomic correspondence. -/
noncomputable def targetDefectMass (f : ChartMap X Y) : ℝ :=
  Y.massOf (Finset.univ \ f.target)

/-- Inverse-symmetric, mass-weighted discrepancy between two chart maps. -/
noncomputable def twoSidedMassDisagreement (f g : ChartMap X Y) : ℝ :=
  X.massOf (f.disagreement g) + Y.massOf (f.symm.disagreement g.symm)

@[simp]
theorem sourceDefectMass_symm (f : ChartMap X Y) :
    sourceDefectMass f.symm = targetDefectMass f :=
  rfl

@[simp]
theorem targetDefectMass_symm (f : ChartMap X Y) :
    targetDefectMass f.symm = sourceDefectMass f :=
  rfl

theorem twoSidedMassDisagreement_comm (f g : ChartMap X Y) :
    twoSidedMassDisagreement f g = twoSidedMassDisagreement g f := by
  unfold twoSidedMassDisagreement
  rw [FinitePartialBijection.disagreement_comm f g]
  exact congrArg (fun s ↦ X.massOf (g.disagreement f) + Y.massOf s)
    (FinitePartialBijection.disagreement_comm f.symm g.symm)

/-- Counting mass recovers the original cardinality discrepancy exactly. -/
theorem twoSidedMassDisagreement_counting (A B : FiniteModel)
    (f g : ChartMap (PangenomeChart.counting A) (PangenomeChart.counting B)) :
    twoSidedMassDisagreement f g = f.twoSidedDisagreement g := by
  simp [twoSidedMassDisagreement, PangenomeChart.massOf,
    PangenomeChart.counting, FinitePartialBijection.twoSidedDisagreement]

end ChartMap

/-! ### Quotienting finite chart maps to the biological groupoid -/

/-- Semantic equivalence data sufficient to turn partial chart correspondences into an exact
groupoid.  The operations are the canonical partial-bijection identity, composition and
inverse; only the relation and the laws modulo it are supplied by an application. -/
structure ChartGroupoidRelation (I : Type u) where
  chart : I → PangenomeChart
  rel : ∀ X Y, Setoid (ChartMap (chart X) (chart Y))
  comp_respects : ∀ {X Y Z} {f f' : ChartMap (chart X) (chart Y)}
      {g g' : ChartMap (chart Y) (chart Z)},
    rel X Y f f' → rel Y Z g g' → rel X Z (f.trans g) (f'.trans g')
  inv_respects : ∀ {X Y} {f f' : ChartMap (chart X) (chart Y)},
    rel X Y f f' → rel Y X f.symm f'.symm
  one_comp : ∀ {X Y} (f : ChartMap (chart X) (chart Y)),
    rel X Y ((FinitePartialBijection.refl (chart X).carrier).trans f) f
  comp_one : ∀ {X Y} (f : ChartMap (chart X) (chart Y)),
    rel X Y (f.trans (FinitePartialBijection.refl (chart Y).carrier)) f
  inv_comp : ∀ {X Y} (f : ChartMap (chart X) (chart Y)),
    rel Y Y (f.symm.trans f) (FinitePartialBijection.refl (chart Y).carrier)
  comp_inv : ∀ {X Y} (f : ChartMap (chart X) (chart Y)),
    rel X X (f.trans f.symm) (FinitePartialBijection.refl (chart X).carrier)

namespace ChartGroupoidRelation

variable {I : Type u}

/-- The generic representative presentation underlying a pangenome chart system. -/
noncomputable def toPresentation (P : ChartGroupoidRelation I) : GroupoidPresentation I where
  Rep X Y := ChartMap (P.chart X) (P.chart Y)
  rel := P.rel
  one X := FinitePartialBijection.refl (P.chart X).carrier
  comp f g := f.trans g
  inv f := f.symm
  comp_respects := P.comp_respects
  inv_respects := P.inv_respects
  one_comp := P.one_comp
  comp_one := P.comp_one
  assoc f g h := by
    rw [FinitePartialBijection.trans_assoc]
  inv_comp := P.inv_comp
  comp_inv := P.comp_inv

/-- Objects of the exact biological groupoid presented by a chart system. -/
abbrev Obj (P : ChartGroupoidRelation I) := P.toPresentation.Obj

/-- A finite chart-map representative determines an arrow of the exact pangenome groupoid. -/
def ofMap (P : ChartGroupoidRelation I) {X Y : P.Obj}
    (f : ChartMap (P.chart X.val) (P.chart Y.val)) : X ⟶ Y :=
  P.toPresentation.ofRep f

end ChartGroupoidRelation

/-! ### Sandwich bridges descend to functors -/

/-- Exact relation-level obligations for transporting a chart groupoid through partial
bridges.  The transported representative is fixed to `FinitePartialBijection.sandwich`; the
three proof fields are precisely what its quantitative bounds are used to establish. -/
structure BridgeFunctorData {I J : Type u}
    (P : ChartGroupoidRelation I) (Q : ChartGroupoidRelation J) where
  obj : I → J
  bridge : ∀ X, ChartMap (P.chart X) (Q.chart (obj X))
  map_respects : ∀ {X Y} {f g : ChartMap (P.chart X) (P.chart Y)},
    P.rel X Y f g →
      Q.rel (obj X) (obj Y)
        (FinitePartialBijection.sandwich (bridge X) (bridge Y) f)
        (FinitePartialBijection.sandwich (bridge X) (bridge Y) g)
  map_one : ∀ X,
    Q.rel (obj X) (obj X)
      (FinitePartialBijection.sandwich (bridge X) (bridge X)
        (FinitePartialBijection.refl (P.chart X).carrier))
      (FinitePartialBijection.refl (Q.chart (obj X)).carrier)
  map_comp : ∀ {X Y Z} (f : ChartMap (P.chart X) (P.chart Y))
      (g : ChartMap (P.chart Y) (P.chart Z)),
    Q.rel (obj X) (obj Z)
      (FinitePartialBijection.sandwich (bridge X) (bridge Z) (f.trans g))
      ((FinitePartialBijection.sandwich (bridge X) (bridge Y) f).trans
        (FinitePartialBijection.sandwich (bridge Y) (bridge Z) g))

namespace BridgeFunctorData

variable {I J : Type u} {P : ChartGroupoidRelation I} {Q : ChartGroupoidRelation J}

/-- A bridge supplies the generic representative-level functor data. -/
noncomputable def toFunctorData (D : BridgeFunctorData P Q) :
    GroupoidPresentation.FunctorData P.toPresentation Q.toPresentation where
  obj := D.obj
  map f := FinitePartialBijection.sandwich (D.bridge _) (D.bridge _) f
  map_respects := D.map_respects
  map_one := D.map_one
  map_comp := D.map_comp

/-- **Representation bridge theorem.**  Compatible partial chart bridges induce an honest
functor between the quotient pangenome groupoids. -/
noncomputable def toFunctor (D : BridgeFunctorData P Q) : P.Obj ⥤ Q.Obj :=
  D.toFunctorData.toFunctor

/-- If sandwich transport also reflects biological equivalence, the induced pangenome
functor is faithful. -/
noncomputable def faithful (D : BridgeFunctorData P Q)
    (hreflects : ∀ {X Y} {f g : ChartMap (P.chart X) (P.chart Y)},
      Q.rel (D.obj X) (D.obj Y)
        (FinitePartialBijection.sandwich (D.bridge X) (D.bridge Y) f)
        (FinitePartialBijection.sandwich (D.bridge X) (D.bridge Y) g) →
      P.rel X Y f g) : D.toFunctor.Faithful :=
  D.toFunctorData.faithful hreflects

end BridgeFunctorData

end Descent.Pangenome
