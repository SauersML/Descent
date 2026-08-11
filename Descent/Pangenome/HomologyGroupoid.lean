/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Chart
import Descent.Pangenome.Presentation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Witness-valued homology and its coarse pangenome

The witness-valued object is the ordinary Mathlib `Groupoid` already produced by
`GroupoidPresentation` and `ChartGroupoidRelation`; this file does not define a second groupoid
structure.  It defines the one operation needed by the coarse presentation theory:
propositionally truncate each Hom-type to the assertion that at least one homology witness exists.

For any groupoid `C`, `coarseSetoid C` relates `x` and `y` exactly when `x ⟶ y` is inhabited,
and `coarsePresentation C` presents that relation.  `coarsePresentationOfCharts` is the explicit
bridge from the finite chart core to `Presentation`.  Consequently the finite partial-bijection
atlas, its quotient groupoid, and the representation-invariant coarse pangenome form one pipeline
rather than three parallel models.

This is deliberately a one-way operation: representation-invariant coarse statistics use the
resulting kernel, while symmetry calculations stay on the witness-valued chart groupoid.
-/

namespace Descent.Pangenome

open CategoryTheory
open Descent.Core

universe u v

namespace HomologyGroupoid

/-- Propositional truncation of a groupoid.  It remembers that a witness exists and forgets
which witness, how many witnesses, and the isotropy action on them. -/
def coarseSetoid (C : Type u) [Groupoid.{v} C] : Setoid C where
  r x y := Nonempty (x ⟶ y)
  iseqv := by
    refine ⟨fun x ↦ ⟨𝟙 x⟩, ?_, ?_⟩
    · rintro x y ⟨f⟩
      exact ⟨Groupoid.inv f⟩
    · rintro x y z ⟨f⟩ ⟨g⟩
      exact ⟨f ≫ g⟩

/-- The ordinary pangenome presentation obtained by forgetting homology witnesses. -/
def coarsePresentation (C : Type u) [Groupoid.{v} C] : Presentation C :=
  Presentation.ofSetoid (coarseSetoid C)

/-- Coarse presentation records exactly the existence of a groupoid arrow. -/
@[simp]
theorem kernel_coarsePresentation (C : Type u) [Groupoid.{v} C] :
    (coarsePresentation C).kernel = coarseSetoid C :=
  Presentation.kernel_ofSetoid (coarseSetoid C)

/-- The coarse presentation of the exact chart groupoid.  This is the single bridge from the
finite atlas core to the representation-invariant semantic quotient. -/
abbrev coarsePresentationOfCharts {I : Type u} (P : ChartGroupoidRelation I) :
    Presentation P.Obj :=
  coarsePresentation P.Obj

end HomologyGroupoid

end Descent.Pangenome
