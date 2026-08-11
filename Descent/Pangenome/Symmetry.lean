/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.HomologyGroupoid
import Descent.Core.BisectionWreath

assert_below Descent.Coalescent Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# Symmetries of a pangenome chart groupoid

This module adds no second notion of correspondence, groupoid, or wreath product.  A chart
system already produces one exact Mathlib groupoid: its arrows are biological equivalence
classes of finite partial-bijection representatives.  Its global symmetries are therefore
its bisections.

For a connected chart groupoid, the shared bisection theorem gives the exact local structure

`Bis(P.Obj) ≃ Aut_P(X) ≀ Sym(P.Obj)`.

The left factor is one self-homology group element at every equivalent chart object; the
right factor exchanges those objects.  The theorem requires chosen transport arrows, making
the biological exchangeability assumption explicit rather than inferring it from sequence
similarity.
-/

namespace Descent.Pangenome

open CategoryTheory

universe u

/-- Global structural symmetries of the exact groupoid presented by a chart system. -/
abbrev ChartSymmetry {I : Type u} (P : ChartGroupoidRelation I) :=
  Descent.Core.FiniteGroupoid.Bisection P.Obj

/-- Local structural symmetry at one object of the exact chart groupoid. -/
abbrev ChartIsotropy {I : Type u} (P : ChartGroupoidRelation I) (X : P.Obj) :=
  X ⟶ X

/-- **Local wreath decomposition for pangenome charts.**  Chosen homology transports from
`X` to every chart object identify global structural symmetries with independent local
isotropy states together with permutations of the equivalent objects. -/
noncomputable def chartSymmetryEquivWreath {I : Type u} (P : ChartGroupoidRelation I)
    (X : P.Obj) (transport : ∀ Y : P.Obj, X ⟶ Y) :
    ChartSymmetry P ≃* Descent.Core.Wreath (ChartIsotropy P X) P.Obj :=
  Descent.Core.FiniteGroupoid.Bisection.mulEquivWreath X transport

/-- Connectedness is exactly the hypothesis needed for a chart symmetry wreath
decomposition; the transports can then be chosen noncomputably. -/
theorem nonempty_chartSymmetryEquivWreath {I : Type u} (P : ChartGroupoidRelation I)
    (X : P.Obj) (connected : ∀ Y : P.Obj, Nonempty (X ⟶ Y)) :
    Nonempty (ChartSymmetry P ≃* Descent.Core.Wreath (ChartIsotropy P X) P.Obj) :=
  Descent.Core.FiniteGroupoid.nonempty_bisection_mulEquiv_wreath X connected

end Descent.Pangenome
