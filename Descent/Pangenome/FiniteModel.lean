/-
Released under Apache 2.0 license as described in the file LICENSE.

The bundled finite carrier and Hamming primitives are adapted from
SauersML/nonsofic_existence, `NonsoficGroupsExist/Sofic/Sofic.lean`.
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Support
import Descent.Layer

assert_below Descent.Coalescent Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# Finite carriers and Hamming discrepancy

`FiniteModel` is the carrier used by the quantitative pangenome machinery.  Bundling the
finite type and decidable equality makes source and target charts first-class objects while
leaving all genomic interpretation to structures built above it.
-/

namespace Descent.Pangenome

/-- A finite type bundled with the instances required by partial bijections and permutation
models. -/
structure FiniteModel where
  carrier : Type
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

instance finiteModelCoeSort : CoeSort FiniteModel Type := ⟨FiniteModel.carrier⟩

@[reducible, instance]
def finiteModelFintype (Y : FiniteModel) : Fintype Y := Y.fintype

@[reducible, instance]
def finiteModelDecidableEq (Y : FiniteModel) : DecidableEq Y := Y.decidableEq

/-- Points on which two permutations of a finite carrier disagree. -/
def hammingDisagreement {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun y ↦ p y ≠ q y

@[simp]
theorem mem_hammingDisagreement {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) (y : Y) :
    y ∈ hammingDisagreement p q ↔ p y ≠ q y := by
  simp [hammingDisagreement]

/-- Normalized Hamming distance.  The empty carrier has distance zero; nonempty hypotheses
are stated by approximation structures that need a genuine panel. -/
noncomputable def hammingDistance (Y : FiniteModel) (p q : Equiv.Perm Y) : ℝ :=
  ((hammingDisagreement p q).card : ℝ) / Fintype.card Y

@[simp]
theorem hammingDistance_self (Y : FiniteModel) (p : Equiv.Perm Y) :
    hammingDistance Y p p = 0 := by
  simp [hammingDistance, hammingDisagreement]

end Descent.Pangenome
