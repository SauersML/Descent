/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Data.Fintype.Card

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

/-!
# Finite carriers

`FiniteModel` bundles a type with the `Fintype` and `DecidableEq` instances that
every counting argument about it needs, so that a statement quantifying over
finite carriers does not have to carry two instance arguments everywhere.

This is the only thing `FinitePartialBijection` used from its old home. The file it
came from is a 433-line development of soficity -- local finite-permutation
approximations, Hamming distances between permutations, sequential models -- none of
which the partial-bijection combinatorics touches. Taking the twelve lines and
leaving the rest is the whole reason this library does not import a theory of sofic
groups to talk about partial matchings.
-/

namespace Descent.Core

/-- A type equipped with the finiteness and decidability its counting arguments
need. -/
structure FiniteModel where
  /-- The underlying type. -/
  carrier : Type
  /-- Finiteness of the carrier. -/
  fintype : Fintype carrier
  /-- Decidable equality on the carrier. 
## Provenance

Extracted from github.com/SauersML/nonsofic_existence (Apache 2.0, same
owner). Original path: `NonsoficGroupsExist/Sofic/Sofic.lean`, the `FiniteModel`
bundle only.
-/
  decidableEq : DecidableEq carrier

instance finiteModelCoeSort : CoeSort FiniteModel Type := ⟨FiniteModel.carrier⟩

@[reducible, instance] def finiteModelFintype (Y : FiniteModel) : Fintype Y :=
  Y.fintype

@[reducible, instance] def finiteModelDecidableEq (Y : FiniteModel) : DecidableEq Y :=
  Y.decidableEq

end Descent.Core
