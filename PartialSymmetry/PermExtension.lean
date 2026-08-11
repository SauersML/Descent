/-
Released under Apache 2.0 license as described in the file LICENSE.

`Equiv.Perm.exists_extending_pair` is BACKPORTED FROM MATHLIB (Apache 2.0,
Mathlib contributors), file `Mathlib/Logic/Equiv/Fintype.lean`. It postdates the
Mathlib revision this repository pins, so it is restated here rather than imported.
-/
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Set

/-!
# Extending a pair of injections to a permutation

Two injections of the same finite type into a common target are related by a
permutation of the target: whatever `f` labels, `g` relabels, and the difference can
be realized by moving the target around.

This is Mathlib's `Equiv.Perm.exists_extending_pair`, which does not exist at the
Mathlib revision this repository pins -- `Equiv.extendSubtype`, which does the work,
is present, and only the wrapper was added later. The proof below is Mathlib's.

It is what turns a partial matching into a total one: a partial bijection is exactly
a pair of injections out of its source (the inclusion, and the map to the target),
so extending it to a permutation is this lemma applied to that pair. That is the use
in `PartialSymmetry.FinitePartialBijection.exists_extension`.
-/

namespace PartialSymmetry

open Equiv

universe u v

/-- **Two injections from a finite type are related by a permutation of the target.**
Backported from Mathlib; see the file header.

The target carries `Fintype` here, which is what `Equiv.extendSubtype` needs at this
Mathlib revision, and is satisfied everywhere this library uses it. -/
theorem perm_exists_extending_pair {α : Type u} {β : Type v} [Finite α] [Fintype β]
    (f g : α → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : Equiv.Perm β, ∀ a, σ (f a) = g a := by
  classical
  have : Finite {x | x ∈ Set.range f} :=
    .of_surjective _ (Set.codRestrict_range_surjective f)
  refine ⟨((Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)).extendSubtype, ?_⟩
  simp [Equiv.extendSubtype_apply_of_mem]

end PartialSymmetry
