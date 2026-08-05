/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic

/-!
# Core: the two populations

**Depth 0. Imports Mathlib and nothing else.**

`Pop` is a corpus-wide type rather than a kernel shape, so it keeps the `Descent`
namespace it has always had: this file MOVES it to the bottom of the import graph, it
does not rename it. Every existing `Pop.pair` and `Pop.source` reads unchanged.

It used to live in `Foundations/Probability`, which is low in the graph but not at the
bottom: it imports Mathlib's measure theory, its probability mass functions and its
information theory, so a module that wanted only to say WHICH POPULATION it meant had to
take all of that with it. Saying which of two populations a quantity belongs to needs no
measure theory.

## What this is not

`Pop` is not a population. It is an INDEX over two of them, and the point of indexing is
that a source-and-target pair of quantities becomes one function rather than two fields
whose agreement is carried only by their names.

The corpus has two other things called populations, and they are not this and not each
other:

  * `Program.Conclusions.BinaryPopulation` -- a pair of measures, cases and controls, on
    which an AUC is an integral. It has no source/target structure at all.
  * `Portability.DeploymentPopulation` -- an expectation functional together with genotype codings,
  causal effects and a residual. It is a whole model.

A census that saw three names containing "population" and proposed collapsing them would
be reading the word and not the type. They are kept apart, and this note is why.
-/

namespace Descent

/-- **Which population a quantity is evaluated in.**

Every cross-population quantity in this development is a function of this index rather
than a pair of separately written definitions. That is not cosmetic: when the source and
target forms are written twice, the fact that they are the *same* quantity is carried only
by their names, and nothing forces the two bodies to stay in step. Indexing makes the
shared content one object and leaves only the genuine asymmetries to be stated — and to be
discharged — explicitly.

It lives here, at the base of the import graph, because it is used by the transport, the
calibration and the confounding modules alike, none of which should have to depend on each
other to say which population they mean. -/
inductive Pop where
  | source
  | target
  deriving DecidableEq, Repr

/-- A population-indexed value given by its two components. Model literals supply their
fields with this, so a field that genuinely differs between populations still reads as one
line rather than two. -/
def Pop.pair {α : Sort*} (s t : α) (p : Pop) : α :=
  match p with
  | Pop.source => s
  | Pop.target => t

@[simp] theorem Pop.pair_source {α : Sort*} (s t : α) : Pop.pair s t Pop.source = s := rfl

@[simp] theorem Pop.pair_target {α : Sort*} (s t : α) : Pop.pair s t Pop.target = t := rfl

/-- Replace the target component of a population-indexed value, keeping the source one.
Witness models that perturb exactly one population are written with this. -/
def Pop.withTarget {α : Sort*} (f : Pop → α) (t : α) : Pop → α := Pop.pair (f Pop.source) t

@[simp] theorem Pop.withTarget_source {α : Sort*} (f : Pop → α) (t : α) :
    Pop.withTarget f t Pop.source = f Pop.source := rfl

@[simp] theorem Pop.withTarget_target {α : Sort*} (f : Pop → α) (t : α) :
    Pop.withTarget f t Pop.target = t := rfl

/-- A real vector of length `n`.

`PopGen.DGP` carried this twice, as `CausalVec` and `TagVec`. The two names are worth
keeping -- a causal-effect vector and a tag-weight vector are indexed by different things
and a theorem that swapped them would be wrong -- but the TYPE is one type, and writing
it twice meant a change to the coding convention had two places to reach.

Lean's abbreviations are transparent, so this buys no type safety: `CausalVec c` and
`TagVec c` are interchangeable to the elaborator either way. What it buys is that the
convention has one home. -/
abbrev RealVec (n : ℕ) := Fin n → ℝ

/-- **`CausalVec` and `TagVec` are the same type, and that is the point.**

Both abbreviate this, so the elaborator finds them interchangeable: a theorem about one
applies to the other and a caller can pass either. The distinction between a causal-effect
vector and a tag-weight vector is DOCUMENTARY, carried by the names and by the index sets
their callers use, and nothing in the type system enforces it.

Stating it is what stops the names being read as a guarantee. A corpus that wanted the
guarantee would need two one-field structures, as `Core.Fst` does for `NeiFst` and
`HudsonFst` -- and there the guarantee was worth its cost because substituting one for the
other is a measured factor-of-two-to-four error. Here the index sets differ, so the
mistake does not typecheck for a different reason, and the abbreviation is enough. -/
theorem realVec_is_one_type (n : ℕ) : RealVec n = (Fin n → ℝ) := rfl

/-- **A two-state index**, for a witness that contrasts exactly two of something.

`Conditionals.DynamicsContrast` abbreviated `Fin 2` as `BinaryBiologicalState` and
`Conditionals.FunctionalDescent` abbreviated it as `BinaryDescentCovariate`, in sibling
modules neither of which imports the other. Same type, same purpose -- two states a witness
contrasts -- named twice because neither module could see the other's name.

The same reading as `RealVec` above applies: this is transparent, so it buys no type
safety, and the biological reading each module attaches -- a context, a covariate -- stays
documentary and stays in that module. What it buys is that `Fin 2` is not independently
renamed a third time. -/
abbrev BinaryState := Fin 2

end Descent
