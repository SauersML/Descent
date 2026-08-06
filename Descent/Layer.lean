/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# The layer order, as a compile error

**Depth 0. Imports `Lean` and nothing else -- not Mathlib, not `Core`.**

## What this is for

This corpus has a layer order:

    Core < Meta < Foundations < Coalescent < Pangenome < PopGen < Spectral
         < Blindness < Conditionals < Portability < Decision < Program

and until now it had it the way a corpus usually has one: as a fact an audit could
establish about the import graph after the fact. An audit finds a violation once someone
runs it, names a number, and leaves the repair to a later pass. Forty-two edges ran the
wrong way when this file was written, thirteen of them from `PopGen` into `Portability`,
five of those inside `PopulationGeneticsFoundations` -- the population-genetics foundations
depending on the portability layer built on top of them.

`assert_below` makes the next one a compile error in the file that commits it.

## Why not `assert_not_imported`

Mathlib has `assert_not_imported`, and it checks EXACT module names. A layer is not a
module: `Descent.Portability` is sixty-seven files, and naming them all in every file that
owes the assertion is a list that goes stale the first time someone adds a file -- silently,
in the direction of passing.

`assert_below` takes the layer's NAMESPACE and fails on any imported module beneath it, so a
new file in a layer is covered by every assertion already written. That is the property that
makes it a gate rather than a snapshot.

## Why not `assert_not_exists`

`assert_not_exists` names a DECLARATION. Renaming that declaration disables the guard and
nothing says so -- the failure direction is "passes", which is the one a guard may never
fail in. A module name is not renamed by an ordinary refactor, and when it is, the import
line that would have to change is in the same commit.

## What it does not do

It says nothing about which layer the FILE is in; a file asserts the layers it is above and
that assertion is written by hand. There is no ledger of layer membership here to disagree
with the directory structure, because the directory structure IS the membership and a second
record of it could only be wrong.
-/

namespace Descent

open Lean Elab Command

/-- `assert_below Descent.Portability Descent.Program` fails to compile if any module whose
name lies under one of the given namespaces is among this module's transitive imports.

The whole layer is covered, not a list of its files: a module added to
`Descent.Portability` tomorrow is caught by every `assert_below Descent.Portability` written
today. Report names the offending modules, capped so a file that has drifted a long way
gives a readable error rather than a wall. -/
elab "assert_below " ids:ident+ : command => do
  let imported := (← getEnv).allImportedModuleNames
  for id in ids do
    let layer := id.getId
    let bad := imported.filter fun m ↦ layer.isPrefixOf m
    unless bad.isEmpty do
      let shown := bad.toList.take 6
      let more := if bad.size > 6 then s!" (and {bad.size - 6} more)" else ""
      let names := String.intercalate ", " (shown.map toString)
      throwError "layer order: this module is below `{layer}` and imports \
        {bad.size} module(s) from it: {names}{more}.\n\n\
        Either the import is wrong -- move the declaration it reaches for DOWN to the \
        lowest layer that can state it -- or this file belongs in a higher layer and the \
        assertion above it is the thing to change. Do not delete the assertion to make \
        the build pass; a layer order nothing enforces is the arrangement this command \
        exists to end."

end Descent
