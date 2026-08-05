/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Elab.Command
import Lean.DocString
import Descent.Meta.DocConvention

/-!
# A command linter for the status convention

The environment linters in `Descent.Meta.Linters` answer when someone runs
`validation/code/Lint.lean`.  This one answers while a person is typing, at the
line they typed, because two of the status rules need nothing but the text of
the docstring in front of them and there is no reason to make a person ask.

NONE OF THIS HAS BEEN COMPILED.  It follows the shape of Mathlib's `docPrime`
linter at the pinned revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` and
every core name in it was read out of the pinned toolchain's sources, but no
build has accepted it.

## It is off, and where it looks

`linter.descentEmpiricalStatus` defaults to FALSE.  Switching an unproven check
on across 150,000 never-linted lines produces warnings by the thousand, and a
corpus that scrolls past thousands of warnings has been taught to read warnings
as scenery -- which is the blindness this corpus exists to measure, installed by
the tool meant to fight it.  Turn it on for a file with `set_option`, or for the
library in `lakefile.lean`, once a build has accepted the module and once the
findings on a directory have been read by a person.

A COMMAND LINTER ONLY SEES MODULES THAT IMPORT IT.  Nothing under `Descent/`
imports this module today except the `Descent.Meta` head, so switching the
option on right now would lint the head and nothing else.  Making it reach the
corpus means putting the import somewhere every module already depends on, and
that is a change to the import graph rather than to this file.

## What it checks, and what it does not

Two rules, both purely textual, both also held by `check.py`'s `conventions`
guard:

  * a docstring stating more than one status -- every scanner reads the first,
    so a superseded marker above a current one IS the reported verdict;
  * a status head outside the closed vocabulary in
    `Descent.Meta.DocConvention.vocabulary`.

It does NOT see module-level doc sections, which parse as a different command,
and the Python scan does see them.  It does not join against the ledger; nothing
in Lean can.  See `Descent.Meta.Linters` for why.
-/

open Lean Elab Linter

namespace Descent.Meta

/-- Report docstrings whose status marker is repeated or whose head is outside
the closed vocabulary. -/
register_option linter.descentEmpiricalStatus : Bool := {
  defValue := false
  descr := "enable the Descent empirical-status docstring linter"
}

namespace StatusLinter

open Descent.Meta.DocConvention

/-- The first complaint the status convention has about `text`, if any. -/
def complaint (text : String) : Option MessageData :=
  let heads := statusHeads text
  if heads.length > 1 then
    let spelled := String.intercalate ", " heads
    some m!"this docstring carries {heads.length} status markers ({spelled}); \
      every scanner reads the first, so the others are invisible and the first \
      may not be the current verdict"
  else
    match (heads.filter fun head ↦ !headIsTerm head).head? with
    | none => none
    | some head =>
        match miscasedTerm head with
        | some canonical =>
            some m!"status head {head} is {canonical} in the wrong case; one \
              verdict under two spellings cannot be counted"
        | none =>
            some m!"status head {head} is not in the vocabulary; use an \
              existing term, or adjudicate a new one INTO \
              `empirical_status_vocabulary` rather than beside it"

@[inherit_doc Descent.Meta.linter.descentEmpiricalStatus]
def statusLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.descentEmpiricalStatus (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  unless [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind do
    return
  let docKind := ``Lean.Parser.Command.docComment
  let some doc := stx.find? (·.isOfKind docKind) | return
  let text ← getDocStringText ⟨doc⟩
  match complaint text with
  | none => return
  | some msg => Linter.logLint linter.descentEmpiricalStatus doc msg

initialize addLinter statusLinter

end StatusLinter

end Descent.Meta
