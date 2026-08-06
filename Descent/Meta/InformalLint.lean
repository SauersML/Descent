/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Meta.Informal

assert_below Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

/-!
# The gap report

`#informal_report` prints the ledger `Descent.Meta.Informal` collects and, in the one case
that is a contract violation rather than a state of the work, fails.

## What it is for

The question worth asking of a gap is not "is it still open" -- the author knows that --
but **has it become closeable without anyone noticing**.  A gap records the names it waits
on; the corpus grows those names elsewhere, in a module whose author never read the gap;
and nothing connects the two events.  That is the state this report finds: every dep of
some `informal_lemma` is now a constant in the environment, so the work it describes has
no missing prerequisite left.

## Which axis it measures, and where it is blind

`Descent.lean` records three ways a check can be dead -- it cannot fire, it fires on the
wrong axis, or its condition is inert -- and one of them is a live hazard here.  A gap with
an EMPTY deps list has vacuously closed deps, so a naive "all deps closed" test reports
every such gap as ready, forever, and the real signal drowns.  Ready-to-close is therefore
defined as **a non-empty deps list, all of it closed**, and gaps with no deps are reported
separately and honestly as unblocked-because-nothing-was-recorded.  That is not the same
finding and this file does not conflate them.

Where it is blind, stated so nobody reads a clean report as more than it is: a dep is
closed when a constant of that name exists, and nothing checks that the constant says what
the gap wanted.  A dep naming something that will never exist is indistinguishable from one
naming something not written yet, which is `Descent.lean`'s "a search string that does not
match is indistinguishable from an absent feature" in its native habitat.  The report
cannot tell those apart and does not pretend to.

## The one hard failure

A duplicate tag is a defect rather than a state of the work: the tag is the gap's identity,
citations are by tag, and two gaps under one tag make every citation of it ambiguous.  That
is `logError`, so the build fails at whoever runs the report.  It is not thrown when the
gap is declared, because a collision is caused by two files jointly and throwing in the
second one blames a file that did nothing wrong.

## Unverified

NOT COMPILED -- see the header of `Descent.Meta.Informal`.  This file is separate from that
one so that a defect here can be deleted without taking the recording commands, which
content modules import, with it.
-/

namespace Descent.Meta

open Lean Elab Command

/-- One ledger line: the tag, the name it is filed under, and where it was written. -/
def GapInfo.locator (g : GapInfo) : String :=
  let named := if g.name == Name.anonymous then "" else s!" {g.name}"
  let where_ := if g.line == 0 then s!"{g.fileName}" else s!"{g.fileName}:{g.line}"
  s!"  [{g.tag}] {g.kind.label}{named}  ({where_})"

/-- The tags carried by more than one gap.  Each is listed once. -/
def duplicateTags (gaps : Array GapInfo) : Array String := Id.run do
  let mut seen : Array String := #[]
  let mut dups : Array String := #[]
  for g in gaps do
    if seen.contains g.tag then
      if !dups.contains g.tag then
        dups := dups.push g.tag
    else
      seen := seen.push g.tag
  return dups

/-- The whole report, as a string, so that the elaborator below does nothing but print it
and decide whether to fail. -/
def gapReport (env : Environment) : String := Id.run do
  let gaps := allGaps env
  let mut nDef := 0
  let mut nLem := 0
  let mut nSemi := 0
  let mut nTodo := 0
  let mut nWith := 0
  let mut ready : Array String := #[]
  let mut blocked : Array String := #[]
  let mut undeclared : Array String := #[]
  for g in gaps do
    match g.kind with
    | .informalDefinition => nDef := nDef + 1
    | .informalLemma => nLem := nLem + 1
    | .semiformal => nSemi := nSemi + 1
    | .todo => nTodo := nTodo + 1
    | .withdrawn => nWith := nWith + 1
    let open_ := openDeps env g
    if g.deps.isEmpty then
      undeclared := undeclared.push g.locator
    else if open_.isEmpty then
      ready := ready.push g.locator
    else
      blocked := blocked.push
        (g.locator ++ "\n      waiting on: "
          ++ String.intercalate ", " (open_.map (fun d ↦ toString d)))
  let mut out := s!"Descent gap ledger: {gaps.size} objects\n"
  out := out ++ s!"  informal_definition: {nDef}\n"
  out := out ++ s!"  informal_lemma: {nLem}\n"
  out := out ++ s!"  semiformal_result: {nSemi}\n"
  out := out ++ s!"  TODO: {nTodo}\n"
  out := out ++ s!"  withdrawn: {nWith}\n"
  out := out ++ s!"\nREADY TO CLOSE ({ready.size}) -- every recorded dep is now a constant:\n"
  for l in ready do
    out := out ++ l ++ "\n"
  out := out ++ s!"\nBLOCKED ({blocked.size}):\n"
  for l in blocked do
    out := out ++ l ++ "\n"
  out := out ++ s!"\nNO DEPS RECORDED ({undeclared.size}) -- unblocked, or unexamined:\n"
  for l in undeclared do
    out := out ++ l ++ "\n"
  return out

/-- Syntax for the `#informal_report` command. -/
syntax (name := informalReportCmd) "#informal_report" : command

/-- Elaborator for `#informal_report`.  Prints the ledger, and fails only on a duplicate
tag, which is the one thing in it that is a defect rather than a state of the work.

It must be invoked from a module that imports the corpus, because a gap is recorded in the
module that declares it and this one sits at the bottom of the layer order: run from here it
would truthfully report zero, which is the shape of report `Descent.lean` warns about. -/
@[command_elab informalReportCmd]
def elabInformalReport : CommandElab := fun _ ↦ do
  let env ← getEnv
  logInfo m!"{gapReport env}"
  let dups := duplicateTags (allGaps env)
  unless dups.isEmpty do
    let names := String.intercalate ", " dups.toList
    logError m!"gap ledger: {dups.size} duplicated tag(s): {names}"

end Descent.Meta
