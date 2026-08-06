/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Elab.Command
import Descent.Layer

assert_below Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

/-!
# Gaps as objects

A "TODO" IS THE MOST AUTHORITATIVE-LOOKING SENTENCE IN A CODEBASE.  `Descent.lean` says
so at length, and gives the specimen: a paragraph in `Conventions.lean` told the next
agent that a collapse to one name "is the fix and has not been done", was written from a
name census before the bodies had been read, survived three commits looking like a
decision already taken, and was wrong.  A deferred-work note is a claim and inherits the
error rate of the analysis that produced it, but nothing in the corpus treated it as one:
it was prose, so nothing could query it, count it, or fail because of it.

This file makes a gap a **queryable object that cannot be used**.  The design is
PhysLean's, which faced the same problem in a physics corpus and solved it with
`informal_definition`, `informal_lemma`, `semiformal_result` and a tagged `TODO`.  Four
properties are what matter, and each is why one of the decisions below was taken.

**A gap is data, not a declaration.**  `TODO "tag" "text"` and `informal_lemma` push a
record into an environment extension; they add no constant to the environment.  So there
is nothing for a downstream proof to cite -- not a `sorry`, not an axiom, not an opaque
constant.  The alternative everyone reaches for first, a `sorry`d lemma, is exactly the
thing that must not exist here, because a `sorry`d lemma IS usable and the corpus would
then contain results resting on an unproved claim with only a warning to say so.

PhysLean does emit a `def name : InformalLemma := ⟨deps, tag⟩` -- a real constant, but of
an inert record type that no proof can consume -- because its documentation pipeline
reads the declaration.  This corpus has no such pipeline, and the extension is what the
report reads, so no declaration is emitted at all.  That is a deliberate divergence from
the source, and it is the stricter of the two: the gap is not merely unusable, it is
absent from the environment.

**A gap carries a stable tag.**  Prose has no identity, so a note cannot be cited,
cross-referenced, or reported as still open.  The tag is a string chosen by the author
and never derived from the content, because a hash of the content changes when a typo is
fixed and then every citation of it is silently wrong.  `#informal_report` errors on a
duplicate tag; that is the only enforcement of uniqueness, and it is deliberately a
report rather than an elaboration-time throw, so a collision cannot break a build in a
file that did nothing wrong.

**A gap names what it waits on.**  `deps` is a list of FULLY QUALIFIED names.  A dep is
CLOSED when the environment contains a constant of that exact name and OPEN otherwise,
which is a decidable question a machine answers, and is the whole content of "ready to
close": when every dep is closed, the gap is a piece of work whose prerequisites are all
present.  Deps are stored as written and never resolved against the ambient namespace,
because a gap frequently names something that does not exist yet and name resolution
throws on those -- the case the mechanism exists for.

**A withdrawn instruction stays, with its reason.**  `Descent.lean`: "WITHDRAW IT IN
PLACE AND QUOTE WHAT IT USED TO SAY: a withdrawn instruction with its reason is more
useful than a clean paragraph, because the clean paragraph loses the fact that a careful
reader was misled here once."  `@[withdrawn "tag" "reason"]` attaches that to the
declaration the instruction was about; the `withdrawn "tag" "reason"` command carries the
cases -- the majority -- where the retracted instruction had no declaration to attach to.

## Unverified

**NONE OF THIS HAS BEEN COMPILED.**  It was written while every build partition was in
maintenance, against PhysLean's pre-module-system sources read at
`3b16e1b45d2e3cd498658895415703688361a3ff`, which is why it stays as close to them as it
does: `registerSimplePersistentEnvExtension`, `registerBuiltinAttribute` and the
`getPos?`/`getFileMap`/`mainModule` tail of each elaborator are copied rather than
invented.  The `#informal_report` command lives in `Descent.Meta.InformalLint` and
`semiformal_result` in `Descent.Meta.Semiformal`, one file each, so that a defect in
either is deletable without taking this file -- which content modules import -- with it.
-/

namespace Descent.Meta

open Lean Elab Command

/-- Which kind of gap a record came from.  Kept as data rather than as five extensions so
that one report reads all of them and a reader sees the whole ledger at once. -/
inductive GapKind where
  /-- An object the corpus refers to and has not defined. -/
  | informalDefinition
  /-- A claim the corpus relies on or wants and has not proved. -/
  | informalLemma
  /-- A statement whose type elaborates and whose proof is absent. -/
  | semiformal
  /-- Deferred work, with no statement yet. -/
  | todo
  /-- An instruction that was issued, acted on or nearly acted on, and retracted. -/
  | withdrawn

/-- The keyword each kind is written with, for the report. -/
def GapKind.label : GapKind → String
  | .informalDefinition => "informal_definition"
  | .informalLemma => "informal_lemma"
  | .semiformal => "semiformal_result"
  | .todo => "TODO"
  | .withdrawn => "withdrawn"

/-- One recorded gap.

`name` is `Name.anonymous` for a `TODO`, which has no name because it has no statement;
for `withdrawn` used as an attribute it is the declaration the instruction was about.
`line` is `0` for the attribute form, whose position is the declaration's rather than the
attribute's. -/
structure GapInfo where
  /-- Which command recorded it. -/
  kind : GapKind
  /-- The stable tag, chosen by the author and never derived from the content. -/
  tag : String
  /-- The name the gap is filed under, or `Name.anonymous`. -/
  name : Name
  /-- The prose: a docstring for the informal commands, the string for `TODO`. -/
  content : String
  /-- Fully qualified names this gap waits on, stored exactly as written. -/
  deps : List Name
  /-- The module the gap was declared in. -/
  fileName : Name
  /-- The line it was declared on, or `0`. -/
  line : Nat

/-- Environment extension holding every gap in the import closure.

`addImportedFn` concatenates, so `getState` on a module that imports the corpus root sees
the whole corpus -- which is the only place the report can be run from and see anything,
since a gap is recorded in the module that declares it and this one is at the bottom of
the layer order. -/
initialize gapExtension : SimplePersistentEnvExtension GapInfo (Array GapInfo) ←
  registerSimplePersistentEnvExtension {
    name := `Descent.Meta.gapExtension
    addEntryFn := fun arr gap ↦ arr.push gap
    addImportedFn := fun es ↦ es.foldl (· ++ ·) #[]
  }

/-- The shared tail of every gap command: locate the syntax, then push the record.

Factored out because four commands need it identically, and because two places that must
agree about what a gap record contains are better off with one of them calling the other
-- `Descent.lean` records a defect that survived a warning comment sitting forty lines
above it, and concludes that a note explaining why two places must agree is not a
mechanism. -/
def recordGap (stx : Syntax) (kind : GapKind) (tag : String) (name : Name)
    (content : String) (deps : List Name) : CommandElabM Unit := do
  match stx.getPos? with
  | some pos =>
    let env ← getEnv
    let modName := env.mainModule
    let fileMap ← getFileMap
    let line := (fileMap.toPosition pos).line
    modifyEnv fun env ↦ gapExtension.addEntry env
      { kind := kind, tag := tag, name := name, content := content, deps := deps,
        fileName := modName, line := line }
  | none => throwError "a gap command must have a source position"

/-! ### `TODO`

Copied from PhysLean's `Meta/TODO/Basic.lean`, with the tag kept as the author's string.
PhysLean's newest revision derives the tag by hashing the content; this one does not, for
the reason given in the header -- a tag that changes when the prose is corrected cannot be
cited. -/

/-- Syntax for `TODO "tag" "text"`. -/
syntax (name := todoCmd) "TODO " str str : command

/-- Elaborator for `TODO "tag" "text"`.  Records the note and adds nothing to the
environment, so a `TODO` is a line in the ledger and not a claim anything can rest on. -/
@[command_elab todoCmd]
def elabTODO : CommandElab := fun stx ↦
  match stx with
  | `(TODO $t $s) => recordGap stx GapKind.todo t.getString Name.anonymous s.getString []
  | _ => throwError "invalid `TODO` command"

/-! ### `informal_definition` and `informal_lemma`

The deps list is bracketed rather than introduced by a keyword because an atom in a
`syntax` rule enters the global token table: writing `" deps "` would reserve `deps` as a
keyword across the whole corpus and Mathlib, and a mechanism for recording gaps that
takes an ordinary English word out of circulation has made the corpus worse in exchange.
`[` and `]` are tokens already. -/

/-- Syntax for `informal_definition "tag" Name [dep, dep]`. -/
syntax (name := informalDefinitionCmd)
  docComment "informal_definition " str ident "[" ident,* "]" : command

/-- Syntax for `informal_lemma "tag" Name [dep, dep]`. -/
syntax (name := informalLemmaCmd)
  docComment "informal_lemma " str ident "[" ident,* "]" : command

/-- Elaborator for `informal_definition`.  Adds no constant: the docstring is the whole
content, and it goes into the ledger. -/
@[command_elab informalDefinitionCmd]
def elabInformalDefinition : CommandElab := fun stx ↦
  match stx with
  | `($doc:docComment informal_definition $t $n:ident [$deps,*]) =>
    recordGap stx GapKind.informalDefinition t.getString n.getId doc.getDocString
      (deps.getElems.toList.map (fun d ↦ d.getId))
  | _ => throwError "invalid `informal_definition` command"

/-- Elaborator for `informal_lemma`.  Adds no constant, which is the point: an unproved
claim must be impossible to cite, not merely marked. -/
@[command_elab informalLemmaCmd]
def elabInformalLemma : CommandElab := fun stx ↦
  match stx with
  | `($doc:docComment informal_lemma $t $n:ident [$deps,*]) =>
    recordGap stx GapKind.informalLemma t.getString n.getId doc.getDocString
      (deps.getElems.toList.map (fun d ↦ d.getId))
  | _ => throwError "invalid `informal_lemma` command"

/-! ### `withdrawn`

Two forms, because retracted instructions come in two shapes.  Most of them named no
declaration -- the `Conventions.lean` specimen was a paragraph about four names, none of
which it was attached to -- and those take the command.  One that was about a specific
declaration takes the attribute, so a reader of that declaration sees the retraction. -/

/-- Syntax for `@[withdrawn "tag" "reason"]`. -/
syntax (name := withdrawn) "withdrawn " str str : attr

/-- Syntax for the free-standing `withdrawn "tag" "reason"` command. -/
syntax (name := withdrawnCmd) "withdrawn " str str : command

/-- The `@[withdrawn "tag" "reason"]` attribute: this declaration was the subject of an
instruction that has been retracted, and the reason is recorded here rather than lost. -/
initialize withdrawnAttribute : Unit ←
  registerBuiltinAttribute {
    name := `withdrawn
    descr := "records a retracted instruction about this declaration, with its reason"
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun declName stx _ ↦ do
      match stx with
      | `(attr| withdrawn $t $r) =>
        modifyEnv fun env ↦ gapExtension.addEntry env
          { kind := GapKind.withdrawn, tag := t.getString, name := declName,
            content := r.getString, deps := [], fileName := env.mainModule, line := 0 }
      | _ => throwError "invalid `withdrawn` attribute"
  }

/-- Elaborator for the free-standing `withdrawn "tag" "reason"` command. -/
@[command_elab withdrawnCmd]
def elabWithdrawn : CommandElab := fun stx ↦
  match stx with
  | `(withdrawn $t $r) =>
    recordGap stx GapKind.withdrawn t.getString Name.anonymous r.getString []
  | _ => throwError "invalid `withdrawn` command"

/-! ### Reading the ledger

`depClosed` is the whole definition of progress this file offers, and it is deliberately
crude: a dep is closed when a constant of that exact name exists.  It does not check that
the constant says what the gap wanted, because nothing can -- that is what the docstring
is for.  What it does catch is the state the report exists to find, every prerequisite
present and the gap still open. -/

/-- A dep is closed when the environment contains a constant of exactly that name. -/
def depClosed (env : Environment) (n : Name) : Bool := env.contains n

/-- The deps of a gap that are not yet in the environment. -/
def openDeps (env : Environment) (g : GapInfo) : List Name :=
  g.deps.filter fun d ↦ !depClosed env d

/-- Every gap in the import closure. -/
def allGaps (env : Environment) : Array GapInfo := gapExtension.getState env

end Descent.Meta
