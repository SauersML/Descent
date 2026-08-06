/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Batteries.Tactic.Lint
import Descent.Meta.DocConvention

/-!
# Environment linters for the empirical-status convention

Four linters in Batteries' `#lint` framework, each holding a rule that
`validation/code/check.py` also holds, and each reading the ELABORATED
ENVIRONMENT rather than the source text.

Run them, after a successful build of `Descent`:

    lake env lean validation/code/Lint.lean

NONE OF THIS HAS BEEN COMPILED.  It was written against the pinned toolchain's
sources and the pinned Batteries revision, and every core and Batteries name in
it was read out of `~/.elan/toolchains/leanprover--lean4---v4.24.0` and the
pinned `Batteries/Tactic/Lint/*.lean`, but no build has accepted it.  Treat a
failure here as a defect in this module until a build says otherwise.

## What an environment linter can see, and what it cannot

The rules that `check.py`'s `core-empirics` guard enforces are these:

  SILENT     a Core declaration with a FALSIFIED ledger row whose docstring
             never names the battery that rejected it;
  UNMARKED   a Core declaration the ledger has measured that states no status;
  DENIED     a Core declaration whose status head says no measurement can bear
             on it, against a ledger row that did.

ONLY PART OF THAT IS EXPRESSIBLE HERE, AND THE PART THAT IS NOT IS THE FIRST
ONE.  All three rules are joins between the corpus and
`validation/empirical/simcov/ledger.json`, and the ledger is not in the
environment: it is JSON written by simulation runs, outside Lean, with no
representation among the constants the kernel accepted.  A linter cannot see
that a battery returned FALSIFIED at 15.61 sems.

What it can see is the half of the join the corpus itself states.  A docstring
citing `simcov/battery_NAME.py` is the declaration's own admission that a
measurement bore on it, and that admission IS in the environment.  So two of the
linters below are the ledger-free shadows of UNMARKED and DENIED:

  `coreStatusMissing`  a Core definition that cites a battery and states no
                       status of its own -- the subset of UNMARKED that the
                       declaration confesses;
  `coreStatusDenied`   a Core definition whose status head denies measurability
                       while its own docstring cites a battery -- the subset of
                       DENIED that is a self-contradiction inside one docstring.

Neither replaces the Python guard, and neither is meant to.  A declaration that
cites nothing and was measured is invisible here and visible there.  What they
add is that the contradiction is caught with no ledger present at all, which is
exactly the state a fresh checkout is in.

The other two linters are not ledger joins and are therefore FULLY expressible:

  `empiricalStatusVocabulary`   a status head outside the closed vocabulary;
  `empiricalStatusMultiplicity` a docstring stating more than one status.

## Two ways this reads differently from the text scan, on purpose

  * SCOPE IS BY ELABORATED NAME.  `check.py` scopes Core by the written name
    containing `Descent.Core.` or the file living under `Descent/Core/`.  Here a
    declaration is on Core's surface when its resolved name or its module is
    under `Descent.Core`, so a `_root_.Descent.Core...` definition housed in
    `Portability/` is in scope with no rule about `_root_` at all.
  * DEFINITIONS ARE `defnInfo`, not the token `def`.  That takes in `abbrev` and
    `instance`, which the text scan's `^def ` does not.  It is a widening, so a
    declaration reported here and not there is not a disagreement between them.

## Which of these are in the default set, and what changed the answer

`empiricalStatusVocabulary` and `empiricalStatusMultiplicity` are registered
NORMALLY and are in the default `#lint` set.  They were `disabled` on the
argument that switching an unproven check on across 150,000 never-linted lines
is how a corpus learns to read warnings as scenery.  That argument was right
and it has been discharged: both were run over the whole of `Descent` --
10,376 declarations, 44 seconds -- and reported nothing.  A check that has been
run once and found clean is no longer unproven, and leaving it out of the
default set after that is not caution, it is a second place the rule has to be
remembered.  Neither joins a ledger; both are decidable from the docstring
alone, which is why these two and not the other pair.

`coreStatusMissing` and `coreStatusDenied` stay `@[env_linter disabled]` and
are named explicitly by `validation/code/Lint.lean`.  That is deliberate and is
not the same caution: they scope to Core's surface and read a battery citation,
so they are about a rule this corpus states and not about Lean hygiene, and a
`#lint` run on some unrelated module that happens to import this one should not
report them.  Their first run found one -- `Core.PopGenParameters.fstAtGeneration`
denying measurement while citing `battery_dis4`, which was a citation about a
different body sitting on a definition's own docstring.
-/

open Lean Meta

namespace Descent.Meta.Linters

open Descent.Meta.DocConvention

/-- The module a declaration was written in.

`findModuleOf?` answers `none` for a declaration in the module being elaborated,
which is the right answer to a different question than the one asked here. -/
def moduleOf (declName : Name) : MetaM Name := do
  match (← findModuleOf? declName) with
  | some m => return m
  | none => getMainModule

/-- Is this a definition rather than a theorem, an axiom or an inductive? -/
def isDefinition (env : Environment) (declName : Name) : Bool :=
  match env.find? declName with
  | some (.defnInfo _) => true
  | _ => false

/-- Is `declName` a declaration of this corpus at all?

The runner's own helper declarations sit in the environment beside the corpus,
and `#lint ... in Descent` includes the current file unconditionally, so without
this every linter would also be a linter on the runner. -/
def inCorpus (declName : Name) : MetaM Bool := do
  return (← moduleOf declName).getRoot == `Descent

/-- Is `declName` on Core's surface: named into `Descent.Core`, or housed under
`Descent/Core/`?

Core's surface is not its directory.  `migrationSharedBoostAt` is a Core
declaration housed in `Portability/PortabilityDrift/Generational.lean` under a
`_root_.` prefix, and a scope rule reading only the path would not look at it. -/
def onCoreSurface (declName : Name) : MetaM Bool := do
  if (`Descent.Core).isPrefixOf declName then return true
  return (`Descent.Core).isPrefixOf (← moduleOf declName)

/-- The docstring of a corpus declaration, when it has one. -/
def corpusDoc (declName : Name) : MetaM (Option String) := do
  if (← Batteries.Tactic.Lint.isAutoDecl declName) then return none
  unless (← inCorpus declName) do return none
  return (← findDocString? (← getEnv) declName)

/-- The docstring of a definition on Core's surface, when it has one. -/
def coreDefinitionDoc (declName : Name) : MetaM (Option String) := do
  unless isDefinition (← getEnv) declName do return none
  unless (← onCoreSurface declName) do return none
  corpusDoc declName

/-- A definition on Core's surface that cites a battery and states no status.

The module-level section is the right host for a file of shapes and the wrong
one for the single law in that file that is on trial, so a declaration whose own
docstring names the run that measured it has to carry its own verdict. -/
@[env_linter disabled] def coreStatusMissing : Batteries.Tactic.Lint.Linter where
  noErrorsFound :=
    "Every Core definition citing a battery states a status of its own."
  errorsFound :=
    "CORE DEFINITIONS CITING A MEASUREMENT AND STATING NO STATUS OF THEIR OWN:"
  test declName := do
    let some doc ← coreDefinitionDoc declName | return none
    let cited := batteryCitations doc
    if cited.isEmpty then return none
    unless (statusTexts doc).isEmpty do return none
    let names := String.intercalate ", " cited
    return m!"cites battery {names} and carries no `Empirical status:` line \
      of its own"

/-- A definition on Core's surface denying that measurement can bear on it,
while its own docstring cites a battery.

The citation is the docstring saying a run bore on the body; the head is the
docstring saying none could.  One docstring, both claims, and no ledger needed
to see that they cannot both hold. -/
@[env_linter disabled] def coreStatusDenied : Batteries.Tactic.Lint.Linter where
  noErrorsFound :=
    "No Core definition denies measurement while citing one."
  errorsFound :=
    "CORE DEFINITIONS DENYING MEASUREMENT WHILE CITING A BATTERY:"
  test declName := do
    let some doc ← coreDefinitionDoc declName | return none
    let cited := batteryCitations doc
    if cited.isEmpty then return none
    match (statusHeads doc).head? with
    | none => return none
    | some head =>
        unless headDeniesMeasurement head do return none
        let names := String.intercalate ", " cited
        return m!"says {head} while citing battery {names}; replace the head \
          with the verdict that run carries, or, if the run is about a \
          different quantity, say which"

/-- A status head outside the closed vocabulary.

A status marker exists to be COUNTED -- the corpus's coverage denominator is
built from these -- and a vocabulary that drifts cannot be counted. -/
@[env_linter]
def empiricalStatusVocabulary : Batteries.Tactic.Lint.Linter where
  noErrorsFound :=
    "Every status head is a term of the closed vocabulary."
  errorsFound :=
    "STATUS HEADS OUTSIDE THE CLOSED VOCABULARY:"
  test declName := do
    let some doc ← corpusDoc declName | return none
    let bad := (statusHeads doc).filter fun head ↦ !headIsTerm head
    match bad.head? with
    | none => return none
    | some head =>
        match miscasedTerm head with
        | some canonical =>
            return m!"status head {head} is {canonical} in the wrong case; one \
              verdict under two spellings cannot be counted"
        | none =>
            return m!"status head {head} is not in the vocabulary; use an \
              existing term, or adjudicate a new one INTO \
              `empirical_status_vocabulary` rather than beside it"

/-- More than one status marker in one docstring.

Every scanner, and every reader who stops at the first status line, takes the
FIRST marker as the verdict.  A superseded marker sitting above a current one IS
the reported status, and the corpus has been counted wrong that way. -/
@[env_linter]
def empiricalStatusMultiplicity : Batteries.Tactic.Lint.Linter where
  noErrorsFound :=
    "Every docstring states its status at most once."
  errorsFound :=
    "DOCSTRINGS STATING MORE THAN ONE STATUS:"
  test declName := do
    let some doc ← corpusDoc declName | return none
    let heads := statusHeads doc
    if heads.length ≤ 1 then return none
    let spelled := String.intercalate ", " heads
    return m!"carries {heads.length} status markers ({spelled}); every scanner \
      reads the first, so the others are invisible and the first may not be \
      the current verdict"

end Descent.Meta.Linters
