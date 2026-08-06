/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent
import Batteries.Tactic.Lint

/-!
# Linter runner

Runs the environment linters of `Descent.Meta.Linters` over every declaration in
every `Descent` module.  Run, after a successful build of `Descent`:

    lake env lean validation/code/Lint.lean

A failing linter is reported by `#lint` with `logError`, so the exit status is
nonzero and the run fails a script that checks it.

COMPILED AND RUN.  This file and `Descent.Meta.Linters` build, and this runner
has been executed over the whole corpus: 10,376 declarations plus 5,387
generated ones, four linters, 44 seconds.  It is a step in
`.github/workflows/prover.yml` and runs on every commit.

Its first run found one thing, and it was real:
`Core.PopGenParameters.fstAtGeneration` said NOT AN EMPIRICAL CLAIM while its
own docstring cited `battery_dis4.py`.  The run was about a different body --
the superseded decay base of `Generational.fstTransientAt` -- so the citation
moved to `fstEquilibrium_lt_fstAtGeneration_of_late`, the theorem that is the
machine-checked form of the warning, where naming a battery says something true.

## Why the linters are named one at a time

`#lint only` runs exactly the linters listed and nothing else.  The alternative,
`#lint`, runs every linter registered in the default set across the whole
environment -- which here means every Batteries linter over 150,000 lines that
have never been linted, and a report in the thousands that nobody will read
twice.  Each name below was put here by someone who had read what it reports on
this corpus.  Add the next one the same way.

## What this does not check

The `core-empirics` rules that join against
`validation/empirical/simcov/ledger.json` are not here and cannot be: the ledger
is not in the environment.  `python3 validation/code/check.py --only
core-empirics` remains the only reader of those, and this file does not reduce
what that guard is for.  See the module docstring of `Descent.Meta.Linters`.
-/

#lint only coreStatusMissing coreStatusDenied in Descent

-- `scaledQuantityUntyped` is `disabled` and named here for the reason the other two
-- explicitly-named linters are: it holds a rule this corpus states rather than a rule
-- about Lean, so a `#lint` on an unrelated importing module should not report it. It is
-- also the one linter here whose findings are DEBT rather than defects -- every one of
-- them is a signature that predates `Core/Scaling.lean` -- so it is kept separate from
-- the gate above until the count reaches zero.
#lint only scaledQuantityUntyped in Descent

/-!
## Mathlib/Batteries hygiene, which this corpus had never run

`simpNF` and `simpVarHead` check the 420 `@[simp]` declarations for confluence and for
head symbols that make a lemma fire on everything; `dupNamespace`, `defLemma` and
`unusedArguments` are the ordinary Batteries checks. None had ever been run here -- the
corpus pins one Mathlib commit and has no upgrade path, so a simp set that has never been
checked for confluence is latent until the first bump and expensive at it.

Named explicitly rather than left to a bare `#lint` for the reason in this file's header:
`#lint` would also run every other Batteries linter over 150,000 never-linted lines, and a
report in the thousands is a report nobody reads twice. Each name here was added by
someone who intended to read what it says about THIS corpus.

FIRST RUN: `simpNF` 23, `simpVarHead` 0, `dupNamespace` 0, `defLemma` 0. The 23 are real
confluence debt in a 420-lemma simp set that has never been checked, and they are latent
rather than harmless: this corpus pins one Mathlib commit and has no upgrade path, so a
non-confluent simp set costs nothing until the first bump and everything at it.

`unusedArguments` was run once and is NOT here. It reported 135, and in this corpus an
unused binder is frequently deliberate -- a regime hypothesis carried so a caller has to
state the regime, whether or not the proof consumes it. A linter whose findings are
mostly intended is how a corpus learns to read warnings as scenery, which is the failure
this file's header is about. It belongs in a pass that first decides which of the 135 are
regime documentation, not in the gate.
-/
#lint only simpNF simpVarHead dupNamespace defLemma in Descent

-- `empiricalStatusVocabulary` and `empiricalStatusMultiplicity` are in the
-- default set now, so this line is redundant with a bare `#lint` and is kept
-- anyway: it states which checks this runner is FOR, and a default set that
-- someone later narrows should not silently narrow the gate too.
#lint only empiricalStatusVocabulary empiricalStatusMultiplicity in Descent
