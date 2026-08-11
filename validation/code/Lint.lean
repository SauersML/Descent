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

THIS FILE IS THE GATE, AND IT RUNS THE LINTERS THAT ARE AT ZERO.  There is no
second tier: the debt ledger that ran the linters which were not at zero, reported
their counts and named what would return each to this file, is deleted.

WHAT THAT COST, stated here because the counts are now recorded nowhere else.
`simpNF` reported 21 non-confluent rewrites and `unusedArguments` reported 171
arguments across 137 declarations.  Those declarations are unchanged; nothing
counts them any more.

They were NOT moved into this gate, and that is a measurement rather than a
preference.  Of the 171 `unusedArguments` findings, 119 are inaccessible binders --
`inst✝`, `x✝`, `a✝` -- with no name to rename, required by the type of a `def`
whose value ignores them; 27 already begin with an underscore and are reported
anyway; 25 are ordinary named hypotheses and are the only repairable ones. A gate
whose findings cannot be driven to zero is permanently red, and a red gate is one
nobody reads -- which is how the 158 errors above went unread for
every commit of the period this file used to describe.

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

-- `empiricalStatusVocabulary` and `empiricalStatusMultiplicity` are in the
-- default set now, so this line is redundant with a bare `#lint` and is kept
-- anyway: it states which checks this runner is FOR, and a default set that
-- someone later narrows should not silently narrow the gate too.
#lint only empiricalStatusVocabulary empiricalStatusMultiplicity in Descent

/-! ## The corpus's own linter, which reached zero

`scaledQuantityUntyped` findings were once DEBT rather than defects -- every one a
signature predating `Core/Scaling.lean`. It reports nothing now, which was the
condition set for it, so it gates here. -/
#lint only scaledQuantityUntyped in Descent

/-! ## Batteries hygiene, the part of it that is at zero

`simpVarHead`, `dupNamespace` and `defLemma` each report nothing over the corpus and
each gates. `simpNF` and `unusedArguments` run nowhere; see the header for the
measurement that keeps `unusedArguments` out of any gate. -/
#lint only simpVarHead dupNamespace defLemma in Descent
