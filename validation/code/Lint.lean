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

NOT COMPILED.  Neither this file nor the linters it names has been through a
build; every MSI partition was in maintenance when they were written.  A run
that fails to elaborate this file is a defect in the Lean, not a finding about
the corpus, and the two must not be confused in a report.

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

#lint only empiricalStatusVocabulary empiricalStatusMultiplicity in Descent
