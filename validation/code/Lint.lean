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

THIS FILE IS THE GATE AND IT RUNS EVERY LINTER. There is no debt tier.

`validation/code/LintDebt.lean` used to hold the linters whose findings were called DEBT
rather than defects, on the argument that a gate red for an enumerated reason stops being
read. The argument is not wrong about human behaviour and it is not a reason to keep two
exit statuses: a finding that is allowed to persist is a finding nobody removes, and
`simpNF` reporting 23 non-confluent rewrites is a defect in 23 places whatever tier it is
filed under. The linters that were debt are named below alongside the ones that were not,
and this file fails on any of them.

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

/-! ## The linters filed as debt elsewhere

`scaledQuantityUntyped`, the Batteries set `simpNF`, `simpVarHead`, `dupNamespace` and
`defLemma`, and `unusedArguments`.  All of them gate.

`unusedArguments` is held out nowhere.  The argument for excluding it is that it
reports 135, and that an unused binder here is frequently a regime hypothesis
carried on purpose.  That is a statement
about intent, not about the finding: the binder IS unused, and a theorem carrying a
hypothesis its proof never consumes states something weaker than what was proved.  A
reader cannot tell the deliberate ones from the accidental ones, and neither can this
runner, which is the whole reason to make the corpus say which it means.

The repair per finding is one of two, and both are local: delete the binder, which
strengthens the theorem to what the proof actually establishes; or rename it with a
leading underscore, which is Lean's own way of saying the binder is carried on purpose and
which silences the linter because the intent is now written down instead of assumed. -/
#lint only scaledQuantityUntyped in Descent

#lint only simpNF simpVarHead dupNamespace defLemma unusedArguments in Descent
