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

THIS FILE IS THE GATE, AND IT RUNS THE LINTERS THAT ARE AT ZERO.
`validation/code/LintDebt.lean` runs the ones that are not, reports their counts, and
names what returns each to this file.

That split was abolished here, on the argument that "a finding that is allowed to
persist is a finding nobody removes" and that `simpNF` reporting 23 non-confluent
rewrites is a defect in 23 places whatever tier it is filed under. Both sentences are
true. Neither is an argument for naming a linter in a gate without clearing it, which
is what happened: `simpNF` and `unusedArguments` were moved here and their findings
were not repaired, so this runner has exited 1 on every commit since -- 158 errors,
137 declarations -- and its CI step sits behind a step that fails first, so no run has
ever reached it. A gate red since the day it was widened, unread because something
else is redder, is the exact case the ledger's header predicts and the exact route it
names.

`unusedArguments` is in the ledger for a second reason, and this one is measured
rather than argued. The repair this file prescribed was "rename it with a leading
underscore, which is Lean's own way of saying the binder is carried on purpose and
which silences the linter". It does not silence this linter. Of the 171 arguments
reported across 137 declarations:

* 27 ALREADY begin with an underscore and are reported anyway;
* 119 are inaccessible -- `inst✝`, `x✝`, `a✝` -- and cannot be renamed at all, having
  no name; for a `def` whose value ignores an argument, which is most of them, the
  argument is required by the type and deleting it is not a repair but a different
  function;
* 25 are ordinary named hypotheses, and those 25 are the ones the argument above is
  actually about.

A repair that reaches 25 of 171 does not make a linter gateable, and a gate whose
findings cannot be driven to zero is not a ratchet -- it is a permanent red. The 25
are real and they are in the ledger with that number on them.

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

`scaledQuantityUntyped` was the one linter in `LintDebt.lean` whose findings were
DEBT rather than defects -- every one a signature predating `Core/Scaling.lean`. It
reports nothing now, which is the condition that file set for it, so it gates here
and its entry there is gone. This is what a debt tier is for and what graduating out
of one looks like. -/
#lint only scaledQuantityUntyped in Descent

/-! ## Batteries hygiene, the part of it that is at zero

`simpVarHead`, `dupNamespace` and `defLemma` each report nothing over the corpus and
each gates. `simpNF` and `unusedArguments` are in `LintDebt.lean` with their counts;
see the header for why, and for the measurement that decided `unusedArguments`. -/
#lint only simpVarHead dupNamespace defLemma in Descent
