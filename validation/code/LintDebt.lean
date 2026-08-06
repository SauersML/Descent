/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent
import Batteries.Tactic.Lint

/-!
# Debt ledger, as linters

The companion to `validation/code/Lint.lean`. That file is the GATE: every linter in it
reports nothing, and a finding there fails the build. This one runs the linters whose
findings are enumerated DEBT -- known, deliberately carried, and not defects of the commit
under test. It runs on every commit and prints its counts; it does not fail the build.

The split exists because the two must not share an exit status. A gate that is red for a
reason everyone knows about stops being read, and the defect it was built to catch then
arrives into a red build and nobody looks. A debt ledger that fails the build gets deleted
or `continue-on-error`-ed wholesale, and then it stops being read too.

Run it the same way:

    lake env lean validation/code/LintDebt.lean

## What is in here, and what would move it to the gate

Each of these leaves when its count reaches zero. Nothing else moves it: not a decision
that the remainder is acceptable, and not a budget.
-/

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
