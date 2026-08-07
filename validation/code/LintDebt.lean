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

-- `scaledQuantityUntyped` HAS LEFT. It reported the signatures predating
-- `Core/Scaling.lean`; it reports nothing now, which is the condition this file set for
-- it, so it gates in `Lint.lean` and is not run twice. Nothing else moved it -- not a
-- decision that the remainder was acceptable, and not a budget -- which is what the
-- header asks of every name below.

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

TODAY: `simpNF` 21. `simpVarHead`, `dupNamespace` and `defLemma` are at zero and have
left for `Lint.lean`. FLIP CONDITION for `simpNF`: 0. Each finding names a lemma whose
left-hand side is not in simp-normal form, and the repair per finding is local -- restate
the lemma in normal form, or drop the `@[simp]` if the normal form makes it redundant.

## `unusedArguments`, and why the prescribed repair does not reach it

It was moved to the gate with a repair attached: "delete the binder ... or rename it with
a leading underscore, which ... silences the linter". The second half is false against
this toolchain, and it is false by measurement rather than by argument. 171 arguments over
137 declarations:

* 27 ALREADY begin with an underscore and are reported anyway;
* 119 are inaccessible -- `inst✝`, `x✝`, `a✝`. They have no name to rename. Most sit on a
  `def` whose value ignores an argument its TYPE requires, where deleting the binder does
  not strengthen anything: it writes a different function;
* 25 are ordinary named hypotheses. These are the ones the gate's argument is about -- a
  theorem carrying a hypothesis its proof never consumes states something weaker than
  what was proved -- and every one of them is real.

FLIP CONDITION, and it is not zero: 25 named hypotheses triaged, each either deleted or
carried with a reason a reader can check, and this linter is then a report on the 146 the
repair cannot reach rather than a queue. It returns to the gate only if a later toolchain
skips underscored and inaccessible binders, at which point the count that matters is the
count of NAMED ones and the flip condition is zero again.
-/
#lint only simpNF unusedArguments in Descent
