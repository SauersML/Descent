/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Counterexamples.SteppingStoneNonIdentifiability

/-!
# `Counterexamples` -- the deliberately-wrong library

**Every module under `Counterexamples/`, and nothing else.**

A body that asserts nothing about the world is not a law. Keeping one inside `Descent/`
means every reader who meets it has to be warned off it, and every guard that reads
declaration heads has to be told to make an exception. Both costs are paid here instead,
once, by the directory it lives in. Mathlib keeps its counterexamples in a separate library
for the same reason.

What earns a module a place here is not being wrong. It is being wrong ON PURPOSE, in the
service of a true statement that cannot be made without naming the falsehood -- a
non-identifiability result needs the rival form it rules out to be an object, not a remark.
A body that merely failed its measurement does not belong here; it belongs nowhere, and the
purge deletes it.

These modules `import Descent`, so they are built and type-checked with the rest of the
corpus. They are NOT outside the reach of `validation/code/check.py`: it takes the repository
root as its corpus, so `style`, `laundering` and `duplication` read them like any
production body, and only the `Descent/`-scoped guards pass them by.

    lake build Descent Counterexamples ValidationShared

This file contains no declarations. It is a table of contents.
-/
