/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Meta.DocConvention
import Descent.Meta.Linters
import Descent.Meta.StatusLinter

/-!
# The corpus's own linters

`Descent/Meta/` holds the corpus's machinery about itself, written IN the
corpus's language.  NO MODULE OF `Descent/Meta/` MAY IMPORT A PROOF MODULE, and
that is the one thing this group has to keep: a proof module able to import its
own auditor can be written to satisfy it.  Everything here imports `Lean`,
`Batteries` or another `Descent.Meta` module, and nothing else.

**Checks, which read the corpus and are read by nothing.**  `DocConvention` is
the shared reading of the empirical-status docstring convention and touches no
environment.  `Linters` holds environment linters for Batteries' `#lint`, run by
`validation/code/Lint.lean`.  `StatusLinter` holds a command linter, off by
default, that reports the two textual rules at the line a person typed.

That is the whole group: it reads the corpus and nothing reads it back, which is
what makes the rule above enforceable by the import graph alone.

None of it has been compiled; see the module docstrings for what that means for
a reader.
-/
