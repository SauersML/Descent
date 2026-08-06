/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Meta.DocConvention
import Descent.Meta.Informal
import Descent.Meta.InformalLint
import Descent.Meta.Linters
import Descent.Meta.Semiformal
import Descent.Meta.StatusLinter
import Descent.Layer

assert_below Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# The corpus's own linters

`Descent/Meta/` holds the corpus's machinery about itself, written IN the
corpus's language.  NO MODULE OF `Descent/Meta/` MAY IMPORT A PROOF MODULE, and
that is the one thing this group has to keep: a proof module able to import its
own auditor can be written to satisfy it.  Everything here imports `Lean`,
`Batteries` or another `Descent.Meta` module, and nothing else.

That single rule covers two groups that face in opposite directions, which is
worth saying plainly because the file names do not.

**Checks, which read the corpus and are read by nothing.**  `DocConvention` is
the shared reading of the empirical-status docstring convention and touches no
environment.  `Linters` holds environment linters for Batteries' `#lint`, run by
`validation/code/Lint.lean`.  `StatusLinter` holds a command linter, off by
default, that reports the two textual rules at the line a person typed.

**Vocabulary, which the corpus reads.**  `Informal` supplies `TODO`,
`informal_definition`, `informal_lemma` and `@[withdrawn]`, the commands that
turn a deferred-work note into a tagged object that cannot be cited, and proof
modules import it -- `Descent.Program.OpenQuestions` and
`Descent.Coalescent.Program` do.  `Semiformal` adds `semiformal_result`, whose
statement elaborates and whose proof does not exist.  `InformalLint` reads the
ledger the first two write.

Both directions are consistent with the rule above, and the import graph is what
enforces it: `Informal` imports `Lean.Elab.Command` alone, so it can sit under
anything, and nothing that reads the corpus is ever underneath it.

None of it has been compiled; see the module docstrings for what that means for
a reader.
-/
