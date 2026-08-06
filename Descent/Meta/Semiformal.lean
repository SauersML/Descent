/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Meta.Informal

assert_below Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# Semiformal results

A semiformal result sits between an `informal_lemma`, which has only prose, and a theorem:
its STATEMENT elaborates -- so it is type-correct, and the names in it are the corpus's
real names rather than a docstring's spelling of them -- and its proof is absent.

That middle rung is worth having for the reason `Descent.lean` gives about the deleted
`LDDecayMechanism`: with `autoImplicit` a bare undefined name becomes a fresh implicit
variable, so "a well-formed claim about nothing" is a shape this corpus has already shipped
once, green, among its headline results.  Prose has that failure mode by construction --
nothing checks that the names in a paragraph exist.  A `semiformal_result` does not: the
signature is elaborated, and a statement naming something that is not there fails here,
where it is written.

## Why it still cannot be used

The declaration is elaborated inside `withoutModifyingEnv`, so the environment is restored
afterwards and neither the statement nor the `helper` axiom standing in for its proof
survives the command.  Nothing downstream can cite it, exactly as with `informal_lemma`.
The axiom is real while it exists and gone before the next command, which is why it does
not reach the corpus's axiom audit.

## Source and status

Copied from PhysLean's `Meta/Informal/SemiFormal.lean` at
`3b16e1b45d2e3cd498658895415703688361a3ff`, which itself adapts Batteries' `proof_wanted`
(Apache 2.0, copyright 2023 Lean FRO, David Thrane Christiansen).  The parser is left
exactly as PhysLean writes it, including the absence of a deps list -- adding brackets to a
hand-written `leading_parser` is the kind of edit that cannot be checked without a compiler,
and every semiformal result records `[]` for its deps until one can be.

NOT COMPILED -- see the header of `Descent.Meta.Informal`.  This is the one command in the
group that manufactures a declaration, so it is the one most likely to be wrong, and it is
alone in this file so that deleting it costs nothing else.  Nothing in the corpus uses it
yet.
-/

namespace Descent.Meta

open Lean Parser Elab Command

/-- Syntax for `semiformal_result "tag" name (binders) : statement`, with a mandatory
docstring. -/
@[command_parser]
def «semiformal_result» := leading_parser
    docComment >> "semiformal_result" >> strLit >> declId >> ppIndent declSig

/-- Elaborator for `semiformal_result`.  Records the gap, then elaborates the signature
against a placeholder proof inside `withoutModifyingEnv`, so the statement is checked and
nothing is added. -/
@[command_elab «semiformal_result»]
def elabSemiformalResult : CommandElab := fun stx ↦
  match stx with
  | `($doc:docComment semiformal_result $s $name $args* : $res) => do
    let declName := (Lean.Elab.expandDeclIdCore name).1
    recordGap stx GapKind.semiformal s.getString declName doc.getDocString []
    let _ ← withoutModifyingEnv do
    elabCommand <| ←
      `(section
      set_option linter.unusedVariables false
      axiom helper {α : Sort _} : α
      $doc:docComment noncomputable def $name $args* : $res := helper
      end)
    pure ()
  | _ => throwError "invalid `semiformal_result` command"

end Descent.Meta
