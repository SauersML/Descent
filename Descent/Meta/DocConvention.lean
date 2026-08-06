/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The docstring convention, read in Lean

The corpus states what measurement has said about a declaration in the
declaration's own docstring: a status marker whose head is drawn from a closed
vocabulary, and a citation of the battery that produced the verdict.  Until now
the only reader of that convention was `validation/code/check.py`, which scans
the SOURCE TEXT with regular expressions.  This module reads the same
convention, and it is the shared half of the readers that do: the environment
linters in `Descent.Meta.Linters` and the command linter in
`Descent.Meta.StatusLinter`.

NOTHING HERE TOUCHES THE ENVIRONMENT.  Every function is a total function on
strings, which is what lets the same code serve a linter that has an elaborated
environment and one that has only the syntax of the command in front of it.

## Why a second reader at all

The Python scan and this one see different things and neither subsumes the
other, in the same way `validation/code/Check.lean` does not subsume
`validation/code/check.py`:

  * the text scan sees a file that does not compile, a module-level section, a
    comment, and the exact line a person typed;
  * this one sees the docstring Lean actually attached to the declaration Lean
    actually accepted, under the name it actually has after `_root_` and
    namespace resolution -- which is how a Core declaration housed outside
    `Descent/Core/` is in scope here without a path rule.

## The parsing rules, and that they are copies

The three rules below are transcriptions of `CONVENTION_STATUS`,
`convention_status_head` and `BATTERY_CITE` in `validation/code/check.py`.  They
are copies, and a copy can drift.  They are written out rather than derived
because a Lean module cannot read a Python regex, and the alternative -- having
the linter shell out to the Python -- would make the Lean side a wrapper rather
than a second reader, which is the whole point of moving the check.

THE VOCABULARY BELOW IS A COPY OF `empirical_status_vocabulary` IN
`validation/conventions.json`, AND THE JSON IS THE ADJUDICATING RECORD.  A term
adjudicated into the JSON and not added here becomes a finding this module
reports and the Python does not.  There is at present no guard that compares the
two lists; adding one is the natural next step, and until it exists this is a
duplication that a reader has to hold.
-/

namespace Descent.Meta.DocConvention

/-- The marker that opens a status line, never written contiguously in this
file: `validation/code/check.py` scans every Lean source in the corpus for the
bare phrase and would read a Lean string literal containing it as a status
marker asserted by this module. -/
def statusMarker : List Char := ("Empirical" ++ " status:").toList

/-- The opening of a battery citation, `simcov/battery_NAME.py`. -/
def batteryMarker : List Char := "simcov/battery_".toList

/-- The closed vocabulary of status heads.

A copy of `empirical_status_vocabulary.terms` in `validation/conventions.json`;
see the module docstring for why it is a copy and what that costs. -/
def vocabulary : List String :=
  ["UNTESTED",
   "VALIDATED",
   "MEASURED",
   "DERIVED",
   "FALSIFIED",
   "VACUOUS",
   "CONDITIONALLY VALID",
   "MIXED",
   "ASSERTED",
   "THIS IS THE MODEL",
   "NOT AN EMPIRICAL CLAIM",
   "NOT EMPIRICALLY TESTABLE",
   "NOT TESTED BY THE DESIGN THAT LOOKED LIKE IT WAS",
   "EXACT BY CONSTRUCTION",
   "AN IDENTITY",
   "DISAGREES WITH AN EXISTING MEASUREMENT",
   "CONVENTION PINNED"]

/-- The heads that assert nothing measurable is at stake.

A copy of `CORE_DENIES_MEASUREMENT` in `validation/code/check.py`, and its
comment there is the reason the list is this short: `VACUOUS`, `AN IDENTITY` and
`NOT TESTED BY THE DESIGN THAT LOOKED LIKE IT WAS` each describe an existing
measurement honestly rather than denying that one could bear on the body, so
none of them is refuted by a battery having run. -/
def deniesMeasurement : List String :=
  ["NOT AN EMPIRICAL CLAIM",
   "NOT EMPIRICALLY TESTABLE",
   "EXACT BY CONSTRUCTION",
   "THIS IS THE MODEL",
   "UNTESTED"]

/-- Every occurrence of `pat` in the text, as the character immediately before
it and the text immediately after it.

The preceding character is carried because it is the whole discriminator between
a status marker and a mention of one: the corpus writes the phrase in backticks
when it is talking ABOUT a status line and bare when it is asserting one.

**Tail recursive, and it has to be.** The obvious spelling computes the tail first and
conses onto it, which puts one interpreter frame on the stack per CHARACTER of the
docstring. That is fine at a hundred characters and fatal at a few thousand: `#lint` runs
these in the interpreter, and this module's linters crashed the runner with `deep recursion
was detected at 'interpreter'` on a corpus whose longest docstrings run to several thousand
characters. The failure was in the SCANNER, not in anything it was scanning, and it arrived
as a stack trace of ten thousand identical frames rather than as a finding -- so a corpus
where it fires reports no linter results at all rather than reporting the wrong ones.

The accumulator version compiles to a loop and is bounded by the output, not the input. -/
def occurrencesAfter (pat : List Char) (prev : Option Char) (cs : List Char) :
    List (Option Char × List Char) :=
  go prev cs []
where
  /-- The loop: `acc` holds the matches found so far, most recent first. -/
  go : Option Char → List Char → List (Option Char × List Char) →
      List (Option Char × List Char)
  | _, [], acc => acc.reverse
  | prev, c :: cs, acc =>
      match pat.isPrefixOf? (c :: cs) with
      | some after => go (some c) cs ((prev, after) :: acc)
      | none => go (some c) cs acc

/-- The text following each ASSERTED status marker in `doc`, clipped to the same
140 characters the Python scan reads.

A marker preceded by a backtick is a quotation and is skipped. -/
def statusTexts (doc : String) : List (List Char) :=
  (occurrencesAfter statusMarker none doc.toList).filterMap fun (before, rest) ↦
    if before == some '`' then none
    else some ((rest.dropWhile fun c ↦ c == ' ' || c == '\t').take 140)

/-- Leading whitespace and emphasis asterisks, dropped. -/
def dropLeadIn : List Char → List Char
  | [] => []
  | c :: cs => if c == '*' || c.isWhitespace then dropLeadIn cs else c :: cs

/-- The text up to the first punctuation or emphasis that ends a status head. -/
def upToBreak : List Char → List Char
  | [] => []
  | c :: cs =>
      if c == '(' || c == '[' || c == ',' || c == '.' || c == ';' || c == ':'
          || c == '\n' || c == '—' then []
      else if c == '-' && cs.head? == some '-' then []
      else if c == '*' && cs.head? == some '*' then []
      else c :: upToBreak cs

/-- Runs of whitespace collapsed to a single space, with none left at the end. -/
def collapseSpaces : List Char → List Char
  | [] => []
  | c :: cs =>
      if c.isWhitespace then
        match collapseSpaces cs with
        | [] => []
        | rest => ' ' :: rest
      else c :: collapseSpaces cs

/-- Trailing backticks dropped. -/
def dropTrailingTicks (cs : List Char) : List Char :=
  (cs.reverse.dropWhile fun c ↦ c == '`').reverse

/-- The vocabulary term a status line claims, stripped of emphasis. -/
def statusHead (text : List Char) : String :=
  (dropTrailingTicks (collapseSpaces (upToBreak (dropLeadIn text)))).asString

/-- The head of every asserted status marker in `doc`, in the order written. -/
def statusHeads (doc : String) : List String :=
  (statusTexts doc).map statusHead

/-- Is `head` a term of the closed vocabulary, possibly followed by its own
qualifying words?

`MEASURED AGAINST HGDP` is `MEASURED` with a qualification and not a new term,
so a term may be followed by anything that does not continue the word. -/
def headIsTerm (head : String) : Bool :=
  vocabulary.any fun t ↦
    let hs := head.toList
    let ts := t.toList
    ts.isPrefixOf hs &&
      (match (hs.drop ts.length).head? with
       | none => true
       | some c => !c.isAlpha)

/-- The canonical term `head` spells in the wrong case, if there is one.

One verdict under two spellings cannot be counted, and the defect this names is
real: the corpus once carried one verdict written 138 times in capitals and 5
times in lower case. -/
def miscasedTerm (head : String) : Option String :=
  vocabulary.find? fun t ↦ t.toLower == head.toLower

/-- Does `head` deny that any measurement can bear on the body? -/
def headDeniesMeasurement (head : String) : Bool :=
  deniesMeasurement.contains head

/-- Is `c` part of a battery name? -/
def isBatteryNameChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Every battery cited as `simcov/battery_NAME.py` in `doc`, in the order
written and with repeats kept. -/
def batteryCitations (doc : String) : List String :=
  (occurrencesAfter batteryMarker none doc.toList).filterMap fun (_, rest) ↦
    let name := rest.takeWhile isBatteryNameChar
    if name.isEmpty then none
    else if (".py".toList).isPrefixOf (rest.dropWhile isBatteryNameChar) then
      some name.asString
    else none

end Descent.Meta.DocConvention
