# Extraction layer for the Calibrator corpus

> ## Read this first: coherence is the trap
>
> Four bugs were found across two tiers in one session. Every one was a claim
> that **fitted all the available evidence while answering a different question
> than the one asked**:
>
> | the claim | what it actually answered |
> |---|---|
> | "the values disagree, so my transcription is wrong" | the values disagreed because a tolerance was applied in the wrong direction — widening a *hypothesis* admits points the theorem excludes |
> | "these examples are multi-line, so it's a multi-line-signature bug" | the examples happened to be multi-line; the pattern failed on **nested parentheses in a binder type** |
> | "the standard error says the verdict is safe" | an SE estimated from **two** samples is chi-square with one degree of freedom — too noisy to be a criterion |
> | "this tier is deterministic, so it has no seed problem" | determinism makes a run *repeatable*; it says nothing about whether a verdict survives drawing 40 **different** points |
>
> None of these felt like carelessness, and none of them was. Each stopped one
> step early at a point where the story was already coherent — and **a wrong
> diagnosis that explains all the evidence provides no signal that it is
> wrong.** At the level of the evidence, wrong-but-coherent is indistinguishable
> from right.
>
> The only defence found: **check the mechanism, not the fit.** Go one level
> below the evidence to the thing generating it. Confirm a binder bug by finding
> the pattern that fails, not by counting examples that failed. Find a crash in
> a consumer by reading the consumer, not the producer. Establish stability by
> varying the seed, not by observing that the code looks deterministic.
>
> ### The sharpest version: resemblance supplies false confidence
>
> A fifth instance arrived while this section was being written, and it is worse
> than the four above. One tier proposed that its `proved` verdict pooled two
> claims — sampling and a proof — exactly mirroring the determinism/stability
> conflation in the row above. It was elegant, it fitted the shape of the code,
> and it was **invented**: reading the function showed `proved` is only ever set
> by branch-and-bound, z3 UNSAT, or exact evaluation, never by sampling. The
> author had not opened the function. The other tier (this one) **endorsed it
> and relayed it upward without asking for evidence**, because it rhymed with a
> real bug already confirmed here.
>
> So: **a story that explains the evidence *and* rhymes with a story you already
> trust is more dangerous than one that only does the first.** The resemblance
> supplies the confidence that checking would have. And an analogy between two
> systems is a claim about *both* of them — endorsing one costs you the right to
> treat your own half as still-verified.
>
> The practical rule this yields: when a diagnosis about someone else's code
> arrives and matches your own, that is the moment to ask which function they
> read, not the moment to agree.
>
> This cannot be automated — an automated check is itself a fit to evidence. It
> is written here because it applies to every tier and to every number in this
> directory, and because message history is not where anyone looks in a week.
>
> Corollaries that have already earned their place:
> - A number that only ever rises is not being checked. Five corrections in one
>   session lowered a number and all five were right.
> - Every count is a count of *something*, and the thing is usually not what the
>   name of the count says. Three separate metrics here were counting mentions,
>   internal verdicts, or absences.
> - A clean run on the wrong revision is worse than no run, because it reads as
>   confirmation.
> - **Elaboration reads as rigour.** A 2001-point grid search was found where a
>   closed form existed — the search was not buying accuracy over solving it, it
>   was *costing* accuracy by quantising the answer to the grid, and it had been
>   kept because it looked more empirical. This tier is the same shape: it
>   samples 40 admissible points where, for many bodies, monotonicity or a value
>   at a distinguished point would settle the question exactly. Sampling is what
>   you do when you cannot solve, not a more honest version of solving.
> - A diff can only report a number. A **prediction** can be wrong in a way that
>   indicts the tool. Prefer instruments that can embarrass themselves.
> - **Neither line numbers nor files are a key.** Definitions move between lines
>   under concurrent editing and between files under reorganisation. A tier that
>   scanned a hardcoded list of six filenames silently lost two definitions when
>   a commit relocated them into a seventh, with identical bodies. Only the
>   fully-qualified `name` survives.

## Single-sourced definitions

Four definitions in the cross-validation battery — `cumulativeDrift`,
`fstVariableNe`, `harmonicMeanNe`, `ldMismatchFrobenius` — take `Fin n → ℝ` or
matrix arguments, which the independent translator refuses by design rather
than guessing. **They are extractable by this tier alone.** If the finite-vector
evaluator is wrong about them, nothing in this project would catch it, which is
why `verify.py`'s adversarial cases target exactly that feature. The right fix
is not to add vector support to the second translator: a second translator is
only worth having while it is independently written, and writing it against this
one would make it a copy rather than a check.

**They are also invisible to staleness.** When three definitions were repaired
upstream and this table was twelve minutes behind, the drift was caught because
the second translator reads the Lean directly and disagreed on exactly those
three. For these four there is no second reader: if one of them is repaired and
the table is stale, every consumer gets a confident wrong number and nothing in
this project notices. `api.require_fresh()` is the only guard they have.

Every validation script in this repo used to re-transcribe a Lean formula into
Python by hand. That transcription is an unvalidated step *inside* the
validator: a slip produces a false verdict in either direction. This directory
removes the step. Formulas are parsed out of the Lean source and translated
mechanically; the only hand-written formulas left are in `test_parser.py`, where
they are the thing being checked rather than the thing being trusted.

## Pipeline

```
proofs/Calibrator/**.lean
   -> lean_parse.py   the definition table                 -> defs.json
   -> translate.py    Lean expression -> Python source
   -> emit.py         executable module + taxonomy         -> lean_defs.py, classes.json
   -> coverage_v2.py  falsifiable coverage accounting      -> coverage.json
```

Regenerate everything:

```
python3 validation/extract/emit.py          # defs.json, lean_defs.py, classes.json
python3 validation/extract/coverage_v2.py   # the coverage report
python3 validation/extract/test_parser.py   # hand-verified ground truth
```

`validation/popgen_defs/coverage.py` is untouched and still works.

## Using the extracted definitions

`api.py` is the stable, documented interface.  Import it; do not re-parse Lean.

```python
import sys; sys.path.insert(0, "proofs/validation/extract")
import api

api.definition_table()                  # dict[fully-qualified name -> Definition]
api.definition("Calibrator.coalFst")    # one record (see api.py for the schema)
fn, argnames = api.callable_for("Calibrator.coalFst")
fn(100.0, 1000.0)                       # -> 0.0476...,  argnames == ["t", "Ne"]

api.resolve("coalFst")                  # bare -> fully-qualified; raises if ambiguous
api.classification("Calibrator.coalFst")# NUMERIC | STRUCTURAL | WRAPPER | NOT-EXTRACTABLE
api.admissible_box("Calibrator.coalFst")# {arg: (lo, hi)} mined from theorem hypotheses
api.hypotheses("Calibrator.coalFst")    # (predicates, source_text, NOT_ENFORCED)
api.satisfies(name, point, theorem=None)# is this point admissible? USE THIS --
                                        # the raw predicates are exec-mode code
                                        # objects; eval-ing one returns None,
                                        # which reads False and manufactures a
                                        # violation at every point
api.body_checksum("Calibrator.coalFst") # pin next to a result; changes if the Lean changes
api.stamp()                             # corpus-wide fingerprint for a results file
```

`api.callable_for` raises `api.NotExtractable(name, reason)` rather than guessing.

The lower-level module is also importable directly:

```python
import lean_defs
lean_defs.neiFst(0.4, 0.3)        # (H_T - H_S) / H_T, straight from the Lean body
```

`lean_defs.py` is generated; do not edit it. Argument order matches the Lean
signature. Lean identifiers that are not legal Python (`p₁`, `H₀`, `x'`) are
mapped by `translate.pyname`.

### Mathlib totality is preserved

`lean_rt.py` implements Mathlib's conventions rather than Python's, because the
difference is exactly where a definition's edge-case behaviour lives:

| Lean            | value          | naive Python       |
|-----------------|----------------|--------------------|
| `x / 0`         | `0`            | `ZeroDivisionError`|
| `x⁻¹` at `0`    | `0`            | `ZeroDivisionError`|
| `Real.log 0`    | `0`            | `ValueError`       |
| `Real.log (-x)` | `log x`        | `ValueError`       |
| `Real.sqrt (-1)`| `0`            | `ValueError`/`nan` |
| `(0:ℝ) ^ (y:ℝ)` | `0` for `y≠0`  | varies             |

A hand transcription that raises where Lean returns `0` will report a defect
that does not exist, or hide one that does.

## The taxonomy

Every definition lands in exactly one class (`classes.json`):

* **NUMERIC** — arithmetic over reals; testable by evaluation.
* **STRUCTURAL** — `Prop`-valued, set-valued, a type alias, or a structure
  literal; testable by exhibiting a witness and a non-witness.
* **WRAPPER** — a bare call to another definition; covered exactly when its
  target is.
* **NOT-EXTRACTABLE** — with the specific reason (indexed sum, integral, matrix
  literal, derivative, quantifier, ...). Never silently guessed at.

## What "covered" means here

> A definition counts as COVERED only if some check exists that CAN FAIL.

This is enforced, not asserted. For each definition the accounting runs the
check on the real body and on a family of **nearby wrong bodies** — mutants
produced by perturbing the parsed Lean source (`+`↔`-`, `*`↔`/`, `1 - x` →
`1 + x`, `^2` → `^1`, a bumped literal, a negated body). Mutants that are
numerically indistinguishable from the original on the admissible box are
discarded as equivalent. Then:

* check passes on the real body **and** fails on ≥1 distinguishable mutant
  → **COVERED**, and `coverage.json` records *which* wrong bodies it rejects;
* check passes on the real body and on every mutant → **VACUOUS**, and earns
  nothing. "The function returns a float" scores zero here, by construction;
* check fails on the real body → a finding, tiered by how much the corpus
  actually proves (below).

`constraints["hypotheses"]` is the **union** over every theorem mentioning a
definition, not a domain. Read as a conjunction it excludes admissible points —
`coalFst` carries `100 * Ne < t` from one asymptotic lemma. Use
`constraints["hypotheses_by_theorem"]`, or `api.hypotheses(name, theorem)`, and
enforce the preconditions of the one theorem whose claim you are testing.

The admissible box is not invented. Per-argument bounds come from the
hypotheses of the theorems that mention the definition, plus the quantity kind
implied by the argument's name; inter-argument constraints (`H_S ≤ H_T`,
`c * frob_sq < 1`) are compiled into predicates and enforced by rejection
sampling. Sampling outside the corpus's own stated preconditions manufactures
false defects, which is the failure mode this whole directory exists to prevent.

### Finding tiers

| status | meaning |
|---|---|
| `DEFECT` | the body leaves a range a **Lean theorem proves** for it, with every hypothesis of that theorem enforced. Either a real inconsistency or a translator bug; both matter. |
| `DEFECT-CANDIDATE` | same, but ≥1 stated precondition could not be enforced, so the violating point may be inadmissible. A lead, not a verdict. |
| `RANGE-MISMATCH` | the body leaves the range its **name or docstring implies**, which no theorem proves. Either the name is misleading or the body is. A lead, not a verdict. |

A bound proved by a theorem and a bound merely suggested by a docstring are
tracked with separate provenance and are never conflated. When two theorems
bound a definition in contradictory directions, at least one of them is
conditional on something not enforced; the definition is reported as needing a
hand-written check rather than being accused.

## Cross-validation

`test_parser.py` also compares this extraction against `leanexpr` in
`validation/differential/`, an independently written translator using the
opposite arithmetic convention (strict Python, raising where Mathlib returns 0).
Agreement at every point means a transcription error would have to be the same
error in both — the strongest evidence either translator is right. The test
fails on any disagreement **and** on any drop in the number of definitions
compared: a definition quietly leaving the comparison is how the `hetDecayFactor`
overload bug stayed hidden.

## Reconciliation with the other parsers

`reconcile.py` diffs this table against `validation/invariants/defs.json` and
`validation/symbolic/decls.json` on body text, parameter set, and parameter
order, and writes `reconcile.json`.  Run it after any parser change.  A
parameter-ORDER disagreement is the most dangerous kind: both parsers produce a
callable, both callables run, and they compute different functions.

## Adding a stronger check

The generated range invariants are a floor, not a ceiling. To add a real check
for a definition, import `lean_defs`, write the check against the extracted
function, and — this is the part that matters — verify it kills a mutant:

```python
from coverage_v2 import mutants, compile_variant     # the same machinery
```

If your check survives every mutant of the body it is meant to check, it is
vacuous, and the accounting will say so.
