#!/usr/bin/env python3
"""Code validation for the proof corpus: the source-text half.

Every guard in this file reads the LEAN SOURCE TEXT.  `Check.lean`, beside it, is
the elaborated-environment half.  The two are different instruments and neither
subsumes the other:

  * this half sees comments, docstrings, `variable` lines, status markers, the
    shape of what a person actually typed, and files that do not compile.  It
    needs no build, so it runs in seconds and it runs on a broken tree;
  * `Check.lean` sees the premises Lean actually inserted, a definition that
    unfolds to something other than its written form, a proof term's real head
    symbol, whether a type is inhabited, and the transitive axiom closure --
    none of which exists in the source text at all.

Run everything:

    python3 validation/code/check.py

Run one guard:

    python3 validation/code/check.py --only laundering
    python3 validation/code/check.py --list

Exit is nonzero if any guard that ran fails.  Guard-specific flags go after the
guard name; `--only laundering --json out.json` reaches the laundering guard.

THE GUARDS, and what each one catches:

  style           corpus style policy: license header, module docstring,
                  import placement, line length, snake_case theorem names,
                  `↦` over `=>`, and documentation that narrates development
                  history rather than mathematics.
  identifications structural guards over the corpus: admissions (`sorry` is
                  reported, `admit` is forbidden), convention drift, equilibria
                  with no dynamic, and duplicate bodies. Every count is zero.
  duplication     the same mathematics written twice: two theorems stating one
                  proposition under two names, one proof script serving two
                  different statements, and verbatim repeated blocks of source.
                  It complements the duplicate-BODY screen in `identifications`,
                  which sees `def` bodies and nothing else.
  mathlib         a corpus declaration whose name Mathlib already uses, which
                  means the corpus re-proved something upstream.  Name-based,
                  so it is a lower bound: a duplicate under a different name is
                  invisible to it.  It FAILS rather than passes when Mathlib's
                  source is absent, because it cannot look.
  laundering      a valid proof of a weaker, conditional, vacuous or circular
                  statement advertised under the intended theorem's name.
  regimes         external theorem packaging in production structures: a
                  scientific conclusion accepted from a caller and re-exported
                  by field projection.
  closure         a Descent module outside the root import closure, which
                  `lake build Descent` cannot validate and so cannot fail on.
  wiring          an upstream-arc module with no biological dependent: a result
                  adjacent to the corpus rather than wired into it.
  conventions     a quantity used under an unstated or contradictory convention,
                  and a numeric constant that has drifted from the value a source
                  paper gives.  Checked against `validation/conventions.json`,
                  which is the corpus's convention ledger; a definition whose name
                  carries a ledgered quantity and whose entry is missing FAILS, and
                  so does a ledger entry whose declaration no longer exists.
  ledger          the simulation-coverage verdict record against the docstrings:
                  a docstring citing a battery the ledger has never seen or whose
                  results are stale, a ledger row banking agreement with no
                  competing formula rejected on the same cells, and a definition
                  carrying contradictory verdicts with no adjudication.  Reads
                  `validation/empirical/simcov/ledger.json`, which is generated
                  and committed; the simulations themselves are NOT gated, and
                  `prover.yml` says why.  Calibrated by `test_ledger.py`.
  core-empirics   the same verdict record held against `Descent/Core/` alone,
                  at a standard the whole corpus could not carry: a Core
                  declaration with a FALSIFIED row that never names the battery,
                  one that has been measured and states no status of its own,
                  and one whose status head denies that any measurement can bear
                  on it.  Depth 0-1 is where an unstated verdict is an unstated
                  premise, so these are GATED at zero rather than reported.
  field-proofs    theorems whose ENTIRE proof is a structure-field projection,
                  measured on origin/main rather than the worktree.  DIAGNOSTIC,
                  not a gate: it has known false positives and never fails the
                  run.  It is excluded from the default set because it shells
                  out to git and reads a remote ref.

THE SHAPE GUARDS are five more, and they are a family rather than five checks
that happen to be adjacent.  Every one of them measures a property this corpus
has already been repaired to have and has already lost again, because the tree is
organised by the order a person would read it in and a reading order is invisible
to a build.  They read the import graph and the declaration index from
`architecture.py` rather than deriving either, and the only thing they add is an
exit code.

  shape-depth     the longest import chain, with the tables of contents removed.
                  A chain of thirty-eight modules in which each file imports the
                  one written before it is a manuscript order compiled into the
                  build graph.
  shape-chains    a module whose ONE internal import is a sibling in its own
                  directory that it names nothing from.  The finding prints where
                  the symbols it does name actually live, which is the import it
                  wanted.
  shape-components  a module outside the corpus's single weak component.
                  `Coalescent` was an island one release ago and `Pangenome` was
                  one in this release; both were wired in by hand, which is the
                  argument for the guard rather than against it.
  shape-spine     cross-module theorem reuse, and the count of theorems joining
                  `PopGenParameters` to a metric computed from the `Core/Moments`
                  kernel.  The second is the corpus's headline claim, counted.
  shape-routes    a definition taking four or more bare reals that shares a name
                  stem with a record-typed one: two routes to one metric, of
                  which only one carries the record's constraints.  GATED; the
                  other four are DIAGNOSTIC while their repairs land, and the
                  `GUARDS` entry for each names what flips it.

WHY ONE FILE.  These seven were seven scripts in three directories, and the cost
was not tidiness.  Three of them independently re-derived "which files are the
corpus" and the three answers disagreed; one walked `Descent/` and
could not see `Descent.lean`, the corpus root, which is a SIBLING of
that directory rather than a child.  Two definitions were deleted as unreferenced
on the strength of that blind spot.  There is now exactly one `REPO`, one
`CORPUS`, and one place to look.

A `sorry` IS PREFERRED TO EVERY PATTERN THESE GUARDS DETECT.  A `sorry` is an
honest, machine-visible, kernel-tracked hole that `Check.lean` reports as
`sorryAx`.  A laundered theorem is an invisible hole that every automated report
calls green.  When the intended statement is not proved, state the intended
statement and admit it; do not restate a provable shadow of it.
"""

from __future__ import annotations

import argparse
import collections
import glob
import json
import os
import re
import subprocess
import functools
import sys
import traceback
from collections import defaultdict
from dataclasses import dataclass, field as dc_field
from pathlib import Path

# The one answer to "where is the corpus".  check.py lives at
# validation/code/check.py, so parents[2] is the repository root.
REPO = Path(__file__).resolve().parents[2]

# DESCENT_CORPUS points every guard at a different tree, and exists so the guards
# can be CALIBRATED against fixtures rather than only ever run against the corpus.
#
# This is not a convenience.  A detector that reports nothing is
# indistinguishable from a clean corpus, so a guard's clean report is not
# evidence until it has been shown to fire on a planted defect AND stay silent on
# clean input.  Six of the seven guards here had no such control, and the cost was
# paid: a refactor rewrote the word `declarations` inside the wiring guard's own
# JSON keys and printed label, changing a machine-readable contract, and every
# guard still passed.  Nothing in the repository could have caught it.
#
# Unset, this is the repository root and nothing changes.  There is no
# intervening `proofs/` directory: this is a Lean repository, so the whole
# repository is the proofs, and `Descent/` sits at the top level beside the
# lakefile that names it.
CORPUS = Path(os.environ.get("DESCENT_CORPUS") or REPO)

# What findings are reported relative to.  It must track the tree actually
# scanned: `relative_to` RAISES on a path outside its argument, so a guard
# reporting relative to REPO aborts outright on any corpus outside the
# repository -- which is every fixture.  Since the scanned tree IS the
# repository root now, the two coincide for an ordinary run and still diverge
# for a fixture, which is the case that made them separate names.
CORPUS_BASE = CORPUS


def lean_sources(root: Path) -> list:
    """Every Lean source under `root`, in a stable order, excluding junk.

    One place decides what counts as a corpus file, because the alternative is
    what this replaced: four separate `rglob("*.lean")` walks, exactly one of
    which skipped AppleDouble `._*` files.  Those are resource forks written by
    macOS tar and by some copy tools; they are not UTF-8, they are not Lean, and
    a walk that includes them either crashes on decode or reports findings for a
    file nobody wrote.  Dotfiles are excluded for the same reason -- editor swap
    files and `.#` locks are not corpus, and `.lake/` -- the build cache and the
    vendored Mathlib checkout -- is excluded by that same rule.

    `lakefile.lean` is excluded BY NAME, and that exclusion became load-bearing
    when the corpus moved to the repository root.  It used to be excluded by
    accident of geography: the corpus was `proofs/` and the lakefile sat beside
    it, so no walk could reach it.  Now the walk starts at the root and would
    sweep it up, which would put build configuration through every corpus guard
    and hand `style_lean_files` -- which adds the lakefile deliberately, once --
    a second copy of it.  It is Lean-shaped and it is not corpus.
    """
    return sorted(
        path
        for path in root.rglob("*.lean")
        if not any(part.startswith(".") for part in path.parts)
        and path.name != "lakefile.lean"
    )


def read_source(path: Path) -> str:
    """Decode a corpus file, or fail with the file named.

    `read_text(encoding="utf-8")` raises `UnicodeDecodeError`, whose message
    names a byte offset and no path.  When that escapes a guard it aborts the
    whole run, and -- because the runner reported only the first failure -- every
    guard after it was silently skipped.  A decode failure is a finding about one
    file, so it is raised as one.
    """
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(
            f"{path.relative_to(CORPUS_BASE)}: not valid UTF-8 ({exc.reason} at byte "
            f"{exc.start}); a corpus file must be UTF-8"
        ) from exc

@functools.lru_cache(maxsize=1)
def corpus_capitalized_identifiers() -> frozenset:
    """Capitalised names the corpus itself defines.

    Mathlib names a declaration after the objects it mentions, so a capitalised
    head is correct exactly when it IS an identifier -- `Phi_nonneg` is about the
    definition `Phi`, `V_P_pos` about the field `V_P`,
    `GenerationalPopGenParameters_theta_eq_ploidy_form` about that structure.
    Rejecting every capitalised head therefore fails on correct names and would
    be "fixed" by renaming the theorem away from the thing it is about.

    The exemption is earned, not listed: a head is allowed only when some `def`,
    `structure`, `inductive`, `abbrev`, `class` or structure field in the corpus
    declares it.  A capitalised head that names nothing still fails.
    """
    names = set()
    decl = re.compile(
        r"(?m)^\s*(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
        r"(?:def|structure|inductive|abbrev|class)\s+([A-Za-z_][A-Za-z_0-9'.]*)"
    )
    field = re.compile(r"(?m)^\s{2,}([A-Z][A-Za-z_0-9']*)\s*:")
    for path in lean_sources(CORPUS):
        try:
            src = read_source(path)
        except ValueError:
            continue  # decode failures are reported by the guard that reads it
        for match in decl.finditer(src):
            names.add(match.group(1).rsplit(".", 1)[-1])
        for match in field.finditer(src):
            names.add(match.group(1))
    return frozenset(n for n in names if n and n[0].isupper())



# ======================================================================================
# GUARD: style -- mathlib style policy
#
# Was `validation/code/check.py`.
#
# Check repository Lean sources against the local mathlib style policy.
# ======================================================================================

# The header carries the LICENSE pointer and no authorship. The corpus is
# unattributed by choice, so a rule that demanded a specific name would now fail
# every file. What still matters -- and what this checks -- is that the licence
# notice is present and in the mathlib block form; a file with no header, or one
# that reintroduces a copyright holder, still fails.
STYLE_LICENSE_HEADER = (
    "/-\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "-/\n"
)


def style_lean_files() -> list[Path]:
    """Return source-controlled Lean-shaped files, excluding macOS resource forks."""
    # The lakefile is corpus for style purposes but sits beside `proofs/`
    # rather than inside it, and a fixture tree has none.
    files = [f for f in [CORPUS_BASE / "lakefile.lean"] if f.is_file()]
    files.extend(
        path for path in lean_sources(CORPUS)
    )
    return sorted(files)


def style_line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def style_check_file(path: Path) -> list[str]:
    source = path.read_text()
    rel = path.relative_to(CORPUS_BASE)
    errors: list[str] = []

    if not source.startswith(STYLE_LICENSE_HEADER):
        errors.append(f"{rel}:1: missing or nonstandard license header")

    lines = source.splitlines()
    for number, line in enumerate(lines, 1):
        if len(line) <= 100:
            continue
        # A markdown table row is atomic: wrapping it moves cells onto their own
        # lines and destroys the table, so reporting it asks for a change that
        # makes the docstring worse.  The rule is about lines a reader could
        # reflow; a row that opens and closes with `|` is not one.
        stripped = line.strip()
        if stripped.startswith("|") and stripped.endswith("|"):
            continue
        errors.append(f"{rel}:{number}: line has {len(line)} characters")

    module_doc = source.find("/-!")
    import_lines = [
        number
        for number, line in enumerate(lines, 1)
        if line.startswith("import ")
        and (module_doc == -1 or source.find(line) < module_doc)
    ]
    if module_doc == -1:
        errors.append(f"{rel}: missing module docstring")
    elif import_lines and style_line_number(source, module_doc) <= import_lines[-1]:
        errors.append(f"{rel}:{style_line_number(source, module_doc)}: module docstring precedes an import")

    if import_lines:
        expected_first_import = STYLE_LICENSE_HEADER.count("\n") + 1
        if import_lines[0] != expected_first_import:
            errors.append(
                f"{rel}:{import_lines[0]}: imports must immediately follow the license header"
            )
        last_import = import_lines[-1]
        if last_import >= len(lines) or lines[last_import] != "":
            errors.append(f"{rel}:{last_import}: imports must be followed by a blank line")

    theorem_pattern = re.compile(
        r"(?m)^\s*(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9'.]*)"
    )
    for match in theorem_pattern.finditer(source):
        local_name = match.group(1).rsplit(".", 1)[-1]
        known = corpus_capitalized_identifiers()
        names_an_identifier = any(
            local_name == ident or local_name.startswith(ident + "_") for ident in known
        )
        if local_name and local_name[0].isupper() and not names_an_identifier:
            errors.append(
                f"{rel}:{style_line_number(source, match.start())}: theorem name `{local_name}` "
                "must use snake_case"
            )

    for match in re.finditer(r"\bfun\s+[^\n]*?\s=>", source):
        errors.append(
            f"{rel}:{style_line_number(source, match.start())}: lambda must use `↦` rather than `=>`"
        )

    for match in re.finditer(r":=\s*\n\s+by\b", source):
        errors.append(
            f"{rel}:{style_line_number(source, match.start())}: put `by` on the declaration line"
        )

    history = re.compile(
        r"(?i)\b(?:earlier drafts?|previous versions?|originally defined|replaces? the old|"
        r"used to (?:be|use)|no longer uses? axioms?)\b"
    )
    for match in history.finditer(source):
        errors.append(
            f"{rel}:{style_line_number(source, match.start())}: documentation mentions development history"
        )

    return errors


def run_style() -> int:
    errors = [error for path in style_lean_files() for error in style_check_file(path)]
    if errors:
        print("LEAN STYLE FAILURES\n")
        print("\n".join(f"  {error}" for error in errors))
        return 1
    print(f"Lean style checks pass for {len(style_lean_files())} files")
    return 0


# ======================================================================================
# GUARD: identifications -- structural guards over the corpus
#
# Was `validation/code/check.py`.  Its full header, which carries the
# reasoning behind every budget and the record of two wrong deletions, is
# reproduced immediately below.
# ======================================================================================

#
# Guards, in order of what they catch:
#
# 1. Admissions. Every `sorry` is reported with its owning declaration. A visible
#    admission is incomplete mathematics, but it is preferable to a weakened
#    statement, a laundered premise, or a hidden axiom. `admit` remains forbidden
#    so the corpus has one explicit spelling for unresolved proof obligations.
#
#    The rule is: `sorry` is FREE TO WRITE and BUYS NOTHING. Free to write,
#    because a guard that fails the build on an admission while passing a
#    weakened statement has made honesty the most expensive option on the board
#    and will get what it pays for; `AxiomScan.admissible` records the same
#    decision at the kernel. Buys nothing, because guards 3m, 3n and 3p ignore
#    admitted declarations when deciding what has been established or inhabited.
#    Without that second half, `def witness : Bundle := sorry` would discharge
#    three screens at once by writing down the very assumption they look for.
#
# 2. Convention drift. Every numeric literal 2 or 4 used as a multiplier inside
#    a definition is a restatement of a ploidy or coalescent-scaling convention.
#    The count is pinned; adding new inline restatements without relating them
#    to `ploidy` in Conventions.lean fails, so the number can only go down.
#
# 3. Equilibria with no dynamic. A definition named for a rest point or a limit
#    must be derived as the fixed point of a process defined in the same file,
#    not stipulated as a closed form that no theorem can contradict.
#
# 4. Duplicate bodies across files. Two definitions in different modules whose
#    bodies are alpha-equivalent are one quantity written twice; unless one calls
#    the other or a theorem equates them, fixing one leaves the other wrong.
#
# DO NOT ADD A GUARD THAT DELETES DEFINITIONS BY REFERENCE COUNT. It was tried,
#    twice, and both times it removed correct work. Two failure modes, both proved
#    on 2026-02:
#
#    (a) WRONG ROOT. A scan walking `Descent/` cannot see
#        `Descent.lean`, the corpus root, which is a SIBLING of that
#        directory rather than a child. `decaySlope` was deleted as having "no use
#        anywhere"; its only consumer was a theorem in the root. `LDDecayMechanism`
#        was then deleted for having "lost its only consumer" -- the second
#        deletion inheriting the first's blind spot. The file list built below
#        includes `Descent.lean` explicitly for exactly this reason; do not
#        "simplify" it into a single recursive glob.
#
#    (b) UNREFERENCED BY DESIGN, which no reference count can detect.
#        `targetCorrectionCurvature` and `targetCorrectionOptimum` are applied by
#        nothing, AND THAT IS WHAT THEY ARE FOR: `sharedCorrectionConsensus` and
#        `sharedCorrectionSpread` take `curvature` and `optimum` as arbitrary
#        `ι → ℝ`, and these two say which functions the section is about. Their
#        section docstring claims the curvature weight is "forced rather than
#        stipulated" -- without them it is a free parameter, the spread law holds
#        for any weights whatsoever, and that sentence is false. A definition that
#        names which functions a section is ABOUT is unreferenced by design, so
#        every one of that category is a false positive waiting to be deleted.
#
#    Neither deletion broke the build, and that is the part to internalise. In (a)
#    Lean auto-binds an undefined bare name as an implicit variable, so the
#    consuming theorem kept elaborating as a claim about nothing. In (b) the
#    arguments were already abstract, so removing the definitions that gave them
#    meaning changed no type. ABSENCE OF A BUILD FAILURE IS NOT EVIDENCE THAT A
#    DELETION WAS SAFE. Before removing anything as unused, grep the FULL `proofs/`
#    tree -- root module and validation Python included -- and grep the PROSE, not
#    just the identifier: in both cases a docstring within a few lines of the
#    deletion site named the consumer outright.
#
# 5. Regimes baked into bodies. A definition whose value depends on an assumption
#    about the data-generating process -- closed population, no mutation, infinite
#    sites -- must name that assumption, because a formula carries no record of
#    the regime it was derived in and a use site cannot discharge what it cannot
#    see.
#
# 6. Validation inherited from a sibling identity. Over-determination detects
#    divergence between formulas and is provably blind to a premise they share, so
#    a VALIDATED tag must cite a measurement against an observable, never another
#    definition. Guards 6 and 7 exist because one wrong number was certified five
#    times, each time by a cross-check that could not have failed.
#
# 7. Validation with no power. A validation is evidence in proportion to the range
#    its prediction spanned; a design on which the prediction is constant cannot
#    reject a wrong functional form, however small the residual.
#
# 8. Laundered assumptions. An unproved proposition can be made to look proved
#    without a `sorry` and without an axiom: name it as a theorem, pass it as an
#    ordinary argument, bundle it into a setup structure, project that structure's
#    fields into local instances so they bind silently, and give the wrapper an
#    unconditional-sounding name. `#print axioms` stays clean through all five
#    moves, because an assumption discharged by the caller is invisible to a scan
#    that reads only the proof term. Four screens ask instead whether anything can
#    ever satisfy the hypothesis: a proposition never concluded (3m), a bundle
#    never inhabited (3n), a supplied field installed as an instance (3o), and a
#    result whose name hides what it rests on (3p). Every count must be zero.
#    Nothing is pinned at what was measured and nothing ratchets: a screen that
#    permits the defects already present has agreed to them.
#
#    Prefer `sorry`. An admission is a debt this corpus can enumerate; a laundered
#    premise is a debt it cannot, and guard 1 exists to keep the first cheap.
#
# 9. Trust-boundary syntax. Production proof modules may not declare custom
#    axioms, use native/compiler-backed decision procedures, introduce unsafe
#    declarations, or install custom syntax/elaborators.  These checks cover
#    explicit source constructs; the environment-level axiom scan remains
#    responsible for dependencies hidden behind imports or generated terms.
#
# Guards 5-7 are the subject of `Descent.DriftRegime`, which proves that 6 and 7
# are impossibilities rather than oversights.

# Was `os.path.join(os.path.dirname(__file__), "..", "proofs")` when this guard
# lived in `scripts/`.  It is now derived from the one `CORPUS` above, which is
# the point of the merge: three guards used to re-derive this and disagree.
IDENT_ROOT = str(CORPUS)

# THERE ARE NO BUDGETS. A screen that permits N existing instances of the defect
# it names is a screen that has agreed to the defect, and "it was already there"
# is not a standard. Every count above 0 fails the build.
#
# The last remnant of the old discipline was a table of the values seven screens
# carried before they were zeroed, printed beside any failure so a reader could
# tell progress from regression. It is deleted too. A number that no screen
# enforces is not a standard, and keeping it invited exactly the comparison the
# zeroing was meant to end -- "7 unwitnessed bundles, down from 38" reads as
# progress, and the standard says it is seven failures. `git log` still holds
# the history for anyone who wants it.

def ident_strip_comments(src: str) -> str:
    """Remove Lean block and line comments so prose cannot trip the guards."""
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if src.startswith("-/", i):
            depth = max(0, depth - 1); i += 2; continue
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j == -1 else j
            continue
        if depth == 0:
            out.append(src[i])
        elif src[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)

IDENT_BLOCK_OPEN = re.compile(r"[ \t]*(?:noncomputable[ \t]+)?(namespace|section|mutual)\b[ \t]*([^\s]*)[ \t]*$")
IDENT_BLOCK_CLOSE = re.compile(r"[ \t]*end\b[ \t]*([A-Za-z_0-9'À-￿.]*)[ \t]*$")

def ident_block_structure_errors(src: str):
    """Match `namespace`/`section`/`mutual` openers against their `end`s.

    An earlier form of this guard asked whether the file's last line was
    literally `end Descent`. That is only one of several correct ways to
    close the namespace: `end Descent.CertificateGrading` closes
    `namespace Descent.CertificateGrading`, and a matched inner `end Foo`
    followed by `end Descent` is equally correct. Both were reported as
    failures, which is how the guard came to flag every `BundleRigidity`
    module and one file got restructured to satisfy the guard rather than the
    language. What the check is actually for is a namespace that is opened and
    never closed, so it tracks a stack instead of inspecting the last line.
    """
    stack, errors = [], []
    for n, line in enumerate(src.splitlines(), 1):
        m = IDENT_BLOCK_OPEN.match(line)
        if m:
            stack.append((m.group(1), m.group(2), n))
            continue
        m = IDENT_BLOCK_CLOSE.match(line)
        if not m:
            continue
        name = m.group(1)
        if not stack:
            shown = f"`end {name}`" if name else "a bare `end`"
            errors.append(f"line {n}: {shown} closes nothing that is open")
            continue
        if not name:
            # A bare `end` closes an anonymous `section` or a `mutual` block.
            stack.pop()
            continue
        # `end A.B` closes a single `namespace A.B`, or a run of frames whose
        # names concatenate to it.
        depth, acc = None, []
        for k in range(len(stack) - 1, -1, -1):
            acc.insert(0, stack[k][1])
            if ".".join(x for x in acc if x) == name:
                depth = k
                break
        if depth is None:
            opened = ", ".join(f"{k} {nm}".strip() for k, nm, _ in stack) or "nothing"
            errors.append(f"line {n}: `end {name}` matches no open block (open here: {opened})")
            continue
        del stack[depth:]
    for kind, name, n in stack:
        errors.append(f"line {n}: `{kind} {name}`".rstrip() + " is never closed")
    return errors

def skip_attribute_block(lines, j):
    """Walk `j` back past blank lines and whole `@[...]` attribute blocks.

    AN ATTRIBUTE IS NOT ALWAYS ONE LINE. This used to skip only lines that
    THEMSELVES begin with `@[`, which is every `@[simp]` and no `@[withdrawn
    "tag" "a sentence of justification"]` -- that form wraps, so the line
    directly above the declaration is the tail of the attribute's string
    argument and matches nothing. The docstring above it then failed the
    `endswith("-/")` test and the declaration was read as carrying NO docstring
    at all, which for an `Empirical status:` marker is indistinguishable from
    carrying none: `ldTaggingDecay` documents a two-sided FALSIFICATION with a
    residual table and was counted as undeclared coverage debt.

    Blocks are matched by bracket balance rather than by a regex, because the
    justification strings contain prose and the block ends where the brackets
    close. An unbalanced or non-attribute `]` leaves `j` where it was, which is
    the old behaviour and the safe direction: a missed skip reports a status as
    absent, never a neighbour's status as this declaration's.
    """
    while j >= 0:
        if not lines[j].strip() or lines[j].lstrip().startswith("@["):
            j -= 1
            continue
        if not lines[j].rstrip().endswith("]"):
            break
        depth, k = 0, j
        while k >= 0:
            depth += lines[k].count("]") - lines[k].count("[")
            if depth <= 0:
                break
            k -= 1
        if k < 0 or depth != 0 or not lines[k].lstrip().startswith("@["):
            break
        j = k - 1
    return j


def ident_preceding_docstring(lines, i):
    """The whole `/-- ... -/` block attached to the declaration on line `i`.

    The status may be declared anywhere in a docstring, and these run to forty
    lines, so a fixed lookback window reports a declared status as missing and
    invites a second, contradictory marker next to the first. The block is
    delimited, so read the delimiters."""
    j = skip_attribute_block(lines, i - 1)
    if j < 0 or not lines[j].rstrip().endswith("-/"):
        return ""
    end = j
    while j >= 0 and "/--" not in lines[j]:
        # A `/-! -/` section header is not this declaration's docstring, and
        # walking past it would borrow the status of whatever precedes it.
        if "/-!" in lines[j] or "-/" in lines[j] and j != end:
            return ""
        j -= 1
    return "\n".join(lines[max(0, j):end + 1])

def ident_result_kind(args: str) -> str:
    """`"N::"` when a definition returns `ℕ`, and the empty string otherwise.

    The coarsest split that separates truncated natural subtraction from real
    subtraction, and deliberately no finer: a result type compared as WRITTEN would
    separate `Fin 2 → ℝ` from `TwoCoordinateConfiguration` and from `Fin 2 -> Real`,
    three spellings of one type, and every group it split that way would be a finding
    silenced rather than a false one removed.
    """
    result = args.rsplit(":", 1)[-1].strip() if ":" in args else ""
    return "N::" if result in ("ℕ", "Nat") else ""


def ident_lean_files():
    """Every corpus file, at any depth, plus the root module.

    THIS USED TO GLOB EXACTLY TWO LEVELS -- `Descent/*.lean` and
    `Descent/*/*.lean` -- and the corpus has since grown a third. Splitting
    `PortabilityDrift.lean` into `PortabilityDrift/` and
    `PopulationGeneticsFoundations.lean` into its own directory moved 54 ledgered
    declarations to depths this walk could not see, and the guard reported them
    as "no longer a `def`" in files they had merely moved out of; repointing the
    ledger at the new paths then produced "module is not in the corpus", because
    it was not, to this function. `PCCorrectability/Threshold.lean` had been
    reporting the same thing for far longer, and was written off as a known
    pre-existing failure rather than read as the depth bug it was.

    The two-level glob was deliberate about one thing and it is preserved: the
    root `Descent.lean` is a SIBLING of `Descent/`, not a child, so no walk of
    that directory reaches it and it is still added by name. The warning above
    against "a single recursive glob" is about that sibling, not about depth.
    `lean_sources` recurses and drops AppleDouble files, dotfiles and the
    lakefile, which is what the hand-rolled globs did not do.
    """
    root = Path(IDENT_ROOT)
    return [str(p) for p in lean_sources(root / "Descent")] + \
           [os.path.join(IDENT_ROOT, "Descent.lean")]

def run_identifications() -> int:
    bad = []
    admissions = []

    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        rel = os.path.relpath(f, IDENT_ROOT)

        for m in re.finditer(r'\bsorry\b', src):
            line = src[:m.start()].count("\n") + 1
            owner = None
            for d in re.finditer(r'^(?:noncomputable )?(?:def|theorem) ([A-Za-z_0-9\'.]+)', src[:m.start()], re.M):
                owner = d.group(1)
            admissions.append(f"{rel}:{line}: sorry in `{owner}`")

        forbidden = [
            (r"\badmit\b", "contains `admit`"),
            (r"(?m)^\s*(?:(?:private|protected)\s+)*axiom\b",
             "declares a custom axiom"),
            (r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:unsafe|partial)\b",
             "declares unsafe or partial code"),
            (r"\bnative_decide\b", "uses `native_decide`"),
            (r"\b(?:sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler)\b",
             "references a forbidden proof/compiler axiom directly"),
            (r"\b(?:implemented_by|csimp)\b",
             "changes the compiler implementation or simplification path"),
            # A TACTIC macro is exempt, and only a tactic macro.  What this screen
            # is for is elaboration that can change what a declaration MEANS:
            # `elab`, `macro_rules`, `initialize` and `run_cmd` all run code at
            # elaboration time, and a term-level `macro` rewrites the statement a
            # reader thinks they are reading.  `macro "t" : tactic => `(tactic|
            # simp [...])` does none of that -- it names a tactic call, the
            # statement is untouched, and the proof still has to close through the
            # kernel.  Refusing it pushes the corpus to copy the lemma list at
            # every use site instead, which is what the duplication guard is for.
            #
            # The escapes stay closed: `sorry`, `sorryAx` and `native_decide` are
            # screened over the whole file text, so a tactic macro cannot smuggle
            # one in.
            (r"(?m)^\s*(?:syntax|macro_rules|elab|elab_rules|initialize|builtin_initialize|run_cmd|run_tac)\b",
             "installs custom syntax, elaboration, or initialization code"),
            (r"(?m)^\s*macro\b(?![^\n]*:\s*tactic\s*=>)",
             "installs a non-tactic macro, which rewrites what a reader reads"),
            # --- Below: patterns with ZERO occurrences in the corpus when added.
            # Each is a ratchet, not a cleanup. They cost nothing to adopt and
            # each closes a way to make the kernel accept something without the
            # mathematics having been done.
            (r"(?m)^[ \t]*set_option\b",
             "sets a compiler option in a proof module: `debug.skipKernelTC` "
             "stops the kernel from checking the declaration at all, "
             "`debug.byAsSorry` turns every `by` block into a sorry, and "
             "`autoImplicit true` re-enables inside one file the very thing "
             "lakefile.lean disables for the library"),
            (r"(?m)^[ \t]*(?:(?:scoped|local)[ \t]+)*(?:notation|infixl|infixr|infix|prefix|postfix|notation3)\b",
             "rebinds notation: `+`, `≤`, `∈` or `‖·‖` bound to a convenient "
             "operation leaves every theorem statement in the file reading as "
             "ordinary mathematics while elaborating to something else"),
            (r"(?m)^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*opaque\b",
             "declares an `opaque` constant, which asserts an inhabitant "
             "without giving one -- for a `Prop` that is an axiom under "
             "another keyword"),
            (r"(?m)^[ \t]*attribute[ \t]*\[[^\]\n]*\binstance\b",
             "registers an instance by attribute, which puts a proposition "
             "where typeclass synthesis will find it without any use site "
             "naming it"),
            # A `Fact` instance is banned only when it takes a PARAMETER. The
            # distinction is the whole point, and the corpus has one instance on
            # each side of it.
            #
            # `local instance : Fact (2 ≤ 2) := ⟨by decide⟩` in Descent.lean
            # is closed and proved: it discharges the `[Fact (2 ≤ t)]` binders on
            # the two-locus definitions in DGP at `t = 2`, and `decide` settles
            # it outright. Nothing is being assumed, so there is nothing to
            # launder, and banning it would delete a proof.
            #
            # A PARAMETERIZED `Fact` instance is the opposite: it takes the
            # proposition, or something implying it, from its own argument and
            # then hands it to synthesis. Every later `simp` and every later
            # lemma application depends on it without any signature saying so,
            # which is precisely the invisibility guard 3o exists to prevent.
            (r"(?m)^[ \t]*(?:(?:local|scoped)[ \t]+)*instance\b[^\n]*[({\[][^\n]*:[ \t]*Fact\b",
             "declares a parameterized `Fact` instance: synthesis then supplies "
             "the proposition silently, and every proof that uses it looks like "
             "routine instance plumbing"),
            (r"(?m)^[ \t]*#(?:eval|reduce|print|check|exit)\b",
             "leaves an elaboration-time command in a proof module: `#eval` "
             "runs arbitrary `IO` while the file elaborates, which can rewrite "
             "the very artefacts a later step checks"),
            (r"@\[\s*extern\b", "binds a declaration to an external implementation"),
            (r"\b(?:exact|apply|rw|simp|try)\?",
             "leaves an exploratory suggestion tactic in production"),
            (r"(?m)^\s*hint\b", "leaves the exploratory `hint` command in production"),
        ]
        for pattern, reason in forbidden:
            if re.search(pattern, src):
                bad.append(f"{rel}: {reason}")

    # convention drift
    DOMAIN = re.compile(r"fst|drift|selection|herit|linkage|allele|geno|migrat|coalesc|mutation|"
                        r"epistat|domin|recomb|ancestr|spike|admix|haplo|polygenic|prevalence|"
                        r"liability|penetrance|pgs|gwas|singleton|winners|power|ncp|effect", re.I)
    DOMAIN_CASED = re.compile(r"^ld|(?:^|[a-z0-9])LD(?=[A-Z_]|$)")
    defpat = re.compile(r'^(?:noncomputable )?def ([A-Za-z_0-9\'.]+)(.*?)(?=\n(?:/-|@\[|theorem |noncomputable |def |abbrev |structure |section |end |namespace ))', re.S | re.M)
    # A convention restatement is a 2 or a 4 adjacent to a population-genetic
    # parameter: 2 Ne, 4 Ne mu, 2 p (1 - p). The 2 in a Gaussian density or in
    # a quadratic expansion is not a ploidy convention, and tying it to `ploidy`
    # would be wrong, so the pattern requires the neighbouring symbol.
    POP = r"(?:Ne|N|N_b|N₀|N₁|mu|μ|m|m_rate|m_into|mig|p|p0|p₁|p₂|p_bar|maf|fst|freq|theta|θ|sigma_sq)"
    mult = re.compile(r"(?<![\^A-Za-z_0-9.])[24]\s*\*\s*(?:\([^)]*\)|[A-Za-z_0-9.]*\.)?" + POP + r"\b"
                      r"|/\s*\(\s*[24]\s*\*\s*(?:[A-Za-z_0-9.]*\.)?" + POP + r"\b"
                      r"|\b(?:[A-Za-z_0-9]+\.)?" + POP + r"\s*\*\s*[24]\b")
    # Definitions that a theorem relates back to `ploidy` or to a derived
    # primitive are not loose restatements: their constant is forced.
    #
    # This used to accept a tie only from a file named `Conventions.lean`,
    # which located the tie by the file it sits in rather than by what it
    # says. That reading has the dependency backwards. A tying theorem
    # constrains a definition only where both are in scope, so the place it
    # belongs is BESIDE the definition -- and moving it there, which is the
    # repair, silently untied the definition and tripped this screen. It also
    # accepted any theorem in that file, including ones naming no convention at
    # all. The test is now what the statement mentions: a tie counts wherever
    # it is stated, and only when it actually reaches a convention primitive.
    PRIMITIVE = re.compile(r"\b(?:ploidy|scalingConstant|coalescentTimeScale|"
                           r"scaledMutationRate|scaledMigrationRate|"
                           r"hweHeterozygosity|genotypeVarianceHWE|"
                           r"islandDemeCorrection)\b")
    tied = set()
    for f in ident_lean_files():
        conv = ident_strip_comments(open(f).read())
        for b in re.split(r"\n(?=theorem )", conv):
            if not b.startswith("theorem"):
                continue
            stmt = b.split(":=", 1)[0]
            if not PRIMITIVE.search(stmt):
                continue
            tied.update(re.findall(r"[A-Za-z_][A-Za-z_0-9']*", stmt))

    sites = 0
    site_names = []
    for f in ident_lean_files():
        if f.endswith("Conventions.lean"):
            continue
        src = ident_strip_comments(open(f).read())
        for m in defpat.finditer(src):
            body = m.group(2)
            body = body.split(":=", 1)[1] if ":=" in body else ""
            body = re.sub(r'\^\s*[0-9]+', '', body)
            short = m.group(1).split(".")[-1]
            # A ploidy convention is restated inside a POPULATION-GENETIC definition.
            # Without that condition the screen read `2 * (Real.log (1 + θ ...))` in a
            # Cauchy conditioning profile as a ploidy factor, because `θ` is in the
            # neighbouring-symbol list for the sake of `4 Ne mu`. Tying that two to
            # `ploidy` would have recorded a claim about genetics the definition does
            # not make.
            if not (DOMAIN.search(short) or DOMAIN_CASED.search(short)):
                continue
            if mult.search(body) and short not in tied:
                sites += 1
                site_names.append(f"{os.path.relpath(f, IDENT_ROOT)}::{short}")
    # 3b. Undeclared empirical definitions. Every definition whose name carries
    #     domain vocabulary, or whose body contains a modelling constant, is a
    #     claim about an observable. It must declare an Empirical status, even
    #     if that status is UNTESTED. Four of the seven falsifications found so
    #     far were in definitions nobody had thought to check; the point of the
    #     marker is that the unchecked ones are enumerable rather than silent.
    #     The `ld` alternative CANNOT live in the case-insensitive pattern, and
    #     putting it there manufactured findings for as long as it was there.
    #     `ld[A-Z_]` is meant to catch linkage disequilibrium where the name
    #     spells it as a word: `ldDecay`, `sharedLDRetention`, `ld_overlap`.
    #     Under `re.I` the `[A-Z_]` class also matches lowercase, so the branch
    #     degenerates to "an l followed by a d, anywhere in the name" and fires
    #     in the middle of ordinary English. Every match it produced that way was
    #     mid-word and had nothing to do with linkage disequilibrium:
    #
    #       criticaLDEgree        Condensation.criticalDegree
    #       totaLDIploid...       FoldedSpectrum.totalDiploidCovarianceMomentInformation
    #       spectraLDIstance...   GenerativePortabilityLaw.historySpectralDistanceSq
    #       residuaLDIscreteness  ScoreDistribution.residualDiscreteness
    #
    #     A screen that invents its own findings is worse than a screen that
    #     misses some: the inventions cost a reader the time to refute them and
    #     teach everyone to discount the real ones. Marking those four with an
    #     Empirical status would have recorded a claim about linkage
    #     disequilibrium that none of them makes.
    #
    #     Dropping `re.I` alone is NOT the fix, and measuring said so. Bare
    #     `ld[A-Z_]` still matches every `threshold` followed by a capital --
    #     `thresholdQalyLoss`, `thresholdBandRate`, nine of them -- because
    #     "threshold" ends in the letters l, d. And it misses the eleven names
    #     that END in `LD` (`admixtureLD`, `bottleneckExcessLD`,
    #     `sourceTruthR2SharedLD`), since it requires a character after.
    #
    #     What the branch wants is `LD` as a word: the lowercase prefix at the
    #     start of a name, or the uppercase pair standing as its own camelCase
    #     segment. Written case-sensitively, and as a separate pattern rather
    #     than an inline `(?-i:...)` scope, which needs Python 3.11 and would
    #     fail on the cluster's 3.6.
    # A module-level `## Empirical status` section inside a `/-! ... -/` header.
    # Anchored at the start of a line so a declaration docstring's own heading
    # cannot be mistaken for one.
    MODULE_STATUS = re.compile(r"(?:^|\n)##+[ \t]*Empirical status\b")
    undeclared = []
    for f in ident_lean_files():
        raw = open(f).read().split("\n")
        stripped = ident_strip_comments(open(f).read()).split("\n")
        for i, line in enumerate(stripped):
            m = re.match(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)", line)
            if not m:
                continue
            short = m.group(1).split(".")[-1]
            body = "\n".join(stripped[i:i + 6])
            body = body.split(":=", 1)[1] if ":=" in body else ""
            if not (DOMAIN.search(short) or DOMAIN_CASED.search(short) or
                    mult.search(re.sub(r"\^\s*[0-9]+", "", body))):
                continue
            if "Empirical status:" in ident_preceding_docstring(raw, i):
                continue
            # A MODULE MAY DECLARE ONE FOR ALL OF ITS DECLARATIONS, and until
            # now nothing could see that it had.  `Descent/Core/Fst.lean` opens
            # with a `## Empirical status` section saying "None. The bodies here
            # are algebra: an equilibrium formula is a claim about a model, and
            # what carries an empirical status is a named quantity in a
            # subsystem module" -- which is the right verdict, is stated once
            # where it belongs, and would otherwise have to be copied onto five
            # declarations that share it.
            #
            # The section is a MODULE header (`/-! ... -/`) rather than a
            # declaration docstring, so it says nothing about any one `def` and
            # cannot be mistaken for one: `ident_preceding_docstring` is checked
            # first and wins wherever a declaration states its own.
            if MODULE_STATUS.search("\n".join(raw[:i])):
                continue
            undeclared.append(f"{os.path.relpath(f, IDENT_ROOT)}: `{short}` has no Empirical status")
    if undeclared:
        bad.append(f"definitions making an empirical claim without an Empirical status marker: "
                   f"{len(undeclared)}")
        bad.extend("    " + u for u in undeclared)

    # 3c. Unrelated same-quantity definitions. Two definitions are the same
    #     quantity when their bodies agree after renaming that definition's own
    #     bound variables, and the shared body contains a constant or a named
    #     function rather than being pure operator shape: `2 p (1 - p)` counts,
    #     `a + b` does not. A group spanning two modules with no theorem
    #     mentioning two of its members is a divergence nothing can detect,
    #     which is how amInflationFactor and fstFromDrift survived.
    bodypat = re.compile(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)(.*?):=\s*\n?\s*(.+?)"
                         r"(?=\n(?:@\[|theorem |noncomputable |def |abbrev |structure |section |end |namespace |/-))",
                         re.S | re.M)
    groups = {}
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        mod = os.path.basename(f)[:-5]
        for m in bodypat.finditer(src):
            name, args, body = m.group(1), m.group(2), " ".join(m.group(3).split())
            if len(body) > 80:
                continue
            bound = set(re.findall(r"[A-Za-z_][A-Za-z_0-9₀-₉']*", args))
            # Binders collapse to ONE placeholder, which is coarser than the
            # alpha-equivalence screen below, and knowingly so.
            #
            # It has a false positive it cannot avoid: `dotProduct left right` and
            # `dotProduct v v` normalise alike, so `configurationOverlap` at `Fin 2`
            # and `transplantSqNorm` at `Fin 3` are reported as one quantity, and no
            # equation between them typechecks. Numbering the binders positionally
            # fixes that pair -- and takes this screen from 2 findings to 65, because
            # the coarse key was ALSO grouping unrelated arities into hubs where each
            # member counted as tied through some sibling. Those 63 are latent in the
            # corpus, not invented by the sharpening; they are a corpus-sized project
            # and they are recorded here rather than either silently kept hidden or
            # dumped into a report nobody can act on. Do not pin a budget to them.
            norm = re.sub(r"[A-Za-z_][A-Za-z_0-9₀-₉'.]*",
                          lambda t: "V" if t.group(0) in bound else t.group(0), body)
            if not re.search(r"[0-9]|[A-Za-z_]{3,}", norm.replace("V", "")):
                continue
            # `n - 1` at `ℕ` and `x - 1` at `ℝ` read alike and are different
            # operations -- one truncates -- and no equation between them typechecks,
            # so grouping them asks for a repair nobody can write. Only THAT split is
            # made: keying on the result type as written would separate `Fin 2 → ℝ`
            # from `TwoCoordinateConfiguration`, which are the same type under two
            # spellings, and would silence findings rather than sharpen them.
            groups.setdefault(ident_result_kind(args) + norm, []).append(
                (mod, name.split(".")[-1]))
    all_stmts = []
    for f in ident_lean_files():
        for b in re.split(r"\n(?=@\[simp\]\s*\n?theorem |theorem |private theorem )",
                          ident_strip_comments(open(f).read())):
            if re.match(r"(?:@\[simp\]\s*)?(?:private )?theorem ", b) and ":=" in b:
                all_stmts.append(b.split(":=", 1)[0])
    # A definition tied to a shared primitive is related in the stronger sense: its whole
    # group is pinned to one object rather than to each other pairwise. Credit that, or the
    # metric penalises exactly the refactor it exists to encourage.
    #
    # The hub is `Descent/Core`, not a file named `Conventions.lean`. This read the filename
    # for the same reason the ploidy screen above once did, and it has the same defect,
    # recorded there: it locates the conventions by where they used to sit rather than by
    # what they are. `Descent/Program/Conventions.lean` DEFINED the shared kernels at depth
    # 22; the repair moved every one of them down into `Core`, where each is beside the
    # definitions it pins and where every module already reaches it, and then the emptied
    # file was deleted. `geometricDecay` -- this credit's own worked example, cited below as
    # `Conventions.geometricDecay` -- is `Core/Ratios.lean:324`.
    #
    # So the set being consulted was empty, and had been since the move. Every group
    # correctly factored through a shared kernel was reported as pinned to nothing, which
    # is the penalty the paragraph above exists to prevent, landing on the refactor that
    # earned the credit.
    primitives = set()
    for f in ident_lean_files():
        if "/Core/" not in f.replace(os.sep, "/"):
            continue
        for m in re.finditer(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)",
                             ident_strip_comments(open(f).read()), re.M):
            primitives.add(m.group(1).split(".")[-1])

    unrelated = []
    for norm, members in groups.items():
        if len({m for m, _ in members}) < 2:
            continue
        names = [n for _, n in members]
        for n in names:
            tied = any(
                re.search(r"\b" + re.escape(n) + r"\b", st) and
                (any(re.search(r"\b" + re.escape(o) + r"\b", st) for o in names if o != n) or
                 any(re.search(r"\b" + re.escape(pr) + r"\b", st) for pr in primitives))
                for st in all_stmts)
            if not tied:
                unrelated.extend(f"{m}:{n}" for m, n in members)
    unrelated = sorted(set(unrelated))
    if unrelated:
        bad.append(f"same-quantity definitions never related to a sibling by any theorem: "
                   f"{len(unrelated)}")
        bad.extend("    " + item for item in unrelated)

    # 3d. Missing-argument screen. Six of the eleven falsified definitions failed
    #     the same way: the signature omits an argument the named quantity is
    #     known to depend on. No constant repairs such a definition, and the
    #     defect is visible statically, without any simulation. Each entry is a
    #     name pattern together with the arguments that quantity must depend on.
    PREVALENCE_FREE = {"populationAUC"}   # rank definition, prevalence-free by construction
    REQUIRED_ARGS = [
        (r"power",            [r"alpha", r"z_?alpha", r"threshold", r"level"],
         "statistical power depends on the significance threshold"),
        # NOT a bare `auc` under `re.I`: those three letters sit inside `cauchy`, and
        # the pattern spent two findings on `cauchyConditioningProfile` and
        # `CauchyConditioningStationary` -- a Cauchy matrix's conditioning does not
        # depend on disease prevalence, and no argument would have repaired it.
        # Written case-sensitively, as `AUC` standing as its own camelCase segment.
        (re.compile(r"(?:AUC|Auc|auc)(?![a-z])"),
                              [r"prev", r"k\b", r"pi\b", r"baseRate"],
         "AUC under a threshold model depends on prevalence"),
        (r"winner|curse",     [r"alpha", r"z_?alpha", r"threshold"],
         "selection bias depends on the selection threshold"),
        (r"singleton|sfs",    [r"\bn\b", r"nsamp", r"sampleSize"],
         "site-frequency quantities depend on sample size"),
        (r"aminflation|assortativeinflation",
                              [r"h2", r"herit"],
         "assortative-mating inflation depends on heritability"),
        (r"ldamplif|amplifld|bottlenecklD",
                              [r"\br\b", r"recomb", r"\bc\b"],
         "LD amplification depends on the recombination rate"),
        # Measured in validation/empirical/simcov. Both entries below
        # cost a falsified definition each, and both were invisible to every
        # other screen because the BODY is unobjectionable -- what is wrong is
        # that no value of the arguments can make it right.
        (r"freqcorr|frequencycorrel|allelefreqcorr",
                              [r"var", r"spread", r"ancestral", r"\bsd\b"],
         "the allele-frequency correlation is Var(p0)/(Var(p0)+F*E[p0(1-p0)]); "
         "at FIXED F_ST the measured correlation runs 0.0004 to 0.7209 as the "
         "ancestral spread changes, so no function of F_ST alone can be it"),
        # NOT a bare `island`: `continentIsland...` names a two-population model
        # in which a deme count is not a parameter at all, and flagging it would
        # be inventing a finding. The pattern wants the symmetric island model.
        (r"(?<!continent)island|migrationmutationequil|migrationdriftequil",
                              [r"ndeme", r"demes", r"\bn\b", r"\bd\b", r"islands"],
         "island-model F_ST depends on the deme count: at fixed 4*Ne*m the "
         "simulated F_ST runs 0.117 at two demes to 0.186 at twenty"),
    ]
    # A definition MAY omit an argument it depends on, but only by declaring the
    # regime in which the omission is exact. `fstMigrationMutationEquilibrium`
    # is the many-deme limit and is right there; what made it a defect was that
    # nothing said so, so a reader at two demes got a number 8.2 sems wrong with
    # no warning attached. A declared regime is a claim someone can check; a
    # silent one is the failure this screen exists to stop.
    REGIME_DECLARED = re.compile(r"\bRegime:|\blimit\b|\bmany-deme\b|"
                                 r"\bapproximation\b|\basymptotic\b", re.I)
    # `power` is two words. Statistical power is a probability and depends on the
    # significance threshold; an algebraic power is an exponent and depends on
    # nothing but itself. A definition that TAKES the exponent as a natural-number
    # argument -- `entryPowerSum (covariance) (order : ℕ)`, `ldPowerScore
    # (covariance) (power : ℕ) (j)` -- is using the second word, and asking it for
    # a significance threshold is asking a sum of `q`-th powers to declare an
    # alpha level.
    EXPONENT_ARG = re.compile(r"\b(power|order|exponent|degree)\b[^:)]*:\s*ℕ")
    # That test reads the exponent's NAME, so it sees `ldPowerScore (power : ℕ)` and misses
    # `power (a : ℝ) (n : ℕ) := a ^ n` -- the corpus's own algebraic power, whose exponent is
    # called `n` like every exponent in ordinary mathematical writing. The decisive evidence
    # is not what the binder is called but what the body DOES with it: a definition that
    # raises something to a natural-number binder is exponentiating, and asking `a ^ n` for a
    # significance threshold is asking the same of `Nat.pow`.
    NAT_BINDER = re.compile(r"[({]\s*([^:()}{]+?)\s*:\s*(?:ℕ|Nat)\s*[)}]")

    def exponentiates(args: str, tail: str) -> bool:
        for b in NAT_BINDER.finditer(args):
            for v in b.group(1).split():
                if re.search(r"\^\s*\(?\s*" + re.escape(v) + r"\b", tail):
                    return True
        return False

    # A MONOTONE ARGUMENT IS NOT THE OBSERVABLE. `aucArgument` is `R²/(1-R²)`, and its
    # docstring states the relation exactly: "the equal-variance Gaussian AUC is `Φ` of a
    # strictly increasing function of this". Naming the argument rather than writing a wrong
    # closed form is a deliberate discipline here -- the corpus has no Mathlib `Φ` -- and
    # every ordering statement about the AUC is one about the argument, which is the whole
    # point of isolating it. Prevalence enters when a liability scale is carried to an
    # observed one; it does not enter `R²/(1-R²)`, and no binder could be added that the
    # quantity depends on. So this screen must read the trailing segment: `<X>Argument` is
    # what X is a function OF, not X.
    MONOTONE_ARGUMENT = re.compile(r"(?:Argument|Arg)$")
    missing = []
    REQUIRED_ARGS = [(p if hasattr(p, "search") else re.compile(p, re.I), a, w)
                     for p, a, w in REQUIRED_ARGS]
    for f in ident_lean_files():
        raw_lines = open(f).read().split("\n")
        body_all = ident_strip_comments(open(f).read())
        # The signature runs to `:=`, not to the first colon.  Stopping at the first
        # colon showed this screen only the FIRST binder, so a definition that takes
        # the argument in its second binder was reported for not taking it at all.
        for m in re.finditer(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)"
                             r"((?:(?!:=|\bwhere\b)[\s\S])*)(?::=|\bwhere\b)",
                             body_all, re.M):
            name, args = m.group(1).split(".")[-1], m.group(2)
            if name in PREVALENCE_FREE or re.search(r"gaussian|interval|approximation", name, re.I):
                continue   # name declares the model it is exact for, or is a wrapper
            if MONOTONE_ARGUMENT.search(name):
                continue   # the argument of the formula, not the formula
            tail = re.split(r"\n(?=@\[|theorem |def |noncomputable |abbrev |instance |end )",
                            body_all[m.end():], maxsplit=1)[0]
            doc = ident_preceding_docstring(raw_lines, body_all[:m.start()].count("\n"))
            # A `Prop` RELATING metrics does not compute one, so it cannot have
            # omitted an argument the computation depends on: `AucDropsAndCitlWorsens`
            # takes the two AUCs as arguments, and whatever prevalence they were read
            # at is already inside them.
            if re.search(r":\s*Prop\s*$", args.rstrip()):
                continue
            for pat, needed, why in REQUIRED_ARGS:
                if not pat.search(name):
                    continue
                if any(re.search(a, args, re.I) for a in needed):
                    continue
                if pat.pattern == r"power" and (EXPONENT_ARG.search(args) or
                                                exponentiates(args, tail)):
                    continue
                if REGIME_DECLARED.search(doc):
                    continue   # omission is exact in a regime the docstring names
                missing.append(f"{os.path.relpath(f, IDENT_ROOT)}: `{name}` takes no "
                               f"{needed[0]}-like argument and declares no regime; {why}")
    if missing:
        bad.append(f"definitions omitting an argument the named quantity depends on: "
                   f"{len(missing)}")
        bad.extend("    " + x for x in missing)

    # 3d-ter. UNRESOLVED CANDIDATE. A definition whose own docstring calls it a
    #     candidate, an alternative, or a form retained for comparison, and which
    #     has never been discriminated from the sibling it is an alternative TO.
    #     Retaining both is defensible exactly until a measurement can separate
    #     them, and not one line past it: `steppingStoneFstQuadratic` sat here
    #     with its rival through a log-log slope of 0.959 against its predicted
    #     2, and `pairwiseFstFromBranchTaus` through a fifty percent error.
    #
    #     Lean cannot raise this. Both members of a fork typecheck, both admit
    #     junk-value and monotonicity theorems, and a `def` is a stipulation --
    #     there is nothing in it for the kernel to disagree with. A green build
    #     is evidence about the ALGEBRA and no evidence at all about which of two
    #     rival formulas is the observable. That is the whole gap the Empirical
    #     status markers cover, and this screen makes one corner of it fail loud.
    CANDIDATE_PHRASE = re.compile(
        r"offered as a candidate|is a candidate|as a candidate for|"
        r"retained so that|the alternative form|competing form|rival form|"
        r"the form the previous", re.I)
    unresolved = []
    for f in ident_lean_files():
        raw = open(f).read()
        for m in re.finditer(r"/--((?:(?!-/).)*)-/\s*\n(?:noncomputable )?def ([A-Za-z_0-9'.]+)",
                             raw, re.S):
            doc, name = m.group(1), m.group(2).split(".")[-1]
            if not CANDIDATE_PHRASE.search(doc):
                continue
            if re.search(r"Empirical status:\s*[*_ ]*(VALIDATED|FALSIFIED|MEASURED|TESTED)", doc):
                continue
            unresolved.append(f"{os.path.relpath(f, IDENT_ROOT)}: `{name}` declares itself an "
                              f"alternative but carries no discriminating measurement")
    if unresolved:
        bad.append(f"self-declared alternatives never discriminated from their sibling: "
                   f"{len(unresolved)}; measure the "
                   f"two apart or drop one")
        bad.extend("    " + x for x in unresolved)

    # 3d-quater. UNRESOLVED FORK. Two definitions of ONE observable, related to
    #     each other by an inequality or a difference but never by an equality,
    #     with neither carrying a measurement. The corpus can then compute two
    #     different numbers for one quantity and prove theorems about both, and
    #     the theorem relating them certifies only that they DIFFER.
    #
    #     `pairwiseFstFromBranchTaus` against `coalFst` is the worked example:
    #     0.50 against 0.33 on one simulated split, with
    #     `pairwiseFstFromBranchTaus_lt_pairwiseFstFromBranches` stating only
    #     that one lies below the other. Guard 3c screens same-BODY duplicates;
    #     a fork has different bodies by construction and walks straight through.
    #
    #     ENFORCED, at zero, like everything else here -- the "advisory until
    #     the count is measured once and pinned" this used to promise was never
    #     what the code did, which appends to `bad` below.
    OBSERVABLE_GROUPS = [
        ("F_ST", re.compile(r"fst|gst", re.I)),
        ("heterozygosity", re.compile(r"^het|heterozyg", re.I)),
        ("AUC", re.compile(r"auc", re.I)),
        ("portability", re.compile(r"portab", re.I)),
    ]
    # THE STATUS HEAD IS A CLOSED VOCABULARY and this screen was reading four of its
    # seventeen terms. `admixedFst` carries `MIXED -- NUMERATOR VALIDATED ... FALSIFIED as a
    # whole F_ST at 14.16 sems`, and `fstMigrationDriftEquilibrium` carries
    # `CONDITIONALLY VALID` beside simulation figures at 40, 10, 5 and 2 demes. Both were
    # counted as carrying no measurement, so a fork with a measured side was reported as one
    # with neither side measured, and the repair demanded -- measure the two apart -- had
    # already been done on one of them. `TESTED` is not a term in the vocabulary at all.
    #
    # The split is by what the vocabulary's own gloss says about whether a measurement bears
    # on the body. VACUOUS and AN IDENTITY are excluded although they mention a measurement:
    # the vocabulary defines them as comparisons that could not have failed, which is exactly
    # what this screen means by unmeasured. NOT TESTED BY THE DESIGN THAT LOOKED LIKE IT WAS
    # is excluded for the reason it exists -- the measurement is about a different quantity.
    MEASURED_STATUS = {"VALIDATED", "MEASURED", "FALSIFIED", "MIXED", "CONDITIONALLY VALID",
                       "DISAGREES WITH AN EXISTING MEASUREMENT"}
    UNMEASURED_STATUS = {"UNTESTED", "DERIVED", "VACUOUS", "ASSERTED", "THIS IS THE MODEL",
                         "NOT AN EMPIRICAL CLAIM", "NOT EMPIRICALLY TESTABLE",
                         "NOT TESTED BY THE DESIGN THAT LOOKED LIKE IT WAS",
                         "EXACT BY CONSTRUCTION", "AN IDENTITY", "CONVENTION PINNED"}
    try:
        vocab = set(json.loads((CORPUS.parent / CONVENTION_LEDGER).read_text())
                    ["empirical_status_vocabulary"]["terms"])
    except Exception:
        vocab = set()
    # A term the ledger declares and this screen has not classified would otherwise default
    # to unmeasured in silence, which is how a vocabulary that drifts stops being countable.
    unclassified = sorted(vocab - MEASURED_STATUS - UNMEASURED_STATUS)
    if unclassified:
        bad.append(f"status terms declared in {CONVENTION_LEDGER} that the fork screen "
                   f"cannot classify as measured or not: {', '.join(unclassified)}")

    def status_is_measured(doc: str) -> bool:
        """The head -- text up to the first bracket, dash, comma, stop or newline."""
        m = re.search(r"Empirical status:\s*[*_ ]*([^\n]*)", doc)
        if not m:
            return False
        head = re.split(r"\s+--|[(\[{,.;:\n]|\s-\s", m.group(1).replace("*", ""))[0]
        return head.strip().upper() in MEASURED_STATUS

    # TWO NUMBERS FOR ONE QUANTITY is what this screen is about, so only a definition that
    # computes a number can be a side of a fork. `commonOnlyPortableModel` and
    # `commonAndRarePortableModel` are instances of `CrossPopulationMetricModel 2 2` -- a
    # matched pair of WITNESSES, sixteen fields copied and two overridden, built so that one
    # comparison can be made between them. The inequality relating them is not a symptom of
    # an unresolved fork, it is the construction's entire purpose, and an equality between
    # them would defeat it. No measurement could resolve them apart, because neither is a
    # claim about a population.
    SCALAR_RESULT = re.compile(r"^(?:ℝ|ℚ|ℤ|ℕ|Real|NNReal|EReal|ℝ≥0(?:∞)?)$")
    def_status, all_defs = {}, []
    for f in ident_lean_files():
        raw_lines = open(f).read().split("\n")
        src = ident_strip_comments(open(f).read())
        for dm in re.finditer(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)"
                              r"((?:(?!:=|\bwhere\b)[\s\S])*)(?::=|\bwhere\b)", src, re.M):
            i = src[:dm.start()].count("\n")
            sig = dm.group(2)
            if not SCALAR_RESULT.match(sig.rsplit(":", 1)[-1].strip() if ":" in sig else ""):
                continue
            nm = dm.group(1).split(".")[-1]
            all_defs.append(nm)
            doc = ident_preceding_docstring(raw_lines, i)
            def_status[nm] = status_is_measured(doc)
    forks = set()
    for _label, pat in OBSERVABLE_GROUPS:
        # DEDUPLICATED. `all_defs` is a list of short names over the whole corpus, so a name
        # declared in two modules appears twice, and `present` then held the SAME name twice
        # from a single occurrence in the statement. That cleared both the "at least two
        # definitions" test and the "at least two unmeasured" test on one definition, and
        # reported `portabilityRatio vs portabilityRatio` -- a fork of a definition with
        # itself, which no repair could resolve because there is nothing to measure apart.
        # A LOSS IS NOT THE QUANTITY IT IS A LOSS OF. `predictedPortability` is a retained
        # fraction and `relativePortabilityLoss` is `lostEffectMass / sourceEffectMass`; they
        # are different observables that share the letters "portab", and an inequality
        # between a quantity and a shortfall is the expected relation rather than an
        # unresolved fork. Demanding they be measured apart asks for a design separating a
        # thing from its own complement.
        COMPLEMENT = re.compile(r"Loss|Gap|Drop|Deficit|Shortfall|Difference|Reduction|"
                                r"Decay|Penalty|Bias|Error")
        members = sorted(set(n for n in all_defs if pat.search(n)))
        if any(COMPLEMENT.search(n) for n in members):
            members = [n for n in members if not COMPLEMENT.search(n)]
        if len(members) < 2:
            continue
        for f in ident_lean_files():
            src = ident_strip_comments(open(f).read())
            for tm in re.finditer(r"^theorem\s+[A-Za-z_0-9'.]+(.*?):=", src, re.S | re.M):
                stmt = tm.group(1)
                present = [n for n in members if re.search(r"\b" + re.escape(n) + r"\b", stmt)]
                if len(present) < 2:
                    continue
                concl = stmt.split(":", 1)[-1]
                if re.search(r"(?<![<>≤≥≠!])=(?!=)", concl):
                    continue          # the theorem asserts agreement: not a fork
                if not re.search(r"[<>≤≥≠]", concl):
                    continue
                if sum(1 for n in present if not def_status.get(n)) >= 2:
                    forks.add(tuple(sorted(present)))
    if forks:
        bad.append(f"definitions of one observable related only by an inequality, neither "
                   f"measured: {len(forks)}")
        bad.extend("    " + " vs ".join(x) for x in sorted(forks))

    # 3d-bis. Overclaiming. Two of the falsified definitions carried the word
    #     "exact" in a docstring while being 26 percent wrong. A definition may
    #     claim exactness or derivation, or it may be untested, but not both:
    #     an untested definition has no standing to call itself exact.
    overclaim = []
    for f in ident_lean_files():
        raw = open(f).read()
        for m in re.finditer(r"/--((?:(?!-/).)*)-/\s*\n(?:noncomputable )?def ([A-Za-z_0-9'.]+)", raw, re.S):
            doc, name = m.group(1), m.group(2).split(".")[-1]
            if "Empirical status: UNTESTED" not in doc:
                continue
            claim = re.search(r"\b(exact|exactly|derived from first principles|"
                              r"the true |precisely)\b", doc, re.I)
            if claim:
                overclaim.append(f"{os.path.relpath(f, IDENT_ROOT)}: `{name}` is UNTESTED but its "
                                 f"docstring claims \"{claim.group(1)}\"")
    if overclaim:
        bad.append(f"untested definitions whose docstring claims exactness: "
                   f"{len(overclaim)}")
        bad.extend("    " + x for x in overclaim)

    # 3f. Convention declarations on composable quantities. A definition
    #     producing a quantity and another consuming it can disagree about its
    #     convention while both remain defensible alone, and Lean cannot object
    #     because both are real-valued. ldCorrelationSq returned r-squared over
    #     four when fed the D that admixtureLDTwoLocus produces, 350 lines apart
    #     in one file. Any definition taking an ambiguity-prone argument must
    #     state the convention it assumes.
    AMBIGUOUS = [
        (r"\bD\b", "linkage disequilibrium: haplotype D or dosage covariance (differ by ploidy)"),
        (r"\bvar_tag\b|\bvar_causal\b", "variance: allelic p(1-p) or genotypic 2p(1-p)"),
        (r"\bmaf\b|\bmaf_causal\b|\bmaf_tag\b",
         "allele frequency: of the causal variant or of the tag, which differ once r < 1"),
    ]
    undeclared_conv = []
    for f in ident_lean_files():
        raw = open(f).read()
        for m in re.finditer(r"/--((?:(?!-/).)*)-/\s*\n(?:noncomputable )?def ([A-Za-z_0-9'.]+)([^:]*):",
                             raw, re.S):
            doc, name, args = m.group(1), m.group(2).split(".")[-1], m.group(3)
            for pat, why in AMBIGUOUS:
                if re.search(pat, args) and "Convention:" not in doc:
                    undeclared_conv.append(
                        f"{os.path.relpath(f, IDENT_ROOT)}: `{name}` takes an ambiguity-prone "
                        f"argument and declares no Convention; {why}")
                    break
    if undeclared_conv:
        bad.append(f"definitions taking an ambiguity-prone quantity with no declared "
                   f"convention: {len(undeclared_conv)}")
        bad.extend("    " + x for x in undeclared_conv)


    # 3g. Naming conflation. One formula carrying names from different concept
    #     families is how allelicVariance came about: 2p(1-p) is correctly the
    #     genotype variance and correctly the HWE heterozygote frequency, and is
    #     not the allelic variance, which is p(1-p). The r-squared-over-four
    #     defect was inherited from that name, not slipped in the formula. Where
    #     one body carries names from two families, each must say what it
    #     denotes.
    FAMILY = {
        "variance": r"variance|var\b", "frequency": r"freq|maf|prop",
        "heterozygosity": r"heteroz|het\b", "rate": r"rate",
        "factor": r"factor|retention|decay", "fst": r"fst",
    }
    bodies = {}
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        for m in re.finditer(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)(.*?):=\s*\n?\s*(.+?)"
                             r"(?=\n(?:@\[|theorem |noncomputable |def |abbrev |structure |section |end |namespace |/-))",
                             src, re.S | re.M):
            name, args, body = m.group(1).split(".")[-1], m.group(2), " ".join(m.group(3).split())
            if len(body) > 60:
                continue
            bound = set(re.findall(r"[A-Za-z_][A-Za-z_0-9₀-₉']*", args))
            norm = re.sub(r"[A-Za-z_][A-Za-z_0-9₀-₉'.]*",
                          lambda t: "V" if t.group(0) in bound else t.group(0), body)
            if not re.search(r"[0-9]", norm):
                continue
            bodies.setdefault(norm, []).append((f, name))
    conflated = []
    for norm, members in bodies.items():
        fams = {fam for _, n in members for fam, pat in FAMILY.items() if re.search(pat, n, re.I)}
        if len(fams) < 2:
            continue
        for f, n in members:
            doc = ""
            raw = open(f).read()
            dm = re.search(r"/--((?:(?!-/).)*)-/\s*\n(?:noncomputable )?def " + re.escape(n) + r"\b", raw, re.S)
            if dm:
                doc = dm.group(1)
            if "Denotes:" not in doc:
                conflated.append(f"{os.path.relpath(f, IDENT_ROOT)}: `{n}` shares a formula with names "
                                 f"from {sorted(fams)} and declares no Denotes")
    if conflated:
        bad.append(f"definitions sharing one formula across concept families with no Denotes "
                   f"declaration: {len(conflated)}")
        bad.extend("    " + x for x in conflated)


    # 3h. Equilibrium without a dynamic. `selectionMigrationEquilibrium s m =
    #     s / (s + m)` was a stipulated closed form, wrong by 4 to 14x and
    #     qualitatively wrong where the allele is lost, yet every theorem about
    #     it was true: value-guards bound a quantity into (0,1) and order it the
    #     right ways, and none of that can pin a constant. Only the process the
    #     equilibrium is an equilibrium *of* can. So a definition named for a
    #     limit or a rest point owes a theorem identifying it as the fixed point
    #     of some other definition in the same file, in the shape of
    #     `selectionMigrationEquilibrium_isFixedPoint`.
    EQUILIBRIUM_CONCEPTS = ("equilibrium", "fixedpoint", "steadystate", "stationary",
                            "limiting", "asymptotic", "balance", "equilibriumfreq")
    FIXEDPOINT_MARKERS = ("isFixedPoint", "_fixedPoint", "_isLimit", "_tendsto")

    def word_starts(name):
        """Offsets at which a camelCase or underscore-separated word begins.

        Substring matching alone reads `globalAncestry` as containing
        `balance`, so a concept counts only where a word does."""
        return {0} | {i for i in range(1, len(name))
                      if name[i - 1] in "_'" or name[i].isupper() or name[i].isdigit()}

    def word_ends(name):
        """Offsets immediately after camelCase or underscore-delimited words."""
        return {len(name)} | {i for i in range(1, len(name))
                             if name[i] in "_'" or name[i].isupper() or name[i].isdigit()}

    def is_prop_shaped(sig, body):
        """Prop-valued by shape, not by name.

        Either the declared return type is `Prop`, or -- for a definition that
        leaves the type to inference -- the body is a proposition rather than a
        value: quantified, or an iff. A value-returning definition never starts
        its body with a quantifier."""
        if re.search(r":\s*Prop\s*$", sig.strip()):
            return True
        b = body.strip()
        return b.startswith("∀") or b.startswith("∃") or "↔" in b.split("\n")[0]

    def names_an_equilibrium(short):
        low, starts, ends = short.lower(), word_starts(short), word_ends(short)
        return any(m.start() in starts and m.end() in ends
                   for c in EQUILIBRIUM_CONCEPTS
                   for m in re.finditer(re.escape(c), low))

    # A fixed-point theorem may live downstream of the primitive it pins.  That
    # is common in an acyclic import graph: DGP owns the formula while
    # PopulationGeneticsFoundations owns the process interpretation.  Requiring
    # both declarations in one file reports the correct architecture as a
    # defect.  Reachability is already checked by Lean elaboration, so search
    # all theorem signatures just as the duplicate-body guard does.
    global_defs = set()
    global_theorems = []
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        global_defs.update(m.group(1).split(".")[-1] for m in re.finditer(
            r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)", src, re.M))
        global_theorems.extend(
            (t.group(1).split(".")[-1], t.group(0).split(":=", 1)[0])
            for t in re.finditer(r"^(?:@\[[^\]]*\]\s*\n)?(?:private )?theorem "
                                 r"([A-Za-z_0-9'.]+)(?:.*?)(?=\n(?:@\[|theorem |"
                                 r"noncomputable |def |abbrev |structure |section |end |"
                                 r"namespace |/-))", src, re.S | re.M))

    stipulated = []
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        rel = os.path.relpath(f, IDENT_ROOT)
        defs, bodies_here, sigs_here = [], {}, {}
        for m in re.finditer(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)(.*?)(?=\n(?:@\[|theorem |"
                             r"noncomputable |def |abbrev |structure |section |end |namespace |/-))",
                             src, re.S | re.M):
            short = m.group(1).split(".")[-1]
            defs.append((short, src[:m.start()].count("\n") + 1))
            bodies_here[short] = m.group(2).split(":=", 1)[-1]
            sigs_here[short] = m.group(2).split(":=", 1)[0]
        allnames = {n for n, _ in defs}
        for short, line in defs:
            if not names_an_equilibrium(short):
                continue
            # A Prop-valued definition has no value to be a fixed point of. The
            # obligation this screen enforces -- exhibit the one-step map and
            # prove the quantity is its rest point -- is meaningful for a
            # stipulated constant and meaningless for a predicate: `∀ x,
            # jointGenotypeProb x = ∏ ...` states that a law factorises, and
            # there is no map iterating it. Exempting by shape rather than by a
            # name list matters, because a list is a place a genuinely
            # stipulated equilibrium could be parked to make the screen quiet.
            if is_prop_shaped(sigs_here.get(short, ""), bodies_here.get(short, "")):
                continue
            # A quantity derived from an equilibrium is not itself stipulated:
            # the obligation to derive belongs to the definition it calls.
            body = bodies_here.get(short, "")
            # Scoped to the WHOLE corpus, not to this file. `allnames` held only the
            # definitions declared here, so a body deriving from an equilibrium declared
            # elsewhere read as stipulating one of its own:
            # `expectedSqMeanPGSDiff_IMEquilibrium` calls `twoDemeIMEquilibriumDelta` from
            # `PortabilityDrift/Definitions.lean`, and `deployedBrierAtEquilibrium` reads
            # `p.fstEquilibrium`, which is a FIELD of `Core.PopGenParameters` and so was
            # never in any file's def list. Both were told to derive a rest point that their
            # own source already derives. The rule is about what the body reaches for, and
            # an identifier reached for is an identifier reached for wherever it lives.
            if any(o != short and names_an_equilibrium(o)
                   for o in set(re.findall(r"[A-Za-z_][A-Za-z_0-9']*", body))):
                continue
            ok = False
            for tname, stmt in global_theorems:
                if not tname.startswith(short) or not any(k in tname for k in FIXEDPOINT_MARKERS):
                    continue
                if any(o != short and re.search(r"\b" + re.escape(o) + r"\b", stmt)
                       for o in global_defs):
                    ok = True
                    break
            if not ok:
                stipulated.append(f"{rel}:{line}  {short}  (no fixed-point theorem)")
    if stipulated:
        bad.append(f"equilibrium definitions with no theorem deriving them as the fixed point "
                   f"of a process in the same file: {len(stipulated)}; "
                   f"define the one-step map and prove `<name>_isFixedPoint`")
        bad.extend("    " + x for x in stipulated)

    # 3i. One body, two files. `t / (t + 2 Ne)`, `1 - (1 - 1/(2 Ne)) ^ t` and
    #     `1 - exp (-tau)` were three definitions of F_ST living in three
    #     modules, and two of them were wrong; repairing one left the other two
    #     standing, because nothing in the corpus said they were the same
    #     quantity. Alpha-equivalent bodies in different files are either one
    #     quantity, and one of them should call the other, or they are two
    #     quantities that happen to coincide, and a theorem should say so.
    #
    #     Equation-style definitions need their own pattern, and the reason is
    #     a defect this check had until it was measured. `def f ... | 0 => a |
    #     n+1 => b` has no `:=` at all, so the value-style pattern below used to
    #     run its non-greedy signature group forward across the match arms until
    #     it found the *next* `:=` in the file -- typically the one in the
    #     `@[simp] theorem f_nil ... := rfl` that follows -- and recorded the
    #     definition's body as `rfl`. Four definitions in this corpus landed on
    #     that single token (`Pop.pair`, `altSum`, `ldRecurrence`,
    #     `driftLDTrajectory`) and were reported as five mutual duplicates, and
    #     the real bodies of all nineteen equation-style definitions were never
    #     compared with anything. A guard that cannot see a body must not report
    #     on it, so the arms are now the body.
    valuedef = re.compile(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)"
                          r"((?:(?!\n[ \t]*\|).)*?):=\s*\n?\s*(.+?)"
                          r"(?=\n(?:@\[|theorem |noncomputable |def |abbrev |structure |section |"
                          r"end |namespace |/-))", re.S | re.M)
    eqndef = re.compile(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)"
                        r"((?:(?!\n[ \t]*\|)(?!:=).)*?)\n((?:[ \t]*\|[^\n]*\n?)+)", re.M)
    IDENT = r"[A-Za-z_][A-Za-z_0-9₀-₉']*"

    def alpha_normal(args, body):
        """Body with whitespace collapsed and binders renamed positionally.

        Renaming is by order of first use in the body, not by order of
        declaration, so `(m Ne)` and `(Ne m)` over the same formula normalise
        together."""
        bound, seen = set(re.findall(IDENT, args)), {}
        def rename(t):
            w = t.group(0)
            if w in bound:
                seen.setdefault(w, "V%d" % (len(seen) + 1))
                return seen[w]
            return w
        return re.sub(IDENT, rename, " ".join(body.split()))

    shapes = {}
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        rel = os.path.relpath(f, IDENT_ROOT)
        for m in list(valuedef.finditer(src)) + list(eqndef.finditer(src)):
            name, args, body = m.group(1).split(".")[-1], m.group(2), m.group(3)
            # `ℕ`-valued and `ℝ`-valued bodies that read alike are not the same
            # operation -- natural subtraction truncates -- and no equation between
            # them typechecks. That one split, and no finer one: see
            # `ident_result_kind`.
            norm = ident_result_kind(args) + alpha_normal(args, body)
            # Pure operator shape is not a shared quantity: `a + b` coincides
            # everywhere. Require a constant or a named function, as 3c does.
            if not re.search(r"[0-9]|[A-Za-z_]{3,}", re.sub(r"\bV[0-9]+\b", "", norm)):
                continue
            shapes.setdefault(norm, []).append((rel, src[:m.start()].count("\n") + 1, name, body))
    file_stmts = {}
    for f in ident_lean_files():
        rel = os.path.relpath(f, IDENT_ROOT)
        for b in re.split(r"\n(?=@\[simp\]\s*\n?theorem |theorem |private theorem )",
                          ident_strip_comments(open(f).read())):
            if re.match(r"(?:@\[simp\]\s*)?(?:private )?theorem ", b) and ":=" in b:
                file_stmts.setdefault(rel, []).append(b.split(":=", 1)[0])
    # The tying theorem does not have to live in either of the two files, and
    # requiring that was this check asking for the wrong thing. What the check
    # is protecting is that divergence between two bodies becomes a compile
    # error, and a theorem in any module importing both files delivers exactly
    # that. Demanding one of the two files instead forced a choice between
    # adding an import purely to satisfy a guard and putting the statement in a
    # module where it does not belong -- and for ten pairs it made the check
    # unsatisfiable, because neither file imports the other and no third module
    # was allowed to speak. `Conventions` is where several of these belong.
    # So: accept a theorem naming both, in any file whose transitive imports
    # include both. Reachability, not residence.
    imports = {}
    for f in ident_lean_files():
        rel = os.path.relpath(f, IDENT_ROOT)
        imports[rel] = [m.replace(".", "/") + ".lean" for m in
                        re.findall(r"^import (Descent\.[\w.]+)", open(f).read(), re.M)]

    def visible_from(rel):
        seen, stack = {rel}, list(imports.get(rel, []))
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            stack += imports.get(x, [])
        return seen

    visible = {rel: visible_from(rel) for rel in imports}

    def tied_by_theorem(fa, na, fb, nb):
        for rel, stmts in file_stmts.items():
            if fa not in visible.get(rel, ()) or fb not in visible.get(rel, ()):
                continue
            for st in stmts:
                if (re.search(r"\b" + re.escape(na) + r"\b", st) and
                        re.search(r"\b" + re.escape(nb) + r"\b", st)):
                    return True
        return False

    # Hub ties, which this check used to report as violations. 3c already credits
    # a definition tied to a shared primitive in Conventions, and says why: a
    # group pinned to one object is related in the stronger sense, and refusing
    # the credit "penalises exactly the refactor it exists to encourage." This
    # check demanded a theorem naming BOTH members and therefore did precisely
    # that. `Conventions.geometricDecay` is the worked example: `(1 - r)^t` lives
    # under four names, and the file proves `ldDecayPerGeneration`,
    # `admixtureLDDecay` and `discreteRecombinationSurvival` each equal to the
    # hub. That is the collapse this guard asks for, done properly -- three
    # theorems rather than the six pairwise ones, and a divergence in any
    # spelling still fails one of them -- and it was being reported as three
    # unrelated duplications.
    #
    # The credit requires the SAME primitive on both sides. Two definitions
    # related to two DIFFERENT Conventions primitives are not tied to each other
    # by anything, and accepting that would let any pair through on the strength
    # of each half being documented somewhere.
    hub_cache = {}

    def hub_primitives(f, n):
        """Conventions primitives this definition is equated to by a visible theorem."""
        key = (f, n)
        if key in hub_cache:
            return hub_cache[key]
        hubs = set()
        for rel, stmts in file_stmts.items():
            if f not in visible.get(rel, ()):
                continue
            for st in stmts:
                if not re.search(r"\b" + re.escape(n) + r"\b", st):
                    continue
                for pr in primitives:
                    if pr != n and re.search(r"\b" + re.escape(pr) + r"\b", st):
                        hubs.add(pr)
        hub_cache[key] = hubs
        return hubs

    duplicates = []
    for norm, members in sorted(shapes.items()):
        for i in range(len(members)):
            for j in range(i + 1, len(members)):
                (fa, la, na, ba), (fb, lb, nb, bb) = members[i], members[j]
                # Same-file pairs were skipped outright, and that was this check
                # blind to its own worst case. The premise of the screen is that
                # one quantity under two names diverges when only one copy is
                # repaired; nothing about that premise needs the two names to be
                # in different modules, and a duplicate inside one file is the
                # TIGHTER defect, because the two bodies sit where a single
                # reader and a single edit can see both and still miss it.
                # Measured on the corpus when the skip was removed: `HorizonCurve`
                # defines the Kronecker delta on `Fin 2` twice, as `stayKernel`
                # and as `agreement`, and `DynamicsContrast` does the same as
                # `persistentTransition` and `contextMatchQuality`. Both were
                # invisible while the five CROSS-file pairings of those very
                # definitions were reported. A check that reports the weaker
                # instance and hides the stronger one produces a count people
                # trust, which is worse than no count.
                #
                # Only an entry paired with itself is skipped now.
                if fa == fb and na == nb and la == lb:
                    continue
                shape = norm[3:] if norm.startswith("N::") else norm
                shape = shape.strip()
                # A BARE CONSTANT IS NOT A SHARED QUANTITY.  The floor above admits a body
                # that is nothing but a literal, because a literal is "a constant".  So
                # `meanTimeSame _M := 2` and `ploidy := 2` were alpha-equivalent, and the
                # remedy offered -- make one call the other -- would tie a coalescent mean
                # time to a chromosome count.  Two definitions being the same small number
                # is the pigeonhole of small numbers, not shared mathematics.
                if re.fullmatch(r"[0-9]+(\.[0-9]+)?", shape):
                    continue
                # ALREADY FACTORED THROUGH A SHARED KERNEL.  Every member of a bucket has
                # the SAME normalised body, so when that body is one named function applied
                # to variables, both definitions call that function -- which is the factored
                # form this screen asks for, reached already.  `neutralFixation`,
                # `gainLinear` and `localizedTransferVariance` are each
                # `Core.identifiedWith <arg>`; they do not call each other because they call
                # the same kernel, and reporting them asks for a fixation probability to be
                # written in terms of a conditional gain.
                if re.fullmatch(r"[A-Za-z_][\w.']*(?:\s+V[0-9]+)*", shape):
                    continue
                # Tied by definition: one is written in terms of the other.
                if (re.search(r"\b" + re.escape(nb) + r"\b", ba) or
                        re.search(r"\b" + re.escape(na) + r"\b", bb)):
                    continue
                if tied_by_theorem(fa, na, fb, nb):
                    continue
                # Tied through a shared Conventions hub, as 3c already credits.
                if hub_primitives(fa, na) & hub_primitives(fb, nb):
                    continue
                duplicates.append(f"{fa}:{la} {na}  ==  {fb}:{lb} {nb}")
    duplicates.sort()
    if duplicates:
        bad.append(f"alpha-equivalent definition bodies tied by neither a call nor a theorem: "
                   f"{len(duplicates)}; make one call the "
                   f"other, or state the identity as a theorem")
        bad.extend("    " + x for x in duplicates)

    # 3j. Regimes baked into bodies. Five definitions -- the within-population
    #     heterozygosity loss, the F_ST read off it, the target heterozygosity,
    #     the target PGS variance, and the neutral benchmark ratio -- were all
    #     functions of one number, `(1 - 1/(2 Ne))^t`, the closed-population
    #     no-mutation retention. Simulation at demographic equilibrium measures
    #     that retention as 1.02 +- 0.02 where the formula predicts e^-2 = 0.135:
    #     mutation replenishes diversity, so heterozygosity is stationary and the
    #     cluster's "F_ST" is ~0 exactly where the measurable between-population
    #     F_ST is 0.50. They are different quantities sharing a name.
    #
    #     The premise was invisible because it lived in a *body*, not in a
    #     hypothesis. A definition carrying the closed-population retention factor
    #     must therefore name its regime, so that a reader and a use site both see
    #     which data-generating process it assumes. `Descent.DriftRegime`
    #     exhibits the two regimes and proves they disagree at every positive time.
    #     The screen this replaces could not fire. It walked the signature with
    #     `[^:]*:[^:=]*:=`, which stops at the first colon inside a binder and
    #     cannot cross the colon of the return type, so it matched only
    #     definitions taking NO arguments -- of which the corpus has effectively
    #     none. Measured on three shapes: `def f (Ne : ℝ) (t : ℕ) : ℝ :=` missed,
    #     `def f (Ne : ℝ) : ℝ :=` missed, `def f : ℝ :=` matched. It had been
    #     printing a passing zero all along, which is worse than no screen,
    #     because a vacuous guard fills the hole with a false reassurance and
    #     stops anyone looking. That is the same failure this file exists to
    #     catch -- a check that could not have failed, passing -- and finding it
    #     on the REGIME screen is the sharpest possible instance, since regime
    #     declarations are exactly the modelling choices being made explicit.
    #
    #     The body is now located by the depth-aware separator scan used by the
    #     under-delivery screen, which handles binders. On repair the screen
    #     found three live sites carrying the falsified closed-population
    #     retention with no Regime declared -- `neutralDriftFactor`,
    #     `ldRetainedFraction`, `fstDerived` -- one leak with three outlets
    #     rather than three omissions. All three now declare it.
    def def_body(rest):
        """Text after the definition's `:=`, at paren depth zero, so a colon or
        a default value inside a binder is not mistaken for the separator."""
        depth = 0
        for i, ch in enumerate(rest):
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
            elif depth == 0 and rest[i:i + 2] == ":=":
                return rest[i + 2:]
        return ""

    regimeless = []
    for f in ident_lean_files():
        raw = open(f).read()
        for m in re.finditer(r"/--((?:(?!-/).)*)-/\s*\n(?:noncomputable )?def "
                             r"([A-Za-z_0-9'.]+)"
                             r"((?:(?!\n/--|\n@\[|\ntheorem |\nnoncomputable |\ndef |\nabbrev |"
                             r"\nstructure |\nsection |\nend |\nnamespace ).)*)", raw, re.S):
            doc, name = m.group(1), m.group(2).split(".")[-1]
            body = def_body(m.group(3))
            # the closed-population retention factor, raised to a power
            if re.search(r"\(\s*1\s*-\s*1\s*/\s*\(\s*2\s*\*[^)]*\)\s*\)\s*\^", body):
                if "Regime:" not in doc:
                    regimeless.append(
                        f"{os.path.relpath(f, IDENT_ROOT)}: `{name}` carries the closed-population "
                        f"retention factor in its body and declares no Regime")
    if regimeless:
        bad.append(f"definitions encoding a drift regime with no declared Regime: "
                   f"{len(regimeless)}; name the "
                   f"data-generating assumption, see Descent.DriftRegime")
        bad.extend("    " + x for x in regimeless)

    # 3j-bis. Under-delivery: a docstring claiming more than the signature
    #     proves. This is the mirror of the overclaim screen. That one catches a
    #     docstring claiming more than the *evidence* supports; this one catches
    #     a docstring claiming more than the *statement* delivers.
    #
    #     `missing_heritability_gap` asserted in prose "We prove that
    #     h2_twin - h2_SNP = V_A_untagged / V_P > 0" above a conclusion that was
    #     only `0 < h2_twin - h2_snp`. The theorem was true, the proof was
    #     correct, and the compiler cannot see the gap, because the defect is in
    #     the documentation of a correct theorem. It matters because people read
    #     prose: a reader who takes the docstring at its word believes an
    #     identity is available that no downstream proof can actually cite.
    #
    #     One principle: fire when a docstring ATTRIBUTES A DISPLAYED EQUATION TO
    #     THIS DECLARATION and the declaration's conclusion contains no equation.
    #     Everything else a docstring does with an `=` is legitimate -- setting up
    #     a model, recalling a definition, running a chain of algebra whose net
    #     claim is an inequality -- and the screen is written to under-fire rather
    #     than to catch those. Measured over the corpus before the budget was set:
    #     a looser first version reported fifteen sites, every one of which was a
    #     false positive on inspection.
    DISPLAYED_EQ = re.compile(r"(?<![:<>!≤≥≠])\s=\s")
    COMPARATOR = re.compile(r"[<>≤≥≠⟺]")
    # A passage labelled as the proof strategy describes intermediate steps, not
    # what the declaration establishes.
    STRATEGY = re.compile(r"^[\s*_]*(?:proof\s+strategy|proof\s+sketch|proof|"
                          r"strategy|sketch|derivation|key\s+identity)\s*:", re.I)
    # `derive` is deliberately absent from the verbs: deriving describes how a
    # model was set up and fires on every docstring that recalls its own
    # definitions. The exactness words exclude their non-identity uses -- "is
    # exactly the point", "is exactly where", "is exactly one", "is exactly
    # optimal" -- each of which was a false positive in the measured run.
    ATTRIBUTION = [
        r"\bwe\s+(?:prove|show|establish)\s+that\b",
        r"\bthis\s+(?:proves|shows|establishes)\s+that\b",
        r"\bis\s+(?:exactly|precisely)\b"
        r"(?!\s+(?:the\s+point|where|when|how|why|what|which|one|two|three|"
        r"optimal|minimal|maximal|because)\b)",
        r"\bequals\s+exactly\b",
    ]
    OPENB, CLOSEB = "([{⟨", ")]}⟩"

    def header_of(block):
        """The declaration header: everything before the proof separator."""
        m = re.search(r":=\s*by\b", block)
        if m:
            return block[:m.start()]
        lines = block.split("\n")
        out = [lines[0]]
        for ln in lines[1:]:
            if ln.strip() == "" or re.match(r"^ {4,}\S", ln):
                out.append(ln)
            else:
                break
        txt = "\n".join(out)
        i = txt.rfind(":=")
        return txt[:i] if i != -1 else txt

    def goal_of(header):
        """Everything after the last top-level `:`: the goal without binders.

        Hypotheses carry equalities routinely, so the goal has to be separated
        from them or every conditional theorem looks like it proves an identity.
        A `:=` inside a `let` in the goal is not a binder colon."""
        depth, pos = 0, -1
        for i, ch in enumerate(header):
            if ch in OPENB:
                depth += 1
            elif ch in CLOSEB:
                depth -= 1
            elif ch == ":" and depth == 0 and header[i:i + 2] != ":=":
                pos = i
        return header[pos + 1:] if pos >= 0 else header

    def delivers_identity(goal):
        """An `↔` counts: a characterisation delivered as an iff is equality of
        propositions, not a one-sided bound."""
        if "↔" in goal or "⟺" in goal:
            return True
        return re.search(r"(?<![:<>!])=(?!=)", goal) is not None

    # A GROUND IS NOT THE CLAIM. `meanTime_le_sum` says the skipped sojourn "is exactly
    # recovered from the `k - 1` levels it skips, BECAUSE `Σ_k (k-1) p_{b,k} = γ_b/λ_b` by
    # the definition of the decrease rate". The attribution's complement is a recovery, not
    # an equation; the equation is the reason offered for it, and it is already in the
    # signature as `hdrift`. Requiring only that verb and equation share a sentence reads
    # the ground as the claim, and the repair it then demands -- put the identity in the
    # conclusion -- would move a hypothesis into the goal.
    SUBORDINATOR = re.compile(r"\b(?:because|since|provided|whenever|given\s+that|"
                              r"by\s+the\s+definition\s+of)\b", re.I)

    def equation_tokens(s, at):
        """Identifiers in the code span carrying the equation, or in the whole sentence."""
        for span in re.finditer(r"`([^`]*)`", s):
            if span.start() < at < span.end():
                return set(re.findall(r"[A-Za-z_][A-Za-z_0-9₀-₉']*", span.group(1)))
        return set(re.findall(r"[A-Za-z_][A-Za-z_0-9₀-₉']*", s))

    def attributed_identity(doc, header):
        # AN EQUATION THIS DECLARATION CANNOT BE COMPARED TO IS NOT A CLAIM ABOUT IT.
        # `covers_nonempty` says a missing next state "is exactly the absorbing case
        # `k = 1`". No `k` occurs anywhere in that declaration -- it is about `ξ` and
        # `blocks ξ` -- so the equation names a neighbouring case in the module's informal
        # notation rather than stating anything this conclusion could deliver. It is in fact
        # the case the theorem EXCLUDES, since it assumes `2 ≤ blocks ξ`, so the demanded
        # repair asks the conclusion to state the negation of its own hypothesis. A real
        # attribution is written in the declaration's own names and still fires.
        names = set(re.findall(r"[A-Za-z_][A-Za-z_0-9₀-₉']*", header))
        for s in re.split(r"(?<=\.)\s+", doc):
            if STRATEGY.match(s.strip()):
                continue
            eq = DISPLAYED_EQ.search(s)
            if not eq:
                continue
            # A comparator standing before the equation means the sentence is a
            # chain whose net claim is the inequality, not the equation:
            # "We show MSE(l*) < MSE(1) = sigma^2" claims a bound.
            if COMPARATOR.search(s[:eq.start()]):
                continue
            if not (equation_tokens(s, eq.start()) & names):
                continue
            for p in ATTRIBUTION:
                am = re.search(p, s, re.I)
                if not am:
                    continue
                if am.end() <= eq.start() and SUBORDINATOR.search(s[am.end():eq.start()]):
                    continue
                return " ".join(s.split())[:120]
        return None

    underdelivered = []
    for f in ident_lean_files():
        raw = open(f).read()
        for m in re.finditer(
                r"/--((?:(?!-/).)*)-/\s*\n(?:@\[[^\]]*\]\s*\n)?(?:private )?theorem\s+"
                r"([A-Za-z_0-9'.]+)", raw, re.S):
            doc, name = m.group(1), m.group(2).split(".")[-1]
            block = raw[m.end(2):]
            nxt = re.search(r"\n(?=/--|@\[|theorem |noncomputable |def |abbrev |"
                            r"structure |section |end |namespace )", block)
            block = block[:nxt.start()] if nxt else block
            header = header_of(block)
            if delivers_identity(goal_of(header)):
                continue
            claim = attributed_identity(doc, name + " " + header)
            if claim:
                underdelivered.append(
                    f"{os.path.relpath(f, IDENT_ROOT)}:{raw[:m.start()].count(chr(10)) + 1}: "
                    f"`{name}` claims an identity its conclusion does not state: "
                    f"\"{claim}\"")
    if underdelivered:
        bad.append(f"docstrings attributing an identity the statement does not deliver: "
                   f"{len(underdelivered)}; state the "
                   f"identity in the conclusion, or stop claiming it in the prose")
        bad.extend("    " + x for x in underdelivered)

    # 3k. Validation inherited from a sibling identity. Over-determination
    #     detects divergence between independently written formulas and is
    #     provably blind to a premise they share
    #     (`Descent.DriftRegime.crossChecks_blind_to_retention`): every identity
    #     among members of a cluster holds at *every* value of the shared premise,
    #     including the wrong one. So a VALIDATED tag may cite a measurement
    #     against an observable, never a sibling formula. A validation note that
    #     only names another definition is an inherited tag, and inherited tags are
    #     what let one wrong number be certified five times.
    inherited = []
    for f in ident_lean_files():
        raw = open(f).read()
        for m in re.finditer(r"Empirical status: VALIDATED(.*?)-/", raw, re.S):
            note = m.group(1)
            cites_identity = re.search(r"\bthis is the identity\b|\bthe theorem\b|"
                                       r"\bby definition\b|\bdefinitionally\b|"
                                       r"\balongside\b `?[A-Za-z_0-9']+`?", note, re.I)
            cites_measurement = re.search(r"simulat|measur|against|observed|grid|"
                                          r"coalescent|SLiM|panel|out-of-sample", note, re.I)
            if cites_identity and not cites_measurement:
                inherited.append(f"{os.path.relpath(f, IDENT_ROOT)}: a VALIDATED note cites a sibling "
                                 f"identity but no measurement: \"{note.strip()[:70]}\"")
    #     ENFORCED, at zero. This comment used to say "reported, not enforced,
    #     until the count is measured once and pinned", and proposed ratcheting a
    #     budget down from that count -- while the code below already appended to
    #     `bad` and failed the build. The prose described a discipline the corpus
    #     no longer has and the code no longer followed. A VALIDATED tag resting
    #     on a sibling identity rather than on a measurement is a defect at one
    #     occurrence, and being retroactive over twenty of them is a reason to
    #     fix twenty, not a reason to permit them.
    if inherited:
        bad.append(f"VALIDATED tags justified by a sibling identity rather than a measurement: "
                   f"{len(inherited)}")
        bad.extend("    " + x for x in inherited)

    # 3l. Validation with no power. `neutralAFBenchmarkRatio` was recorded as
    #     validated to 3.2 percent. The design was symmetric, so both sides of the
    #     ratio collapsed to ~1 and the test could not have failed;
    #     `Descent.DriftRegime.symmetric_design_has_no_power` proves that on any
    #     symmetric design the ratio and its *square* are indistinguishable. On
    #     asymmetric effective sizes the same formula is off by -37 to -74 percent,
    #     at nine to fifteen standard errors.
    #
    #     A validation is evidence in proportion to the range its prediction
    #     spanned, so a VALIDATED note must declare that range in a `Power:`
    #     clause. The range is *declared*, not inferred: a first version of this
    #     guard scanned every number in the note and could not tell a predicted
    #     value from an error bar, so it flagged `ratio 0.99-1.01` -- a residual --
    #     as a constant prediction. A guard that misfires is a guard that gets
    #     ignored, and inferring intent from numbers is exactly the move that
    #     produced the incident. The author states the span; the guard checks the
    #     span is stated and is not degenerate.
    powerless = []
    for f in ident_lean_files():
        raw = open(f).read()
        for m in re.finditer(r"Empirical status: VALIDATED(.*?)-/", raw, re.S):
            note = m.group(1)
            power = re.search(r"Power:(.*?)(?:\n\s*\n|$)", note, re.S)
            if not power:
                powerless.append(f"{os.path.relpath(f, IDENT_ROOT)}: a VALIDATED note declares no "
                                 f"Power; state the span of the prediction across the design")
                continue
            # A WHOLE NUMBER IS A PREDICTED VALUE. Requiring a decimal point made an integer
            # prediction invisible, so `mixedEnvironmentCorrelation` -- whose clause names a
            # rival rejected at 473 sems, a positive control passing at 1.55, and the two
            # competing predictions 0 and `rho/2` at a balanced mixture -- was reported as
            # naming fewer than two predicted values. The comment above states the design of
            # this screen: the author declares the span and the guard checks it is stated and
            # not degenerate. The decimal point was never part of that and only dropped spans
            # that happen to land on integers, which is where a sign cancellation lands.
            nums = [float(x) for x in re.findall(r"\d+(?:\.\d+)?", power.group(1))]
            if len(nums) < 2:
                powerless.append(f"{os.path.relpath(f, IDENT_ROOT)}: a Power clause names fewer than "
                                 f"two predicted values, so no span is declared")
            elif max(nums) - min(nums) <= 0.05 * max(abs(max(nums)), 1.0):
                powerless.append(f"{os.path.relpath(f, IDENT_ROOT)}: a Power clause declares a span of "
                                 f"only {max(nums) - min(nums):.4f}; a near-constant prediction "
                                 f"cannot reject a wrong functional form")
    if powerless:
        bad.append(f"VALIDATED tags whose design had no recorded power: {len(powerless)}; "
                   f"record the spread of the prediction "
                   f"across the design, see Descent.DriftRegime")
        bad.extend("    " + x for x in powerless)

    # 3m. Assumptions laundered into hypotheses. A proposition the corpus cannot
    #     prove can be made to look proved in five moves, none of which is a
    #     `sorry` and none of which declares an axiom:
    #
    #       1. name the unproved proposition as a `theorem`;
    #       2. pass it as an ordinary argument, so `#print axioms` stays clean;
    #       3. bundle the hard facts of a construction into a setup structure;
    #       4. project that structure's fields into local typeclass instances,
    #          so they bind silently at every use site;
    #       5. give the conditional wrapper an unconditional-sounding name and
    #          a docstring to match.
    #
    #     The axiom scan is clean at every step, and that is the point of the
    #     technique: an assumption discharged by the caller is invisible to a
    #     scan that reads only the proof term. the AXIOMS scan in Check.lean cannot see this
    #     and never could; it is not a weaker version of these guards, it is
    #     blind to them by construction.
    #
    #     The load-bearing question is not whether a hypothesis is stated -- it
    #     always is -- but whether anything can ever satisfy it.
    #     `IsSymmetricBilinearMatrix` is assumed by fourteen theorems in
    #     QuadraticShift, and no matrix anywhere in the corpus is proved to
    #     satisfy it. Second-moment matrices really are symmetric, so that one
    #     is almost certainly honest; but were the predicate unsatisfiable, all
    #     fourteen theorems would be vacuously true, every proof would still
    #     elaborate, and no scan in this repository would say a word. A named
    #     proposition that is only ever consumed -- never concluded by a
    #     theorem, never established for a concrete object -- is an axiom with
    #     better manners, and is counted here as one.
    #
    #     A `sorry` is preferred to any of this. An admission is a debt this
    #     corpus can enumerate; a laundered hypothesis is a debt it cannot.
    prop_defs = {}
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        rel = os.path.relpath(f, IDENT_ROOT)
        for m in re.finditer(r"^(?:noncomputable )?(?:(?:private|protected) )*(?:def|abbrev) "
                             r"([A-Za-z_0-9'.]+)((?:(?!\n\S).)*)", src, re.S | re.M):
            if re.search(r":\s*Prop\b", m.group(2).split(":=")[0]):
                prop_defs[m.group(1).split(".")[-1]] = (rel, src[:m.start()].count("\n") + 1)

    # Everything a declaration can *produce*: the goal of a theorem, or the
    # return type of a definition or instance. A name that never appears in one
    # of these positions is never established, only ever required.
    # A declaration whose body is `sorry` PRODUCES NOTHING, and must not be
    # counted below. Guard 1 reports such a declaration as an admission and
    # AxiomScan lets it through deliberately, because an enumerable debt beats a
    # laundered premise. That decision has a matching obligation right here: if
    # an admission also DISCHARGED an inhabitation obligation, then the cheapest
    # edit available -- `def witness : Bundle := sorry` -- would clear 3m, 3n and
    # 3p at a stroke, and would do it by writing down exactly the assumption the
    # three screens exist to find. Permitting the admission and letting it settle
    # the question are different decisions. The first is what lets this corpus be
    # honest about what it has not proved; the second would make `sorry` the
    # laundering instrument rather than the alternative to it.
    #
    # So: `sorry` is free to write, and buys nothing.
    admitted = set()
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        for m in re.finditer(r"^(?:noncomputable )?(?:(?:private|protected) )*"
                             r"(?:def|abbrev|instance|theorem) ([A-Za-z_0-9'.]+)"
                             r"((?:(?!\n\S).)*)", src, re.S | re.M):
            if re.search(r"\bsorry\b", m.group(2)):
                admitted.add(m.group(1).split(".")[-1])

    produced = set()
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        for m in re.finditer(r"^(?:noncomputable )?(?:(?:private|protected) )*"
                             r"(?:def|abbrev|instance) ([A-Za-z_0-9'.]*)((?:(?!\n\S).)*)",
                             src, re.S | re.M):
            # Two tests, because anonymous `instance : Bundle := sorry` has no
            # name to look up and would otherwise slip past the set.
            if m.group(1).split(".")[-1] in admitted:
                continue
            if re.search(r"\bsorry\b", m.group(2)):
                continue
            produced.update(re.findall(IDENT, goal_of(m.group(2).split(":=")[0])))
    for _tname, stmt in global_theorems:
        if _tname in admitted:
            continue
        produced.update(re.findall(IDENT, goal_of(stmt)))

    assumed_by = {}
    for tname, stmt in global_theorems:
        goal = goal_of(stmt)
        for tok in set(re.findall(IDENT, stmt[:len(stmt) - len(goal)])):
            if tok in prop_defs:
                assumed_by.setdefault(tok, []).append(tname)

    laundered = sorted(
        "%s:%d  `%s` is assumed by %d theorem(s) and established by nothing"
        % (prop_defs[p][0], prop_defs[p][1], p, len(ts))
        for p, ts in assumed_by.items() if p not in produced)
    if laundered:
        bad.append("named propositions only ever assumed, never established: %d; "
                   "prove one concrete object satisfies it, or admit it with `sorry` so the "
                   "debt is enumerable" % len(laundered))
        bad.extend("    " + x for x in laundered)

    # 3n. Assumption bundles nothing satisfies (step 3 of the recipe). A
    #     structure whose fields are propositions is a conjunction of
    #     hypotheses wearing a noun for a name. Taken as an argument it reads
    #     like a model; if no construction ever produces one, the theorems
    #     quantifying over it say nothing, and the wider the bundle the less
    #     they say. The obligation is inhabitation: exhibit one.
    RELATION = re.compile(r"∀|∃|↔|≤|≥|≠|<|>|(?<![:<>=!])=(?!=)|\bProp\b")
    bundles = {}
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        rel = os.path.relpath(f, IDENT_ROOT)
        for m in re.finditer(r"^structure ([A-Za-z_0-9'.]+)[^\n]*\n((?:[ \t]+[^\n]*\n)+)",
                             src, re.M):
            fields = []
            for line in m.group(2).split("\n"):
                fm = re.match(r"\s+([A-Za-z_0-9']+)\s*:(.*)", line)
                if fm and RELATION.search(fm.group(2)):
                    fields.append(fm.group(1))
            if fields:
                bundles[m.group(1).split(".")[-1]] = (rel, src[:m.start()].count("\n") + 1,
                                                      len(fields))
    unwitnessed = sorted(
        "%s:%d  `%s` bundles %d hypothesis field(s) and is never constructed"
        % (v[0], v[1], k, v[2])
        for k, v in bundles.items() if k not in produced)
    if unwitnessed:
        bad.append("hypothesis bundles no construction ever satisfies: %d; "
                   "build one concrete instance, or the theorems over it are vacuous"
                   % len(unwitnessed))
        bad.extend("    " + x for x in unwitnessed)

    # 3o. Instances synthesised from supplied fields (step 4). The defect is an
    #     assumption installed where instance resolution finds it while
    #     APPEARING IN NO SIGNATURE, so every later `simp` and every later lemma
    #     application depends on it silently.
    #
    #     SCOPED TO CLASSES DECLARED IN THIS CORPUS, and the scoping is the
    #     whole content of the screen. Deriving a Mathlib class from a field of a
    #     parameter is not the defect: in
    #
    #         instance (dgp : DataGeneratingProcess k) :
    #             IsProbabilityMeasure dgp.jointMeasure := dgp.is_prob
    #
    #     the assumption is `dgp`, which is in the signature of every theorem
    #     that uses it, and `is_prob` is a well-formedness field of the structure
    #     with a default of `by infer_instance`. Nothing is hidden; the structure
    #     IS the disclosure. Flagging it demands that the corpus stop bundling
    #     side conditions, which would make signatures longer and disclose
    #     nothing new.
    #
    #     A corpus-declared class is different, and is the case the original
    #     screen was written for: it puts a proposition this development invented
    #     into synthesis, where no use site names it and no structure parameter
    #     carries it. There are no such classes today, so this is a ratchet
    #     against introducing one rather than a report on what exists.
    #
    #     The Mathlib-class escape route is not left open. `Fact` is the class an
    #     arbitrary proposition can be smuggled through, and the parameterized
    #     `Fact` instance is banned outright by the forbidden-pattern list above.
    corpus_classes = set()
    for f in ident_lean_files():
        for m in re.finditer(r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*class\s+"
                             r"([A-Za-z_][A-Za-z_0-9'.]*)", ident_strip_comments(open(f).read())):
            corpus_classes.add(m.group(1).split(".")[-1])

    def installs_corpus_class(sig):
        """Head symbol of the class being installed, if this corpus declared it."""
        head = re.match(r"\s*([A-Za-z_][A-Za-z_0-9'.]*)", sig)
        return bool(head) and head.group(1).split(".")[-1] in corpus_classes

    laundered_inst = []
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        rel = os.path.relpath(f, IDENT_ROOT)
        for m in re.finditer(r"(?m)^[ \t]*(haveI|letI)\b[^\n]*?:([^\n]*?):=[ \t]*"
                             r"([A-Za-z_][A-Za-z_0-9'.]*\.[A-Za-z_][A-Za-z_0-9']*)", src):
            if not installs_corpus_class(m.group(2)):
                continue
            laundered_inst.append("%s:%d: `%s` installs `%s`, a supplied field, as an instance"
                                  % (rel, src[:m.start()].count("\n") + 1,
                                     m.group(1), m.group(3)))
        for m in re.finditer(r"(?m)^instance\b[^\n]*\([a-zA-Z_][^\n]*\)[^\n]*?:([^\n]*?):=[ \t]*"
                             r"([A-Za-z_][A-Za-z_0-9'.]*\.[A-Za-z_][A-Za-z_0-9']*)", src):
            if not installs_corpus_class(m.group(1)):
                continue
            laundered_inst.append("%s:%d: an instance is built by projecting `%s` out of its "
                                  "own parameter" % (rel, src[:m.start()].count("\n") + 1,
                                                     m.group(2)))
    if laundered_inst:
        bad.append("supplied hypotheses installed as typeclass instances: %d; "
                   "pass the fact explicitly so the dependency stays visible in the signature"
                   % len(laundered_inst))
        bad.extend("    " + x for x in laundered_inst)

    # 3p. Unconditional names on conditional results (step 5). The four screens
    #     above are all defeated by the same follow-up: once the assumption is
    #     in a binder, the theorem may be called anything at all. A result
    #     resting on a proposition nothing establishes, or on a bundle nothing
    #     inhabits, has to say so where a reader will see it -- in the name, or
    #     in an `Assumes:` clause of the docstring.
    CONDITIONAL_NAME = re.compile(r"(?:^|_)(?:of|assuming|given|under|conditional|"
                                  r"when|if|requires)(?:_|$)", re.I)
    #     Scoped to unestablished propositions, not to bundles. Taking a model
    #     structure as a parameter is this corpus's ordinary way of stating what
    #     a theorem is about, and demanding `_of_` in all 162 such names would
    #     be noise -- and a guard that misfires is a guard that gets ignored.
    #     The bundles are already answerable to 3n, which asks the sharper
    #     question of whether anything inhabits them.
    unproven = set(p for p, _ in assumed_by.items() if p not in produced)
    docs = {}
    for f in ident_lean_files():
        raw = open(f).read()
        for m in re.finditer(r"/--((?:(?!-/).)*)-/\s*\n(?:@\[[^\]]*\]\s*\n)?(?:private )?"
                             r"theorem\s+([A-Za-z_0-9'.]+)", raw, re.S):
            docs[m.group(2).split(".")[-1]] = m.group(1)
    misnamed = []
    for tname, stmt in global_theorems:
        goal = goal_of(stmt)
        rests_on = sorted(set(re.findall(IDENT, stmt[:len(stmt) - len(goal)])) & unproven)
        if not rests_on:
            continue
        if CONDITIONAL_NAME.search(tname) or "Assumes:" in docs.get(tname, ""):
            continue
        misnamed.append("`%s` rests on %s, which nothing establishes, and neither its name "
                        "nor an `Assumes:` clause says so" % (tname, ", ".join(rests_on[:3])))
    if misnamed:
        bad.append("conditional results named as though unconditional: %d; "
                   "name the assumption in the theorem or declare `Assumes:` in its docstring"
                   % len(misnamed))
        bad.extend("    " + x for x in misnamed)

    # 3q. Genetics in the name, arithmetic in the statement. Guard 3p asks
    #     whether a theorem rests on a named proposition nothing establishes.
    #     It is blind to the commoner shape: the assumption is not a named
    #     proposition at all but a bare inequality between free reals, and the
    #     genetics lives only in the identifier.
    #
    #     `functional_equivalence_aids_portability` proved `b^2 < k * b^2`.
    #     `coding_more_portable_than_regulatory` proved that squaring is
    #     monotone on the nonnegatives, with the entire biological step -- that
    #     purifying selection makes coding effects more correlated -- supplied
    #     as the hypothesis `rg_regulatory < rg_coding`.
    #     `matched_panel_optimal` proved `x * m <= x`. In each case the goal
    #     mentions no constant this corpus defines, so nothing in the statement
    #     can be read as being about genetics, and the name is doing work the
    #     mathematics does not support.
    #
    #     The test is exactly that: a goal whose identifiers are disjoint from
    #     the corpus's own vocabulary, under a name containing a domain word.
    #     It fires on the name because the name is what gets cited, indexed and
    #     rendered on the site -- several of the theorems found this way had
    #     docstrings that already admitted the content was trivial, which
    #     reached nobody reading a theorem list.
    #
    #     Pinned, not zero. The survivors are grandfathered so the budget can
    #     ratchet down as they are renamed; what it forbids is adding more.
    DOMAIN_WORD = re.compile(
        # `variant` must not fire inside `invariant`: an invariant measure, an
        # invariant subspace and an invariant average are mathematics, not genetics,
        # and flagging them asks for a rename away from the standard term.
        # `loci` and `locus` are genetics only as whole words: they also sit inside
        # `velocity` and `locusOfControl`-style names, so require a boundary.
        r"portab|drift|heritab|genetic|genom|(?<!in)variant|\blocus\b|\bloci\b|allele|pgs|"
        r"ancestr|gwas|snp|calibrat|imputation|selection|polygenic|epistas|"
        r"cohort|population|panel|fst|prevalence|phenotype|trait|marker|"
        r"burden|gene_|_gene(?!rat)|kinship|admixture|coalescent|bottleneck|founder|"
        r"heterozyg|linkage|haplotype|ld_|_ld_|_ld$", re.I)
    corpus_vocab = set(global_defs)
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        for m in re.finditer(r"^(?:noncomputable )?(?:abbrev|structure|inductive|class) "
                             r"([A-Za-z_0-9'.]+)", src, re.M):
            corpus_vocab.add(m.group(1).split(".")[-1])
        # structure fields: indented `name :` lines inside a structure block
        for m in re.finditer(r"^(?:noncomputable )?structure [^\n]*\n((?:[ \t]+[^\n]*\n)+)",
                             src, re.M):
            for fm in re.finditer(r"^[ \t]+([A-Za-z_][A-Za-z_0-9'₀-₉]*)[ \t]*:",
                                  m.group(1), re.M):
                corpus_vocab.add(fm.group(1))
    # `global_theorems` cuts each declaration at its FIRST `:=`, which is the
    # proof's only when the conclusion has no `let`. A conclusion of the form
    #
    #     let sourceProfile := cal.identityCalibrationProfile Pop.source
    #     ...
    #
    # owns that `:=`, so the statement is truncated to `let sourceProfile` and
    # the goal comes out empty -- which reads to this guard as "mentions no
    # constant this corpus defines" and reports a theorem written entirely in
    # corpus vocabulary. `cross_ancestry_exact_metric_profile` is one such.
    #
    # With the budget at zero a false positive here is not noise, it is pressure
    # to rename a correct name, so this guard splits at the PROOF's `:=`: scan at
    # depth zero and let each `let`/`have`/`fun` binder consume the next one.
    def statement_of(decl):
        depth, pending, i = 0, 0, 0
        while i < len(decl):
            ch = decl[i]
            if ch in OPENB:
                depth += 1
            elif ch in CLOSEB:
                depth -= 1
            elif depth == 0:
                if decl.startswith(":=", i):
                    if pending == 0:
                        return decl[:i]
                    pending -= 1
                    i += 2
                    continue
                m = re.match(r"\b(let|have)\b", decl[i:])
                if m and (i == 0 or not decl[i - 1].isalnum()):
                    pending += 1
                    i += m.end()
                    continue
            i += 1
        return decl

    full_decl = {}
    for f in ident_lean_files():
        src = ident_strip_comments(open(f).read())
        for t in re.finditer(r"^(?:@\[[^\]]*\]\s*\n)?(?:private )?theorem "
                             r"([A-Za-z_0-9'.]+)(?:.*?)(?=\n(?:@\[|theorem |"
                             r"noncomputable |def |abbrev |structure |section |end |"
                             r"namespace |/-))", src, re.S | re.M):
            full_decl[t.group(1).split(".")[-1]] = t.group(0)

    # ---- 3d-ter. A citation that lands on a disclaimer ---------------------
    #
    # `CumulantBlindness` said the load-bearing negative result "is the
    # condensation mechanism in `Descent.Condensation`".  Condensation's own
    # header says, in capitals, "THAT PROPOSAL IS NOT PROVED IN THIS FILE".  The
    # arc therefore claimed a result that exists in neither file, and the claim
    # survived because nothing follows a pointer.
    #
    # A citation chain ending at a disclaimer is worse than no citation: it reads
    # as a discharged obligation.
    DISCLAIMER = re.compile(
        r"NOT PROVED IN THIS FILE|not proved in this file|"
        r"is not formalized here|are not proved here|is not proved here|"
        r"not exported from this file|is absent pending", re.I)
    LOAD_BEARING = re.compile(
        r"(load-bearing|substantive|decisive|the real (result|theorem)|"
        r"the hard content)[^.]{0,160}?`Descent\.([A-Za-z_0-9.]+)`", re.I | re.S)
    disclaiming = set()
    for path in lean_sources(CORPUS / "Descent"):
        try:
            text = read_source(path)
        except ValueError:
            continue
        if DISCLAIMER.search(text):
            disclaiming.add(path.stem)
    dead_pointers = []
    for path in lean_sources(CORPUS / "Descent"):
        try:
            text = read_source(path)
        except ValueError:
            continue
        for match in LOAD_BEARING.finditer(text):
            target = match.group(3).split(".")[-1]
            if target in disclaiming and target != path.stem:
                dead_pointers.append(
                    "%s cites `Descent.%s` for load-bearing content, and that file "
                    "disclaims having it" % (path.relative_to(REPO), match.group(3)))
    if dead_pointers:
        bad.append("citations landing on a disclaimer: %d, budget 0; say what the cited "
                   "file actually contains, or drop the claim"
                   % len(dead_pointers))
        bad.extend("    " + x for x in dict.fromkeys(dead_pointers))

    # ---- 3d-bis. A named mathematical law supplied as a hypothesis ----------
    #
    # "Given Cauchy-Schwarz, apply Cauchy-Schwarz" is a modularisation, not a
    # result, and it reads as one only because the law sits in a binder where no
    # audit looks.  The tell is the binder NAME: a hypothesis called
    # `hCauchySchwarz` is not a constraint distinguishing this object from
    # another, it is a classical theorem the proof declines to prove or cite.
    #
    # Named laws only.  A hypothesis quantified over arbitrary functions is NOT
    # flagged on shape alone: `hEbound : ∀ v, ‖v‖ = 1 → |⟪v, E v⟫| ≤ δ` is a
    # genuine property of the operator `E`, and flagging it would push authors to
    # inline the bound rather than name it.
    LAW_HYPOTHESIS = re.compile(
        r"^h_?(cauchy|schwarz|cauchyschwarz|jensen|holder|hoelder|minkowski|"
        r"triangle|chebyshev|markov|hoeffding|bernstein|azuma|mcdiarmid|"
        r"borel|cantelli|fatou|lebesgue|fubini|tonelli|radon|nikodym|"
        r"hahn|banach|riesz|stone|weierstrass|arzela|ascoli|"
        r"gnedenko|kolmogorov|donsker|slutsky|lindeberg|berry|esseen|"
        r"donoho|liu|sion|neumann|brouwer|kakutani|farkas|"
        r"pinsker|bretagnolle|huber|leCam|fano|assouad)",
        re.I)
    law_hypotheses = []
    for tname, stmt in global_theorems:
        decl = full_decl.get(tname, stmt)
        signature = statement_of(decl)
        for hname in re.findall(r"\((h[A-Za-z_0-9']*)\s*:", signature):
            if LAW_HYPOTHESIS.match(hname):
                law_hypotheses.append(
                    "`%s` takes `%s` as a hypothesis: a named theorem supplied as a "
                    "parameter proves only that the theorem was assumed" % (tname, hname))
    if law_hypotheses:
        bad.append("named mathematical laws supplied as hypotheses: %d, budget 0; "
                   "prove the law for the object at hand, or state the theorem about "
                   "an object that has it" % len(law_hypotheses))
        bad.extend("    " + x for x in law_hypotheses)

    domain_named_arithmetic = []
    for tname, stmt in global_theorems:
        if not DOMAIN_WORD.search(tname):
            continue
        signature = statement_of(full_decl.get(tname, stmt))
        goal = goal_of(signature)
        goal_idents = set(re.findall(IDENT, goal))
        if goal_idents & corpus_vocab:
            continue
        # A hypothesis can earn the name too, but only if it constrains what the
        # goal talks about. `continental_portability_forces_two_thirds_tagging_loss`
        # bounds `shared_ld` GIVEN that `taggedDriftR2RatioCorrected` takes a stated
        # value at it: the corpus quantity is in the hypothesis and the variable it
        # pins is in the goal, so the claim is about genetics and the name is honest.
        # An unrelated hypothesis earns nothing -- the shared variable is the test.
        hyps = signature[:len(signature) - len(goal)] if goal and goal in signature else ""
        for hyp in re.findall(r"\([^()]*:[^()]*\)", hyps):
            hyp_idents = set(re.findall(IDENT, hyp))
            if (hyp_idents & corpus_vocab) and (hyp_idents & goal_idents):
                break
        else:
            domain_named_arithmetic.append(
            "`%s` names genetics but its goal mentions no constant this corpus "
            "defines" % tname)
    if domain_named_arithmetic:
        bad.append("genetics-asserting names on domain-free statements: %d; "
                   "either state the theorem about a defined quantity or name it for "
                   "the arithmetic it does"
                   % len(domain_named_arithmetic))
        bad.extend("    " + x for x in domain_named_arithmetic)

    # 3e. Cheap structural integrity, run before the build so that a broken
    #     rename or an unterminated comment fails in seconds rather than after a
    #     full elaboration. The "+/-" incident is the motivating case: text in a
    #     status marker contained "/-", which opened a nested comment and left a
    #     docstring unterminated.
    for f in ident_lean_files():
        raw = open(f).read()
        rel = os.path.relpath(f, IDENT_ROOT)
        if raw.count("/-") != raw.count("-/"):
            bad.append(f"{rel}: unbalanced comment delimiters "
                       f"({raw.count('/-')} open, {raw.count('-/')} close)")
        for err in ident_block_structure_errors(ident_strip_comments(raw)):
            bad.append(f"{rel}: {err}")
        # `[A-Za-z.]*` stopped at the first digit, so a module whose name
        # contains one -- `MetricSpecificPortability.R2Decomposition` -- was read
        # as `...MetricSpecificPortability.R` and reported as an import of a
        # module that does not exist.  The corpus had no such name until a split
        # produced one from `section R2Decomposition`.
        for imp in re.findall(r"^import (Descent[\w.]*)", raw, re.M):
            if not os.path.exists(os.path.join(IDENT_ROOT, imp.replace(".", "/") + ".lean")):
                bad.append(f"{rel}: imports {imp}, which does not exist")

    # 4. semantic isolation. A module that no theorem ever relates to another
    #    module cannot be contradicted by anything: a false definition inside it
    #    is consistent with the whole corpus. This is the condition that let two
    #    falsified identifications survive review, so the count is ratcheted.
    # A LEAN-SIDE DEFINITION IS NOT A QUANTITY. This screen's own scoping note says the risk
    # is "a false DEFINITION sheltered where nothing can contradict it", and scopes the count
    # to modules that define something. What it must mean by "something" is something a
    # measurement could contradict. `DocConvention.statusMarker : List Char`,
    # `Linters.moduleOf : MetaM Name`, `StatusLinter.statusLinter : Linter` and
    # `Semiformal.elabSemiformalResult : CommandElab` are the corpus's own tooling; they
    # assert nothing about a population, and the link demanded -- a theorem naming one of
    # them beside another module's quantity -- is not a statement anyone can write. The same
    # reasoning already exempts a module of pure theorems over Mathlib objects, which owns
    # nothing to be wrong about; a module owning only elaboration machinery owns no more.
    LEAN_SIDE = re.compile(r"\b(?:MetaM|CoreM|CommandElab|CommandElabM|TermElabM|Linter|"
                           r"MessageData|Syntax|Expr|Environment|Name|String|Char|Format|"
                           r"IO)\b")
    owner = {}
    for f in ident_lean_files():
        mod = os.path.basename(f)[:-5]
        for m in re.finditer(r"^(?:noncomputable )?(?:def|abbrev|structure) ([A-Za-z_0-9'.]+)"
                             r"((?:(?!:=|\bwhere\b)[\s\S])*)(?::=|\bwhere\b)",
                             ident_strip_comments(open(f).read()), re.M):
            if LEAN_SIDE.search(m.group(2)):
                continue
            owner[m.group(1).split(".")[-1]] = mod
    linked = {}
    for f in ident_lean_files():
        body = ident_strip_comments(open(f).read())
        for b in re.split(r"\n(?=@\[simp\]\s*\n?theorem |theorem |private theorem )", body):
            if not re.match(r"(?:@\[simp\]\s*)?(?:private )?theorem ", b) or ":=" not in b:
                continue
            stmt = b.split(":=", 1)[0]
            mods = {owner[t] for t in re.findall(r"[A-Za-z_][A-Za-z_0-9']*", stmt) if t in owner}
            if len(mods) > 1:
                for a in mods:
                    linked.setdefault(a, set()).update(mods - {a})
    # A module that defines no quantity is not in scope. The risk this screen
    # exists for is a false DEFINITION sheltered where nothing can contradict
    # it, and the link it asks for is a theorem naming this module's own
    # definitions beside another module's. A module of pure theorems over
    # Mathlib objects owns nothing to be wrong about and nothing to put in such
    # a statement, so requiring one asks it to invent a definition it does not
    # need. Scope the count to modules that define something.
    defining = {m for m in owner.values()}
    all_mods = {os.path.basename(f)[:-5] for f in ident_lean_files()}
    isolated = sorted(m for m in all_mods & defining if not linked.get(m))
    if isolated:
        bad.append(f"semantically isolated modules: {len(isolated)}: "
                   f"{', '.join(isolated)}; relate the new "
                   f"module's quantities to an existing one so it can be contradicted")

    if sites:
        # NAME the sites. This reported a bare count for a long time, and a
        # count is not actionable: locating the offenders meant re-implementing
        # the screen's own detection by hand -- domain-name test, ploidy regex,
        # tied set -- which someone did, correctly, to answer "is this mine?".
        # A guard that can find a finding can afford to say where it is.
        # The advice used to say "in Conventions.lean", which is now the one place
        # the tie should NOT go: a theorem far downstream of the definition it
        # constrains is a report about it.  It also ran the count into the advice
        # with no separator, printing `rose to 5relate the new constant`.
        bad.append(f"convention restatement sites rose to {sites}; "
                   f"state a theorem BESIDE the definition relating the new "
                   f"constant to `ploidy` or to a derived primitive, rather than "
                   f"inlining it"
                   + "".join(f"\n      {s}" for s in sorted(site_names)))

    # The ledger prints before the guard verdict, and unconditionally. Printing
    # it after the `return 1` made it dead code on exactly the runs that matter:
    # a corpus with a failing guard is the one whose outstanding admissions a
    # reader most needs to see, and `sorry` is the admission this corpus asks
    # for in preference to a laundered premise. Debt that only lists itself when
    # everything else is green is not enumerable.
    if admissions:
        print("TRANSPARENT ADMISSIONS (these declarations are incomplete)\n")
        for admission in admissions:
            print("  " + admission)
        print()
    if bad:
        print("STRUCTURAL GUARD FAILURES\n")
        for b in bad:
            print("  " + b)
        return 1
    print(f"structural guards pass: convention sites {sites}, "
          f"undeclared {len(undeclared)}, conventions {len(undeclared_conv)}, "
          f"unrelated {len(unrelated)}, "
          f"stipulated equilibria {len(stipulated)}, "
          f"duplicate bodies {len(duplicates)}, "
          f"isolated modules {len(isolated)}, "
          f"admissions {len(admissions)} (reported, not trusted)")
    return 0


# ======================================================================================
# GUARD: laundering -- proof of a weaker statement under the right name
#
# Was `validation/code/check.py`.  Its full header, which defines the standard
# and enumerates every family this guard detects, is reproduced immediately below.
# ======================================================================================

# Ban proof laundering: a valid Lean proof of a weaker, conditional, vacuous, or
# circular statement presented as the intended theorem.
#
# WHAT THIS IS NOT.  It is not a kernel check.  The kernel is not being fooled in any
# of the patterns below; every one of them typechecks.  `validation/code/check.py`
# guards the source text and `validation/code/Check.lean` guards the
# transitive axiom closure, and NEITHER CAN SEE ANY OF THIS, because a laundered proof
# has no `sorry`, no custom axiom, and a clean `#print axioms` report.  The defect is
# that the declaration's TYPE is not the advertised mathematics.
#
# THE STANDARD, which is the only one that matters and which no tool applies for you:
#
#     A development has closed a theorem only when the final declaration states exactly
#     the intended mathematics, has no unresolved substantive premise (explicit, implicit,
#     or instance), constructs every certificate it consumes, instantiates every abstract
#     parameter with a concrete object proved to satisfy it, quantifies over a domain
#     proved nonempty, and has a clean transitive axiom report.
#
#     Anything less may be a useful conditional library.  It is not the advertised proof.
#
# A `sorry` IS PREFERRED TO EVERY PATTERN BELOW.  A `sorry` is an honest, machine-visible,
# kernel-tracked hole that the AXIOMS scan in Check.lean reports as `sorryAx`.  A laundered theorem is
# an invisible hole that every automated report calls green.  When the intended statement
# is not proved, state the intended statement and admit it; do not restate a provable
# shadow of it.  This inverts the usual repository rule -- see the LEDGER section in
# `validation/code/check.py` -- and it is deliberate.
#
# FAMILIES DETECTED.  Numbering follows the audit taxonomy; `severity` decides exit code.
#
#   FATAL -- the declaration does not prove what its name says.
#     F1   hypothesis laundering: the conclusion is one of the hypotheses, verbatim.
#     F1b  proof is a bare application of a hypothesis binder (`h`, `h x`, `hDeep prem`).
#     F4   certificate laundering: a parameter is a structure carrying the conclusion
#          (or any Prop) in a field; the theorem consumes a certificate it never builds.
#          Also reported when the whole proof is `h.field` or `h.field h'` -- the field
#          handed straight back.  NOT reported when an argument to the field is itself a
#          proved step (`B.fails (S.collapses B ▸ B.holds)`): that is modus ponens on a
#          corpus theorem, the same case the `h s` rule below already exempts, and the
#          2026-08 audit of `ProbeSeparation.no_blindness` found it to be a false positive
#          -- both structures there are constructed in-corpus and the content is in
#          `witness_collapses`.
#     F7   conclusion-by-definition: a predicate one of whose conjuncts IS the conclusion.
#     F8   definitional weakening: a target property defined as `True` or trivially.
#     F9   premise strengthening: premise and conclusion are the same existential.
#     F11  inconsistent instance context: a class with a `False` field, or premises
#          asserting both `Nontrivial` and `Subsingleton` of one type.
#     F24  trust bypass: custom `axiom`, `native_decide`, `unsafe`, custom elaborators.
#
#   CONDITIONAL -- valid implication, but the antecedent is unproved in this corpus.
#     F2   Prop alias with a theorem-like name and no inhabitant anywhere.
#     F3   typeclass laundering: a nonstandard class, `Fact`, `Nonempty`, `Inhabited`, or
#          a local instance obtained from a caller-supplied field. A local instance proved
#          in the tactic block is ordinary proof plumbing, not an assumption.
#     F16  wrapper chain: every Prop-valued binder in a theorem's signature.
#     F19  hidden assumptions: Prop-valued *implicit* and *instance* binders, plus
#          section `variable`s inherited silently.
#     F23  conditional bootstrapping: `Nonempty`/`Exists` conclusion whose witness came
#          in as an argument.
#
#   FIDELITY -- statement may be right, but nothing ties it to the intended object.
#     F5   existential repackaging.
#     F6   `Classical.choice`/`choose` applied to an assumed existence premise.
#     F10  vacuity: quantification over a domain with no inhabitant proved in-corpus.
#     F12  subtype laundering: domain is `{x // DesiredProperty x}`.
#     F13  a `.range`/image construction named as if it were the canonical object.
#     F15  prose claims one definition induces another and no theorem states the bridge.
#     F17  name inflation: `_complete`, `_proved`, `_exists`, `explicit_` on a
#          declaration that still carries premises.
#     F18  `#print axioms` aimed at a Prop DEFINITION rather than at a proof of it.
#     F20  semantic shadowing: a corpus predicate reusing a standard name.
#     F21  degenerate normalization: a THEOREM whose conclusion divides by a quantity
#          no premise shows is nonzero. Not definitions -- they have nothing to guard.
#     F22  the noun does the work: a parameter structure whose field IS the conclusion.
#
#   NOT DETECTED, deliberately -- listed so a clean report is not read as covering it:
#     F14  concrete-looking dead end. Every mechanical proxy is a reference count, and
#          a reference count cannot distinguish a dead end from a definition that is
#          unreferenced BY DESIGN (`X.witness`, `targetCorrectionCurvature`). Reference
#          counting has twice deleted correct work in this repository. See the comment
#          at the F14 site in `check_files`.
#
# USAGE
#     validation/code/check.py                  # whole corpus, human report
#     validation/code/check.py --json out.json  # machine-readable
#     validation/code/check.py path/to/File.lean ...
#
# Exit status is 1 if any FATAL or CONDITIONAL finding survives.  There is deliberately
# NO SUPPRESSION FILE.  A ledger of accepted laundering is how a corpus normalises it;
# if a finding is wrong, fix the detector and say why in this docstring.
#
# LIMITS, stated so a clean report is not over-read.  This is a source-text analysis: it
# sees what was typed, not what the elaborator produced.  It cannot see premises
# introduced by `export`ed instances from an import, a `Fact` synthesised at elaboration
# time, or a definition unfolded to something other than its written form.  The
# environment-level companion, `validation/code/Check.lean`, walks
# the fully elaborated telescope of every `Descent` declaration and is authoritative
# where the two disagree.  Run both.

FATAL, CONDITIONAL, FIDELITY = "FATAL", "CONDITIONAL", "FIDELITY"
SEVERITY_ORDER = {FATAL: 0, CONDITIONAL: 1, FIDELITY: 2}

# WHAT GATES, AND WHY IT IS NOT EVERYTHING.
#
# FATAL gates.  Those families are laundering proper: the declaration does not prove
# what its name says, and no amount of context makes that acceptable.
#
# EVERY SEVERITY GATES.  There is no ledger tier any more.  CONDITIONAL used to be
# exempt on the argument that a Prop-valued premise is ordinary mathematics and that a
# permanently red guard is read as broken and then ignored.  Both halves were true and
# neither is a reason to keep a tolerance: what a ledger measures is how much the corpus
# assumes, and a number that is allowed to sit there is a number nobody reduces.
#
# The consequence is stated rather than hidden: turning this on makes the guard red until
# the assumptions it names are discharged or the detector is fixed.  That redness is the
# corpus's true state, and a build that reports it is worth more than a green one that
# does not.  The flags that used to narrow the view -- `--severity` and `--strict` --
# are gone rather than defaulted: an option that can only weaken a gate is a tolerance
# with a command-line interface.
EXIT_ON = {FATAL, CONDITIONAL, FIDELITY}

FAMILY_SEVERITY = {
    "F1": FATAL, "F1b": FATAL, "F4": FATAL, "F7": FATAL, "F8": FATAL,
    "F9": FATAL, "F11": FATAL, "F24": FATAL,
    "F2": CONDITIONAL, "F3": CONDITIONAL, "F16": CONDITIONAL,
    "F19": CONDITIONAL, "F23": CONDITIONAL, "F22": FIDELITY,
    "F5": FIDELITY, "F6": FIDELITY, "F10": FIDELITY, "F12": FIDELITY,
    "F13": FIDELITY, "F15": FIDELITY, "F18": FIDELITY, "F14": FIDELITY, "F17": FIDELITY, "F20": FIDELITY,
    "F21": FIDELITY,
}

FAMILY_TITLE = {
    "F1": "hypothesis laundering (conclusion is a hypothesis)",
    "F1b": "proof is application of a hypothesis",
    "F2": "Prop alias with theorem-like name, never inhabited",
    "F3": "typeclass laundering",
    "F4": "certificate laundering (structure parameter carrying Props)",
    "F5": "existential repackaging",
    "F6": "choice applied to an assumed existence premise",
    "F7": "conclusion-by-definition",
    "F8": "definitional weakening",
    "F9": "premise strengthening to tautology",
    "F10": "vacuity: domain with no inhabitant proved",
    "F11": "inconsistent instance context",
    "F12": "subtype laundering",
    "F13": "range/image advertised as canonical construction",
    "F15": "claimed bridge between two definitions with no theorem proving it",
    "F18": "#print axioms on a Prop definition, not on a proof",
    "F16": "assumed fact about a corpus-defined object (laundered premise)",
    "F17": "theorem-name inflation",
    "F19": "hidden premise (implicit/instance/section variable)",
    "F20": "semantic shadowing of a standard name",
    "F22": "artificially narrow universe (bundled-premise parameter)",
    "F21": "degenerate normalization (unguarded denominator)",
    "F23": "conditional bootstrapping (witness supplied as argument)",
    "F24": "trust bypass",
}

# --------------------------------------------------------------------------------------
# Lexing: mask comments and string literals, preserving offsets
# --------------------------------------------------------------------------------------


def mask(src: str) -> str:
    """Replace comment and string content with spaces, keeping every offset and newline.

    Structural scans (delimiter depth, `:=` position) must not see a `(` inside a
    docstring.  Offsets are preserved so a match in the masked text indexes the original.
    """
    out = list(src)
    i, n = 0, len(src)
    depth = 0  # block-comment nesting; Lean's /- -/ nests
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if src.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        if src.startswith("/-", i):
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if c == '"':
            out[i] = " "
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\":
                    out[i] = " "
                    i += 1
                    if i < n:
                        out[i] = " "
                        i += 1
                    continue
                if src[i] != "\n":
                    out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


OPEN = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
CLOSE = {v: k for k, v in OPEN.items()}


def depths(text: str) -> list[int]:
    """Delimiter depth before each character."""
    d, out = 0, []
    for c in text:
        out.append(d)
        if c in OPEN:
            d += 1
        elif c in CLOSE:
            d = max(0, d - 1)
    return out


# --------------------------------------------------------------------------------------
# Declaration model
# --------------------------------------------------------------------------------------

DECL_KINDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "class", "instance",
    "inductive", "example", "opaque", "axiom",
)
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(" + "|".join(DECL_KINDS) + r")\b[ \t]*"
    r"([A-Za-z_À-ɏͰ-Ͽ][\w.'À-ɏͰ-Ͽ]*)?",
    re.M,
)
STOP_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(?:" + "|".join(DECL_KINDS) + r"|namespace|end|section|open|import|variable|"
    r"universe|attribute|macro|elab|syntax|notation|run_cmd|#\w+|/-)\b",
    re.M,
)


@dataclass
class Binder:
    name: str
    type: str
    kind: str          # "explicit" | "implicit" | "instance" | "strict"
    inherited: bool = False   # came from a section `variable`


@dataclass
class Decl:
    file: str
    line: int
    kind: str
    name: str
    header: str        # binders + `: conclusion`
    conclusion: str
    body: str
    doc: str
    binders: list[Binder] = dc_field(default_factory=list)
    attrs: str = ""


@dataclass
class Finding:
    family: str
    file: str
    line: int
    decl: str
    detail: str

    @property
    def severity(self) -> str:
        return FAMILY_SEVERITY[self.family]


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def split_binders(header: str) -> tuple[list[Binder], str]:
    """Split a declaration header into binders and the conclusion after the top-level `:`.

    A binder is a balanced delimiter group at depth 0; the conclusion is whatever follows
    the first depth-0 `:` that is not inside such a group.  Bare `{α}`-style anonymous
    binders and `∀`-bound variables inside a binder type stay inside that binder's type.
    """
    d = depths(header)
    binders: list[Binder] = []
    i, n = 0, len(header)
    concl_start = None
    while i < n:
        c = header[i]
        if d[i] == 0 and c in OPEN and c != "⟨":
            j = i
            depth = 0
            while j < n:
                if header[j] in OPEN:
                    depth += 1
                elif header[j] in CLOSE:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            group = header[i : j + 1]
            binders.extend(parse_binder_group(group))
            i = j + 1
            continue
        if d[i] == 0 and c == ":":
            concl_start = i + 1
            break
        i += 1
    conclusion = header[concl_start:] if concl_start is not None else ""
    return binders, norm(conclusion)


def parse_binder_group(group: str) -> list[Binder]:
    kind = {"(": "explicit", "{": "implicit", "[": "instance", "⦃": "strict"}[group[0]]
    inner = group[1:-1]
    d = depths(inner)
    colon = next((k for k, c in enumerate(inner) if c == ":" and d[k] == 0), None)
    if colon is None:
        # `[Group G]` -- anonymous instance, or `{α}` -- anonymous implicit.
        return [Binder(name="", type=norm(inner), kind=kind)]
    names = norm(inner[:colon])
    ty = norm(inner[colon + 1 :])
    return [Binder(name=nm, type=ty, kind=kind) for nm in names.split()] or [
        Binder(name="", type=ty, kind=kind)
    ]


def split_header_body(text: str) -> tuple[str, str]:
    """Split at the `:=` that opens the proof/definition body.

    Not the first `:=` in the text: a `let` inside a hypothesis binder or inside the
    conclusion has one too.  Take the first depth-0 `:=` whose line does not begin a
    `let`/`have`/`set`/`obtain`/`fun` -- those are body-internal.
    """
    d = depths(text)
    for m in re.finditer(r":=", text):
        i = m.start()
        if d[i] != 0:
            continue
        ls = text.rfind("\n", 0, i) + 1
        if re.match(r"\s*(let|have|set|obtain|fun|match|if|with)\b", text[ls:i]):
            continue
        return text[:i], text[i + 2 :]
    return text, ""


def parse_file(path: Path) -> tuple[list[Decl], list[tuple[int, str]]]:
    src = path.read_text(encoding="utf-8", errors="replace")
    m = mask(src)
    # Paths outside the repo must stay scannable: the calibration fixture writes to a
    # temp dir, and a detector that only runs on the corpus it judges cannot be tested
    # against known answers.
    try:
        rel = str(path.relative_to(CORPUS_BASE))
    except ValueError:
        rel = str(path)

    starts = []
    for mo in DECL_RE.finditer(m):
        starts.append((mo.start(), mo.group(1), mo.group(2) or "", mo.end()))

    # Section-scoped `variable` binders, tracked as (offset, group_text).
    variables: list[tuple[int, str]] = []
    for mo in re.finditer(r"^variable\b(.*)$", m, re.M):
        variables.append((mo.start(), src[mo.start(1) : mo.end(1)]))

    decls: list[Decl] = []
    for idx, (off, kind, name, hdr_off) in enumerate(starts):
        nxt = len(src)
        for mo in STOP_RE.finditer(m, hdr_off):
            nxt = mo.start()
            break
        # `mask` blanks comments, so STOP_RE cannot see the `/--` that opens the next
        # declaration's docstring.  Stop at a comment opener in the ORIGINAL text too, or
        # a declaration's body runs on into its neighbour's prose.
        cm = re.search(r"^\s*/-", src[hdr_off:nxt], re.M)
        if cm:
            nxt = hdr_off + cm.start()
        raw = src[off:nxt]
        raw_m = m[off:nxt]
        # docstring immediately above
        pre = src[max(0, off - 4000) : off]
        doc = ""
        # THE DOCSTRING IMMEDIATELY ABOVE, AND ONLY THAT ONE.  `/--(.*?)-/\s*$` under
        # `re.S` searches left to right, so it matched from the FIRST `/--` in four
        # thousand preceding characters through to the last `-/` -- swallowing every
        # docstring in between and the code between them.  A declaration then inherited
        # its neighbours' prose: `equalityPatternRangeEquiv` was reported for calling a
        # range construction "canonical" when the word belonged to a different definition
        # six lines above it, and two more F13 findings had no such word within twenty
        # lines of themselves at all.
        #
        # Forbidding `-/` inside the captured content stops the match at the nearest
        # complete block, which is the one attached to this declaration.
        dm = re.search(r"/--((?:(?!-/)[\s\S])*)-/\s*$", pre)
        if dm:
            doc = norm(dm.group(1))
        header_m, body_m = split_header_body(raw_m[hdr_off - off :])
        # Header and body come from the MASKED text.  Slicing the original at masked
        # offsets leaves comments inside the slice, and every check that compares a body
        # against an exact string then fails silently on a trailing `--` line.
        header = header_m
        body = body_m
        binders, conclusion = split_binders(header_m)
        # restore original (unmasked) text for binder types where possible
        line = src.count("\n", 0, off) + 1
        inherited = []
        for voff, vtext in variables:
            if voff < off:
                inherited.extend(
                    b for b in parse_binder_group_line(vtext)
                )
        for b in inherited:
            b.inherited = True
        attrs = ""
        am = re.match(r"^(@\[[^\]]*\])", raw)
        if am:
            attrs = am.group(1)
        decls.append(
            Decl(
                file=rel, line=line, kind=kind, name=name,
                header=norm(header), conclusion=conclusion,
                body=norm(body), doc=doc, binders=binders + inherited, attrs=attrs,
            )
        )
    return decls, variables


def parse_binder_group_line(text: str) -> list[Binder]:
    """Parse the binder groups on a `variable ...` line."""
    out: list[Binder] = []
    d = depths(text)
    i, n = 0, len(text)
    while i < n:
        if d[i] == 0 and text[i] in OPEN and text[i] != "⟨":
            j, depth = i, 0
            while j < n:
                if text[j] in OPEN:
                    depth += 1
                elif text[j] in CLOSE:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            out.extend(parse_binder_group(text[i : j + 1]))
            i = j + 1
            continue
        i += 1
    return out


# --------------------------------------------------------------------------------------
# Prop-ness
# --------------------------------------------------------------------------------------

# LEAN IDENTIFIERS ARE NOT ASCII.  `[A-Za-z_]` does not match `β`, `τ`, `κ`, `μ`, `η`,
# and this corpus names most of its mathematical variables with Greek letters.  With the
# ASCII class, a premise `0 < additiveGeneticVariance β` appeared to mention no binder of
# its own theorem, so it was classed as a handed-over fact rather than the side condition
# on `β` that it is -- 27 false positives, every one of them a correct hypothesis.
# `[^\W\d]` is the Unicode-aware "word character that is not a digit".
IDENT = r"[^\W\d][\w'!?₀-₉]*"

REL = ["=", "≠", "≤", "<", "≥", ">", "∈", "∉", "⊆", "⊂", "≡", "≈", "∼", "∣"]
LOGIC = ["∀", "∃", "¬", "∧", "∨", "↔"]

# Mathlib classes that are ordinary algebraic structure, not smuggled mathematics.
STANDARD_CLASSES = {
    "Fintype", "DecidableEq", "Decidable", "MeasurableSpace", "NormedAddCommGroup",
    "NormedSpace", "InnerProductSpace", "TopologicalSpace", "MetricSpace", "Group",
    "AddCommGroup", "CommRing", "Field", "LinearOrder", "Preorder", "PartialOrder",
    "Module", "Ring", "Monoid", "AddMonoid", "CommMonoid", "SeminormedAddCommGroup",
    "MeasureSpace", "IsProbabilityMeasure", "IsFiniteMeasure", "CompleteSpace",
    "SecondCountableTopology", "BorelSpace", "OpensMeasurableSpace", "T2Space",
    "Countable", "Encodable", "Semiring", "CommSemiring", "Algebra", "Star",
    "ContinuousMul", "ContinuousAdd", "MeasurableSingletonClass", "SFinite",
    "IsFiniteKernel", "IsMarkovKernel", "NeZero", "CharZero", "Nontrivial",
    "Subsingleton", "Unique", "FunLike", "Coe", "CoeFun", "Repr", "ToString",
    "Zero", "One", "Add", "Mul", "Neg", "Inv", "Sub", "Div", "Pow", "SMul",
    "LE", "LT", "HAdd", "HMul", "Membership", "Insert", "Singleton", "Lattice",
    "OrderedAddCommGroup", "LinearOrderedField", "RCLike", "IsROrC", "Norm",
    "Dist", "EDist", "PseudoMetricSpace", "UniformSpace", "ProperSpace",
    "FiniteDimensional", "Basis", "NormedRing", "NormedField", "NNRealAlgebra",
}
# Classes whose whole content is an assumption, regardless of who defined them.
ASSUMPTION_CLASSES = {"Fact", "Nonempty", "Inhabited"}


def is_prop_type(ty: str, prop_aliases: set[str], prop_structs: set[str],
                 type_names: frozenset = frozenset()) -> bool:
    """Whether a binder type is a PROPOSITION (a hypothesis), as opposed to data.

    `(f : α → Prop)` is data -- an abstract predicate parameter, reported separately.
    `(h : ∀ x, f x)` is a proposition.  The discriminator is the head, not the presence
    of the token `Prop`.

    A LEADING `∀` DOES NOT MAKE A PROPOSITION.  `∀ x, body` is a dependent function type,
    and it is a proposition exactly when `body` is one; when `body` is a type family it is
    ORDINARY DATA.  `(ξ : ∀ n, ER n)` is a family of equivalence relations, one per index,
    and reading it as an assumed fact reported a data parameter as a laundered premise.

    The recursion uses POSITIVE KNOWLEDGE ONLY: it reclassifies as data when the body's
    head is a name this corpus defines and does not define as a proposition.  A head that
    is a bound predicate -- the documented `∀ x, f x` -- is not a corpus name, so it stays
    a proposition, and no case the caller could not verify is decided here.
    """
    t = norm(ty)
    if not t:
        return False
    if re.search(r"(→|->)\s*Prop$", t) or t == "Prop":
        return False          # predicate-valued data, not an assumption
    if any(t.startswith(k + " ") or t == k for k in LOGIC) or t.startswith("¬"):
        if t.startswith("∀") and "," in t:
            body = t.split(",", 1)[1].strip()
            bhead = re.match(r"([A-Za-z_][\w.']*)", body)
            if bhead:
                bbase = bhead.group(1).split(".")[-1]
                if (bbase in type_names and bbase not in prop_aliases
                        and bbase not in prop_structs):
                    return False
        return True
    # `ℝ≥0` AND `ℝ≥0∞` ARE TYPE NAMES.  The relation scan below looks for `≥` anywhere at
    # depth zero, and Mathlib spells the non-negative reals with one inside the name -- so
    # `(C : ℝ≥0)`, an ordinary numeric parameter, read as the proposition `ℝ ≥ 0` and was
    # reported as a hidden premise.  The scan runs over the type with those two notations
    # blanked, so a relation has to be a relation and not a letter in a noun.
    scan = t.replace("ℝ≥0∞", "NNRealInf").replace("ℝ≥0", "NNRealName")
    d = depths(scan)
    for op in REL + LOGIC:
        for k in range(len(scan) - len(op) + 1):
            if scan[k : k + len(op)] == op and d[k] == 0:
                return True
    head = re.match(r"([A-Za-z_][\w.']*)", t)
    if head:
        h = head.group(1)
        base = h.split(".")[-1]
        if h in prop_aliases or base in prop_aliases:
            return True
        if base in prop_structs:
            return True
        if base in ASSUMPTION_CLASSES:
            return True
        if re.match(r"^(Is|Has)[A-Z]", base) and base not in STANDARD_CLASSES:
            return True
    return False


# --------------------------------------------------------------------------------------
# Corpus index
# --------------------------------------------------------------------------------------


@dataclass
class Corpus:
    decls: list[Decl]
    prop_aliases: set[str]                     # `def X : Prop`
    struct_fields: dict[str, list[Binder]]     # structure/class -> fields
    prop_structs: set[str]                     # structures with >=1 Prop field
    inhabited: set[str]                        # types with an in-corpus inhabitant
    used_names: dict[str, int]                 # identifier -> occurrence count
    corpus_names: set[str]                     # definitions this corpus APPLIES


FIELD_RE = re.compile(r"^\s{2,}([a-zA-Z_][\w']*)\s*:(?!=)(.*)$")


def build_corpus(files: list[Path]) -> Corpus:
    decls: list[Decl] = []
    for f in files:
        d, _ = parse_file(f)
        decls.extend(d)

    prop_aliases = {
        d.name for d in decls
        if d.kind in ("def", "abbrev") and norm(d.conclusion) == "Prop"
    }

    struct_fields: dict[str, list[Binder]] = {}
    for f in files:
        src = mask(f.read_text(encoding="utf-8", errors="replace"))
        cur = None
        for line in src.split("\n"):
            sm = re.match(
                r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
                r"(structure|class)\s+([A-Za-z_][\w.']*)", line)
            if sm:
                cur = sm.group(2).split(".")[-1]
                struct_fields.setdefault(cur, [])
                continue
            if cur is None:
                continue
            if line.strip() and not line.startswith((" ", "\t")):
                cur = None
                continue
            fm = FIELD_RE.match(line)
            if fm and not line.strip().startswith(("--", "|", "/-")):
                struct_fields[cur].append(
                    Binder(name=fm.group(1), type=norm(fm.group(2)), kind="field"))

    prop_structs: set[str] = set()
    # Fixed point: a structure with a Prop field, or with a field whose type is a
    # structure already known to carry Props, is itself a certificate.
    for _ in range(6):
        grew = False
        for s, fs in struct_fields.items():
            if s in prop_structs:
                continue
            if any(is_prop_type(b.type, prop_aliases, prop_structs) for b in fs):
                prop_structs.add(s)
                grew = True
        if not grew:
            break

    inhabited: set[str] = set()
    for d in decls:
        c_ = norm(d.conclusion)
        m = re.match(r"Nonempty\s+\(?([A-Za-z_][\w.']*)", c_)
        if m:
            inhabited.add(m.group(1).split(".")[-1])
        # A SUBTYPE IS NAMED BY ITS PREDICATE.  `Nonempty {η : ER n // Covers ξ η}` began
        # with `{`, which the pattern above cannot match, so proving a subtype inhabited
        # recorded nothing and F12 could not be cleared by any amount of correct work.
        ms = re.match(r"Nonempty\s*\{[^/]*//\s*([A-Za-z_][\w.']*)", c_)
        if ms:
            inhabited.add(ms.group(1).split(".")[-1])
        # Theorems count too.  A Prop-valued structure (`IsRankAllocation k M : Prop`)
        # is inhabited by a THEOREM proving it holds of some `k` and `M`, and a data
        # structure by a theorem concluding `Nonempty S`, matched above.
        if d.kind not in ("def", "abbrev", "instance", "theorem", "lemma"):
            continue
        # A WITNESS MAY TAKE DATA AND MAY NOT TAKE HYPOTHESES.  `f (k : ℕ) (β : ℝ) : S k`
        # builds the structure for every choice of its numeric inputs, so `S` is inhabited.
        # `f (h : HardProblemSolved) : S` builds nothing: it moves the obligation to the
        # caller, which is the pattern this file exists to catch.
        if any(is_prop_type(b.type, prop_aliases, prop_structs)
               for b in d.binders if not b.inherited):
            continue
        head = re.match(r"([A-Za-z_][\w.']*)", c_)
        if head:
            inhabited.add(head.group(1).split(".")[-1])
        if d.kind == "instance":
            for tok in re.findall(r"[A-Za-z_][\w.']*", c_):
                inhabited.add(tok.split(".")[-1])

    used: dict[str, int] = defaultdict(int)
    for f in files:
        for tok in re.findall(r"[A-Za-z_][\w.']*", mask(
                f.read_text(encoding="utf-8", errors="replace"))):
            used[tok.split(".")[-1]] += 1

    # NAMES THAT MAKE A PREMISE SUBSTANTIVE: definitions the corpus APPLIES.
    #
    # Field names are deliberately NOT in this set.  `Ne`, `V_A`, `mu` and `t` are fields
    # of some structure somewhere AND are ordinary names for free reals, so including
    # them classified every `(hNe : 0 < Ne)` side condition as an assumed corpus fact --
    # about four times more findings than there is laundering.  A premise is substantive
    # when it APPLIES a definition of this corpus (`hetMutationFloor Ne mu ≤ x`), not
    # when it happens to name a variable the way a field is named.
    #
    # Field ACCESS (`0 < m.V_A`) is also not substantive: it is a side condition on a
    # model's own component, and the model parameter is already judged by F4 and F22.
    corpus_names: set[str] = {
        d.name.split(".")[-1] for d in decls
        if d.name and d.kind in ("def", "abbrev", "structure", "class", "inductive")
    }
    corpus_names |= prop_aliases
    corpus_names -= {"", "witness", "nonempty"}

    return Corpus(decls, prop_aliases, struct_fields, prop_structs, inhabited, used,
                  corpus_names)


# --------------------------------------------------------------------------------------
# Detectors
# --------------------------------------------------------------------------------------

THEOREMISH = re.compile(
    r"(?i)(theorem|conjecture|lemma|principle|law|classification|result)$")
INFLATED = re.compile(
    r"(?i)(_complete|_proved|_holds|_exists$|^explicit_|_established|_settled"
    r"|_construction$|_theorem$|_conjecture$)")
# A name that QUALIFIES its inflated token is not claiming a closed result.  Two kinds of
# qualifier, and all four F17 findings were one or the other.
#
#   A CONDITION.  `coverers_const_of_exists` matched `_exists$` and was reported for
#   "claiming a closed result", when `_of_` is this corpus's own convention for saying
#   exactly the opposite.  This is the vocabulary the `identifications` guard already uses.
#
#   A POINT.  `r2_momentsUnderDrift_at_complete` matched `_complete`, but `_at_complete`
#   names where the statement is evaluated -- `F_ST = 1`, complete differentiation -- and
#   its sibling is `r2_momentsUnderDrift_at_source`.  `_at_` introduces a location in
#   parameter space, never a claim about a proof's status.
QUALIFIED_NAME_TOKEN = re.compile(
    r"(?:^|_)(?:of|assuming|given|under|conditional|when|if|requires|at)_", re.I)
STANDARD_PREDICATES = {
    "IsSofic", "IsFinitelyPresented", "HasPropertyT", "IsAmenable", "IsCompact",
    "IsOpen", "IsClosed", "IsIntegral", "Measurable", "Continuous", "Integrable",
    "IsUnit", "IsNoetherian", "IsSeparable", "IsErgodic", "IsStationary",
    "IsProbabilityMeasure", "IsMartingale", "Convex", "Differentiable",
}


def analyse(corpus: Corpus) -> list[Finding]:
    out: list[Finding] = []
    proved_props: set[str] = set()
    for d in corpus.decls:
        if d.kind in ("theorem", "lemma"):
            head = re.match(r"([A-Za-z_][\w.']*)", d.conclusion)
            if head and not [b for b in d.binders
                             if is_prop_type(b.type, corpus.prop_aliases,
                                             corpus.prop_structs)]:
                proved_props.add(head.group(1).split(".")[-1])

    for d in corpus.decls:
        out.extend(check_decl(d, corpus, proved_props))
    out.extend(check_files(corpus))
    out.extend(check_bridges(corpus))
    return out


def hypotheses(d: Decl, c: Corpus) -> list[Binder]:
    return [b for b in d.binders if is_prop_type(b.type, c.prop_aliases, c.prop_structs, frozenset(c.corpus_names))]


def check_decl(d: Decl, c: Corpus, proved_props: set[str]) -> list[Finding]:
    f: list[Finding] = []
    add = lambda fam, detail: f.append(Finding(fam, d.file, d.line, d.name, detail))
    hyps = hypotheses(d, c)
    concl = norm(d.conclusion)
    body = norm(d.body)

    if d.kind in ("theorem", "lemma", "example"):
        # F1 -- the conclusion is verbatim one of the hypotheses.
        for b in hyps:
            if norm(b.type) == concl and concl:
                add("F1", f"conclusion is hypothesis `{b.name} : {b.type}`")
                break
        else:
            # F9 -- premise and conclusion are the same existential, modulo binder name.
            for b in hyps:
                if concl and _same_existential(b.type, concl):
                    add("F9", f"premise `{b.name}` is the conclusion up to renaming")
                    break

        # F1b -- the whole proof is an application of a binder.
        p = re.sub(r"^by\s+", "", body).strip()
        p = re.sub(r"^exact\s+", "", p).strip()
        p = re.sub(r"^intro[s]?\s+[\w\s]*;?\s*", "", p).strip()
        m = re.fullmatch(r"([A-Za-z_][\w']*)((?:\.[a-zA-Z_][\w']*)*)((?:\s+\S+)*)", p)
        if m:
            root = m.group(1)
            names = {b.name for b in d.binders if b.name}
            if root in names:
                b = next(x for x in d.binders if x.name == root)
                fld = m.group(2).lstrip(".").split(".")[0] if m.group(2) else ""
                owners = [s for s, fs in c.struct_fields.items()
                          if any(x.name == fld for x in fs)] if fld else []
                # Only two shapes are content-free:
                #
                #   `h`            -- the proof IS the premise.
                #   `h.field args` -- the proof is a field the caller filled in,
                #                     PROVIDED the arguments are themselves binders.
                #
                # `h s` is modus ponens: unfolding a definition at a point, or applying a
                # premise to a theorem the corpus proves, is ordinary mathematics.  Its
                # conditionality is real and F16 is where that is reported.
                if not fld and not m.group(3).strip() and \
                        is_prop_type(b.type, c.prop_aliases, c.prop_structs, frozenset(c.corpus_names)):
                    add("F1b", f"proof is the bare premise `{root}`: the theorem "
                               f"restates its own hypothesis")
                elif owners:
                    # The same discrimination the `h s` case makes, one level down.
                    # `h.field` and `h.field h'` hand back a field the caller supplied.
                    # `h.field (thm x ▸ h.other)` applies that field to something the
                    # CORPUS PROVES; the proved step is the mathematics, and reporting it
                    # as laundering would demand the corpus stop using its own theorems.
                    args = m.group(3).split()
                    if all(re.fullmatch(r"[A-Za-z_][\w'.]*", a)
                           and a.split(".")[0] in names for a in args):
                        add("F4", f"proof is projection `{p[:60]}` "
                                  f"[field of {', '.join(owners[:3])}]")

        # F4 -- a parameter is a certificate structure.
        for b in d.binders:
            head = re.match(r"([A-Za-z_][\w.']*)", norm(b.type))
            if not head:
                continue
            base = head.group(1).split(".")[-1]
            if base in c.prop_structs:
                carrying = [x.name for x in c.struct_fields.get(base, [])
                            if is_prop_type(x.type, c.prop_aliases, c.prop_structs, frozenset(c.corpus_names))]
                if base not in c.inhabited:
                    add("F4", f"parameter `{b.name} : {base}` is a certificate "
                              f"(Prop fields: {', '.join(carrying[:4])}) and no "
                              f"inhabitant of `{base}` is constructed in-corpus")
                else:
                    # F22 IS NOT "TAKES A STRUCTURE WITH PROP FIELDS".  That fires on
                    # every theorem quantified over an algebraic structure -- 877 of
                    # them here, starting with `ExpFunctional`, whose Prop fields are
                    # the linearity axioms.  Quantifying over a witnessed class is
                    # ordinary mathematics, not a narrowed universe.
                    #
                    # The real defect is the taxonomy's `GoodAction`: a structure one of
                    # whose fields IS the conclusion, so the noun does all the work and
                    # the theorem is its own hypothesis wearing a type. Detect exactly
                    # that -- the conclusion, with the parameter's projections stripped,
                    # equals a Prop field's statement.
                    bare = norm(concl.replace(f"{b.name}.", "")) if b.name else ""
                    for fld in c.struct_fields.get(base, []):
                        if not is_prop_type(fld.type, c.prop_aliases, c.prop_structs, frozenset(c.corpus_names)):
                            continue
                        if bare and bare == norm(fld.type):
                            add("F22", f"parameter `{b.name} : {base}` has field "
                                       f"`{fld.name}` whose statement IS this "
                                       f"conclusion; the noun does all the work")
                            break

        # F16/F19 -- any remaining Prop-valued premise.
        for b in hyps:
            head = re.match(r"([A-Za-z_][\w.']*)", norm(b.type))
            base = head.group(1).split(".")[-1] if head else ""
            if base in c.prop_structs:
                continue      # already reported as F4
            # THE DISCRIMINATION THAT MATTERS.  `(hx : 0 < x)` on a free real is a side
            # condition: the theorem is about all `x` meeting it, and deleting it makes
            # the statement FALSE, not honest.  `(h : portability F = calibration G)` is
            # an assumed fact about objects THIS CORPUS DEFINES -- something it could be
            # proving and is instead receiving.  Only the second is laundering, and only
            # the second is worth an agent's time.
            # WHAT SEPARATES A LAUNDERED PREMISE FROM A RESTRICTION.
            #
            # `(h : Even' f)` applies a corpus definition, but `f` is one of the
            # theorem's own binders: the premise SELECTS which `f` the theorem is about.
            # Deleting it makes the statement FALSE, not honest, and the theorem
            # "for every even f, ..." is ordinary mathematics.  Same for
            # `(h : hetMutationFloor Ne mu ≤ tol)` -- a constraint on this theorem's own
            # reals.
            #
            # A premise is a HANDED-OVER FACT when it is CLOSED with respect to those
            # binders: it constrains nothing the theorem quantifies over, so it cannot be
            # selecting a sub-class.  It is simply a claim about this corpus's own
            # definitions, arriving as a gift instead of being proved.
            #
            #     (h : ∀ y, portabilityDecay y ≤ 1) (x : ℝ) : ...     <- laundering
            #     (x : ℝ) (h : portabilityDecay x ≤ 1)  : ...        <- restriction on x
            #
            # This distinction is the whole difference between 435 findings and ~4600,
            # and getting it wrong in either direction destroys the tool: too loose and
            # agents delete hypotheses that theorems need, too tight and real assumed
            # results hide among the side conditions.
            plain = set(re.findall(rf"(?<![.\w'])({IDENT})", b.type))
            own = {x.name for x in d.binders if x.name}
            local: set[str] = set()
            for q in re.findall(r"[∀∃]([^,]*),", b.type):
                local |= set(re.findall(IDENT, q.split(":")[0]))
            for q in re.findall(r"fun([^=]*)=>", b.type):
                local |= set(re.findall(IDENT, q.split(":")[0]))
            mentions = (plain - own - local) & c.corpus_names
            constrains_own = bool((plain & own) - local)
            substantive = bool(mentions) and not constrains_own
            # WHAT THIS FAMILY ASKS IS *WHERE*, NOT *WHAT*.  F16 below asks whether a
            # premise assumes something about this corpus's definitions.  This one asks
            # whether the premise is CONCEALED, and concealment does not depend on what is
            # concealed: `theorem foo {h : 1 = 1} : True` shows a reader no premise at all,
            # and nothing resolves `h` for them either.  An implicit or strict binder, and
            # a section variable, are reported whatever they say.
            #
            # AN INSTANCE BINDER OF A FIXED-CONTENT CLASS IS NOT CONCEALED.  `[Nonempty ι]`
            # stands in the signature where a reader sees it, and typeclass inference is a
            # documented mechanism rather than a hiding place.  Reporting it made the same
            # side condition a finding as `[Nonempty ι]` and clean as `(h : Nonempty ι)`,
            # decided by the brackets.  So an instance premise is reported when its class
            # carries arbitrary content, or when it assumes something about a definition
            # this corpus makes -- and `Fact`, which exists to carry an ARBITRARY
            # proposition through inference, is caught by F3 on exactly that ground.
            # WHOSE CLASS IS IT.  A hand-kept list of "ordinary Mathlib structure" cannot
            # be right for long -- `IsStrictOrderedRing` was missing from it, and seven
            # findings in one file were that omission.  The question the list was standing
            # in for is answerable directly: this corpus can only launder a definition it
            # OWNS, so an instance of a class it does not define is infrastructure.
            concealed = True
            if b.kind == "instance" and not substantive:
                # THE CLASS CAN SIT UNDER BINDERS.  `[∀ k, IsProbabilityMeasure (μ k)]`
                # names a Mathlib class, but the head regex starts at the first character
                # and `∀` is not one it matches, so the class went unidentified and the
                # premise was reported as concealed.  Strip the quantifier prefix and ask
                # about the class actually being required.
                itype = norm(b.type)
                while re.match(r"[∀∃]", itype) and "," in itype:
                    itype = itype.split(",", 1)[1].strip()
                ihead = re.match(r"([A-Za-z_][\w.']*)", itype)
                if ihead:
                    ibase = ihead.group(1).split(".")[-1]
                    corpus_owned = (ibase in c.struct_fields or ibase in c.prop_structs
                                    or ibase in c.prop_aliases)
                    if not corpus_owned:
                        concealed = False
            if (b.kind in ("implicit", "instance", "strict") or b.inherited) and concealed:
                add("F19", f"hidden premise `{b.kind}"
                           f"{' (section variable)' if b.inherited else ''}"
                           f" {b.name} : {_clip(b.type)}`")
            elif substantive:
                add("F16", f"premise `{b.name} : {_clip(b.type)}` assumes a fact about "
                           f"{', '.join(sorted(mentions)[:3])}")
            # A non-substantive explicit premise -- a side condition constraining only the
            # theorem's own free variables, `(hx : 0 < x)` -- emits NOTHING.
            #
            # It used to emit `F16s`, whose own title ended "(not laundering)" and whose
            # fixture asserted it "correctly does not gate".  A family documented in two
            # places as correctly reported on clean mathematics is not a finding; it is an
            # annotation, and the only thing keeping it out of the exit status was a
            # severity tier.  With every severity gating there is nowhere to put a
            # non-defect, so the non-defect goes rather than the gate.

        # F3 -- typeclass laundering.
        for b in d.binders:
            if b.kind != "instance":
                continue
            head = re.match(r"([A-Za-z_][\w.']*)", norm(b.type))
            if not head:
                continue
            base = head.group(1).split(".")[-1]
            # `Fact` wraps an arbitrary proposition and hands it to instance resolution;
            # the wrapper IS the laundering, so it is reported on sight.  `Nonempty` and
            # `Inhabited` have fixed content and smuggle nothing, so they are reported on
            # the same ground every other premise is: when they assume something about a
            # definition this corpus makes, rather than about a type the theorem is
            # quantified over.  Measured before the change: fifty findings, every one
            # `Nonempty`, not one `Fact`.
            assumes_corpus_object = bool(
                (set(re.findall(rf"(?<![.\w'])({IDENT})", b.type)) - {base})
                & c.corpus_names)
            if base == "Fact" or (
                (base in ASSUMPTION_CLASSES
                 or (base in c.struct_fields and base not in STANDARD_CLASSES))
                and assumes_corpus_object
            ):
                add("F3", f"instance premise `[{_clip(b.type)}]`")

        # F11 -- contradictory instance context.
        insts = [norm(b.type) for b in d.binders if b.kind == "instance"]
        for a in insts:
            if a.startswith("Nontrivial"):
                arg = a[len("Nontrivial"):].strip()
                if any(x.strip() == f"Subsingleton {arg}" for x in insts):
                    add("F11", f"premises assert both `Nontrivial {arg}` and "
                               f"`Subsingleton {arg}`: the context is empty")

        # F23 -- existential conclusion whose witness is a parameter.
        # `∃` IS NOT A WORD CHARACTER, so `∃\b` requires a word boundary that never
        # occurs and the branch was dead for every `∃` conclusion in the corpus.
        if re.match(r"(?:(?:Nonempty|Exists)\b|∃)", concl):
            wit = re.match(r"\s*⟨\s*([A-Za-z_][\w.']*)", re.sub(r"^by\s+", "", body))
            if wit and wit.group(1).split(".")[0] in {b.name for b in d.binders if b.name}:
                add("F23", f"existence proved by wrapping the parameter "
                           f"`{wit.group(1)}`")
            elif any(re.match(r"(?:(?:Nonempty|Exists)\b|∃)", norm(b.type)) for b in hyps):
                add("F5", "existential conclusion repackaging an existential premise")

        # F21 -- a quotient in the STATEMENT whose denominator is never shown nonzero.
        #
        # Not on definitions.  `def portableFraction (r2_total : ℝ) := x / r2_total` is an
        # ordinary definition; a definition takes no premises, so "unguarded denominator"
        # is not a defect it can commit, and firing there produced 80 findings and zero
        # defects.  The vacuity lives in a THEOREM: Lean's `x / 0 = 0` makes a claim about
        # a ratio silently true wherever the denominator vanishes, so a theorem whose
        # conclusion divides by a quantity it never constrains proves nothing there.
        # Capture the WHOLE dotted path. `m.V_A / m.V_P` divides by `m.V_P`, but a bare
        # `{IDENT}` captured the prefix `m` -- which IS a binder -- and reported the model
        # parameter as an unguarded denominator. Only a bare variable qualifies: a
        # projection like `m.V_P` is guarded by its own structure's invariants
        # (`V_P_pos`), and the structure parameter is judged by F4 and F22 instead.
        # ONLY INEQUALITIES. An EQUATION whose denominator appears on both sides is an
        # identity that also holds at zero -- `(lam*c)^2 / (lam^2*V) = c^2/V` is true at
        # `V = 0` because both sides are `0`, and demanding `V ≠ 0` would weaken a
        # correct theorem for nothing. What goes silently true is a BOUND: `0 ≤ x / d`
        # and `x / d < 1` claim nothing at `d = 0`, where the quotient collapses to `0`.
        concl_is_bound = any(op in concl for op in ("≤", "<", "≥", ">"))
        for m in (re.finditer(rf"/\s*({IDENT}(?:\.{IDENT})*)", concl)
                  if concl_is_bound else []):
            den = m.group(1)
            if "." in den:
                continue
            if den not in {b.name for b in d.binders if b.name}:
                continue
            # GUARDED means "some premise constrains this quantity", not "some premise
            # literally reads `den ≠ 0`". Two real shapes are missed by the literal test:
            #   * transitively: `(h : v_total = v_add + v_epi)` with both summands
            #     positive forces `0 < v_total`, and no premise names `v_total ≠ 0`;
            #   * by application: the denominator is `y 0`, and the premise is
            #     `hy0 : y 0 ≠ 0` -- about the applied term, not the bare `y`.
            # Deciding either needs a prover, so the rule is the conservative one: report
            # only when NO premise mentions the quantity at all. That under-reports a
            # denominator constrained nowhere near zero, and it never cries wolf over a
            # theorem whose hypotheses do pin the denominator down.
            guarded = any(re.search(rf"(?<![.\w']){re.escape(den)}(?![\w'])", b.type)
                          for b in d.binders
                          if is_prop_type(b.type, c.prop_aliases, c.prop_structs, frozenset(c.corpus_names)))
            if not guarded:
                add("F21", f"conclusion divides by `{den}`, which no premise shows is "
                           f"nonzero; `x / 0 = 0` in Lean, so the claim is silently true "
                           f"wherever `{den}` vanishes")
                break

        # F17 -- name inflation on a conditional statement.
        if (INFLATED.search(d.name) and not QUALIFIED_NAME_TOKEN.search(d.name)
                and (hyps or any(
                b.kind == "instance" and
                re.match(r"([A-Za-z_][\w.']*)", norm(b.type)) and
                re.match(r"([A-Za-z_][\w.']*)", norm(b.type)).group(1).split(".")[-1]
                not in STANDARD_CLASSES
                for b in d.binders))):
            add("F17", f"name claims a closed result but the signature carries "
                       f"{len(hyps)} premise(s)")

        # F6 -- choice on an assumed existence premise.
        # The premise can be consumed in the STATEMENT as well as the proof
        # (`0 < Classical.choose h`), and `\b` keeps `Classical.choose_spec` from
        # matching `choose` -- it is the spec lemma, not an application to a premise.
        for m in re.finditer(rf"Classical\.(choice|choose|arbitrary|some)\b\s+({IDENT})",
                             concl + " " + body):
            if m.group(2).split(".")[0] in {b.name for b in hyps if b.name}:
                add("F6", f"`Classical.{m.group(1)}` applied to premise `{m.group(2)}`")

        # F10/F12 -- vacuous or self-satisfying domain.
        for b in d.binders:
            t = norm(b.type)
            # THE WHOLE TYPE, NOT ITS FIRST TOKEN.  `re.match` anchors at the start only,
            # so `Fin 0 → ℝ` was read as "the empty type" -- and `Fin 0 → ℝ` is not empty,
            # it is a SINGLETON whose one inhabitant is the empty function.  Every one of
            # the twelve findings this produced was a function out of an empty index,
            # several of them theorems named `..._empty_panel_is_junk` whose whole purpose
            # is to record what the quantity does there.  Quantifying over `Fin 0` is
            # vacuous; quantifying over `Fin 0 → ℝ` is quantifying over one point.
            if re.fullmatch(r"(Empty|PEmpty|Fin 0)", t):
                add("F10", f"quantifies over the empty type `{t}`")
            # `{n : ℕ // 0 < n}` ascribes the bound variable, so `\w+\s*//` never
            # matched a real subtype -- only the rarer `{n // p n}` spelling.
            sm = re.match(r"\{[^/]*//\s*(.+)\}$", t)
            if sm:
                # THE PREDICATE, NOT THE BOUND VARIABLE.  `_head_ident` on
                # `{η : ER n // Covers ξ η}` returns `η` -- the binder's own name -- and
                # that was compared against the set of types shown inhabited.  A bound
                # variable is never in that set, so the finding was unconditional, and
                # together with the extractor above it made this family unsatisfiable: no
                # theorem anyone could write would clear it.  What identifies the subtype
                # is the predicate cutting it out.
                base = _head_ident(sm.group(1))
                # AND AN INHABITED SUBTYPE IS NOT LAUNDERING.  This reported the domain
                # either way, differing only in the wording, so proving inhabitation
                # changed the message and not the count.
                if base not in c.inhabited:
                    add("F12", f"domain is the subtype `{_clip(t)}`; "
                               f"no `Nonempty` for it is proved in-corpus")

    if d.kind in ("def", "abbrev"):
        # F8 -- definitional weakening.
        if norm(d.conclusion) == "Prop" and norm(d.body) in ("True", "trivial", "⊤"):
            add("F8", "target property is defined as `True`")
        # F2 -- Prop alias with a theorem-like name and no inhabitant.
        if norm(d.conclusion) == "Prop" and THEOREMISH.search(d.name):
            if d.name.split(".")[-1] not in proved_props:
                add("F2", "Prop named like a theorem, with no proof of it in-corpus")
        # F7 -- conclusion-by-definition.
        #
        # The conjunct must APPLY A NAMED PREDICATE of this corpus whose name is
        # the claim -- `isCalibrated x`, `hasPortability p` -- because that is the
        # shape where the content hides: the definition swallows the claim and a
        # theorem "concluding" it only unfolds.  A conjunct that spells its claim
        # out as an equation or an inequality hides nothing; whoever proves it has
        # proved it, and naming the conjunction does not change that.
        #
        # Keying on the words alone read a FIELD ACCESSOR as a claim: a corpus
        # about calibration mentions `identityCalibrationProfile` in most of its
        # propositions, and every conjunction of equations over one was reported.
        if norm(d.conclusion) == "Prop":
            parts = _top_conjuncts(d.body)
            if len(parts) > 1:
                for p in parts:
                    head = _head_ident(p)
                    if head not in c.prop_aliases:
                        continue
                    # No leading `\b`: the telling word is usually INSIDE a camelCase
                    # identifier (`isCalibrated`, `hasPortability`), where no boundary
                    # precedes it.
                    if re.search(r"(?i)(correct|desired|conclusion|holds|valid|"
                                 r"calibrat|portab|identif|sound|complete)", head):
                        add("F7", f"predicate `{d.name}` has the advertised conclusion "
                                  f"as a conjunct: `{_clip(p)}`")
                        break
        # F13 -- range advertised as canonical.
        # `Finset.range n` IS NOT AN IMAGE.  It is the interval `{0, …, n-1}`, and
        # `\.range\b` matched it, so `∏ j ∈ Finset.range extra, …` -- an ordinary finite
        # product -- counted as a range construction.  What this family is about is
        # `Set.range f`, the image of a function advertised as the canonical copy of
        # something.
        if re.search(r"Set\.range\b|Set\.image\b", d.body) and re.search(
                r"(?i)(canonical|universal|the standard|concrete copy)", d.doc):
            add("F13", "a range/image construction is described as canonical or "
                       "universal with no isomorphism theorem cited")
        # F20 -- semantic shadowing.
        if d.name.split(".")[-1] in STANDARD_PREDICATES:
            add("F20", f"redefines the standard predicate `{d.name}` locally")
        pass

    if d.kind == "structure" or d.kind == "class":
        fields = c.struct_fields.get(d.name.split(".")[-1], [])
        if any(norm(x.type) == "False" for x in fields):
            add("F11", f"`{d.name}` has a field of type `False`: every theorem "
                       f"assuming it is vacuous")

    if d.kind == "axiom":
        add("F24", f"custom axiom `{d.name}` expands the trusted base")

    return f


def _clip(s: str, n: int = 70) -> str:
    s = norm(s)
    return s if len(s) <= n else s[: n - 1] + "…"


def _head_ident(t: str) -> str:
    m = re.match(r"[({\[]*\s*([A-Za-z_][\w.']*)", norm(t))
    return m.group(1).split(".")[-1] if m else ""


def _same_existential(a: str, b: str) -> bool:
    ra, rb = norm(a), norm(b)
    if not ra.startswith("∃") or not rb.startswith("∃"):
        return False
    strip = lambda s: re.sub(r"[a-zA-Z_][\w']*", "·", s)
    return strip(ra) == strip(rb)


def _top_conjuncts(s: str) -> list[str]:
    s = norm(s)
    d = depths(s)
    parts, last = [], 0
    for i, ch in enumerate(s):
        if ch == "∧" and d[i] == 0:
            parts.append(s[last:i])
            last = i + 1
    parts.append(s[last:])
    return [p.strip() for p in parts if p.strip()]


# DIRECTIONAL claims only. `is the ... of`, `represents` and `acts as` describe the
# definition itself ("the drift variance is the variance of the frequency"), and every
# such docstring that happened to contain another corpus name became a finding -- 471 of
# them, none a defect. What family 15 is about is a claim that one object INDUCES or
# TRANSPORTS another, which is a theorem-shaped assertion and needs a theorem.
BRIDGE_VERB = re.compile(
    r"(?i)\b(induces?|induced by|corresponds? to|conjugat\w*|factors? through|"
    r"is realis\w+ by|is realiz\w+ by|implements?)\b")


def check_bridges(c: Corpus) -> list[Finding]:
    """F15 -- prose claims one definition induces another, and no theorem says so.

    Proximity and naming are not a mathematical relationship. When a docstring says
    `compressor` induces `compressionMap`, the bridge is a THEOREM
    (`embed (compressionMap g) = compressor * embed g * compressor⁻¹`); without it the
    two objects sit next to each other and nothing connects them.
    """
    out: list[Finding] = []
    defs = {d.name.split(".")[-1]: d for d in c.decls if d.kind in ("def", "abbrev")}
    # every pair of corpus names that some theorem's STATEMENT mentions together
    bridged: set[tuple[str, str]] = set()
    for d in c.decls:
        if d.kind not in ("theorem", "lemma"):
            continue
        seen = {t.split(".")[-1] for t in re.findall(IDENT, d.header)} & set(defs)
        for a in seen:
            for b in seen:
                if a != b:
                    bridged.add((a, b))
    for name, d in defs.items():
        if not d.doc or not BRIDGE_VERB.search(d.doc):
            continue
        # The verb and the other name must occur in the SAME SENTENCE, or a docstring
        # that says "induces" anywhere pairs with every corpus name it mentions.
        others: set[str] = set()
        for sentence in re.split(r"(?<=[.;])\s+", d.doc):
            if not BRIDGE_VERB.search(sentence):
                continue
            # ONLY BACKTICKED NAMES. Prose words collide with definition names --
            # `and`, `covariance` and `variance` are all corpus definitions AND ordinary
            # English, so scanning bare words made every sentence a finding. This corpus
            # cites code in backticks, and that is the only reliable signal that a word
            # is meant as a reference to a definition.
            quoted = {t.split(".")[-1] for t in re.findall(rf"`({IDENT}(?:\.{IDENT})*)`",
                                                           sentence)}
            others |= (quoted & set(defs)) - {name}
        for other in sorted(others):
            if (name, other) not in bridged and (other, name) not in bridged:
                out.append(Finding("F15", d.file, d.line, d.name,
                                   f"docstring claims a relationship to `{other}`, and "
                                   f"no theorem's statement mentions both; proximity and "
                                   f"naming are not a mathematical relationship"))
                break
    return out


# Files whose custom syntax IS the corpus's mechanism for enumerating unproved
# statements, rather than a way of smuggling one in.
#
# `Meta/Informal.lean` declares `informal_lemma`, `informal_definition`, `TODO`
# and `withdrawn`; `Meta/InformalLint.lean` reports on them. Their design point,
# stated at length in `Informal.lean`'s own module docstring, is that a gap
# pushes a record into an environment extension and ADDS NO CONSTANT -- "not a
# `sorry`, not an axiom, not an opaque constant" -- precisely so that no proof
# can rest on one. That is the opposite of a trust bypass, and it is stricter
# than the PhysLean design it is taken from, which does emit an inert record.
#
# These six findings are the only FATAL ones in the guard, so they gate it
# entirely: `laundering` has been failing on the two files that exist to stop
# the thing it is looking for, and every real FATAL would have arrived into a
# guard already red.
#
# THE EXEMPTION CHECKS ITS OWN PREMISE. It covers only the two
# "custom syntax or elaborator" patterns, never `native_decide`, `unsafe`,
# `opaque` or `@[implemented_by]`; and it lapses the moment an exempted file
# acquires any of those, or an `axiom` or a `sorry`. An exemption that cannot
# expire is indistinguishable from not looking.
# NO FILE IS EXEMPT.  This is empty and stays empty.
#
# It carried two `Descent/Meta/` files that declare and report the gap vocabulary, on the
# argument that a gap is an environment-extension record emitting no constant, so their
# `syntax`/`elab` moves nothing into the trusted base.  That argument is almost certainly
# right, and it is not a thing this guard can check: "emits no constant" is a fact about
# the elaborated environment, and this is a source-text scan.  The exemption was an
# environment-level judgement parked in a text-level tool.
#
# An `elab` runs arbitrary code at elaboration time whoever wrote it.  Reporting the two
# declaration sites costs a reader one glance at a comment; carrying a list that says
# which elaborators are the safe ones costs the guard its meaning.  If the distinction
# is worth drawing it belongs in `validation/code/Check.lean`, which can see whether a
# constant was emitted.
TRUST_BYPASS_EXEMPT: dict[str, str] = {}
_EXEMPTION_VOIDED = re.compile(
    r"\bnative_decide\b|^\s*(?:unsafe|opaque)\s+|@\[implemented_by"
    r"|^\s*axiom\s+|\bsorry\b", re.M)


def check_files(c: Corpus) -> list[Finding]:
    """Whole-file syntax that bypasses trust, and dead concrete constructions."""
    out: list[Finding] = []
    seen_files = {d.file for d in c.decls}
    for rel in sorted(seen_files):
        src = (CORPUS_BASE / rel).read_text(encoding="utf-8", errors="replace")  # abs rel is a no-op
        m = mask(src)
        exempt = (rel in TRUST_BYPASS_EXEMPT
                  and not _EXEMPTION_VOIDED.search(m))
        for pat, fam, msg in [
            (r"\bnative_decide\b", "F24", "`native_decide` moves the compiler into the "
                                          "trusted base"),
            (r"^\s*(unsafe|opaque)\s+", "F24", "unsafe/opaque declaration"),
            # A TACTIC macro is exempt here for the same reason it is exempt from
            # the `identifications` screen: it names a tactic call, leaves every
            # statement untouched, and its proof still closes through the kernel,
            # so it moves nothing into the trusted base.  `elab` and `macro_rules`
            # run code at elaboration time and a term macro rewrites the statement
            # a reader reads; those stay reported.
            # `syntax` IS NOT HERE, and the two additions below are why.
            #
            # A `syntax` declaration declares GRAMMAR.  It has no elaboration behaviour at
            # all: parsing is not elaboration, and a parse rule on its own cannot put
            # anything into the trusted base.  Flagging it reported six findings in
            # `Meta/Informal.lean` and `Meta/InformalLint.lean` that were parse rules.
            #
            # What those files actually declare is `@[command_elab todoCmd] def elabTODO`,
            # and the attribute form was INVISIBLE here -- including one in
            # `Meta/Semiformal.lean` that no exemption ever covered and that this guard
            # never reported.  A screen that reports the grammar and misses the elaborator
            # is wrong in both directions at once.
            #
            # The carve-out is the one already written for `tactic`, extended to `command`
            # for the same reason: a command elaborator introduces a top-level command and
            # cannot change what any theorem SAYS, which is the risk `F24` names.  What it
            # puts in the environment is visible to `validation/code/Check.lean`, which
            # walks the real axiom closure -- the division of labour this file's own header
            # states.  A `term` elaborator rewrites the statement a reader reads and stays
            # reported, in both its bare and its attribute spelling.
            (r"^\s*macro\b(?![^\n]*:\s*(?:tactic|command)\s*=>)", "F24",
             "custom syntax or elaborator"),
            (r"^\s*(elab|macro_rules|elab_rules)\b(?![^\n]*:\s*(?:tactic|command)\s*=>)",
             "F24", "custom syntax or elaborator"),
            (r"@\[(?:builtin_)?(?:term_elab|app_unexpander)\b", "F24",
             "term elaborator attached by attribute"),
            (r"@\[implemented_by", "F24", "compiled implementation substituted for the "
                                          "definition"),
            (r"#print axioms", "F24_INFO", "handled by the F18 pass below"),
        ]:
            for mo in re.finditer(pat, m, re.M):
                if fam == "F24_INFO":
                    continue
                if exempt and msg == "custom syntax or elaborator":
                    continue
                out.append(Finding(fam, rel, m.count("\n", 0, mo.start()) + 1,
                                   "<file>", msg))
    # F18 -- `#print axioms P` where `P` is a Prop DEFINITION, not a proof of it.
    # That checks how the proposition was CONSTRUCTED; it says nothing about whether
    # anything proves it, while reading exactly like a clean audit of a theorem.
    for rel in sorted({d.file for d in c.decls}):
        src = (CORPUS_BASE / rel).read_text(encoding="utf-8", errors="replace")
        for mo in re.finditer(rf"#print\s+axioms\s+({IDENT}(?:\.{IDENT})*)", mask(src)):
            target = mo.group(1).split(".")[-1]
            if target in c.prop_aliases:
                out.append(Finding("F18", rel, src.count("\n", 0, mo.start()) + 1,
                                   target,
                                   f"`#print axioms {mo.group(1)}` names a Prop "
                                   f"DEFINITION; it reports how the statement was built, "
                                   f"not that anything proves it"))

    # F14 IS DELIBERATELY NOT IMPLEMENTED, and this comment is the reason.
    #
    # The family is real: a corpus can build a concrete object while its headline still
    # quantifies over an abstract parameter, leaving the dependency graph open. But
    # deciding it requires knowing which theorem is the headline and whether the
    # concrete object was meant to instantiate it -- neither is in the source text.
    #
    # Every mechanical proxy reduces to a REFERENCE COUNT, and a reference count cannot
    # tell a dead end from a definition that is unreferenced BY DESIGN:
    #   * `X.witness` exists precisely so that a class is inhabited. Nothing consumes it
    #     and nothing should; the F4 scan reads it, not another theorem.
    #   * `targetCorrectionCurvature` names which functions a section is ABOUT, and the
    #     section's claim that its weighting is forced rather than stipulated is false
    #     without it.
    # the `identifications` guard in check.py records two separate occasions on which reference
    # counting deleted correct work, neither of which broke the build. A family whose
    # every hit invites that deletion is worse than no family, so it is not shipped.
    return out


# --------------------------------------------------------------------------------------
# Report
# --------------------------------------------------------------------------------------


def run_laundering(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("paths", nargs="*", help="files to check (default: all of proofs/)")
    ap.add_argument("--json", metavar="PATH")
    ap.add_argument("--summary", action="store_true",
                    help="counts per family and per file only")
    ap.add_argument("--family", action="append",
                    help="restrict to one family, e.g. --family F1")
    args = ap.parse_args(argv)

    if args.paths:
        files = [Path(p).resolve() for p in args.paths]
    else:
        files = lean_sources(CORPUS)
    files = [f for f in files if f.is_file()]

    corpus = build_corpus(files)
    findings = analyse(corpus)

    # No severity filter.  There is no view of this guard that shows less than all of it.
    if args.family:
        findings = [f for f in findings if f.family in set(args.family)]

    # ONE FINDING PER FACT.  `sharedCorrectionConsensus_no_curvature_is_junk` and
    # `jointDensity_indep_of_cover` were each reported twice, identically, because the same
    # binder is reached by two paths.  A count that double-reports is a count nobody can
    # act on: it says two things are wrong where one is.
    findings = list({(f.family, f.file, f.line, f.decl, f.detail): f
                     for f in findings}.values())
    findings.sort(key=lambda f: (SEVERITY_ORDER[f.severity], f.family, f.file, f.line))

    by_family = defaultdict(int)
    by_file = defaultdict(int)
    for f in findings:
        by_family[f.family] += 1
        by_file[f.file] += 1

    print(f"scanned {len(files)} .lean files, "
          f"{sum(1 for d in corpus.decls if d.kind in ('theorem','lemma'))} theorems, "
          f"{len(corpus.struct_fields)} structures "
          f"({len(corpus.prop_structs)} carrying Props)")
    print()
    for sev in (FATAL, CONDITIONAL, FIDELITY):
        fams = sorted(x for x in by_family if FAMILY_SEVERITY[x] == sev)
        if not fams:
            continue
        print(f"{sev}")
        for fam in fams:
            print(f"  {by_family[fam]:6}  {fam:4} {FAMILY_TITLE[fam]}")
    print()
    print(f"TOTAL {len(findings)}")

    if not args.summary:
        print()
        cur = None
        for f in findings:
            if f.family != cur:
                cur = f.family
                print(f"\n=== {f.family} [{f.severity}] {FAMILY_TITLE[f.family]} "
                      f"({by_family[f.family]}) ===")
            print(f"{f.file}:{f.line}  {f.decl}\n      {f.detail}")

    if args.json:
        Path(args.json).write_text(json.dumps(
            [dict(family=f.family, severity=f.severity, file=f.file, line=f.line,
                  decl=f.decl, detail=f.detail) for f in findings], indent=1))

    n_gated = sum(1 for f in findings if f.severity in EXIT_ON)
    if n_gated:
        print(f"\nFAIL: {n_gated} finding(s).  Every severity gates and no flag changes "
              f"that.")
    else:
        print("\nPASS: no findings at any severity.")
    return 1 if n_gated else 0


# ======================================================================================
# GUARD: regimes -- no external theorem packaging in production structures
#
# Was `validation/code/check.py`.
#
# Model data and genuine algebraic laws may live in structures.  A scientific or
# analytic conclusion may not be accepted from a caller and then re-exported by
# field projection.  This check guards the concrete anti-patterns removed from the
# Descent corpus and rejects bare `Prop` switches, which carry no mathematical
# content at all.
#
# Lean compilation remains the proof check.  This guard is an architectural check
# that prevents the old `AssumedTheorem.result` interface from returning under a
# new edit.
# ======================================================================================

REGIMES_SOURCE_ROOT = CORPUS / "Descent"

# Names used by the historical result-as-data interfaces.  Exact matching keeps
# legitimate algebraic fields such as ``stationary`` and ``mass_sum`` legal.
REGIMES_FORBIDDEN_FIELDS = {
    "accuracy",
    "barrier",
    "complete",
    "completeness",
    "freezing",
    "identification",
    "limit_adequate",
    "maximalSpectrum",
    "recovered_eq",
    "renormalization",
    "transferThreshold",
}

# WHY THIS LIST EXISTS, AND WHY DELETING AN ENTRY IS NOT A FIX.
#
# Every name here was a structure whose Prop-valued fields CONTAINED THE DESIRED
# CONCLUSION, paired with a theorem that reached that conclusion by `rw` or `exact` on one
# of those fields. `kernelTrivial_of_no_section` applied `D.dichotomy`;
# `assumedCeiling_collapses_to_support_wall` rewrote with `C.characterization`. The
# statement's content was the assumption, so it was not a theorem of this corpus.
#
# Naming such a structure `Assumed...` does not repair it. That is why
# `AssumedDeploymentCeiling` and `AssumedMembraneThreshold` are on this list despite having
# been honestly named: an honest name on a restatement still yields a restatement.
#
# THE ENTRIES ARE NOT STALE CRUFT. A name here means the structure was deleted deliberately
# and must not return. If the `regimes` guard fails on one of these, something reintroduced it,
# and the repair is to remove the reintroduction — NOT to prune the list. Pruning restores
# the blindness rather than fixing the break, which is the failure mode every guard in this
# corpus has eventually suffered.
#
# The honest alternative, when the underlying input is real, is the one used in
# `Descent.BundleRigidity.DeploymentCeiling`: state the input as a TYPED HYPOTHESIS of
# the theorem that needs it, so it appears in the signature and cannot be forgotten, and
# leave the unproved direction as a named gap with no theorem attached. A used hypothesis
# is an argument of the theorem that needs it; an unused one in a record is decoration.
REGIMES_FORBIDDEN_STRUCTURES = {
    "AtomicCramerFailure",
    "AssumedDeploymentCeiling",
    "AssumedMembraneThreshold",
    "BundleDichotomy",
    "ChaosSpectroscopy",
    "CycleDeterminacy",
    "FittedSelectionLaw",
    "FreezingTransition",
    "GaussianLiabilityRegime",
    "GenotypeChaosLimits",
    "InfiniteIslandLimit",
    "LDBandIntegralIdentification",
    "LinearArchitectureCertificateAssumptions",
    "MarkovModulatedChain",
    "MeanAbsoluteEffectCertificateAssumptions",
    "MellinProfile",
    "MomentReading",
    "ObservableDegradation",
    "ObservableTower",
    "PGSBenDavidCertificate",
    "PowerAgreement",
    "RecoveryAttenuation",
    "ScaleSequence",
    "SubthresholdPCCertificate",
    "TowerRigidity",
    "TransferThreshold",
    "TwoPointIdentification",
    "VertexWeightCompleteness",
}

REGIMES_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
REGIMES_STRUCTURE = re.compile(
    r"^structure\s+([A-Za-z_][A-Za-z0-9_']*)[^\n]*\swhere\n"
    r"((?:(?:[ \t]+[^\n]*)?\n)*)",
    re.M,
)
REGIMES_FIELD = re.compile(r"^[ \t]+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^\n]+)$", re.M)


def run_regimes() -> int:
    violations = []
    for path in lean_sources(REGIMES_SOURCE_ROOT):
        text = REGIMES_BLOCK_COMMENT.sub("", read_source(path))
        for match in REGIMES_STRUCTURE.finditer(text):
            structure = match.group(1)
            rel = path.relative_to(CORPUS_BASE)
            if structure in REGIMES_FORBIDDEN_STRUCTURES:
                violations.append(f"{rel}: forbidden result carrier {structure}")
            for field, type_text in REGIMES_FIELD.findall(match.group(2)):
                if field in REGIMES_FORBIDDEN_FIELDS:
                    violations.append(
                        f"{rel}: {structure}.{field} packages an advertised result"
                    )
                if type_text.strip() == "Prop":
                    violations.append(
                        f"{rel}: {structure}.{field} is a content-free bare Prop switch"
                    )

    if violations:
        print("\n".join(violations))
        return 1
    print("NO_EXTERNAL_THEOREM_PARAMETERS\tOK")
    return 0


# ======================================================================================
# GUARD: closure -- every Descent module is in the root import closure
#
# Was `validation/code/check.py`.
#
# `lake build Descent` can only validate modules reachable from
# `Descent.lean`.  This guard compares that transitive closure with the
# source tree, so adding an unimported module cannot produce a false-green root
# build.
# ======================================================================================

CLOSURE_ROOT = CORPUS / "Descent.lean"
CLOSURE_IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")


def closure_module_path(module):
    return CORPUS / (module.replace(".", "/") + ".lean")


def closure_direct_imports(path):
    imports = set()
    for line in read_source(path).splitlines():
        match = CLOSURE_IMPORT.match(line)
        if match is not None:
            imports.add(match.group(1))
    return imports


def closure_corpus_sources():
    modules = {
        path
        for path in lean_sources(CORPUS / "Descent")
        if not any(part.startswith("._") for part in path.parts)
    }
    return {CLOSURE_ROOT, *modules}


def closure_root_closure():
    closure = {CLOSURE_ROOT}
    pending = list(closure_direct_imports(CLOSURE_ROOT))
    seen_modules = set()
    while pending:
        module = pending.pop()
        if module in seen_modules:
            continue
        seen_modules.add(module)
        path = closure_module_path(module)
        if not path.is_file():
            continue
        closure.add(path)
        pending.extend(closure_direct_imports(path) - seen_modules)
    return closure


def run_closure() -> int:
    sources = closure_corpus_sources()
    closure = closure_root_closure()
    absent = sorted(path.relative_to(CORPUS_BASE) for path in sources - closure)
    print(f"CORPUS_SOURCES\t{len(sources)}")
    print(f"ROOT_CLOSURE\t{len(closure & sources)}")
    for path in absent:
        print(f"MODULE_ABSENT\t{path}")
    if absent:
        return 1
    return 0


# ======================================================================================
# GUARD: wiring -- is a result wired into the biology, or only adjacent to it
#
# Was `validation/code/check.py`.  Its full header is reproduced
# immediately below.
# ======================================================================================

#
# The condition this enforces is the team lead's, and it is deliberately not a
# style rule:
#
#     A result is wired in when removing it breaks something biological.
#
# That is testable. For a Lean corpus it means: some module outside the upstream
# arc must *reference a declaration* of the arc module. Import edges alone do not
# count -- a module can import another and use nothing from it, and the import
# graph then records an intention rather than a dependency. Conversely a shared
# vocabulary does not count either: two modules can both talk about allele
# frequencies while neither depends on the other, which is the "two corpora that
# agree" failure this script exists to detect.
#
# WHAT IT MEASURES
#
# For every module in ARC, collect its declared names, then count references to
# those names from modules outside ARC, with docstrings and comments stripped so
# that a mention in prose is not scored as a dependency. A module with zero
# genuine cross-boundary references is UNWIRED however many files import it.
#
# WHY THE COMMENT-STRIPPING MATTERS
#
# The corpus's house style cites sibling theorems in docstrings extensively. Those
# citations are how a reader navigates, and they are exactly what makes an
# unwired module look wired. Stripping them is the whole point of the measurement.
#
# KNOWN PARSE HAZARD, HANDLED
#
# Lean keywords can follow a `def`-like token in constructs this regex does not
# model, which yields phantom declarations named `in`, `at`, `with`. Those match
# everywhere and manufacture false dependencies. Short and reserved names are
# therefore dropped; an earlier version of this script reported six spurious
# dependents of HiddenConeAmbiguity, all of them the keyword `in`.
#
# Run:  python3 validation/code/check.py
#       python3 validation/code/check.py --json

# The upstream arc: modules whose content is mathematics about coordinate laws,
# designs and limits rather than about genotypes, phenotypes or study design.
WIRING_ARC = {
    # Added with the horizon/circulation/transplantation/lumping results. Each is
    # Mathlib-only mathematics with a named biological consumer, and each is listed
    # here so that the guard -- not a docstring -- is what holds the consumer in place.
    "HorizonCurve",
    "CirculationDefect",
    "TransplantationStability",
    "LumpedRateBlindness",
    "MarkedBreakoutUniversality",
    "XiFromMarkedBreakouts",
    "TrafficInvariantSeparation",
    "Condensation",
    "StandardizedGenotypeMoments",
    "CumulantBlindness",
    "EpistaticChaos",
    "HiddenConeAmbiguity",
    "JetBarrier",
    "LatentMechanismCollapse",
    "LocalToGlobalCoherence",
    "ObservationalCeiling",
    "PolygenicSpectroscopy",
    "BlindnessRegistry",
}

# Names too short or too generic to attribute; `in`/`at`/`with` are Lean
# keywords that the declaration regex can pick up in constructs it does not
# model, and they match in every file.
WIRING_RESERVED = {
    "in", "at", "with", "fun", "by", "do", "then", "else", "from",
    "have", "show", "let", "this", "where", "deriving", "extends",
}
WIRING_MIN_NAME_LEN = 4

WIRING_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|structure|class|abbrev|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)",
    re.M,
)


def wiring_strip_comments(text: str) -> str:
    """Remove Lean block comments/docstrings and line comments.

    Block comments do not nest in this corpus in practice, and a non-greedy
    match is correct for that case.
    """
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def wiring_load(root: str) -> dict[str, str]:
    """Load exactly the canonical corpus sources used by every other guard."""
    return {str(path): read_source(path) for path in lean_sources(Path(root))}


def wiring_stem(path: str) -> str:
    return os.path.basename(path)[:-5]


def wiring_declarations(text: str) -> set[str]:
    names = set()
    for m in WIRING_DECL.finditer(text):
        n = m.group(1)
        if n in WIRING_RESERVED or len(n) < WIRING_MIN_NAME_LEN:
            continue
        names.add(n)
    return names


def wiring_analyze(files: dict[str, str]) -> dict:
    decls = {}
    for p, t in files.items():
        s = wiring_stem(p)
        if s in WIRING_ARC:
            decls[s] = wiring_declarations(t)

    bodies = {}
    for p, t in files.items():
        s = wiring_stem(p)
        if s not in WIRING_ARC:
            bodies[s] = wiring_strip_comments(t)

    report = {}
    for s, names in decls.items():
        if not names:
            report[s] = {"declarations": 0, "dependents": {}, "wired": False}
            continue
        # One alternation pass per consumer beats len(names) passes per consumer.
        pattern = re.compile(
            r"(?<![A-Za-z0-9_.'])(" + "|".join(sorted(map(re.escape, names), key=len, reverse=True)) + r")(?![A-Za-z0-9_'])"
        )
        dependents: dict[str, list[str]] = {}
        for consumer, body in bodies.items():
            hits = sorted(set(pattern.findall(body)))
            if hits:
                dependents[consumer] = hits
        report[s] = {
            "declarations": len(names),
            "dependents": dependents,
            "wired": bool(dependents),
        }
    return report


def run_wiring(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true", help="emit machine-readable output")
    ap.add_argument(
        "--require",
        nargs="*",
        default=[],
        help="modules that MUST be wired; exit nonzero if any is not",
    )
    args = ap.parse_args(argv)

    corpus_dir = str(CORPUS / "Descent")
    if not os.path.isdir(corpus_dir):
        print(f"cannot find {corpus_dir}", file=sys.stderr)
        return 2

    files = wiring_load(corpus_dir)
    report = wiring_analyze(files)

    if args.json:
        print(json.dumps(report, indent=1, sort_keys=True))
    else:
        total_decls = sum(r["declarations"] for r in report.values())
        total_edges = sum(
            len(hits) for r in report.values() for hits in r["dependents"].values()
        )
        print(f"upstream-arc modules:      {len(report)}")
        print(f"upstream-arc declarations: {total_decls}")
        print(f"cross-boundary references: {total_edges}")
        print()
        width = max((len(s) for s in report), default=0)
        for s in sorted(report):
            r = report[s]
            mark = "WIRED  " if r["wired"] else "UNWIRED"
            detail = ""
            if r["dependents"]:
                detail = "  <- " + ", ".join(
                    f"{k}({','.join(v)})" for k, v in sorted(r["dependents"].items())
                )
            print(f"  {mark} {s:{width}s} {r['declarations']:4d} decls{detail}")

    failures = [m for m in args.require if not report.get(m, {}).get("wired")]
    if failures:
        print(file=sys.stderr)
        print(
            "WIRING CONTRACT VIOLATED: these modules have no biological dependent, "
            "so deleting them would break nothing outside the arc:",
            file=sys.stderr,
        )
        for m in failures:
            print(f"  - {m}", file=sys.stderr)
        return 1
    return 0


# ======================================================================================
# GUARD: field-proofs -- theorems whose whole proof is a field projection
#
# Was `validation/code/check.py`.  Its full header, including the calibration
# record and the known false-positive modes, is reproduced immediately below.
#
# DIAGNOSTIC, NOT A GATE.  It returns 0 whatever it finds, and it is not in the
# default set: it shells out to git and reads `origin/main`.
# ======================================================================================

# Find theorems whose ENTIRE proof is a structure-field projection, on origin/main.
#
# This is the review's defect in its mechanically checkable form, and the standard is
# the coordinator's: if replacing the proof body with the field yields the same theorem,
# there is no theorem. Such a proof states nothing -- the conclusion IS the hypothesis.
#
# Precise by construction: no prose parsing, no backtick guessing. A theorem qualifies
# only if its proof body reduces to `X.f` / `exact X.f` / `X.f args` where `f` is a
# declared field of a structure in this corpus.
#
# Runs against origin/main, never the worktree. THIS IS NOT A STYLE POINT. On 2026-08-03
# three agents in one day reported a structure "removed from the corpus" after grepping a
# worktree that carried another agent's UNCOMMITTED deletions. A worktree grep and an origin
# grep answer different questions, and only the second answers "is this in the corpus".
#
# CALIBRATION AND KNOWN LIMITS -- read before quoting a number.
#
#   Calibrated against ground truth: it independently finds the `GenotypeChaosLimits`
#   consumers in EpistaticChaos that an external review named, which is the evidence that
#   it detects the real thing.
#
#   It also found sites the review did not name. Two verified by hand:
#     * PortabilityBounds.FittedSelectionLaw.magnitude_pinned -- the purest instance in the
#       corpus. The field `fits` IS the theorem's statement; the proof is `F.fits fst hlo hhi`.
#     * EpistaticChaos.no_moment_matching_calibration_off_temperedness := CD.divergence_phase.
#
#   FALSE POSITIVES REMAIN and the raw count is NOT a measurement. Two modes, one fixed and
#   one open:
#     FIXED  -- taking the first `:=` in the declaration text picked up field names out of
#               HYPOTHESIS binders (`(h : (let mu := dgp.jointMeasure) = ...)`), reporting a
#               hypothesis as a proof. Now takes the last `:=`.
#     OPEN   -- line-joining can absorb a following tactic or the next declaration, so
#               entries whose printed proof ends in `linarith`, `simpa using h`,
#               `positivity`, or `open ... in` have MORE proof than the projection and are
#               probably not this defect. Inspect every hit before acting on it.
#
#   NOT EVERY HIT IS A DEFECT. An accessor forwarding a genuine model invariant can be
#   plumbing. The retired `Identification.formula_eq_observable := i.derivation` pattern,
#   however, is now forbidden: it accepted the desired scientific conclusion from a caller.
#   The defect is a theorem whose name and statement claim a result that a field already
#   asserts.
#
#   The standard to apply, which no tool can apply for you: if replacing the proof body with
#   the field yields the same theorem, there is no theorem.

def run_field_proofs() -> int:
    def sh(*a): return subprocess.run(a, capture_output=True, text=True).stdout
    REF = "origin/main"
    files = [f for f in sh("git","ls-tree","-r","--name-only",REF).splitlines()
             if f.endswith(".lean") and f.startswith("proofs/")]
    srcs = {f: sh("git","show",f"{REF}:{f}") for f in files}

    # --- structure fields declared in the corpus ---
    fields = collections.defaultdict(set)
    for f, s in srcs.items():
        cur = None
        for l in s.split("\n"):
            m = re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(structure|class)\s+([A-Za-z_][\w.\']*)', l)
            if m:
                cur = m.group(2); continue
            if cur:
                if re.match(r'^\S', l) and l.strip():
                    cur = None; continue
                fm = re.match(r"\s{2,}([a-z_][\w']*)\s*:", l)
                if fm and not l.strip().startswith(("--","/-","|")):
                    fields[cur].add(fm.group(1))
    allfields = set()
    for v in fields.values(): allfields |= v

    # --- theorems and their proof bodies ---
    THM = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(theorem|lemma)\s+([A-Za-z_][\w.\']*)')
    hits = []
    for f, s in srcs.items():
        lines = s.split("\n")
        for i, l in enumerate(lines):
            m = THM.match(l)
            if not m: continue
            # gather until the next top-level declaration
            body = []
            j = i
            while j < len(lines):
                j += 1
                if j >= len(lines): break
                nl = lines[j]
                if THM.match(nl) or re.match(r'^\s*(?:noncomputable\s+)?(def|structure|class|inductive|instance|end|namespace|/-)', nl):
                    break
                body.append(nl)
            text = "\n".join(body)
            # proof body after := or `by`
            # Take the LAST top-level `:=`, not the first: the first is often inside a
            # hypothesis binder (`(h : (let mu := ...) = ...)`), which produced two false
            # positives -- a field name lifted out of a HYPOTHESIS and reported as a proof.
            idx = text.rfind(':=')
            if idx < 0: continue
            proof = re.sub(r'--.*', '', text[idx+2:]).strip()
            p = re.sub(r'^by\s+', '', proof).strip()
            p = re.sub(r'^exact\s+', '', p).strip()
            # The WHOLE proof must be the projection. A multi-step tactic block is not this
            # defect, however many `X.field` terms appear inside it.
            p = ' '.join(x.strip() for x in p.split('\n') if x.strip())
            fm = re.fullmatch(r'([A-Za-z_][\w.\']*)\.([a-z_][\w\']*)((?:\s+[\w.\'()\u25b8\u2190:\u211d\-]+)*)', p)
            if fm and fm.group(2) in allfields:
                owners = [st for st, fs in fields.items() if fm.group(2) in fs]
                hits.append((f, i+1, m.group(2), p[:70], owners[:3]))

    print(f"scanned {len(files)} .lean files on {REF}")
    print(f"structures with fields: {len(fields)}   distinct field names: {len(allfields)}")
    print(f"THEOREMS WHOSE WHOLE PROOF IS A FIELD PROJECTION: {len(hits)}\n")
    by = collections.Counter(h[0].replace("Descent/","") for h in hits)
    for f,c in by.most_common(): print(f"  {c:3}  {f}")
    print()
    for f,ln,name,p,ow in sorted(hits, key=lambda r:(r[0],r[1])):
        print(f"{f.replace('Descent/','')}:{ln}")
        print(f"    theorem {name}")
        print(f"    proof := {p}      [field of {', '.join(ow)}]")
    return 0


# ======================================================================================
# GUARD: duplication -- one piece of mathematics, or one piece of text, written twice
#
# The `identifications` guard already screens DEFINITION BODIES: two `def`s whose
# bodies are alpha-equivalent and which nothing ties together.  That screen sees
# `def`s and nothing else, and the corpus is mostly not `def`s.  Three duplication
# shapes were therefore invisible to every guard here:
#
#   statements   two THEOREMS whose statements are the same proposition under two
#                names.  This is the definition case's exact analogue and it is
#                worse, because a theorem's content is entirely its statement:
#                the second name adds no mathematics, it adds a second thing that
#                must be kept in step by hand, and a reader who finds one has no
#                way to know the other exists.
#   proofs       two theorems with DIFFERENT statements and a character-identical
#                proof script.  A repeated script is a lemma that has not been
#                named: the argument is being re-run rather than applied, so a
#                repair to the argument reaches one site and not the other.
#   clones       any run of repeated source lines, anywhere -- inside a structure,
#                inside a `variable` block, inside a proof, across files.  This is
#                the catch-all: it needs no parse and so it catches the copy-paste
#                the two structural screens above cannot name.
#
# WHY THREE AND NOT ONE.  They fail differently.  A duplicate statement is a
# naming defect and the fix is deletion; a duplicate proof is a missing
# abstraction and the fix is a lemma; a clone is neither -- it is text, and the
# fix is whatever the text turns out to be.  Collapsing them into one number
# would report the count that matters least.
#
# WHAT IS NOT REPORTED, and why.  A tie is credit here exactly as it is in the
# duplicate-body screen: if one member's PROOF cites another member by name, the
# two are related by a compile-checked arc and a divergence between them is a
# build error rather than a silent drift.  That is the outcome these screens
# exist to produce, so producing it is not a finding.


# A clone is CLONE_WINDOW or more repeated lines carrying at least CLONE_MIN_CHARS
# of text.  Both thresholds exist to keep the screen off Lean's unavoidable
# repetition: `  intro h`, `  simp`, `  ring` recur everywhere and three of them
# in a row is idiom, not copy-paste.  Eight lines that agree to the character are
# not idiom.
CLONE_WINDOW = 8
CLONE_MIN_CHARS = 160

# A SHORTER run counts when it happens MORE often.  Eight lines twice and five
# lines four times are the same defect with the copying spread differently, and
# the first threshold alone reports one and hides the other.  Five lines repeated
# three times is the second bar.
CLONE_SHORT_WINDOW = 5
CLONE_SHORT_MIN_CHARS = 100
CLONE_SHORT_MIN_OCCURRENCES = 3

# Field assignments inside a structure instance: `fieldName := value`.  Whether a
# repeated block of these is shareable depends on the two instances' TYPES, which
# is what `dup_same_result_type` asks.
CLONE_FIELD_LINE = re.compile(r"^[A-Za-z_][\w'À-ɏͰ-Ͽ]*\s*:=")

# Lines that repeat across every module by construction and say nothing about
# duplication of MATHEMATICS.  Leaving them in the stream lets a file's import
# block and namespace scaffolding pair with any other file's.
CLONE_BOILERPLATE = re.compile(
    r"^(?:import|open|namespace|end|section|set_option|universe|attribute)\b")

DUP_IDENT = re.compile(r"[^\W\d][\w'!?₀-₉]*", re.UNICODE)

# A proof shorter than this is idiom rather than an argument: `rfl`, `by simp`,
# `by norm_num [foo]`, `⟨h, h'⟩`.  Two theorems both proved by `by simp` is not a
# missing lemma, and reporting it is how a screen teaches people to skim.
#
# The floor was 15 tokens, which is a token count standing in for "is this an
# argument or a reflex".  Ten tokens plus a tactic that is not one of the closers
# below asks that question directly: `unfold f; rw [h]; linarith` is an argument
# at twelve tokens and was invisible, while `simp [a, b, c, d, e, f, g]` is a
# reflex at fifteen and was reported.
DUP_PROOF_MIN_TOKENS = 10

# A proof this short that invokes one of the corpus's own theorems is an
# APPLICATION of an already-named lemma, not an unnamed argument two theorems are
# secretly sharing.  The screen's remedy is "name the repeated script and apply
# it"; a script that has already done that must not be reported again, or every
# successful factoring leaves its two call sites behind as a fresh finding.
DUP_APPLICATION_MAX_TOKENS = 14

# Tactics that finish a goal by search rather than by an argument someone chose.
# A proof made only of these is idiom however long its lemma list runs.
DUP_CLOSING_TACTICS = {
    "simp", "simpa", "norm_num", "rfl", "decide", "ring", "ring_nf", "omega",
    "positivity", "linarith", "nlinarith", "trivial", "aesop", "field_simp",
    "bound", "gcongr", "fin_cases", "constructor", "exact", "assumption",
}


def dup_alpha(text: str, bound: set) -> str:
    """`text` with the declaration's own binder names renamed by order of first use.

    Order of USE, not of declaration, so `(m Ne : ℕ)` and `(Ne m : ℕ)` over the
    same formula normalise together -- the same rule the duplicate-body screen in
    `identifications` uses, and for the same reason.
    """
    seen: dict[str, str] = {}

    def rename(m):
        w = m.group(0)
        if w in bound:
            seen.setdefault(w, "V%d" % (len(seen) + 1))
            return seen[w]
        return w

    return norm(DUP_IDENT.sub(rename, text))


def dup_statement_key(d: Decl) -> str:
    """The proposition a theorem states, independent of its binder names.

    Section `variable` binders are included only when the header actually
    mentions them.  `parse_file` attaches EVERY `variable` declared earlier in the
    file, used or not, so keying on all of them would make two identical theorems
    in one file look different the moment an unrelated `variable` line was added
    between them -- and make two identical theorems in different files look
    different always.
    """
    used = set(DUP_IDENT.findall(d.header))
    context = sorted(
        f"({b.name} : {norm(b.type)})"
        for b in d.binders
        if b.inherited and b.name and b.name in used
    )
    bound = {b.name for b in d.binders if b.name}
    return dup_alpha(" ".join(context) + " " + d.header, bound)


def dup_substantive(key: str, corpus_names: frozenset) -> bool:
    """Whether a normalised statement says enough to be worth pairing on.

    `∀ x, x = x` and `0 ≤ n` are true of everything and coincide across unrelated
    modules; the same screen in `identifications` requires a constant or a named
    function for exactly this reason.

    The test used to be "thirty characters long, and containing some identifier of
    three letters or more".  Both halves were wrong in the same direction: length
    is not aboutness, so `fstFromTau V1 0 = 0` -- nineteen characters naming a
    corpus definition -- was dropped, while any statement mentioning `Finset` or
    `Real` reached the bar without saying anything about this corpus.  What makes
    a statement THIS corpus's is that it names something this corpus defines.

    Asked by tokenising the statement and looking each token up, not by searching
    the statement for each of five thousand names in turn: the second is the same
    question and it ran twenty million regex searches to answer it, which cost
    this guard the seconds-not-minutes property its header promises.
    """
    return any(w in corpus_names for w in DUP_IDENT.findall(key))


@functools.lru_cache(maxsize=1)
def dup_corpus_names() -> frozenset:
    """Every name the corpus itself defines, for asking whether text is about it.

    Structure and class FIELDS count.  They are named by this corpus and carry its
    meaning as much as its theorems do -- a repeated block of field declarations is
    the corpus repeating itself -- and a set built from declaration names alone
    would have made the planted structure clone in the calibration invisible.
    """
    names = {d.name.split(".")[-1] for d in dup_lean_decls()
             if d.name and len(d.name.split(".")[-1]) >= 3}
    # `FIELD_RE` is anchored with `^` and carries no `re.M`, so it matches a LINE
    # and not a file; running it over whole sources finds only a first line that
    # happens to be a field, which is none of them.
    for f in lean_sources(CORPUS):
        for line in mask(read_source(f)).split("\n"):
            m = FIELD_RE.match(line)
            if m and len(m.group(1)) >= 3:
                names.add(m.group(1))
    return frozenset(names)


def dup_corpus_theorems() -> frozenset:
    """Names of the corpus's own theorems -- the things a proof can APPLY.

    Separate from `dup_corpus_names` because the two questions differ: a
    definition's name in a proof (`unfold shrinkage`) says what the proof is
    about, while a theorem's name says which already-named step it is invoking.
    Only the second answers "is the shared content already a lemma?".
    """
    return frozenset(d.name.split(".")[-1] for d in dup_lean_decls()
                     if d.name and d.kind in ("theorem", "lemma")
                     and len(d.name.split(".")[-1]) >= 3)


def dup_decl_index() -> dict:
    """file -> ascending `(start_line, Decl)`, for asking which declaration owns a line."""
    index: dict[str, list] = defaultdict(list)
    for d in dup_lean_decls():
        index[d.file].append((d.line, d))
    for rel in index:
        index[rel].sort(key=lambda p: p[0])
    return index


def dup_decl_at(index: dict, rel: str, line: int):
    """The declaration containing `line`, or `None` above the file's first one."""
    rows = index.get(rel) or index.get(os.path.join("proofs", rel), [])
    found = None
    for start, d in rows:
        if start <= line:
            found = d
        else:
            break
    return found


def dup_same_result_type(a, b) -> bool:
    """Whether two declarations state their result at the same type.

    Two structure instances at DIFFERENT types cannot share a field block: the
    fields have different types there, so no definition returns both.  The copy is
    forced by Lean rather than chosen by the author, and reporting it asks for
    something that cannot be written.  At the SAME type it can be written -- that
    is the case this corpus factored into `singleLocusGenerationalWitness` -- so
    the report stands.
    """
    if a is None or b is None:
        return True
    return norm(a.conclusion) == norm(b.conclusion)


def dup_lean_decls() -> list:
    """Every parsed declaration in the corpus, from the one file walk."""
    decls = []
    for f in lean_sources(CORPUS):
        d, _ = parse_file(f)
        decls.extend(d)
    return decls


def dup_cites(a: Decl, b: Decl) -> bool:
    """Whether either declaration's proof names the other: a compile-checked tie."""
    if not a.name or not b.name:
        return False
    return (re.search(r"\b" + re.escape(b.name) + r"\b", a.body) is not None or
            re.search(r"\b" + re.escape(a.name) + r"\b", b.body) is not None)


def dup_untied(members: list) -> list:
    """Members left once everything tied to an earlier member is dropped."""
    kept: list = []
    for d in members:
        if any(dup_cites(d, k) for k in kept):
            continue
        kept.append(d)
    return kept


def dup_clone_lines() -> list:
    """The corpus as a list of (file, line, text), comments and boilerplate removed.

    Read from the MASKED source: a licence header repeated in every file is a
    licence header, not a clone, and comparing raw text would report the corpus's
    own conventions as its worst duplication.
    """
    stream = []
    for f in lean_sources(CORPUS):
        rel = os.path.relpath(f, CORPUS_BASE)
        for i, raw in enumerate(mask(read_source(f)).split("\n"), start=1):
            text = " ".join(raw.split())
            if not text or CLONE_BOILERPLATE.match(text):
                continue
            stream.append((rel, i, text))
    return stream


# A line split so that odd positions are identifiers and even positions are the
# text between them.  Splitting once per line and renaming by list walk is what
# keeps the clone scan in seconds: doing it with `re.sub` per window ran the
# substitution machinery about 1.6 million times over the corpus.
DUP_SPLIT = re.compile(r"([^\W\d][\w'!?₀-₉]*)", re.UNICODE)

# The placeholder that `dup_alpha_parts` writes for a local name, matched so that the
# periodicity test can ask whether two lines have the same SHAPE.
DUP_LOCAL_MASK = re.compile(r"\bL\d+\b")


def dup_alpha_parts(parts: list, corpus_names: frozenset, seen: dict) -> str:
    """One pre-split line, with local names renamed through the shared `seen` map."""
    out = list(parts)
    for k in range(1, len(out), 2):
        w = out[k]
        if w in corpus_names:
            continue
        if k + 1 < len(out) and out[k + 1].startswith("."):
            continue
        renamed = seen.get(w)
        if renamed is None:
            renamed = "L%d" % (len(seen) + 1)
            seen[w] = renamed
        out[k] = renamed
    return "".join(out)


def dup_local_alpha(window: tuple, corpus_names: frozenset) -> tuple:  # noqa: D401
    """A window with its LOCAL names canonicalised by order of first appearance.

    Two proofs that agree on every corpus name, every Mathlib lemma and every
    operator, and differ only in what they called their own hypotheses, are the
    same argument written twice -- and comparing raw text misses exactly that, the
    way a copy-paste-then-rename does.  Only names the corpus does not define are
    renamed, so a window whose agreement is nothing but variable shape (`intro a;
    exact a`) cannot collide with an unrelated one: it has no corpus name to
    agree on, and `dup_clone_named_enough` requires some.
    """
    seen: dict[str, str] = {}
    return tuple(dup_alpha_parts(DUP_SPLIT.split(line), corpus_names, seen)
                 for line in window)


# How many mentions of a corpus-defined name a window must carry to be worth
# pairing on.  Counted by OCCURRENCE and not by distinct name: a block that puts
# one corpus function through five steps is about this corpus, and requiring
# three different names would have hidden it while admitting nothing extra.  What
# the bar keeps out is two windows agreeing on keywords and punctuation alone --
# `have`, `exact`, `≤`, `0` -- which is what canonicalising local names would
# otherwise make identical everywhere.
CLONE_MIN_MENTIONS = 3


def dup_periodic(lines: tuple) -> bool:
    """Whether `lines` is at least two repeats of a shorter pattern of its own.

    Such a window is not a block: it is a shorter repeat seen through a window too
    wide for it.  Eight consecutive `have hx : 0 ≤ b t := le_trans (abs_nonneg _)
    (hb t)` lines match the next eight exactly, and calling that "eight lines
    copied" misreads a one-line idiom repeated eight times -- which is below the
    bar this screen sets, deliberately.
    """
    # Compared with the local names MASKED, not merely canonicalised: canonicalising
    # numbers each new local in order, so the second copy of a repeated line reads
    # `L13 L14` where the first reads `L9 L10` and the repetition is invisible.
    masked = [DUP_LOCAL_MASK.sub("L", line) for line in lines]
    width = len(masked)
    for period in range(1, width // 2 + 1):
        if all(masked[i] == masked[i - period] for i in range(period, width)):
            return True
    return False


def dup_disjoint(occ: list, width: int) -> list:
    """`occ` with windows that overlap an already-kept window in the same file dropped."""
    kept: list = []
    last: dict[str, int] = {}
    for rel, i in occ:
        if rel in last and i < last[rel] + width:
            continue
        kept.append((rel, i))
        last[rel] = i
    return kept


def dup_clones() -> list:
    """Repeated runs of source lines: verbatim, or alike up to local names.

    Two bars, because one number cannot express "enough copying".  A long run
    repeated twice and a shorter run repeated three times are the same defect with
    the copying spread differently.
    """
    corpus_names = dup_corpus_names()
    index = dup_decl_index()
    stream = dup_clone_lines()
    by_file: dict[str, list] = defaultdict(list)
    for rel, line, text in stream:
        by_file[rel].append((line, text))

    # Windows are indexed WITHIN a file, so a window never straddles two files.
    #
    # The two cheap tests -- enough text, enough corpus names -- run off prefix
    # sums, and the expensive one, canonicalising local names, runs only on the
    # windows that survive them.  Computed per window instead, this scan took
    # eighty times as long as the whole rest of the file, which would have cost
    # the guard the property its header promises: that it runs in seconds and so
    # can run on a broken tree.
    positions: list[tuple[str, int]] = []
    keys: list[tuple] = []
    for rel in sorted(by_file):
        rows = by_file[rel]
        texts = [t for _, t in rows]
        split = [DUP_SPLIT.split(t) for t in texts]
        char_prefix = [0]
        mention_prefix = [0]
        for t, parts in zip(texts, split):
            char_prefix.append(char_prefix[-1] + len(t))
            mention_prefix.append(mention_prefix[-1] + sum(
                1 for w in parts[1::2] if w in corpus_names))
        for width, min_chars, min_occ in (
                (CLONE_WINDOW, CLONE_MIN_CHARS, 2),
                (CLONE_SHORT_WINDOW, CLONE_SHORT_MIN_CHARS, CLONE_SHORT_MIN_OCCURRENCES)):
            for i in range(len(rows) - width + 1):
                if char_prefix[i + width] - char_prefix[i] < min_chars:
                    continue
                if mention_prefix[i + width] - mention_prefix[i] < CLONE_MIN_MENTIONS:
                    continue
                seen: dict = {}
                positions.append((rel, i))
                keys.append((width, min_occ) + tuple(
                    dup_alpha_parts(split[j], corpus_names, seen)
                    for j in range(i, i + width)))

    groups: dict[tuple, list] = defaultdict(list)
    for pos, key in zip(positions, keys):
        groups[key].append(pos)
    key_at = {pos: key for pos, key in zip(positions, keys)}

    findings = []
    for key, occ in groups.items():
        # Two windows that OVERLAP are not two copies of anything: they are one
        # region that repeats with a period shorter than the window.  A run of six
        # `have h : 0 ≤ x := le_trans (abs_nonneg _) (hx t)` lines matches itself at
        # every shift, and reporting those shifts says "eight lines copied" about a
        # region whose actual repeat is one line -- below the bar this screen sets.
        # Keeping the leftmost of each overlapping run leaves genuine copies, which
        # are disjoint, untouched.
        if dup_periodic(key[2:]):
            continue
        occ = dup_disjoint(sorted(occ), key[0])
        if len(occ) < key[1]:
            continue
        # A clone whose sites are TIED -- one declaration citing the other by name --
        # is the relation the corpus asks for, exactly as it is for a duplicated
        # statement or proof.  A specialisation that repeats its parent's hypotheses
        # and then applies the parent is not two copies of a claim; it is a claim and
        # its instance, and a divergence between them is already a build error.
        owners = [dup_decl_at(index, rel, by_file[rel][i][0]) for rel, i in occ]
        named = [d for d in owners if d is not None and d.name]
        if len(named) >= 2 and len(dup_untied(named)) < 2:
            continue
        # A repeated block of structure FIELDS is shareable only if the two
        # instances have the same type; at different types the fields have
        # different types and no definition returns both.
        if all(CLONE_FIELD_LINE.match(t) for t in key[2:]):
            if any(not dup_same_result_type(owners[0], o) for o in owners[1:]):
                continue
        # Drop a window whose left-neighbour window repeats the same way: it is
        # the tail of a longer clone that is already being reported.  Without
        # this a 30-line clone is reported 23 times.
        prev = [(rel, i - 1) for rel, i in occ]
        if all(p in key_at for p in prev):
            prev_keys = {key_at[p] for p in prev}
            if len(prev_keys) == 1 and len(groups[next(iter(prev_keys))]) == len(occ):
                continue
        # Extend right while every occurrence still agrees, to report the run's
        # true length rather than the window's.  Agreement is judged line by line
        # up to local names, which is coarser than the window's own keying: a run
        # continuing in renamed form is followed, and the reported length can
        # overshoot by a line where two locals happen to occupy the same position.
        # The length is descriptive -- what gates is the window.
        length = key[0]
        while True:
            nxt = set()
            for rel, i in occ:
                if i + length >= len(by_file[rel]):
                    nxt.add(None)
                    break
                nxt.add(dup_local_alpha((by_file[rel][i + length][1],), corpus_names))
            if len(nxt) != 1 or None in nxt:
                break
            length += 1
        findings.append((length, sorted(occ)))

    # A region that repeats with PERIOD shorter than itself -- five copies of the
    # same nine-line block, one after another -- produces a family of shifted
    # windows, each a genuine repeat and all of them the same defect.  Reporting
    # all of them buried the corpus's real clones under one file's arithmetic
    # blocks.  Longest first, and a finding is dropped when every one of its
    # occurrences already sits inside a longer finding's.
    findings.sort(key=lambda x: (-x[0], x[1]))
    covered: dict[str, list] = defaultdict(list)
    kept = []
    for length, occ in findings:
        if all(any(a <= i and i + length <= b for a, b in covered[rel])
               for rel, i in occ):
            continue
        kept.append((length, sorted(
            f"{rel}:{by_file[rel][i][0]}-{by_file[rel][i + length - 1][0]}"
            for rel, i in occ)))
        for rel, i in occ:
            covered[rel].append((i, i + length))
    return kept


def run_duplication() -> int:
    decls = dup_lean_decls()
    theorems = [d for d in decls
                if d.kind in ("theorem", "lemma") and d.name and d.body]

    corpus_names = dup_corpus_names()
    corpus_theorems = dup_corpus_theorems()

    # 1. One proposition, two names.
    by_statement: dict[str, list] = defaultdict(list)
    for d in theorems:
        key = dup_statement_key(d)
        if dup_substantive(key, corpus_names):
            by_statement[key].append(d)

    dup_statements = []
    for key, members in sorted(by_statement.items()):
        kept = dup_untied(sorted(members, key=lambda d: (d.file, d.line)))
        if len(kept) > 1:
            dup_statements.append((key, kept))

    # 2. One proof script, two statements.  Statements that are ALSO equal are
    #    reported above and are not counted twice here: the finding there is the
    #    stronger one and the fix there subsumes this one.
    by_proof: dict[str, list] = defaultdict(list)
    for d in theorems:
        bound = {b.name for b in d.binders if b.name}
        proof = dup_alpha(d.body, bound)
        tokens = proof.split()
        if len(tokens) < DUP_PROOF_MIN_TOKENS:
            continue
        # A proof made only of closers is a reflex, however long its lemma lists
        # run; a proof that names a step someone chose is an argument, and two
        # theorems sharing one are sharing that choice.
        #
        # TWO THINGS ARE NOT STEPS, and scanning them left this rule dead for every
        # tactic proof in the corpus.
        #
        #   `by` opens every one of them and chooses nothing.  It is lowercase and it
        #   is not a closer, so it satisfied the test on its own and no proof ever
        #   reached the `continue`.
        #
        #   A bracketed argument list carries lemma NAMES, not steps -- which is what
        #   "however long its lemma lists run" above means.  `simp [mul_one, add_zero]`
        #   is `simp`; scanning inside the brackets made every simp call look like an
        #   argument someone constructed.
        #
        # The fixture `two long proofs made only of closing tactics` is exactly this
        # pair and was reported for as long as both holes were open.
        steps = re.sub(r"\[[^\]]*\]", " ", proof)
        if not any(word not in DUP_CLOSING_TACTICS and word != "by"
                   and re.match(r"^[a-z]", word)
                   for word in (re.sub(r"[^\w']", "", t) or "_" for t in steps.split())):
            continue
        # Already factored: a short script naming a corpus theorem is that
        # theorem being applied, and the shared step is the lemma it names.
        if len(tokens) <= DUP_APPLICATION_MAX_TOKENS and any(
                re.sub(r"[^\w']", "", t) in corpus_theorems for t in tokens):
            continue
        by_proof[proof].append(d)

    dup_proofs = []
    for proof, members in sorted(by_proof.items()):
        kept = dup_untied(sorted(members, key=lambda d: (d.file, d.line)))
        if len(kept) < 2:
            continue
        if len({dup_statement_key(d) for d in kept}) == 1:
            continue
        dup_proofs.append((proof, kept))

    # 3. Repeated text, whatever it is made of.
    clones = dup_clones()

    failures = []
    if dup_statements:
        failures.append(
            f"theorems stating the same proposition under different names: "
            f"{len(dup_statements)}; delete all "
            f"but one, or -- if both names are wanted -- prove one FROM the other so "
            f"the corpus records that they are the same claim")
        for key, members in dup_statements:
            failures.append(f"    {_clip(key, 92)}")
            for d in members:
                failures.append(f"        {d.file}:{d.line}  {d.name}")
    if dup_proofs:
        failures.append(
            f"identical proof scripts under different statements: {len(dup_proofs)}, "
            f"the repeated script is an unnamed lemma "
            f"-- name it and apply it")
        for proof, members in dup_proofs:
            failures.append(f"    {_clip(proof, 92)}")
            for d in members:
                failures.append(f"        {d.file}:{d.line}  {d.name}")
    if clones:
        failures.append(
            f"verbatim repeated source blocks of {CLONE_WINDOW}+ lines: {len(clones)}; "
            f"factor the repeated text, or say in the "
            f"corpus what makes the two copies different")
        for length, sites in clones:
            failures.append(f"    {length} lines: " + "  ==  ".join(sites))

    if failures:
        print("DUPLICATION FAILURES\n")
        for line in failures:
            print("  " + line)
        return 1
    print(f"duplication guard passes: duplicate statements "
          f"{len(dup_statements)}, duplicate proofs "
          f"{len(dup_proofs)}, repeated {CLONE_WINDOW}+-line "
          f"blocks {len(clones)} "
          f"(over {len(theorems)} theorems)")
    return 0



# ======================================================================================
# MATHLIB: A CORPUS DECLARATION THAT ALREADY EXISTS UPSTREAM
# ======================================================================================
#
# The corpus must never write something Mathlib already has.  Re-proving an
# upstream lemma is not merely redundant: the local copy is the one that goes
# stale, it is stated under whatever hypotheses the local proof happened to
# need rather than the general ones, and every later reader has to establish
# for themselves that the two agree.  Four cases were found and removed by
# hand -- `one_sub_lt_exp_neg` (weaker than `Real.one_sub_lt_exp_neg`, which
# needs only `x != 0`), `constant_div_natSucc_tendsto_zero`
# (`tendsto_const_div_atTop_nhds_zero_nat`), `dotProduct_comm`, and the whole
# `sigmoid` block (`Real.sigmoid`) -- and this guard exists so the fifth is
# found by a machine.
#
# WHAT IT MEASURES.  A corpus declaration whose own name is, verbatim, the name
# of a Mathlib declaration.  Name equality is the signal because Mathlib's
# naming convention is generated from the statement: two declarations that
# Mathlib would name identically state the same fact about the same operators
# in the same order.  It is a lower bound, not a survey -- a duplicate written
# under a different name is invisible here, and that is the honest limit of a
# name-based screen.  It is stated so no reader mistakes a clean report for
# "the corpus duplicates nothing".
#
# WHY NOT SUFFIX MATCHING.  Comparing bare final components (`Foo.mono` against
# `Mathlib`'s `Bar.mono`) produces almost nothing but noise: structure
# projections, `ext`, `mono`, `nonempty` and `symm` collide across every
# namespace in both libraries and mean nothing.  Only dotless corpus names are
# considered, which is exactly the set that lands in the `Descent` root.
#
# WHICH MATHLIB NAMES COUNT.  Mathlib's FULL name, namespace included, because
# `CategoryTheory.core`, `SimpleGraph.Walk.transfer` and `Ordinal.gamma` are
# not in scope for this corpus and a bare-name comparison reported all three.
# A Mathlib declaration collides only if its full name is the corpus name
# itself, or is that name inside a namespace THIS CORPUS OPENS -- which is read
# off the corpus's own `open` lines rather than hardcoded, so it tracks the
# corpus instead of drifting from it.  That is what keeps `Real.sigmoid` and
# `Matrix.dotProduct_comm` findings while dropping the category theory.
#
# WHY IT CANNOT SILENTLY PASS.  The guard needs Mathlib's SOURCE, which lives
# in `.lake/packages/mathlib` and is absent on a tree that has never been
# built.  A guard that quietly reports zero findings when it could not look is
# the failure mode this whole directory exists to prevent, so a missing Mathlib
# is a FAILURE with the path it looked for, not a pass.  Point it elsewhere
# with DESCENT_MATHLIB.

# Every budget here is 0, like every other budget in this file.  Nothing is
# grandfathered: the four known collisions were removed before the guard
# landed, not pinned.

MATHLIB_DECL = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)?"
    r"(?:private |protected |noncomputable |nonrec |scoped |partial |unsafe |local )*"
    r"(theorem|lemma|def|abbrev|instance)[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_'!?.]*)"
)

# Names that mean something different on each side of the boundary, or that are
# too generic for name equality to be evidence.  Each one is here because it
# was checked BY HAND and found not to be a duplicate; this list is not a place
# to silence a finding that has not been read.
# NO EXEMPTIONS.  This set is empty and stays empty.
#
# It held seven names: five where Mathlib uses the word for a different object
# (`covariance` against a measure versus against an abstract functional, and so on) and
# two where the SHAPE screen normalised a corpus conclusion onto an unrelated Mathlib
# one.  Every entry was read by hand and every entry was correct about the mathematics.
# That is precisely why they are gone: an exemption that is correct is still a place
# where the guard has been told to stop looking, and a list of those grows.
#
# When the screen now fires on something genuinely different, the repair is to the
# SCREEN -- make the normal form carry enough to tell the two apart -- not to a list of
# declarations the screen is asked to skip.
MATHLIB_EXEMPT: set[str] = set()


def mathlib_root() -> Path | None:
    """Where Mathlib's source is, or `None`.

    `DESCENT_MATHLIB` wins so the guard can be calibrated against a fixture
    tree, exactly as `DESCENT_CORPUS` does for the corpus half.
    """
    override = os.environ.get("DESCENT_MATHLIB")
    if override:
        path = Path(override)
        return path if path.is_dir() else None
    path = REPO / ".lake" / "packages" / "mathlib" / "Mathlib"
    return path if path.is_dir() else None


def mathlib_declared_names(root: Path) -> dict:
    """Every declaration name Mathlib writes, mapped to one source location.

    Comments are stripped first for the same reason the corpus side strips
    them: Mathlib's prose contains lines beginning `theorem ...` inside module
    docstrings, and counting those would invent collisions.

    This deliberately does NOT reuse `lean_sources`.  That walk drops any path
    with a dot-prefixed component, which is right for the corpus and fatal
    here: Mathlib lives under `.lake/packages/`, so every one of its files has
    a dotted ancestor and the walk returned nothing.  The guard reported
    "CANNOT RUN" rather than a clean zero, which is the only reason the bug was
    visible at all.  Dot components are filtered relative to `root` instead.
    """
    names: dict = {}
    for path in sorted(
        candidate
        for candidate in root.rglob("*.lean")
        if not any(part.startswith(".")
                   for part in candidate.relative_to(root).parts)
    ):
        try:
            src = ident_strip_comments(read_source(path))
        except ValueError:
            continue
        # `section`s are tracked as well as `namespace`s, and both are pushed on
        # ONE stack, because `end` closes whichever is innermost.  Popping only
        # on `namespace` was wrong in the direction that hides nothing and
        # invents everything: a file with `namespace Stream'` followed by any
        # `section ... end` had `Stream'` popped by the section's `end`, so the
        # rest of the file's declarations were recorded as root-level and
        # collided with every corpus name that happened to match.
        stack: list[str | None] = []
        for lineno, line in enumerate(src.split("\n"), start=1):
            opened = MATHLIB_NAMESPACE_OPEN.match(line)
            if opened:
                stack.append(opened.group(1))
                continue
            if MATHLIB_SECTION_OPEN.match(line):
                stack.append(None)
                continue
            if MATHLIB_NAMESPACE_CLOSE.match(line):
                if stack:
                    stack.pop()
                continue
            match = MATHLIB_DECL.match(line)
            if match:
                written = match.group(2)
                if written.startswith("_root_."):
                    full = written[len("_root_."):]
                else:
                    enclosing = [part for part in stack if part]
                    full = ".".join(enclosing + [written]) if enclosing else written
                names.setdefault(full,
                                 f"{path.relative_to(root.parent)}:{lineno}")
    return names


# --------------------------------------------------------------------------------------
# THE SECOND SCREEN: WHAT THE THEOREM SAYS, NOT WHAT IT IS CALLED
#
# Name equality is a lower bound and a narrow one.  A duplicate written under a
# different name -- which is the common case, because a corpus author who knew
# the Mathlib name would have used the Mathlib lemma -- is invisible to it.
# `constant_div_natSucc_tendsto_zero` and `tendsto_const_div_atTop_nhds_zero_nat`
# share no token at all, and were the same theorem.
#
# So the statement itself is normalised and compared.  The normal form is the
# CONCLUSION with every bound variable replaced by `_` and every namespace
# prefix dropped, so `Real.exp (-x)` and `exp (-h)` become the same text.  What
# survives is the operator skeleton and the global constants, which is what
# "the same theorem" means when the two libraries name their variables
# differently and sit in different namespaces.
#
# WHAT IT DELIBERATELY DOES NOT DO.  It does not look at hypotheses.  A corpus
# lemma whose conclusion matches a Mathlib lemma but which assumes more is
# exactly the case worth reporting -- that is `one_sub_lt_exp_neg` requiring
# `0 < h` where Mathlib requires `x != 0` -- and hiding it behind a hypothesis
# comparison would have suppressed the first finding this guard was written
# for.  Nor does it elaborate: it is source text, so `2⁻¹` and `1 / 2` are
# different, and a statement phrased through a corpus abbreviation does not
# match the unfolded Mathlib one.  Both limits cut the same way, toward missing
# duplicates rather than inventing them.
#
# SIGNIFICANCE FLOOR.  A normal form has to carry at least
# MATHLIB_SHAPE_MIN_CONSTANTS distinct global constants and
# MATHLIB_SHAPE_MIN_LENGTH characters to be reported.  Without it every
# `_ ≤ _` in the corpus matches a hundred Mathlib lemmas and the screen reports
# noise at a volume that guarantees nobody reads it.
# These three floors are MEASURED, not chosen.  Over the corpus and Mathlib as
# they stand, `constants >= 3` reports nothing AND cannot report the known
# duplicate the screen was written for -- `1 - _ < exp (-_)` names exactly one
# constant -- so the floor that looked safe was the floor that made the screen
# decorative.  At `constants >= 1, length >= 15` the corpus yields exactly one
# match, `target = target`, which is a corpus field name equal to itself and
# says nothing.  Hence the third floor: a normal form must also carry at least
# MATHLIB_SHAPE_MIN_OPERATORS operator occurrences, which `X = X` fails with
# one and `1 - _ < exp (-_)` passes with three.  The self-test below holds all
# three to the known pair.
MATHLIB_SHAPE_MIN_CONSTANTS = 1
MATHLIB_SHAPE_MIN_LENGTH = 15
MATHLIB_SHAPE_MIN_OPERATORS = 2

# The operator occurrences that make a normal form say something.  Relations
# and arithmetic only: brackets and commas appear in every statement and so
# separate nothing.
MATHLIB_SHAPE_OPERATORS = re.compile(
    r"[+\-*/<>=^≤≥≠∑∏∫∈⊆∀∃¬∧∨→↔]|⁻¹|\|\|")

MATHLIB_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")

# Tokens that carry no mathematical content for matching purposes: they are
# either Lean syntax or so ubiquitous that their presence says nothing.
MATHLIB_SHAPE_NOISE = frozenset("""
fun forall exists let have show from this at in with by do match if then else
Type Sort Prop and or not iff true false
""".split())


def mathlib_decl_headers(src: str):
    """Yield `(lineno, kind, name, header)` for each declaration in `src`.

    `header` is the text between the declaration's name and the start of its
    proof, which is where the statement lives.
    """
    lines = src.split("\n")
    starts = []
    for index, line in enumerate(lines):
        match = MATHLIB_DECL.match(line)
        if match:
            starts.append((index, match.group(1), match.group(2), match.end(2)))
    for position, (index, kind, name, name_end) in enumerate(starts):
        stop = starts[position + 1][0] if position + 1 < len(starts) else len(lines)
        chunk = [lines[index][name_end:]] + lines[index + 1:stop]
        header = []
        for line in chunk:
            cut = re.search(r":=", line)
            if cut:
                header.append(line[:cut.start()])
                break
            header.append(line)
        yield index + 1, kind, name, "\n".join(header)


def mathlib_statement_key(header: str) -> tuple[str, int]:
    """Normalise a statement to its operator skeleton.

    Returns the normal form and how many distinct global constants it mentions,
    which is the significance measure the caller thresholds on.
    """
    text = header.replace("=>", "↦")
    # Split binders from conclusion at the last colon outside every bracket.
    depth, cut = 0, -1
    for position, char in enumerate(text):
        if char in "([{⟨⦃":
            depth += 1
        elif char in ")]}⟩⦄":
            depth -= 1
        elif char == ":" and depth == 0 and not text.startswith("::", position):
            cut = position
    binder_region, conclusion = (text[:cut], text[cut + 1:]) if cut >= 0 else ("", text)

    # A bound variable is a lowercase, undotted identifier introduced on the
    # left.  Types and structures are capitalised by convention, and dotted
    # names are global, so neither is mistaken for a binder.
    bound = {
        token for token in MATHLIB_IDENT.findall(binder_region)
        if "." not in token and token[:1].islower()
    }
    bound |= {
        token for token in MATHLIB_IDENT.findall(conclusion)
        if "." not in token and token[:1].islower() and len(token) <= 2
    }

    constants: set[str] = set()

    def rewrite(match: re.Match) -> str:
        token = match.group(0)
        if token in bound or token in MATHLIB_SHAPE_NOISE:
            return "_"
        if "." in token and token.split(".", 1)[0] in bound:
            # A PROJECTION OFF A BOUND VARIABLE.  The receiver is anonymous, but the
            # projection PATH is not, and taking only its last component threw away the
            # type: `p.vertices.length` reaches a length through a field that `x.length`
            # does not have, and collapsing both to `length` reported
            # `Quiver.Path.vertices_length` as a restatement of a fact about the length
            # of a list.  Keeping the path is what tells a list from a quiver path.
            short = token.split(".", 1)[1]
        else:
            short = token.rsplit(".", 1)[-1]
        if short in MATHLIB_SHAPE_NOISE:
            return "_"
        constants.add(short)
        return short

    skeleton = MATHLIB_IDENT.sub(rewrite, conclusion)
    skeleton = re.sub(r"\s+", " ", skeleton).strip()
    skeleton = re.sub(r"(?:_ )+_", "_", skeleton)
    return skeleton, len(constants)


MATHLIB_NAMESPACE_OPEN = re.compile(r"^namespace[ \t]+([A-Za-z_][A-Za-z0-9_'.]*)[ \t]*$")
MATHLIB_SECTION_OPEN = re.compile(r"^(?:noncomputable[ \t]+)?section\b")
MATHLIB_NAMESPACE_CLOSE = re.compile(r"^end\b")

# `open` lines in the corpus, which is what decides whose short names are in
# scope.  `open scoped Foo` counts too: it brings `Foo`'s scoped notation and
# instances in, and a corpus name shadowing a `Foo` lemma is the same defect.
CORPUS_OPEN = re.compile(r"^open[ \t]+(?:scoped[ \t]+)?(.+?)[ \t]*(?:\bin\b.*)?$")


def corpus_open_namespaces() -> set:
    """Every namespace the corpus opens, plus the root namespace as `""`.

    Read from the corpus rather than hardcoded so the guard cannot drift away
    from what the corpus actually has in scope.  A hardcoded list would go
    stale in exactly the direction that hides findings.
    """
    namespaces = {""}
    for path in ident_lean_files():
        src = ident_strip_comments(read_source(Path(path)))
        for line in src.split("\n"):
            match = CORPUS_OPEN.match(line)
            if not match:
                continue
            for token in match.group(1).split():
                if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", token):
                    namespaces.add(token)
    return namespaces


# The control for the shape screen.  A detector that reports nothing is
# indistinguishable from a clean corpus, and this one reports nothing over the
# corpus today, so its silence is worth exactly as much as this control.  The
# pair is REAL: it is `one_sub_lt_exp_neg` as the corpus wrote it, against the
# Mathlib lemma of the same content, which differ in variable names, in
# namespace qualification and in hypothesis, and which the screen must
# nonetheless identify.  The negative pair must NOT be identified.
MATHLIB_SHAPE_CONTROL_SAME = (
    "{h : ℝ} (hh : 0 < h) : 1 - h < Real.exp (-h)",
    "{x : ℝ} (hx : x ≠ 0) : 1 - x < exp (-x)",
)
MATHLIB_SHAPE_CONTROL_DIFFERENT = (
    "(a b : ℝ) : Real.exp (a + b) = Real.exp a * Real.exp b",
    "(a b : ℝ) : Real.log (a * b) = Real.log a + Real.log b",
)
# A pair the screen used to identify and must not: one length is a list's, the other is
# reached through a quiver path's vertex list.  Same operators, same literal, different
# projection depth -- which is the only thing in the text that says they are about
# different objects.
MATHLIB_SHAPE_CONTROL_PROJECTION = (
    "{c : List σ} {x : List ι} (hx : x ∈ derivations c) : x.length = c.length + 1",
    "(p : Quiver.Path a b) : p.vertices.length = p.length + 1",
)


def mathlib_shape_is_significant(skeleton: str, constants: int) -> bool:
    """Whether a normal form says enough for a match to be evidence."""
    return (constants >= MATHLIB_SHAPE_MIN_CONSTANTS
            and len(skeleton) >= MATHLIB_SHAPE_MIN_LENGTH
            and len(MATHLIB_SHAPE_OPERATORS.findall(skeleton))
            >= MATHLIB_SHAPE_MIN_OPERATORS)


def mathlib_shape_selftest() -> list:
    """Findings about the screen itself, empty when the screen works."""
    problems = []
    left, right = MATHLIB_SHAPE_CONTROL_SAME
    left_key, left_constants = mathlib_statement_key(left)
    right_key, _ = mathlib_statement_key(right)
    if left_key != right_key:
        problems.append(
            "the shape normal form no longer identifies a known duplicate pair:\n"
            f"      {left}\n        -> {left_key}\n"
            f"      {right}\n        -> {right_key}")
    if not mathlib_shape_is_significant(left_key, left_constants):
        problems.append(
            f"the significance floors ({MATHLIB_SHAPE_MIN_CONSTANTS} constants, "
            f"{MATHLIB_SHAPE_MIN_LENGTH} characters, "
            f"{MATHLIB_SHAPE_MIN_OPERATORS} operators) discard the known duplicate "
            f"pair, whose normal form {left_key!r} carries {left_constants} "
            f"constants, {len(left_key)} characters and "
            f"{len(MATHLIB_SHAPE_OPERATORS.findall(left_key))} operators; the "
            f"screen cannot report the very finding it was written for")
    if mathlib_shape_is_significant(*mathlib_statement_key("(f : α → β) : target = target")):
        problems.append(
            "the significance floors admit `target = target`, a name equal to "
            "itself, which matched a Mathlib field lemma and meant nothing")
    first, second = MATHLIB_SHAPE_CONTROL_DIFFERENT
    if mathlib_statement_key(first)[0] == mathlib_statement_key(second)[0]:
        problems.append(
            "the shape normal form identifies two DIFFERENT statements:\n"
            f"      {first}\n      {second}")
    shallow, deep = MATHLIB_SHAPE_CONTROL_PROJECTION
    if mathlib_statement_key(shallow)[0] == mathlib_statement_key(deep)[0]:
        problems.append(
            "the shape normal form identifies a list length with a length reached "
            "through a projection, which is the false positive that emptied "
            "MATHLIB_EXEMPT:\n"
            f"      {shallow}\n      {deep}")
    return problems


def mathlib_statement_shapes(root: Path) -> dict:
    """Every Mathlib theorem's normalised conclusion, mapped to one location."""
    shapes: dict = {}
    for path in sorted(
        candidate
        for candidate in root.rglob("*.lean")
        if not any(part.startswith(".")
                   for part in candidate.relative_to(root).parts)
    ):
        try:
            src = ident_strip_comments(read_source(path))
        except ValueError:
            continue
        for lineno, kind, name, header in mathlib_decl_headers(src):
            if kind not in ("theorem", "lemma"):
                continue
            skeleton, constants = mathlib_statement_key(header)
            if not mathlib_shape_is_significant(skeleton, constants):
                continue
            shapes.setdefault(
                skeleton, f"{name} ({path.relative_to(root.parent)}:{lineno})")
    return shapes


def run_mathlib() -> int:
    root = mathlib_root()
    if root is None:
        looked = os.environ.get("DESCENT_MATHLIB") or str(
            REPO / ".lake" / "packages" / "mathlib" / "Mathlib")
        print("mathlib guard CANNOT RUN: no Mathlib source at " + looked)
        print("  It compares corpus declaration names against Mathlib's, so with no "
              "Mathlib it has nothing to compare against.  This is reported as a "
              "failure rather than a pass because a screen that cannot look is not "
              "a screen that found nothing.  Build the tree, or set DESCENT_MATHLIB.")
        return 1

    upstream = mathlib_declared_names(root)
    if not upstream:
        print(f"mathlib guard CANNOT RUN: no declarations found under {root}")
        return 1

    broken = mathlib_shape_selftest()
    if broken:
        print("mathlib guard CANNOT RUN: its own shape screen fails its control")
        for problem in broken:
            print(f"    {problem}")
        return 1

    upstream_shapes = mathlib_statement_shapes(root)

    prefixes = sorted(corpus_open_namespaces())
    collisions = []
    scanned = 0
    for path in ident_lean_files():
        src = ident_strip_comments(read_source(Path(path)))
        rel = os.path.relpath(path, IDENT_ROOT)
        # The corpus nests too, and a declaration inside `namespace Foo` is
        # `Foo.bar`, not `bar`: it neither shadows nor duplicates a root-level
        # Mathlib name.  Ignoring this reported `CertificateCalculus.IsComplete`
        # against the uniform-space `IsComplete`, `Fiber.total` against a
        # homology `total`, and four more of the same shape.
        stack: list[str | None] = []
        for lineno, line in enumerate(src.split("\n"), start=1):
            opened = MATHLIB_NAMESPACE_OPEN.match(line)
            if opened:
                stack.append(opened.group(1))
                continue
            if MATHLIB_SECTION_OPEN.match(line):
                stack.append(None)
                continue
            if MATHLIB_NAMESPACE_CLOSE.match(line):
                if stack:
                    stack.pop()
                continue
            match = MATHLIB_DECL.match(line)
            if not match:
                continue
            name = match.group(2)
            scanned += 1
            # `Descent` is the corpus root, so it is not a namespace that
            # makes a name non-root for this purpose.
            enclosing = [part for part in stack if part and part != "Descent"]
            if enclosing or "." in name or name in MATHLIB_EXEMPT:
                continue
            for prefix in prefixes:
                full = f"{prefix}.{name}" if prefix else name
                if full in upstream:
                    collisions.append((rel, lineno, name, f"{full} ({upstream[full]})"))
                    break

    restatements = []
    for path in ident_lean_files():
        src = ident_strip_comments(read_source(Path(path)))
        rel = os.path.relpath(path, IDENT_ROOT)
        for lineno, kind, name, header in mathlib_decl_headers(src):
            if kind not in ("theorem", "lemma") or name in MATHLIB_EXEMPT:
                continue
            skeleton, constants = mathlib_statement_key(header)
            if not mathlib_shape_is_significant(skeleton, constants):
                continue
            if skeleton in upstream_shapes:
                restatements.append((rel, lineno, name, upstream_shapes[skeleton],
                                     skeleton))

    bad = False
    if collisions:
        bad = True
        print(f"mathlib guard FAILS: corpus declarations whose name Mathlib already "
              f"uses: {len(collisions)}; import the "
              f"Mathlib declaration and delete the local one, or -- if the two really "
              f"state different things -- rename the local one and record why in "
              f"MATHLIB_EXEMPT")
        for rel, lineno, name, where in sorted(collisions):
            print(f"  {rel}:{lineno}  {name}  <-  {where}")

    if restatements:
        bad = True
        print(f"mathlib guard FAILS: corpus theorems whose CONCLUSION is a Mathlib "
              f"theorem's, under a different name: {len(restatements)}; "
              f"use the Mathlib lemma. If the corpus one is "
              f"genuinely different -- a different type, a stronger conclusion the "
              f"normal form cannot see -- say which in MATHLIB_EXEMPT")
        for rel, lineno, name, where, skeleton in sorted(restatements):
            print(f"  {rel}:{lineno}  {name}  <-  {where}")
            print(f"      shape: {skeleton}")

    if bad:
        return 1

    print(f"mathlib guard passes: name collisions {len(collisions)}, "
          f"restated conclusions {len(restatements)}, "
          f"over {scanned} corpus declarations against "
          f"{len(upstream)} Mathlib names and {len(upstream_shapes)} Mathlib "
          f"statement shapes (read from {root})")
    return 0

# ======================================================================================
# CONVENTIONS -- the convention ledger, and the four ways it can be violated
# ======================================================================================
#
# WHAT THIS IS FOR.  A convention is invisible to Lean.  Nei's `G_ST`, Hudson's
# `F_ST` and the per-branch drift `F` are all reals in `[0,1)`, all named `fst`,
# and every one of them type-checks in the others' place.  This corpus has paid
# for that three times: the factor-of-four `F_ST` error, a Nei body carrying the
# name `hudsonFst`, and a within-population heterozygosity loss documented as a
# between-population variance ratio.  Each was caught by a person reading the
# corpus against a paper.  `validation/conventions.json` is that reading
# written down as DATA; this guard is what makes the data load-bearing.
#
# THE FOUR RULES, all at budget 0:
#
#   UNLEDGERED   a `def` whose name carries a ledgered quantity's word, under a
#                quantity whose scope is `complete`, with no ledger entry.  The
#                ledger is where the convention is stated, so "no entry" and
#                "no stated convention" are the same condition.
#   STALE        a ledger entry naming a declaration the corpus no longer has,
#                or a bridge naming a theorem the corpus no longer has.  A
#                committed snapshot of a moving corpus goes stale by
#                construction; the only safe design is to make staleness LOUD.
#   UNBRIDGED    one module carrying two conventions the ledger declares
#                incompatible, with no chain of existing bridge theorems
#                connecting them.  `Conventions.lean` may hold both `hudsonFst`
#                and `neiGst` precisely because `hudsonFst_eq_of_neiGst` exists.
#   CONSTANT     a ledgered `constants` multiset that the definition's body no
#                longer has.  This is the durable half of a constant audit: a
#                future edit turning a `4` into a `2` fails here instead of
#                waiting for somebody to re-read the source paper.
#
# ANCHORED TO NAMES, NEVER TO OFFSETS.  Every ledger key is
# `<module>::<declaration>`.  A ledger pinned to line numbers fails on edits
# that have nothing to do with it, which is exactly how `extract/test_parser.py`
# came to be red, and a gate that is red for an unrelated reason stops being
# read.
#
# NOT A REFERENCE COUNT.  This guard never counts citations and never requires
# one.  That shape is deliberately absent from this file (family F14): it has
# twice deleted correct work here.  A ledger entry's `source` is free text that
# no rule inspects.


CONVENTION_LEDGER = "validation/conventions.json"

# Split a declaration name into camel-case words.  `[A-Z]+[0-9]*(?![a-z])` is
# what keeps `narrowSenseH2` yielding `h2` rather than `h` and `2` -- without the
# `[0-9]*` the entire heritability family is invisible to the matcher.
CONVENTION_WORD = re.compile(r"[A-Z]+[0-9]*(?![a-z])|[A-Z][a-z0-9']*|[a-z][a-z0-9']*")

CONVENTION_DEF = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z_0-9'.]+)", re.M)
CONVENTION_THM = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:theorem|lemma)\s+([A-Za-z_0-9'.]+)", re.M)
CONVENTION_NEXT_DECL = re.compile(
    r"^(?:@\[|/-|noncomputable\s|def\s|theorem\s|lemma\s|abbrev\s|structure\s|class\s|"
    r"instance\s|inductive\s|section\b|end\b|namespace\b|open\b|variable\b)", re.M)
CONVENTION_NUMBER = re.compile(r"(?<![A-Za-z_0-9'₀-₉.])([0-9]+(?:\.[0-9]+)?)")

# The head of an `Empirical status:` line: everything up to the first bracket,
# dash, comma, full stop, semicolon, colon or newline.  Deliberately NOT the
# whole status text -- `MEASURED` is also ordinary English inside the evidence
# tables ("against measured 0.53297"), and a whole-text rule produced 99
# findings of which none was a defect.
# A QUOTED MENTION IS NOT A DECLARATION.  `Empirical status:` also occurs inside
# ordinary prose -- `Descent/Core/Ratios.lean` said "This file must never
# acquire an `Empirical status:` line", and this regex read the two characters
# after it as a status head and reported `\` line` as a term outside the closed
# vocabulary.  A guard that fails on a docstring for SAYING it has no status is
# a guard that punishes the clearest possible declaration.
#
# The discriminator is the BACKTICK and only the backtick.  Anchoring at the
# start of a line was tried first and is wrong in both directions: a real marker
# sits on the `/--` opening line in `integratedCoalescentHazard` and mid-line
# after a bolded sentence in `freeRecombinationStep`.  The corpus quotes the
# phrase when talking ABOUT it and never when asserting one.
CONVENTION_STATUS = re.compile(r"(?<!`)Empirical status:[ \t]*(.{0,140})", re.S)


def convention_docstrings(raw: str):
    """(offset, text) for every `/-- ... -/` docstring, nesting respected.

    Needed because a status marker means something only relative to the
    docstring it sits in: two markers in ONE docstring are two verdicts on one
    declaration, whereas two in a file are two declarations.
    """
    out, i, n = [], 0, len(raw)
    while True:
        start = raw.find("/--", i)
        if start < 0:
            return out
        depth, j = 1, start + 3
        while j < n and depth:
            if raw.startswith("/-", j):
                depth += 1
                j += 2
            elif raw.startswith("-/", j):
                depth -= 1
                j += 2
            else:
                j += 1
        out.append((start, raw[start:j]))
        i = j


def convention_status_head(text: str) -> str:
    """The vocabulary term a status line claims, stripped of emphasis."""
    head = text.lstrip()
    while head.startswith("*"):
        head = head.lstrip("*").lstrip()
    head = re.split(r"[(\[,.;:\n]|--|—|\*\*", head)[0]
    return " ".join(head.split()).rstrip("`")


def convention_words(name: str) -> set:
    """The camel-case words of a declaration's LAST dotted component, lowered.

    Matching on words rather than substrings is not fussiness: `steppingStone`
    contains the letters `gSt`, and a substring matcher pulls
    `steppingStoneMeetingTimeOnLattice` into the `F_ST` family, where a ledger
    entry for it would be a lie.
    """
    return {w.lower() for w in CONVENTION_WORD.findall(name.split(".")[-1])}


def convention_body(src: str, name: str) -> str | None:
    """The body of `def name`, comments already stripped, or None if absent."""
    m = re.search(r"^(?:noncomputable\s+)?def\s+" + re.escape(name) + r"(?![A-Za-z_0-9'])",
                  src, re.M)
    if not m:
        return None
    tail = src[m.end():]
    assign = tail.find(":=")
    if assign < 0:
        return ""
    rest = tail[assign + 2:]
    nxt = CONVENTION_NEXT_DECL.search(rest)
    return rest[:nxt.start()] if nxt else rest


CONVENTION_BINDER = re.compile(r"\(([^()]*?):")


def convention_corpus() -> tuple[dict, dict, set, dict]:
    """(defs by `module::name`, source by module, theorem short names, binder words).

    The binder words are what lets the guard see a definition that CONSUMES an
    `F_ST` without being named for one.  That is where the convention mismatch
    actually bites: `presentDayPGSVariance (V_A fst)` reads its argument as a
    heterozygosity retention and says so, and a caller holding a Hudson value is
    making a claim the body does not.  Thirty-three such consumers exist and
    three of them declared their reading.
    """
    defs, sources, theorems, binders = {}, {}, set(), {}
    for path in ident_lean_files():
        rel = os.path.relpath(path, IDENT_ROOT)
        src = ident_strip_comments(read_source(Path(path)))
        sources[rel] = src
        starts = list(CONVENTION_DEF.finditer(src))
        for i, m in enumerate(starts):
            key = f"{rel}::{m.group(1)}"
            defs[key] = m.group(1)
            end = starts[i + 1].start() if i + 1 < len(starts) else len(src)
            chunk = src[m.end():end]
            cut = chunk.find(":=")
            signature = chunk[:cut] if cut >= 0 else chunk[:400]
            words: set = set()
            for group in CONVENTION_BINDER.findall(signature):
                for token in group.split():
                    words |= convention_words(token)
            binders[key] = words
        for m in CONVENTION_THM.finditer(src):
            theorems.add(m.group(1).split(".")[-1])
    return defs, sources, theorems, binders


def convention_connected(present: set, edges: set) -> list:
    """Every declared-incompatible pair inside `present` that `edges` fails to connect.

    Connectivity rather than a direct edge, because the corpus relates
    conventions in a chain: Nei's `G_ST` to Hudson's `F_ST` to the per-branch
    drift `F`.  Demanding a direct bridge for the outer pair would ask for a
    theorem that adds nothing, and asking for a theorem nobody needs is how a
    guard gets satisfied with a stub.
    """
    parent = {c: c for c in present}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in edges:
        if a in parent and b in parent:
            parent[find(a)] = find(b)
    return sorted({(a, b) for a in present for b in present
                   if a < b and find(a) != find(b)})


def run_conventions() -> int:
    ledger_path = CORPUS / CONVENTION_LEDGER
    if not ledger_path.exists():
        print(f"conventions guard CANNOT RUN: no ledger at {ledger_path}")
        print("  The ledger IS the statement of convention for every quantity this "
              "guard covers, so with no ledger there is nothing to check against. "
              "This is reported as a failure rather than a pass for the same reason "
              "the mathlib guard fails when Mathlib is absent: a screen that cannot "
              "look is not a screen that found nothing.")
        return 1
    try:
        ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        print(f"conventions guard CANNOT RUN: {ledger_path} is not parseable JSON: {exc}")
        return 1

    quantities = ledger.get("quantities", {})
    entries = ledger.get("declarations", {})
    known_conventions = set(ledger.get("conventions", {}))
    defs, sources, theorems, binders = convention_corpus()

    # `verified_constants` records values read against a published source that
    # fall OUTSIDE the ledgered quantity families -- the Ohta-Kimura 10/2/11, the
    # LDSC `+1`, the `4` in `4*Ne*mu`.  They carry no convention and take part in
    # only two rules, staleness and constants, which is why they are merged into
    # one dictionary rather than kept on a separate code path: one extractor, one
    # comparison, one place to be wrong.
    verified = {k: v for k, v in ledger.get("verified_constants", {}).items()
                if not k.startswith("$")}

    stale, unledgered, unbridged, constants, malformed, statuses = [], [], [], [], [], []
    multistatus = []

    # MULTIPLICITY.  At most ONE `Empirical status:` marker per docstring.
    #
    # Every scanner, and every reader who stops at the first status line, takes
    # the FIRST marker as the verdict.  So a superseded marker sitting above a
    # current one IS the reported status, and the corpus has been counted wrong
    # that way: `pairwiseFstFromBranchTaus` carried a FALSIFIED describing a body
    # it no longer had, above a VALIDATED describing the body it did have, and
    # was counted among the falsified for it.  The same mechanism let one
    # out-of-regime measurement be read as three separate defects.
    #
    # This is deliberately not a rule about which marker is right. It is a rule
    # that a declaration states its verdict once, so that the first marker and
    # the verdict are the same thing.
    for module in sorted(sources):
        raw = read_source(Path(IDENT_ROOT) / module)
        for offset, doc in convention_docstrings(raw):
            heads = [convention_status_head(m.group(1))
                     for m in CONVENTION_STATUS.finditer(doc)]
            if len(heads) > 1:
                lineno = raw[:offset].count("\n") + 1
                multistatus.append(
                    f"{module}:{lineno}: one docstring carries {len(heads)} status "
                    f"markers {heads}; every scanner reads the first, so the others "
                    f"are invisible and the first may not be the current verdict")

    # STATUS.  A closed vocabulary of `Empirical status:` heads.  A status marker
    # exists to be COUNTED -- the corpus's own coverage denominator is built from
    # these -- and a vocabulary that drifts cannot be counted.  The defect that
    # motivated this: one verdict written in two cases at once, 138 times in
    # capitals and 5 in lower case.
    vocabulary = ledger.get("empirical_status_vocabulary", {}).get("terms", {})
    status_seen = 0
    if vocabulary:
        folded = {term.lower(): term for term in vocabulary}
        for module, src in sorted(sources.items()):
            raw = read_source(Path(IDENT_ROOT) / module)
            for m in CONVENTION_STATUS.finditer(raw):
                head = convention_status_head(m.group(1))
                status_seen += 1
                if head in vocabulary:
                    continue
                # Longest canonical term the head STARTS with, so a term may be
                # followed by its own qualifying words without a finding.
                if any(head.startswith(t) and (len(head) == len(t) or not head[len(t)].isalpha())
                       for t in vocabulary):
                    continue
                lineno = raw[:m.start()].count("\n") + 1
                canonical = folded.get(head.lower())
                if canonical:
                    statuses.append(
                        f"{module}:{lineno}: status head {head!r} is {canonical!r} in the "
                        f"wrong case; one verdict under two spellings cannot be counted")
                else:
                    statuses.append(
                        f"{module}:{lineno}: status head {head!r} is not in the vocabulary; "
                        f"use an existing term, or adjudicate a new one INTO "
                        f"`empirical_status_vocabulary` rather than beside it")

    for key in sorted(set(verified) & set(entries)):
        malformed.append(f"{key}: appears in both `declarations` and "
                         f"`verified_constants`; two records of one definition can "
                         f"disagree and only one of them would be read")
    for key, entry in sorted(verified.items()):
        if not entry.get("constants"):
            malformed.append(f"{key}: is in `verified_constants` and pins no "
                             f"constants, so it records nothing")
    checked = dict(entries)
    checked.update(verified)

    # A ledger that names a convention it never defines, or a quantity no entry
    # uses, is a ledger nobody has read.  Cheap, and it fires on a typo.
    for key, entry in sorted(entries.items()):
        if entry.get("quantity") not in quantities:
            malformed.append(f"{key}: quantity {entry.get('quantity')!r} is not in `quantities`")
        if entry.get("convention") not in known_conventions:
            malformed.append(f"{key}: convention {entry.get('convention')!r} is not in `conventions`")

    # STALE.  Entries first, then bridges.
    # WHERE IT WENT, not just that it left.  A ledger entry is keyed by FILE PATH,
    # which is exactly what splitting a monolith changes, so every split invalidates
    # every key beneath it: `PortabilityDrift`, `PopulationGeneticsFoundations` and
    # `TransferLearningPGS` each did that, and each time the finding said only that
    # the declaration was "no longer a `def`" in a file it had merely moved out of.
    # Locating it again was a search every time. The declaration index already knows
    # where every name lives, so the finding can say, and the repair becomes one edit.
    # This does NOT weaken the check: a moved entry still FAILS, because a record
    # pointing at the wrong file is a record nobody can trust.
    elsewhere: dict = {}
    for k, n in defs.items():
        elsewhere.setdefault(n, []).append(k.partition("::")[0])
    for key in sorted(checked):
        if key not in defs:
            module, _, name = key.partition("::")
            found = sorted(set(elsewhere.get(name, [])))
            if len(found) == 1:
                whither = f"; it is now in {found[0]} -- repoint the key"
            elif found:
                whither = (f"; the name is in {len(found)} files ({', '.join(found[:3])}"
                           f"{', ...' if len(found) > 3 else ''}) -- say which is meant")
            else:
                whither = "; the name is nowhere in the corpus -- delete the entry"
            if module not in sources:
                stale.append(f"{key}: module {module} is not in the corpus{whither}")
            else:
                stale.append(f"{key}: `{name}` is no longer a `def` in {module}{whither}")
    bridge_edges, bridge_records = set(), 0
    for bridge in ledger.get("bridges", []):
        pair = tuple(bridge.get("between", []))
        thm = bridge.get("theorem", "")
        if len(pair) != 2:
            malformed.append(f"bridge {bridge!r} does not name exactly two conventions")
            continue
        if thm.split(".")[-1] not in theorems:
            stale.append(f"bridge {pair[0]} <-> {pair[1]}: theorem `{thm}` is not in the corpus")
            continue
        bridge_edges.add(pair)
        bridge_records += 1

    # UNLEDGERED.  Only `complete` quantities can produce this finding; an
    # `unscoped` quantity is recorded so a later pass has somewhere to put the
    # work, and it is not allowed to look like coverage it does not have.
    complete = {q: set(spec.get("words", []))
                for q, spec in quantities.items() if spec.get("scope") == "complete"}
    # A quantity may ALSO be scoped over argument names.  A definition that
    # consumes an `fst` is where a convention mismatch does its damage, and being
    # unnamed for it is no protection.
    by_argument = {q: set(spec.get("words", []))
                   for q, spec in quantities.items()
                   if spec.get("argument_scope") == "complete"}
    matched = consumers = 0
    for key, name in sorted(defs.items()):
        words = convention_words(name)
        for quantity, quantity_words in complete.items():
            hit = words & quantity_words
            if not hit:
                continue
            matched += 1
            if key not in entries:
                unledgered.append(
                    f"{key}: carries the `{quantity}` word {sorted(hit)} and has no "
                    f"ledger entry, so which {quantity} it is is stated nowhere a "
                    f"machine can read")
            break
        else:
            for quantity, quantity_words in by_argument.items():
                hit = binders.get(key, set()) & quantity_words
                if not hit:
                    continue
                consumers += 1
                if key not in entries:
                    unledgered.append(
                        f"{key}: takes a `{quantity}` ARGUMENT {sorted(hit)} and has "
                        f"no ledger entry, so which {quantity} a caller must supply "
                        f"is stated nowhere a machine can read")
                break

    # UNBRIDGED.  `inherited` commits to no convention and is excluded: a body
    # that returns whatever it was handed cannot disagree with anything.
    by_module: dict = {}
    for key, entry in entries.items():
        module = key.partition("::")[0]
        conv = entry.get("convention")
        if conv and conv not in ("inherited", "undetermined"):
            by_module.setdefault((module, entry.get("quantity")), set()).add(conv)
    for (module, quantity), present in sorted(by_module.items()):
        spec = quantities.get(quantity, {})
        incompatible = {tuple(sorted(p)) for p in spec.get("incompatible", [])}
        if not incompatible or len(present) < 2:
            continue
        edges = {tuple(sorted(p)) for p in bridge_edges}
        for a, b in convention_connected(present, edges):
            if (a, b) in incompatible:
                unbridged.append(
                    f"{module}: carries both `{a}` and `{b}` for `{quantity}`, which the "
                    f"ledger declares incompatible, and no chain of existing bridge "
                    f"theorems relates them")

    # CONSTANT.
    for key, entry in sorted(checked.items()):
        want = entry.get("constants")
        if want is None or key not in defs:
            continue
        module, _, name = key.partition("::")
        body = convention_body(sources[module], name)
        if body is None:
            continue
        got = sorted(CONVENTION_NUMBER.findall(body))
        if got != sorted(want):
            constants.append(
                f"{key}: ledger records constants {sorted(want)}, body now has {got}"
                + (f"; {entry['note']}" if "note" in entry else ""))

    failures = []
    for label, found, advice in (
        ("`Empirical status:` heads outside the closed vocabulary", statuses,
         "the vocabulary is `empirical_status_vocabulary` in the ledger; a new "
         "verdict belongs IN it, with what it means, not beside it"),
        ("docstrings stating more than one `Empirical status:`", multistatus,
         "there are THREE repairs and they are not interchangeable. If one marker "
         "SUPERSEDES the other, delete the superseded one and keep its evidence as "
         "history. If BOTH are true -- unmeasurable in general, validated on a "
         "slice -- merge them into one `MIXED` marker, because deleting either "
         "half misreports it. If the second is a status being DISCUSSED rather "
         "than asserted, reword it so it is not a bare marker: a scanner cannot "
         "tell quotation from assertion, and neither can a reader who stops at "
         "the first line"),
        ("ledger entries that no longer match the corpus", stale,
         "repoint the entry, or delete it if the declaration is gone for good"),
        ("declarations carrying a ledgered quantity with no ledger entry", unledgered,
         "add an entry naming which convention it uses and where that convention "
         "comes from"),
        ("modules mixing incompatible conventions with nothing relating them", unbridged,
         "prove a bridge theorem and name it in `bridges`, or move one of the "
         "declarations"),
        ("ledgered constants the body no longer carries", constants,
         "if the body is right the ledger is stale and the SOURCE should be "
         "re-read before updating it; that re-reading is the point"),
        ("malformed ledger entries", malformed,
         "fix the ledger; a name it does not define is a name nobody checked"),
    ):
        if found:
            failures.append(f"conventions guard FAILS: {label}: {len(found)}; "
                            f"{advice}")
            failures.extend("    " + x for x in found)

    if failures:
        for line in failures:
            print(line)
        return 1

    undetermined = sum(1 for e in entries.values()
                       if e.get("convention") == "undetermined")
    scoped = sorted(q for q, s in quantities.items() if s.get("scope") == "complete")
    unscoped = sorted(q for q, s in quantities.items() if s.get("scope") != "complete")
    with_constants = sum(1 for e in checked.values() if e.get("constants"))
    print(f"conventions guard passes: {len(entries)} ledger entries over "
          f"{matched} declarations NAMED for a scoped quantity and {consumers} "
          f"that merely CONSUME one, in {len(defs)} corpus definitions; "
          f"{undetermined} of those entries carry `undetermined`, which is "
          f"enumerated debt and not coverage; "
          f"quantities scoped complete: {', '.join(scoped)}; "
          f"registered but unscoped (checked for nothing): "
          f"{', '.join(unscoped) or 'none'}; "
          f"{len(verified)} source-verified constant records outside those "
          f"families; {with_constants} entries pin a constant multiset; "
          f"{bridge_records} bridge theorem(s) present over "
          f"{len(bridge_edges)} distinct convention edge(s); "
          f"{status_seen} `Empirical status:` heads all inside a closed "
          f"vocabulary of {len(vocabulary)} terms")
    return 0

# ======================================================================================
# LEDGER: the simulation-coverage verdict record against the docstrings
# ======================================================================================
#
# WHAT THIS CATCHES, and why it is a guard rather than a habit.
#
# Coverage in this corpus is a DOCSTRING property -- a definition counts as
# measured when its own `Empirical status:` line says so -- while the evidence
# lives in `validation/empirical/simcov/`, in sixty-odd battery result
# files that nothing read.  Two things follow, and both happened:
#
#   * batteries ran AHEAD of the docstrings.  Definitions carried a real verdict
#     and still read UNTESTED, so the coverage number understated what had been
#     established and nobody could tell which.
#   * docstrings ran AHEAD of the batteries.  Definitions read VALIDATED off a
#     MATCH that no competing formula was ever run against, which is not a
#     validation: an oracle algebraically pinned to the body under test cannot
#     reject anything, so agreement with it is arithmetic.  `driftVariance`,
#     `haplotypeHomozygosity` and `multiTraitEffectiveSampleSize` were each
#     banked that way.
#
# `simcov/ledger.json` is the committed record, emitted by `simcov/ledger.py`
# from the battery results.  THE COMPETITOR GATE IS APPLIED AT EMIT TIME: a
# corpus row that agrees with its oracle while no competing formula was rejected
# on the same cells is recorded as UNINFORMATIVE, not MATCH.  That is why rule 3
# below reads as though it can never fire -- it fires only if someone hand-edits
# the ledger, which is exactly the hole a generated-and-committed file has.
#
# The guard is deterministic, needs no simulator, no numpy and no network, and
# anchors everything on DECLARATION NAMES.  Nothing here pins a line number:
# `empirical/extract/test_parser.py` is a standing demonstration of what happens
# when a check does.
#
# THE RULES, all at budget 0:
#
#   1. A docstring citing a battery FILE the ledger has never seen.  A renamed
#      or deleted battery leaves a citation pointing at nothing, and a citation
#      that cannot be followed is worse than none: it reads as evidence.
#   2. A docstring that cites a battery whose results are STALE -- the battery's
#      source is newer than the results file, so the numbers quoted came from a
#      source that no longer exists.  The same rule covers INCOMPLETE: a battery
#      whose run had a group raise wrote its results file anyway, carrying
#      whatever verdicts had already been recorded, and the declarations in the
#      group that died simply had no row.  That reads as "this battery does not
#      measure that" rather than as "this battery failed to", which is the
#      difference between a gap and a silent one.  `battery_core.run_groups`
#      records the failure into the results file and `ledger.py` puts it in the
#      freshness field.
#   3. A ledger record banking agreement with no competitor rejected.
#   4. A definition whose docstring cites a battery while the ledger holds both
#      an agreeing and a disagreeing verdict for it, with no adjudication.  A
#      definition cannot be both validated and falsified; one of the two designs
#      is wrong and the docstring has to say which.
#
# REPORTED, NOT GATED, and named as outstanding work rather than given a budget:
# definitions whose docstring asserts agreement while every ledger record for
# them disagrees.  These are real findings -- each is either a stale docstring
# or a stale record -- but a verdict is evidence about the FORMULA a battery
# transcribed, and when a body is corrected the old record becomes history.
# Deciding that automatically needs the transcription and the Lean body to be
# comparable, and they are not: `sum beta_i^2` and `∑ i : Fin m, β i ^ 2` are
# the same formula and share no text.  Until each is adjudicated by hand the
# count is printed in full, with names, so it cannot be mistaken for zero.

LEDGER_PATH = CORPUS / "validation" / "empirical" / "simcov" / "ledger.json"

# The verdicts that assert the corpus body agrees with a measurement, and those
# that assert it disagrees.  Everything else -- UNINFORMATIVE, SELF-TEST, VOID,
# NO POWER, LEAD -- asserts nothing and is not evidence in either direction.
LEDGER_AGREES = {"MATCH", "VALIDATED"}
LEDGER_DISAGREES = {"FALSIFIED", "REFUTED"}
# MEASURED IS NOT IN HERE, BY THE CLOSED VOCABULARY'S OWN DEFINITION OF IT:
# "A number was obtained; whether it confirms the body is stated in the prose."
# A declaration whose head is MEASURED has not asserted agreement, so pairing it
# against a disagreeing ledger row reports a docstring for saying exactly what
# the term means. `liabilitySpecificity` and `effectTurnoverR2Loss` were both
# reported that way, and both read "MEASURED, and what was measured is ..."
DOC_ASSERTS_AGREEMENT = {"VALIDATED", "TESTED"}
DOC_ASSERTS_DISAGREEMENT = {"FALSIFIED", "REFUTED"}

# A CITATION, NOT A DESCRIPTION OF THE CITATION FORMAT. The negative lookahead
# drops an ALL-CAPS metavariable stem, which is how this corpus writes a
# placeholder: `Meta/DocConvention.lean` -- the file that DEFINES what a battery
# citation looks like -- says "the opening of a battery citation,
# `simcov/battery_NAME.py`", and the ledger guard read both of its explanatory
# docstrings as citing a battery nobody has run. That is the same mistake the
# `Empirical status:` scan already carries a discriminator for: a file
# documenting a convention states the convention, and a scanner that cannot tell
# a mention from a use reports the documentation as the defect.
#
# Every battery in the harness is named in lower case (`bulk41`, `strat02`,
# `sved01`, `falsrepair_c2`), so requiring one lower-case character costs no real
# citation and catches any placeholder written the way this corpus writes them.
BATTERY_CITE = re.compile(r"simcov/battery_(?![A-Z][A-Z0-9_]*\.py)"
                          r"([A-Za-z0-9_]+)\.py")
EMPIRICAL_STATUS = re.compile(r"Empirical status:\s*[*_ ]*([A-Za-z_]+)")
STATUS_WORDS = ("UNTESTED", "VALIDATED", "FALSIFIED", "DERIVED", "MEASURED",
                "VACUOUS", "CONVENTION", "TESTED", "REFUTED")


def _ledger_docstrings():
    """[(declaration, file, docstring)] for every top-level `def`.

    Anchored at column 0 and on the same file set as `ident_lean_files`, so this
    guard and the rest of check.py disagree about nothing.  A second, private
    idea of what counts as a definition is how `empirical/extract` came to parse
    zero of them and exit 0.
    """
    out = []
    for path in ident_lean_files():
        try:
            raw = Path(path).read_text(errors="ignore")
        except OSError:
            continue
        lines = raw.split("\n")
        for i, line in enumerate(lines):
            m = re.match(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)", line)
            if not m:
                continue
            j = skip_attribute_block(lines, i - 1)
            if j < 0 or not lines[j].rstrip().endswith("-/"):
                continue
            end = j
            while j >= 0 and "/--" not in lines[j]:
                if "/-!" in lines[j] or ("-/" in lines[j] and j != end):
                    j = -1
                    break
                j -= 1
            if j < 0:
                continue
            out.append((m.group(1).split(".")[-1], Path(path).name,
                        "\n".join(lines[j:end + 1])))
    return out


def run_ledger() -> int:
    if not LEDGER_PATH.exists():
        print(f"ledger guard: {LEDGER_PATH} is absent; regenerate it with "
              f"`python3 validation/empirical/simcov/ledger.py "
              f"<results-dir>`")
        return 1
    try:
        led = json.loads(LEDGER_PATH.read_text())
    except (OSError, ValueError) as exc:
        print(f"ledger guard: {LEDGER_PATH} is unreadable: {exc}")
        return 1

    records = led.get("records", [])
    corpus_rows = [r for r in records if r.get("role") == "corpus"]
    batteries = {r.get("battery") for r in records}
    freshness = {r.get("battery"): r.get("freshness", "") for r in records}
    by_decl = {}
    for r in corpus_rows:
        by_decl.setdefault(r["declaration"], []).append(r)

    adjudicated = set(led.get("adjudications", {}))

    data_only = {r.get("battery") for r in records if r.get("role") == "data"}
    dangling, stale_cite, uncompeted, unadjudicated, contradicted = \
        [], [], [], [], []
    cites_data_only = []

    for name, fname, doc in _ledger_docstrings():
        cited = set(BATTERY_CITE.findall(doc))
        for bat in sorted(cited):
            if bat not in batteries:
                dangling.append(f"{name} ({fname}) cites simcov/battery_{bat}.py, "
                                f"which the ledger has never seen")
            elif "STALE" in freshness.get(bat, "") \
                    or "INCOMPLETE" in freshness.get(bat, ""):
                stale_cite.append(f"{name} ({fname}) cites simcov/battery_{bat}.py, "
                                  f"whose results are {freshness[bat]}")
            elif bat in data_only:
                cites_data_only.append(
                    f"{name} ({fname}) cites simcov/battery_{bat}.py, which "
                    f"emits raw numbers and calls record() nowhere, so it "
                    f"carries evidence but no verdict")
        heads = {r["verdict"] for r in by_decl.get(name, ())}
        if cited and (heads & LEDGER_AGREES) and (heads & LEDGER_DISAGREES) \
                and name not in adjudicated:
            unadjudicated.append(
                f"{name} ({fname}) has both {sorted(heads & LEDGER_AGREES)} and "
                f"{sorted(heads & LEDGER_DISAGREES)} in the ledger and cites a "
                f"battery, with no adjudication saying which design is wrong")
        # THE HEAD, NOT EVERY CAPITAL WORD IN THE PARAGRAPH. This scanned the
        # whole text after `Empirical status:` for any member of STATUS_WORDS,
        # and these paragraphs are mostly PROSE ABOUT COMPETITORS -- a docstring
        # reading "VALIDATED as a rate, FALSIFIED as an exact form" was reported
        # as asserting agreement while the ledger disagreed, when it had already
        # said the same thing the ledger says. `conventions` learned this rule
        # first and records why: applied to the whole status text it produced 99
        # findings, none of them defects.
        #
        # The first word of the head, so that "VALIDATED after correction" and
        # "VALIDATED as a rate" are still read as claiming VALIDATED. What
        # changes is only that a term appearing further down, about a rival or a
        # superseded form, no longer counts as this declaration's own verdict.
        k = doc.rfind("Empirical status:")
        head = (convention_status_head(doc[k + len("Empirical status:"):])
                if k >= 0 else "")
        claimed = head.split()[0] if head.split() else ""
        # AN ADJUDICATION IS THE HUMAN THIS FINDING ASKS FOR. The message says
        # telling a stale docstring from a stale record "needs a human because a
        # transcription and a Lean body share no text", and `adjudications.json`
        # is where that human writes the answer down. The sibling check three
        # lines up already skips adjudicated declarations; this one did not, so
        # `ancestryRecalibratedR2` -- whose entry says the surviving designs
        # locate a REGIME rather than a defect, which is what its docstring then
        # says -- was reported as still needing the decision it carries.
        if claimed in DOC_ASSERTS_AGREEMENT and (heads & LEDGER_DISAGREES) \
                and not (heads & LEDGER_AGREES) and name not in adjudicated:
            contradicted.append(
                f"{name} ({fname}) docstring heads its status {claimed!r} while "
                f"every ledger record for it says "
                f"{sorted(heads & LEDGER_DISAGREES)}")

    for r in corpus_rows:
        if r["verdict"] in LEDGER_AGREES and not r.get("competitors_rejected"):
            uncompeted.append(
                f"{r['declaration']} [{r['battery']}] banks {r['verdict']} with "
                f"no competing formula rejected on the same cells; "
                f"simcov/ledger.py records that as UNINFORMATIVE, so this row "
                f"was hand-edited")

    bad = []
    for label, found, advice in (
        ("docstring citations to a battery the ledger has never seen",
         dangling, "re-emit the ledger, or drop the citation"),
        ("docstring citations to a battery whose results are stale or incomplete",
         stale_cite, "re-run that battery so its results match its source and "
                     "no group raised, then re-emit the ledger"),
        ("ledger rows banking agreement with no competitor rejected",
         uncompeted, "re-emit the ledger with simcov/ledger.py; the gate is "
                     "applied at emit time and cannot be satisfied by editing"),
        ("definitions with contradictory ledger verdicts and no adjudication",
         unadjudicated, "add an `adjudications` entry naming the authoritative "
                        "battery and saying why the other design is wrong"),
    ):
        if found:
            bad.append(f"{label}: {len(found)}, budget 0; {advice}")
            bad.extend("    " + x for x in sorted(set(found)))

    if bad:
        for line in bad:
            print(line)
        return 1

    verdict_census = {}
    for r in corpus_rows:
        verdict_census[r["verdict"]] = verdict_census.get(r["verdict"], 0) + 1
    print(f"ledger guard passes: {len(records)} records over {len(batteries)} "
          f"batteries, {len(corpus_rows)} of them about corpus bodies; "
          f"verdicts after the emit-time competitor gate: "
          + ", ".join(f"{k}={v}" for k, v in
                      sorted(verdict_census.items(), key=lambda kv: -kv[1])))
    if cites_data_only:
        print(f"\nREPORTED, NOT GATED -- {len(cites_data_only)} citation(s) "
              f"resolve to a battery that emits no verdict records. The "
              f"citation is followable and the numbers are real; what is "
              f"missing is a `record()` call, so nothing states what the run "
              f"concluded:")
        for line in sorted(set(cites_data_only)):
            print("    " + line)
    if contradicted:
        print(f"\nREPORTED, NOT GATED -- {len(contradicted)} definitions assert "
              f"agreement while every ledger record for them disagrees. Each is "
              f"either a stale docstring or a record against a body that has "
              f"since been corrected, and telling those apart needs a human "
              f"because a transcription and a Lean body share no text. This "
              f"count is printed in full rather than carried as a budget:")
        for line in sorted(set(contradicted)):
            print("    " + line)
    return 0


# ======================================================================================
# CORE-EMPIRICS -- the load-bearing layer gets the strictest standard, not the same one
# ======================================================================================
#
# `Descent/Core/` is depth 0-1: `Core.Ratios` has 46 consumers, `Core.Fst` 22,
# and `Core.PopGenParameters.fstEquilibrium` is the input to
# `Core.Moments.deployedR2` and so to every demography-to-metric theorem in the
# corpus.  A wrong body in a leaf is one wrong claim.  A wrong body here is the
# premise of the corpus's headline chain.
#
# The `ledger` guard is the right standard for a leaf and the wrong one for
# this layer.  It reports its two sharpest findings -- a docstring asserting
# agreement against a disagreeing record, a citation to a battery that emits no
# verdict -- as REPORTED, NOT GATED, because telling a stale docstring from a
# corrected body needs a human and a budget pinned to the count would be worse
# than none.  That reasoning is sound across 2164 definitions.  Across the
# seven files in `Core/` it is not: the population is small enough to hold at
# zero by hand, and the cost of a silent one is the whole chain.
#
# WHAT THIS GUARD ACTUALLY CAUGHT, and why the rules are these three rather
# than "read the status and think about it".  `Core.PopGenParameters.
# fstEquilibrium` carried `Empirical status: NOT AN EMPIRICAL CLAIM`, inherited
# from the module's reading that a parameter record asserts nothing.  That
# reading is right for the FIELDS and wrong for a LAW computed from them, and
# the ledger held four corpus rows against the name: one FALSIFIED (`bulk38`,
# against the superseded body `1/(1 + theta + bigM)`) and two MATCH (`bulk38b`
# at 1.03 sems, `falsrepair` at 1.10, both against the body actually in the
# file).  Every existing guard passed.  `ledger`'s `contradicted` rule could not
# fire because the docstring asserted no agreement to contradict, and
# `conventions` checks that the head is IN the vocabulary, never that it is the
# RIGHT term.  A declaration that denies being an empirical claim is invisible
# to a guard that reads what declarations claim.
#
# So the three rules below are about the ABSENCE of a claim, which is what the
# other guards structurally cannot see:
#
#   SILENT     a disagreeing corpus row whose battery the docstring never
#              names.  Acknowledgement means naming the run, not gesturing at
#              it: `adjudications.json` settling the row is not enough, because
#              a reader of the Lean never opens that file.
#   UNMARKED   a measured body with no `Empirical status:` of its own.  A
#              module-level `## Empirical status` section is the right host for
#              a file of shapes, and the wrong one for the single law in that
#              file that is on trial.
#   DENIED     a measured body whose status head says no measurement can bear
#              on it.  The row exists; the head says it cannot.
#
# SCOPE IS BY NAME AND BY PATH, because Core's surface is not its directory.
# `Descent.Core.PopGenParameters.migrationSharedBoostAt` is a Core declaration
# housed in `Portability/PortabilityDrift/Generational.lean` under a `_root_.`
# prefix, it is FALSIFIED at 15.61 sems, and a path-scoped guard would not look
# at it.  It passes -- its docstring names `simcov/battery_bulk55.py` and says
# FALSIFIED -- which is the point: the rule is satisfiable, and it is satisfied
# by the declarations that already did the work.

CORE_PATH = "Descent/Core/"
CORE_NAMESPACE = "Descent.Core."

# Heads asserting that nothing measurable is at stake.  A corpus row carrying a
# real verdict is a measurement that bore on the body, so these are refuted by
# the row's existence.  `VACUOUS`, `AN IDENTITY` and `NOT TESTED BY THE DESIGN
# THAT LOOKED LIKE IT WAS` are NOT here: each describes an existing measurement
# honestly rather than denying it, and each is the correct head for a row that
# could not have failed.
CORE_DENIES_MEASUREMENT = {
    "NOT AN EMPIRICAL CLAIM",
    "NOT EMPIRICALLY TESTABLE",
    "EXACT BY CONSTRUCTION",
    "THIS IS THE MODEL",
    "UNTESTED",
}


def _core_docstrings():
    """[(qualified name, file, docstring)] for every `def` on Core's surface.

    Same scan as `_ledger_docstrings` -- column 0, same file set -- and it keeps
    the QUALIFIED name, which that one discards.  A second idea of what a
    definition is would put this guard and the ledger guard into disagreement
    about which declarations exist, which is the failure `_ledger_docstrings`
    records in its own docstring.
    """
    out = []
    for path in ident_lean_files():
        rel = str(path).replace("\\", "/")
        in_core_dir = CORE_PATH in rel
        try:
            raw = Path(path).read_text(errors="ignore")
        except OSError:
            continue
        lines = raw.split("\n")
        for i, line in enumerate(lines):
            m = re.match(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)", line)
            if not m:
                continue
            qualified = m.group(1)
            if not (in_core_dir or CORE_NAMESPACE in qualified):
                continue
            j = skip_attribute_block(lines, i - 1)
            if j < 0 or not lines[j].rstrip().endswith("-/"):
                out.append((qualified, Path(path).name, ""))
                continue
            end = j
            while j >= 0 and "/--" not in lines[j]:
                if "/-!" in lines[j] or ("-/" in lines[j] and j != end):
                    j = -1
                    break
                j -= 1
            if j < 0:
                out.append((qualified, Path(path).name, ""))
                continue
            out.append((qualified, Path(path).name, "\n".join(lines[j:end + 1])))
    return out


def run_core_empirics() -> int:
    if not LEDGER_PATH.exists():
        print(f"core-empirics guard CANNOT RUN: {LEDGER_PATH} is absent. The "
              f"ledger is the only record of what has been measured, so with no "
              f"ledger there is nothing to hold Core against; regenerate it with "
              f"`python3 validation/empirical/simcov/ledger.py <results-dir>`.")
        return 1
    try:
        led = json.loads(LEDGER_PATH.read_text())
    except (OSError, ValueError) as exc:
        print(f"core-empirics guard CANNOT RUN: {LEDGER_PATH} is unreadable: {exc}")
        return 1

    # Rows about the CORPUS body only.  A competitor row is a formula the corpus
    # does not have, and a `data` row states no verdict; neither is evidence
    # about a declaration in this layer.
    rows = {}
    for r in led.get("records", []):
        if r.get("role") == "corpus":
            rows.setdefault(r["declaration"], []).append(r)

    silent, unmarked, denied = [], [], []
    covered = []

    for qualified, fname, doc in _core_docstrings():
        short = qualified.split(".")[-1]
        # JOINED ON THE SHORT NAME, deliberately, and a tiebreak on the file
        # the battery declared was tried here and REVERTED. It removed a
        # `tau` finding that was true: `PopGenParameters.tau` and
        # `EvolutionaryParameters.tau` are both `t_div / (2 Ne)`, so
        # battery_bulk19's measurement of that scaling bears on both, and the
        # Core declaration calling itself NOT AN EMPIRICAL CLAIM was the defect
        # the guard is for. Two declarations with one short name are usually one
        # quantity written over two records in this corpus, not a collision, and
        # a filename test cannot tell those apart. The ledger now carries
        # `lean_file` regardless, because a row that cannot say what it is about
        # is worth less than one that can.
        mine = rows.get(short, [])
        # Only rows that said yes or no.  UNINFORMATIVE, NO POWER, LEAD and
        # SELF-TEST assert nothing, and a declaration is not obliged to answer
        # a run that concluded nothing.
        verdicts = {r["verdict"] for r in mine}
        spoke = verdicts & (LEDGER_AGREES | LEDGER_DISAGREES)
        if not spoke:
            continue
        covered.append(f"{short} ({fname}): {', '.join(sorted(verdicts))}")

        cited = set(BATTERY_CITE.findall(doc))
        for r in mine:
            if r["verdict"] in LEDGER_DISAGREES and r["battery"] not in cited:
                sems = r.get("worst_sems")
                where = f" at {sems:.2f} sems" if isinstance(sems, float) else ""
                silent.append(
                    f"{short} ({fname}) is {r['verdict']}{where} in "
                    f"simcov/battery_{r['battery']}.py and its docstring never "
                    f"names that battery")

        m = CONVENTION_STATUS.search(doc)
        if not m:
            unmarked.append(
                f"{short} ({fname}) has {', '.join(sorted(spoke))} in the ledger "
                f"and carries no `Empirical status:` of its own")
            continue
        head = convention_status_head(m.group(1))
        if head in CORE_DENIES_MEASUREMENT:
            denied.append(
                f"{short} ({fname}) says {head!r} while the ledger holds "
                f"{', '.join(sorted(spoke))} against it from "
                f"{', '.join(sorted(r['battery'] for r in mine))}")

    bad = []
    for label, found, advice in (
        ("Core declarations with an unacknowledged FALSIFIED ledger row",
         silent, "cite the battery in the docstring and say what it rejected -- "
                 "if it rejected a body this one has since replaced, say that, "
                 "and name the run that put the current body back on those cells"),
        ("Core declarations that have been measured and state no status",
         unmarked, "give the declaration its own `Empirical status:` line; the "
                   "module-level section covers the file's shapes, not the law "
                   "in it that is on trial"),
        ("Core declarations denying that any measurement can bear on them, "
         "against a ledger row that did",
         denied, "replace the head with the verdict the rows carry, or, if the "
                 "rows are about a different quantity, say which and use "
                 "`NOT TESTED BY THE DESIGN THAT LOOKED LIKE IT WAS`"),
    ):
        if found:
            bad.append(f"{label}: {len(found)}, budget 0; {advice}")
            bad.extend("    " + x for x in sorted(set(found)))

    if bad:
        for line in bad:
            print(line)
        print(f"core-empirics guard FAILS. This layer is depth 0-1 and the "
              f"corpus's headline chain reads through it, so a silent verdict "
              f"here is not one unstated claim, it is an unstated premise.")
        return 1

    print(f"core-empirics guard passes: {len(covered)} declaration(s) on Core's "
          f"surface carry a corpus verdict, every FALSIFIED row among them names "
          f"its battery in the Lean, and none denies being measurable:")
    for line in sorted(covered):
        print("    " + line)
    return 0


# ======================================================================================
# SHAPE
# ======================================================================================

# WHAT THESE FIVE GUARDS ARE FOR, and why they are a family.
#
# Every structural repair this corpus has shipped was found the same way: an audit
# read the tree, named a defect, a person fixed it by hand, and one release later
# the same defect was back somewhere else.  `Coalescent` was an island in one
# release; `Pangenome` is an island in this one.  A directory was split by reading
# order once and the split was undone; nine directories are split by reading order
# now.  A metric got a second entry point taking its demography as loose reals, the
# parameter record was introduced to stop that, and `deployedR2FromIsland` sits
# beside `deployedR2` today.
#
# The recurrence is not carelessness.  It is that the corpus is organised by
# NARRATIVE -- by the order a person would read it in -- and a narrative order is
# invisible to a build.  `A` imports `B` because `B` was written first, and Lean is
# perfectly happy: an unused import compiles.  Nothing anywhere fails, so the only
# instrument that has ever caught it is a person re-reading the tree, and a person
# re-reading the tree is exactly the mechanism the corpus's own root rule forbids
# relying on:
#
#     When two places must agree, make one of them call the other; a note
#     explaining why they must agree is not a mechanism.
#
# `validation/code/architecture.py` measures these shapes already and prints them.
# Printing is what a note does.  These five guards are the same measurements wired
# to an exit code, which is what makes them a mechanism.
#
# THEY IMPORT `architecture.py` RATHER THAN RE-DERIVING ANYTHING.  Three earlier
# scripts independently re-derived "which files are the corpus" and disagreed, and
# this file's own header records what that cost.  So the import graph, the
# declaration index and the comment stripper come from `architecture.py`, and the
# only thing that lives here is the threshold and the failure.  `architecture.ROOT`
# is patched to `CORPUS` before use so `DESCENT_CORPUS` still redirects these
# guards at a fixture; without that patch they would read the real repository no
# matter what the environment said, and a guard that cannot be pointed at a planted
# defect has never been shown to fire.
#
# CALIBRATION.  All five land nonzero on the corpus as it stands, which is the
# evidence that each fires: a guard whose clean report has never been contradicted
# is indistinguishable from a guard that does nothing.  They are DIAGNOSTIC for
# exactly that reason and no other -- the findings are real and the fixes are in
# flight.  Each entry in `GUARDS` names what has to land before it flips.

# The depth limit.  Twelve is one rung for each of the corpus's eleven top-level
# directories, plus one.  That is the depth a tree gets from its own layer contract
# -- `Core < Foundations < Coalescent < PopGen < Portability < Decision < Program`,
# with `Blindness`, `Conditionals`, `Pangenome` and `Spectral` hanging off it -- so
# a corpus whose imports run downward through the layers and no further can meet
# it.  Anything above 12 is modules stacked on each other INSIDE a layer, which is
# the shape a reading order makes and a dependency order does not.
SHAPE_DEPTH_LIMIT = 12

SHAPE_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'₀-₉]*")
# Where a declaration block ends: the head of the next one.
SHAPE_DECL_STOP = re.compile(
    r"^\s*(noncomputable |def |abbrev |theorem |lemma |structure |inductive "
    r"|instance |class |end |namespace |section |open |variable |@\[)")
SHAPE_THEOREM = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([\w.'₀-₉]+)(.*?):=", re.S | re.M)

# The two spine thresholds.  Both are the audit's, and both are far from where the
# corpus stands; see `run_shape_spine` for how each is counted.
SHAPE_REUSE_PCT = 20.0
SHAPE_SPINE_THEOREMS = 80

# A function of four or more BARE reals is a demography spelled out longhand.
# Three is not: `deployedR2FromTau (V_A V_E tau : ℝ)` is a formula in its own
# coordinates and takes no population history at all, while
# `deployedR2FromIsland (Ne m μ nDemes V_A V_E : ℝ)` takes four fields of
# `PopGenParameters` as loose arguments and rebuilds the record's job by hand.
SHAPE_RAW_ARITY = 4


@functools.lru_cache(maxsize=1)
def _shape_corpus():
    """`(raw, code, graph, decls, architecture)` for the corpus.

    Cached because five guards want the same objects and the walk is the expensive
    part of all of them.  The module itself is handed back so a guard can reach a
    measurement `architecture.py` already defines rather than writing a second one.
    """
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import architecture as arch

    # See the section header: the module computes its own root from `__file__`,
    # which would make every guard below blind to `DESCENT_CORPUS`.
    arch.ROOT = str(CORPUS)
    arch.LEAN_ROOT = str(CORPUS / "Descent")
    raw, code = arch.load()
    return raw, code, arch.import_graph(raw), arch.declarations(code), arch


def _shape_is_toc(mod: str, graph, decls) -> bool:
    """The corpus root, or a module that IS its directory's table of contents.

    A table of contents declares nothing and imports every module under its
    directory, and its edges therefore carry no dependency: they are what `lake
    build` needs to reach the tree, not what a proof rests on.  Counting them
    breaks every measurement below in the same way.  Depth gains rungs no proof
    rests on.  The weak-component count is pinned at one forever, because a head is
    adjacent to every module in its directory whether or not anything in that
    directory is connected to anything else -- `Pangenome`'s two modules are joined
    to the corpus by `Descent/Pangenome.lean` and by nothing else, and with heads
    counted that reads as connected.

    THE TEST IS THE `heads` CONTRACT, not the path shape, and the difference is
    load-bearing.  Eight modules in this corpus have a directory beside them and
    declare nothing, which is what a head looks like from the outside.  Three of
    them -- `TrafficInvariantSeparation`, `MetricSpecificPortability`,
    `PortabilityDrift` -- import their whole directory and are heads.  The other
    five import ONE module out of five, or one out of eight: they are not tables of
    contents, they are links in exactly the chains `shape-chains` reports, and
    excluding them because they resemble a head would hide the defect inside the
    exclusion.  A module earns the exclusion by satisfying the contract, and the
    day one of the five starts importing its directory it earns it automatically.

    `Descent.lean` is the one special case: it declares thirty things, so it fails
    the contract, but it is the build entry point and imports only the eleven heads.
    Its edges reach nothing but tables of contents, so it can add a rung above them
    and nothing else.
    """
    if mod == "Descent":
        return True
    directory = CORPUS.joinpath(*mod.split("."))
    if not directory.is_dir():
        return False
    if decls.get(mod):
        return False
    under = {str(p.relative_to(CORPUS))[:-len(".lean")].replace(os.sep, ".")
             for p in directory.rglob("*.lean")}
    return bool(under) and under <= graph.get(mod, set())


def _shape_graph_without_toc():
    """The import graph with the tables of contents deleted, not merely skipped."""
    _raw, _code, graph, decls, _arch = _shape_corpus()
    toc = {m for m in graph if _shape_is_toc(m, graph, decls)}
    return {m: {d for d in graph[m] if d not in toc}
            for m in graph if m not in toc}


def _shape_depths(graph):
    """Longest path from a leaf, per module, iteratively so a cycle cannot hang us."""
    depth = {}

    def go(mod, seen):
        if mod in depth:
            return depth[mod]
        if mod in seen:
            return 0
        d = 0
        for dep in graph.get(mod, ()):
            d = max(d, go(dep, seen | {mod}) + 1)
        depth[mod] = d
        return d

    for mod in graph:
        go(mod, frozenset())
    return depth


def run_shape_depth() -> int:
    """No module may sit more than `SHAPE_DEPTH_LIMIT` imports above a leaf.

    WHAT THIS CAUGHT.  The audit that asked for this guard measured a longest
    import chain of 38 modules at depth 37, and the top of it was not a deep result
    resting on deep machinery.  It was a sequence: `PortabilityDrift.Definitions` ->
    `ClosedPopulationRegime` -> `PresentDayMetrics` -> `Generational` ->
    `PresentDayMoments` -> `MutationDrift` -> `MigrationDrift` -> ... , each file
    importing the one written before it.  `Generational` did not use a single
    declaration of `PresentDayMetrics`; it used twenty-five of `PopGen.DGP`, which
    it did not import, and reached them through the chain.  The depth was a reading
    order compiled into the build graph.

    WHY DEPTH AND NOT SOMETHING VAGUER.  "Files should be small" and "directories
    should be shallow" are not checkable and would fire on the whole corpus.  Depth
    is checkable, it is exactly the quantity a narrative order inflates and a
    dependency order does not, and it is the one number that cannot be brought down
    by moving files or renaming them: the only way down is for a module to import
    what it uses.

    Measured with the tables of contents removed -- see `_shape_is_toc` for which
    modules earn that and why resembling a head does not.  The chain the guard
    prints is the actionable object; the count of modules over the limit is not,
    because every one of them is over it on account of some chain.
    """
    graph = _shape_graph_without_toc()
    depth = _shape_depths(graph)
    if not depth:
        print("shape-depth guard CANNOT RUN: no Lean modules found under "
              f"{CORPUS / 'Descent'}")
        return 1

    worst = max(depth.values())
    over = sorted(((depth[m], m) for m in depth if depth[m] > SHAPE_DEPTH_LIMIT),
                  reverse=True)

    if worst > SHAPE_DEPTH_LIMIT:
        # The chain, not the count, is the actionable object: the fix is an edit to
        # some module ON it, and a bare number names none of them.
        top = max(sorted(depth), key=lambda m: depth[m])
        chain, cur = [top], top
        while graph.get(cur):
            cur = max(sorted(graph[cur]), key=lambda d: depth[d])
            chain.append(cur)
        print(f"deepest import chain: {len(chain)} modules, depth {worst}, "
              f"limit {SHAPE_DEPTH_LIMIT}")
        for m in chain:
            print(f"    {depth[m]:>3}  {m}")
        print(f"modules above the limit: {len(over)}, budget 0; for each link on "
              f"the chain, check whether the module below it is actually used -- "
              f"`--only shape-chains` names the ones that are not -- and import "
              f"what the module names instead of the file that precedes it")
        print(f"shape-depth guard FAILS: depth {worst} exceeds {SHAPE_DEPTH_LIMIT}. "
              f"A chain of {len(chain)} modules is a reading order compiled into "
              f"the build graph, and every module on it must be rebuilt when the "
              f"bottom one changes, whether or not it uses anything from it.")
        return 1

    print(f"shape-depth guard passes: {len(depth)} modules, deepest sits {worst} "
          f"imports above a leaf, limit {SHAPE_DEPTH_LIMIT}")
    return 0


def run_shape_chains() -> int:
    """A module's one internal import may not be a sibling it uses nothing from.

    WHAT THIS CAUGHT.  Thirty-eight modules import exactly one thing from this
    corpus, that one thing is a file in their own directory, and they name not a
    single declaration it makes.  `Coalescent.Beta` imports `Coalescent.Lambda` and
    uses nothing from it.  `PortabilityDrift.Generational` imports
    `PortabilityDrift.PresentDayMetrics`, uses nothing from it, and uses twenty-five
    declarations of `PopGen.DGP`.  `PopulationGeneticsFoundations` has six such
    files in a row, each importing its predecessor: the directory is a chapter list.

    WHY THESE RULES RATHER THAN "NO UNUSED IMPORTS".  Lean imports are transitive,
    so a module may legitimately import `X` to reach a name that `X`'s own
    dependency declares -- `architecture.py` reports 149 imports naming nothing used
    and deliberately does not gate them, because seven removed from
    `Foundations/Conventions` on that reasoning had to be put back.  Three
    conditions together take the population from 149 to 38 and make every one of
    them a real finding:

      * EXACTLY ONE internal import.  A module with several imports is expressing
        some dependency structure, right or wrong.  A module with one is expressing
        an ordering.
      * The import is a SIBLING, in the same directory.  A single import that
        crosses directories is a real dependency on another layer.  A single import
        of the file next to you is where you were in the manuscript.
      * It names NOTHING the sibling declares.  This is what rules out the
        legitimate case, and it is why the guard prints where the symbols the
        module DOES name actually live: that module is the import it wanted.

    The fix is never to delete the import -- that breaks the build, because the
    sibling is the conduit.  It is to import the modules named below it directly,
    after which the sibling is either used or genuinely removable.

    A DIRECTORY-HEAD EDGE IS EXEMPT, and the exemption is deliberate rather than a
    side effect.  A module whose one import is its own directory head -- today
    `Program/OpenQuestions` and `Portability/PortabilityBounds`, both importing
    `Portability/PortabilityDrift` -- looks exactly like the defect above and is
    not one: the head carries the directory's whole external import surface, so
    that edge is load-bearing until each module under it has been given its own
    external import list.  Six such edges were knowingly left in `PortabilityDrift`
    and `MetricSpecificPortability` during the chain repair, on that reasoning.

    Two independent things keep them out, and both are load-bearing because either
    one alone would be a rule someone could quietly break.  A head sits one level
    UP from the modules under it, so it is never a sibling and the second condition
    rejects it.  And `_shape_graph_without_toc` deletes heads outright, so a module
    whose only import was its head has zero imports in the graph this reads and
    fails the first condition too.  If the sibling test is ever loosened, the second
    protection still holds; do not remove both.
    """
    _raw, code, _graph, decls, _arch = _shape_corpus()
    graph = _shape_graph_without_toc()

    reach, findings = {}, []

    def above(mod, seen):
        if mod in reach:
            return reach[mod]
        if mod in seen:
            return set()
        out = set()
        for dep in graph.get(mod, ()):
            out.add(dep)
            out |= above(dep, seen | {mod})
        reach[mod] = out
        return out

    for mod in sorted(graph):
        deps = graph[mod]
        if len(deps) != 1:
            continue
        sibling = next(iter(deps))
        if mod.rsplit(".", 1)[0] != sibling.rsplit(".", 1)[0]:
            continue
        theirs = {n for _kind, n in decls.get(sibling, ())}
        mine = set(SHAPE_IDENT.findall(code.get(mod, "")))
        if theirs & mine:
            continue
        wanted = collections.Counter()
        for up in above(sibling, frozenset()):
            for _kind, n in decls.get(up, ()):
                if n in mine:
                    wanted[up] += 1
        if wanted:
            where = "; ".join(f"{n} from {m}" for m, n in wanted.most_common(3))
            findings.append(f"{mod}\n        imports only {sibling}, and names "
                            f"nothing it declares; it names {where}")
        else:
            findings.append(f"{mod}\n        imports only {sibling}, and names "
                            f"nothing it declares, nor anything reachable through it")

    if findings:
        print(f"modules whose one internal import is an unused sibling: "
              f"{len(findings)}, budget 0; import the module whose declarations the "
              f"file actually names, then the sibling is used or removable")
        for line in findings:
            print("    " + line)
        print(f"shape-chains guard FAILS. A directory in which each file imports "
              f"the one before it is a directory split by reading order, and the "
              f"import graph is the only place that ordering is recorded -- so it "
              f"is load-bearing, it is invisible, and rearranging the chapters "
              f"breaks the build for reasons no declaration explains.")
        return 1

    print(f"shape-chains guard passes: no module's only internal import is a "
          f"sibling it names nothing from ({len(graph)} modules checked)")
    return 0


def run_shape_components() -> int:
    """Every module must lie in the corpus's one weak component.

    WHAT THIS CAUGHT, TWICE.  `Coalescent` was a self-contained development in the
    previous release -- seventy-nine modules importing each other and nothing else
    importing them.  It was wired in by hand.  `Pangenome` was the same shape in
    this one: `GaugeCounterexample` and `GaugeInvariance` imported each other and
    nothing in the corpus imported either, so a gauge-invariance result and the
    population genetics it is about could not be made to contradict each other.  It
    too was wired in by hand, while this guard was being written.  A third subsystem
    will start as an island unless something fails when it does, and that is the
    entire argument for the guard: both repairs were correct, both were found by
    reading, and reading is not a mechanism.

    WHAT IS LEFT ARE SINGLETONS, and they are the same defect at its smallest.
    `Blindness/BundleRigidity/LinearSCM`, `BundleRigidity/Operator` and
    `Spectral/ResonanceSpectrum` import nothing from this corpus and nothing here
    imports them; each is reachable only through its directory head, which is to
    say only by `lake build`.  `ResonanceSpectrum` is the module the root file's own
    comment records as having failed all day on a missing import while every
    whole-corpus build reported zero errors.

    The component is WEAK -- direction ignored.  A subsystem that only imports the
    corpus and is imported by nothing is wired in for this purpose: something below
    it can be edited and break it.  What this catches is the strictly worse case
    where neither direction exists at all.

    THE TABLES OF CONTENTS MUST COME OUT FIRST, and this is the whole reason the
    check has to be written rather than eyeballed.  `Descent/Pangenome.lean` imports
    both Pangenome modules and `Descent.lean` imports it, so on the raw graph the
    corpus is one component and always will be, no matter how disconnected the
    mathematics is.  The heads are what a build needs; they are not what a
    dependency is.  With them removed the corpus splits, and everything outside the
    largest piece is the finding.
    """
    graph = _shape_graph_without_toc()
    if not graph:
        print("shape-components guard CANNOT RUN: no Lean modules found under "
              f"{CORPUS / 'Descent'}")
        return 1

    adjacent = collections.defaultdict(set)
    for mod, deps in graph.items():
        adjacent.setdefault(mod, set())
        for dep in deps:
            adjacent[mod].add(dep)
            adjacent[dep].add(mod)

    seen, components = set(), []
    for start in sorted(graph):
        if start in seen:
            continue
        stack, comp = [start], []
        seen.add(start)
        while stack:
            cur = stack.pop()
            comp.append(cur)
            for nxt in sorted(adjacent[cur]):
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        components.append(sorted(comp))
    components.sort(key=len, reverse=True)

    stranded = [c for c in components[1:]]
    if stranded:
        n = sum(len(c) for c in stranded)
        print(f"modules outside the corpus's largest weak component: {n} in "
              f"{len(stranded)} island(s), budget 0; give each a theorem relating "
              f"its quantities to something the corpus already deploys, and import "
              f"what that theorem needs -- an island is wired in when an edit "
              f"elsewhere can break it")
        for comp in stranded:
            subsystems = sorted({m.split(".")[1] for m in comp if "." in m})
            print(f"    island of {len(comp)} module(s) under "
                  f"{', '.join(subsystems)}:")
            for m in comp:
                print(f"        {m}")
        print(f"shape-components guard FAILS. {len(components)} weak components "
              f"means {len(components)} developments sharing a repository. Nothing "
              f"in an island can be contradicted by anything outside it, so a "
              f"divergence between an island and the corpus is not a failing build, "
              f"it is a fact nobody has occasion to notice.")
        return 1

    print(f"shape-components guard passes: all {len(graph)} modules lie in one "
          f"weak component once the directory heads are removed")
    return 0


def _shape_metric_names(code):
    """The deployed metrics, read off the source rather than listed here.

    A metric is an `ℝ`-valued definition of `Descent/Core/Moments.lean` -- `r2`,
    `calibrationSlope`, `brier`, `deployedR2` and the rest, which is what the corpus
    means by "a number a deployment reports" -- CLOSED UNDER being computed from
    one.  `sensFromR2` counts because its body names `r2`; `brierFromR2` counts for
    the same reason.

    THE CLOSURE IS THE POINT, not a convenience.  A hardcoded list of metric names
    -- `architecture.py` carries one -- counts `presentDayR2` and
    `portabilityStatistic` as metrics on the strength of their spelling.  Neither
    is computed from the metric kernel, so a theorem joining `PopGenParameters` to
    one of them joins the parameter record to a number that has no stated relation
    to the `R²` the corpus actually deploys.  Reading the set off the bodies means
    a new metric joins it the moment it calls the kernel, and never before, which
    is the same rule `duplicate_body_groups` enforces one level down.
    """
    kernel = set()
    for line in code.get("Descent.Core.Moments", "").split("\n"):
        m = re.match(r"^(?:noncomputable\s+)?def\s+([\w.'₀-₉]+)(.*)", line)
        if m and re.search(r":\s*ℝ\s*:?=?\s*$", m.group(2)):
            kernel.add(m.group(1).split(".")[-1])

    # Parse once.  The closure below sweeps the list repeatedly and re-parsing
    # every module on each sweep is the whole cost of this guard.
    real_defs = []
    for _mod, text in code.items():
        real_defs += _shape_real_defs(text)

    metrics = set(kernel)
    while True:
        grew = {name for name, body in real_defs
                if name not in metrics
                and any(re.search(r"(?<![\w.'])" + re.escape(k) + r"(?![\w'])", body)
                        for k in metrics)}
        if not grew:
            return kernel, metrics
        metrics |= grew


def _shape_real_defs(text):
    """`(short name, body)` for every `ℝ`-valued `def` in one module's code."""
    lines, i, out = text.split("\n"), 0, []
    while i < len(lines):
        m = re.match(r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+([\w.'₀-₉]+)",
                     lines[i])
        if not m:
            i += 1
            continue
        block, j = [lines[i]], i + 1
        while j < len(lines) and lines[j].strip() and not SHAPE_DECL_STOP.match(lines[j]):
            block.append(lines[j])
            j += 1
        i = j
        joined = " ".join(" ".join(block).split())
        sig, _sep, body = joined.partition(":=")
        if re.search(r":\s*ℝ\s*$", sig.strip()):
            out.append((m.group(1).split(".")[-1], body))
    return out


def run_shape_spine() -> int:
    """The corpus must have a spine: theorems joining the parameters to the metrics.

    TWO NUMBERS, one shape.

    CROSS-MODULE REUSE is the fraction of theorems whose name appears in the CODE
    of some other module.  A corpus of independent monographs and a corpus with a
    spine are the same size, the same soundness and the same line count; this is
    the number that tells them apart, and just under 12% this one is much closer to
    the monographs.  The threshold is 20%: not a comfortable number and not an
    arbitrary one -- it is one theorem in five load-bearing, which is roughly what
    it takes for the deepest results to rest on the shallow ones rather than
    beside them.  `architecture.py` computes this figure and REPORTS it, on the
    argument that no value of it is correct.  That argument is right about the
    percentage and wrong about the corpus: 88% of theorems having no consumer
    outside their own file is not a property with no correct value, it is the
    island shape measured one level down, and this is where the same number gets
    an exit code.  The function that computes it is `architecture`'s, called, not
    a second copy.

    A SPINE THEOREM is a theorem whose STATEMENT binds the parameter record
    `PopGenParameters` and names a deployed metric.  Both halves are the point:

      * the record and not a demographic quantity generally.  `Ne`, `m` and `μ`
        passed as three loose reals are what the record exists to replace, and
        `shape-routes` fails on exactly that pattern -- so counting a theorem over
        loose reals as a spine theorem would have the two guards pulling against
        each other.  A theorem is on the spine when it starts where the spine
        starts.
      * the metric read off `Core/Moments.lean` and closed under being computed
        from it -- see `_shape_metric_names`, which explains why a name list would
        count theorems that reach a number the corpus never connects to the `R²`
        it deploys.

    So a spine theorem is `PopGenParameters → … → a number a deployment reports`,
    stated as one claim.  There are nineteen, and every one of them is in
    `Core/Moments.lean`: the spine exists, it is one file long, and not one of the
    subsystems has stated a theorem reaching from the record to a metric.  The
    per-module breakdown is printed for that reason -- the count alone would read
    as "not many theorems", and the finding is that they are all in one place.

    HOW THIS DIFFERS FROM `architecture.composition_theorems`, which reads 64.
    That one matches a statement against two hand-written lists of names, and a
    name on the metric list is a metric by virtue of its spelling.  Three of them
    -- `momentsUnderDrift`, `ScoreMoments`, `presentDayR2` -- are respectively the
    intermediate of the chain, the tuple it passes, and a quantity with no stated
    relation to the `R²` the corpus deploys.  The audit that asked for this guard
    counted 26 with a similar list.  Nineteen is the same population under a
    definition that requires the metric to be computed from the metric kernel, and
    the smaller number is the more useful one: it is the count of theorems that
    actually carry a demography to a reported number.

    The threshold is 80, the audit's, which is roughly one such theorem per
    subsystem module that names a demographic quantity.
    """
    _raw, code, _graph, decls, arch = _shape_corpus()

    reused, total = arch.gate_cross_module_reuse(code, decls)
    pct = round(100.0 * reused / total, 2) if total else 0.0

    kernel, metrics = _shape_metric_names(code)
    spine = []
    for mod, text in code.items():
        for m in SHAPE_THEOREM.finditer(text):
            stmt = m.group(2)
            if not re.search(r"(?<![\w.'])PopGenParameters(?![\w'])", stmt):
                continue
            if any(re.search(r"(?<![\w.'])" + re.escape(k) + r"(?![\w'])", stmt)
                   for k in metrics):
                spine.append((m.group(1), mod))

    bad = []
    if pct < SHAPE_REUSE_PCT:
        bad.append(f"cross-module theorem reuse: {pct}% ({reused} of {total} "
                   f"theorems named in another module's code), floor "
                   f"{SHAPE_REUSE_PCT}%; the gap is "
                   f"{int(SHAPE_REUSE_PCT * total / 100) - reused} theorems that "
                   f"need a consumer somewhere other than the file they are in")
    if len(spine) < SHAPE_SPINE_THEOREMS:
        bad.append(f"spine theorems: {len(spine)}, floor {SHAPE_SPINE_THEOREMS}; "
                   f"state the subsystem's result about `(p : PopGenParameters)` "
                   f"and one of the {len(metrics)} deployed metrics in the same "
                   f"claim, rather than about a free real someone has to believe "
                   f"came from a demography")
        for name, mod in sorted(spine):
            bad.append(f"    have: {name}  ({mod})")
        homes = collections.Counter(mod for _n, mod in spine)
        for mod, n in homes.most_common():
            bad.append(f"    {n:>3} of {len(spine)} in {mod}")

    print(f"deployed metrics: {len(kernel)} in Core/Moments.lean, {len(metrics)} "
          f"once closed under being computed from one")
    print("    " + ", ".join(sorted(metrics)))

    if bad:
        for line in bad:
            print(line)
        print(f"shape-spine guard FAILS. `PopGenParameters → fstEquilibrium → "
              f"momentsUnderDrift → a deployed metric` is the claim this corpus "
              f"exists to make, and a theorem that takes `F_ST` as a free real "
              f"does not make it -- it makes a statement about arithmetic that a "
              f"reader has to supply the population genetics for.")
        return 1

    print(f"shape-spine guard passes: {pct}% cross-module reuse (floor "
          f"{SHAPE_REUSE_PCT}%) and {len(spine)} theorems joining "
          f"`PopGenParameters` to a deployed metric (floor "
          f"{SHAPE_SPINE_THEOREMS})")
    return 0


def _shape_record_fields(code) -> set:
    """The `ℝ`-valued field names of `PopGenParameters`, and their loose spellings.

    A raw-real route is one that re-supplies THE RECORD'S FIELDS as bare arguments.
    Counting bare reals of any name instead was too blunt, and it over-fired the day
    this guard was gated: `deployedPPVFromTau (L) (V_A V_E tau prevalence : ℝ)` has
    four bare reals and is not a second route to anything.  It wraps
    `deployedR2FromTau`, which is the sanctioned kernel in the tau coordinate --
    `run_shape_routes` already said in prose that such a kernel is legitimate, and
    then counted its wrappers anyway, because `prevalence` and `tau` are reals and
    the test was arity.

    `deployedR2FromIsland (Ne m μ nDemes V_A V_E : ℝ)` is the real pattern, and the
    difference is visible in the binder names.  `Ne`, `m`, `μ`, `nDemes` and `V_A`
    are fields of the record rebuilt by hand, and the definition goes on to compute
    `F_ST` itself rather than reading `p.fstEquilibrium`.  `tau` and `prevalence`
    are not fields of anything; they are a coordinate and a clinical input.

    The field list is read off the `structure` rather than typed here, so the deme
    count that joined the record is covered without an edit to this guard.  The
    alias table is the one hand-maintained part, and it has to be: the corpus
    writes the migration rate `m` and the mutation rate `μ` at call sites while the
    record spells them `mig` and `mu`, and a route rebuilding the record under
    those spellings is the same route.
    """
    aliases = {
        "mu": {"mu", "μ"},
        "mig": {"mig", "m", "m_rate", "m_into"},
        "t_div": {"t_div", "t"},
        "recomb": {"recomb", "r"},
    }
    fields, in_structure = set(), False
    for line in code.get("Descent.Core.Parameters", "").split("\n"):
        if re.match(r"^structure\s+PopGenParameters\b", line):
            in_structure = True
            continue
        if not in_structure:
            continue
        m = re.match(r"^\s+([A-Za-z_][\w'₀-₉]*)\s*:\s*ℝ\s*$", line)
        if m:
            fields |= aliases.get(m.group(1), {m.group(1)})
            continue
        # The proof fields (`Ne_pos : 0 < Ne`) end the ℝ-valued run; the first
        # line at column zero ends the structure.
        if line and not line[0].isspace():
            break
    return fields


def _shape_camel_words(name: str) -> list:
    """`deployedR2FromIsland` -> `['deployed', 'R2', 'From', 'Island']`."""
    return re.findall(r"[A-Z]?[a-z0-9'₀-₉]+|[A-Z]+(?![a-z])", name)


def run_shape_routes() -> int:
    """No raw-real entry point may sit beside a record-typed one of the same name.

    WHAT THIS CATCHES.  Until this release the corpus carried both of these:

        deployedR2           (p : PopGenParameters) (V_E : ℝ) : ℝ
        deployedR2FromIsland (Ne m μ nDemes V_A V_E : ℝ)       : ℝ

    Two routes to one metric.  The record's whole job is that a constraint added to
    it -- `recomb_le_half`, `Ne_pos` -- reaches every caller; the second route took
    four of the record's fields as loose reals and reached none of them, so
    `deployedR2FromIsland` could be called at a negative effective size and nothing
    said otherwise.  This is the same defect that produced `EvolutionaryParameters`
    and `GenerationalPopGenParameters`, two records with the same fields in two
    modules that do not import each other, which is what `PopGenParameters` was
    introduced to end.  It came back as a function signature, and it is the third
    time this shape has been fixed by hand.

    THE COUNT IS ZERO, so this is the one of the five shape guards that lands
    GATED.  `deployedR2FromIsland` was deleted while these guards were being
    written -- the timing is the argument, not a coincidence: the repair and the
    guard were two responses to the same audit, and only one of them survives to
    the next release.  A guard whose count has never been nonzero is
    indistinguishable from a guard that does nothing, so this one was calibrated
    against a fixture holding exactly the pair above: it reports the pair, and
    reports nothing once the raw-real route is removed.  `DESCENT_CORPUS` points
    it at that fixture, which is the reason `_shape_corpus` patches
    `architecture.ROOT` rather than letting it compute its own.

    HOW IT IS DETECTED.  A definition taking `SHAPE_RAW_ARITY` or more BARE `ℝ`
    arguments, whose camel-case name shares a full stem with a definition that
    takes a parameter record.  "Shares a full stem" means one name's word sequence
    is a prefix of the other's -- `deployed·R2` is a prefix of
    `deployed·R2·From·Island` -- rather than any shared characters, which would fire
    on every name beginning with `fst`.

    THE MATCH IS CORPUS-WIDE, not within a file.  The pair above happens to be two
    lines apart, but the failure this exists to stop is a second route appearing in
    a DIFFERENT module, which is how both parallel parameter records got written:
    two files that do not import each other cannot see that they are describing the
    same thing.

    A raw-real definition with no record-typed twin is not reported.
    `deployedR2FromTau (V_A V_E tau : ℝ)` is a kernel in its own coordinates and
    takes no population history; it is three reals, below the arity, and it has no
    sibling to be a second route to.
    """
    _raw, code, _graph, _decls, _arch = _shape_corpus()

    fields = _shape_record_fields(code)

    raw_entry, record_entry = {}, {}
    for mod, text in code.items():
        lines, i = text.split("\n"), 0
        while i < len(lines):
            m = re.match(r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+([\w.'₀-₉]+)",
                         lines[i])
            if not m:
                i += 1
                continue
            block, j = [lines[i]], i + 1
            while j < len(lines) and lines[j].strip() and \
                    not SHAPE_DECL_STOP.match(lines[j]):
                block.append(lines[j])
                j += 1
            i = j
            sig = " ".join(" ".join(block).split()).partition(":=")[0]
            name = m.group(1).split(".")[-1]
            binders = [b for g in re.findall(r"\(([^()]*?):\s*ℝ\s*\)", sig)
                       for b in g.split()]
            reals = sum(1 for b in binders if b in fields)
            if reals >= SHAPE_RAW_ARITY:
                raw_entry.setdefault(name, (mod, reals))
            if re.search(r"\([^()]*?:\s*[A-Z][\w.']*Parameters\b", sig):
                record_entry.setdefault(name, mod)

    findings = []
    for raw_name in sorted(raw_entry):
        rmod, reals = raw_entry[raw_name]
        rwords = _shape_camel_words(raw_name)
        for rec_name in sorted(record_entry):
            if rec_name == raw_name:
                continue
            cwords = _shape_camel_words(rec_name)
            k = 0
            while k < min(len(rwords), len(cwords)) and \
                    rwords[k].lower() == cwords[k].lower():
                k += 1
            if k and (k == len(cwords) or k == len(rwords)):
                findings.append(
                    f"{raw_name} ({rmod}) re-supplies {reals} record fields as bare reals and shares the "
                    f"stem `{''.join(rwords[:k])}` with {rec_name} "
                    f"({record_entry[rec_name]}), which takes a parameter record")

    if findings:
        print(f"metrics reachable by two routes, one of them raw reals: "
              f"{len(findings)}, budget 0; make the raw-real definition compute the "
              f"record and call the record-typed one, so the record's field "
              f"constraints hold on both routes -- or delete it if the "
              f"record-typed one already covers its callers")
        for line in findings:
            print("    " + line)
        print(f"shape-routes guard FAILS. A parameter record only enforces what it "
              f"enforces on the callers that go through it; a second entry point "
              f"taking the same demography as loose reals is the record's "
              f"constraints made optional, and nothing in the build says which "
              f"route a caller took.")
        return 1

    print(f"shape-routes guard passes: {len(raw_entry)} definition(s) re-supply "
          f"{SHAPE_RAW_ARITY}+ of the parameter record's fields as bare reals, and "
          f"none shares a stem with a record-typed definition")
    return 0


# ======================================================================================
# LAYERS
# ======================================================================================

# WHAT THIS CAUGHT.  `Descent/Spectral/SpectralDegradation.lean` imported
# `Descent.Portability.GenerativePortabilityLaw` and named not one declaration from it.
# The import was carrying Mathlib: `GenerativePortabilityLaw` reaches `Mathlib.Tactic`,
# `Mathlib.Data.Real.Basic` and `Mathlib.Data.Fintype.BigOperators` through
# `Descent.Blindness.ObservationalCeiling`, and the file was living off that closure
# instead of naming what it uses.  The cost was not an unused import.  `PopGen.DGP`
# imports `SpectralDegradation` for `degradation_eq_zero_iff` -- the positivity
# certificate for excess target risk that does not read an F_ST difference -- so the
# layer that GENERATES the moments reached, one hop later, the layer that CONSUMES
# them.  Nothing in the mathematics wanted that.  A Mathlib import did.
#
# The same shape, fourteen times over, put `Descent.Program.OpenQuestions` -- the
# programme narrative, the module that says what the corpus has and has not settled --
# underneath eight `PopGen` files and six `Portability` ones.  Thirteen of the fourteen
# named nothing from it; `Portability.PortabilityBounds` named one theorem whose whole
# proof was `div_lt_div_of_pos_right (by nlinarith) h`.
#
# WHY THESE RULES AND NOT A VAGUER ONE.  "Imports should go downward" is not checkable
# and "modules should be cohesive" fires on the whole corpus.  These four are each a
# yes-or-no question about one edge:
#
#   ORDER      the seven ranked directories are `Core < Foundations < Coalescent <
#              PopGen < Portability < Decision < Program`, and an import from a lower
#              rank to a higher one is a violation.  That contract is not invented
#              here; it is the corpus's own, quoted in the `SHAPE_DEPTH_LIMIT` comment
#              above, and `SHAPE_DEPTH_LIMIT` is 12 BECAUSE of it.  A guard measuring
#              depth against a layer contract nothing checks is measuring against a
#              wish.
#   CORE       a module under `Descent/Core/` may import `Descent.Core.*` and Mathlib
#              and nothing else.  This is ORDER's strongest case and it is stated
#              separately because it does not need the ranking to be right: Core is
#              depth 0-1, the corpus's headline chain reads through it, and an import
#              out of it is an unstated premise at the bottom of everything.  It is
#              also the rule that makes moving content DOWN into Core a safe repair,
#              which is what most of the fixes below are.
#   NARRATIVE  nothing outside `Descent/Program/` may import `Descent.Program.*`.
#              ORDER already forbids this for the seven ranked directories; this rule
#              extends it to the four unranked ones, and it needs no ranking to be
#              justified.  A narrative module is written AGAINST the corpus and must
#              stay rewritable without breaking a build.  An import from the technical
#              side destroys exactly that property.
#   META       no module of `Descent/Meta/` may import a proof module, and no proof
#              module may import a `Descent/Meta/` AUDITOR.  The head states the first
#              half in prose: "a proof module able to import its own auditor can be
#              written to satisfy it."  That is the whole argument, and it is an
#              argument about auditors.
#
#              THE RULE WAS FIRST WRITTEN AS "no edge in either direction", which is
#              stronger than its own argument and was true only because
#              `Descent/Meta/` then held nothing but checks.  It stopped being true the
#              day the directory acquired VOCABULARY: `Descent.Meta.Informal` supplies
#              the `informal_lemma`, `TODO` and `@[withdrawn]` commands, which a proof
#              module must import in order to record a gap, and which cannot be
#              "written to satisfy" because they have no verdict -- they add data to an
#              environment extension and no constant to the environment.  A file that
#              declares a gap has not passed a check; there is no check.
#
#              So the direction that carries the danger is still absolute, and the
#              direction that carries none is allowed for the named modules in
#              `LAYER_META_VOCABULARY` and no others.  Widening a rule to fit a case is
#              how allowlists start, which is why the set is enumerated here rather
#              than derived from a path shape, and why the Meta-imports-proof half
#              admits no exceptions at all.
#   REACHABLE  a qualified cross-directory name must have its defining module in the
#              importer's transitive closure.  This is not a layer rule and it is here
#              because it is the rule that makes the other three SAFE TO ACT ON.  Lean
#              resolves `Program.f1Score` through any import chain that happens to
#              reach it, so a file can name a declaration for years without importing
#              the module that defines it -- and then a repair two layers away deletes
#              the chain and the file stops compiling.  That happened three times this
#              week: `MetricSpecificPortability.PrecisionRecall` reached
#              `Program.f1Score` through `R2Decomposition -> PopGen.LDDecayTheory ->
#              Program.OpenQuestions`, and the two `PGSCalibrationTheory` files reached
#              `Program.populationAUC` along a FIFTEEN-module path out through
#              `Program.OpenQuestions`, into `Portability.PortabilityDrift`, down its
#              ten-module interior and back out to `Program.Conclusions`.  All three
#              are fixed and this rule is at zero.
#
#              WHAT THIS RULE DOES NOT SEE, stated here so its zero is not read as
#              more than it is.  It matches QUALIFIED names only -- `Portability.foo`
#              written from outside `Descent/Portability/`.  A file sitting in
#              `namespace Descent.Portability` writes `presentDayR2` bare, and that
#              resolves through the same accidental chains and breaks the same way.
#              `necklace-B` measured the difference on one commit: cutting
#              `PGSCalibrationTheory`'s head lost 42 names in
#              `CalibrationVsDiscrimination`, of which this rule sees the 3 that were
#              written with a `Program.` prefix.  So: fourteen to one, on the one
#              commit where both numbers are known.
#
#              THE OBVIOUS EXTENSION IS NOISE, WHICH IS WHY IT IS NOT HERE.  Dropping
#              the prefix requirement -- every identifier of 12 characters or more
#              that exactly one corpus module declares must be reachable -- runs in
#              0.3s and reports 34 findings on the corpus today.  Every one that has
#              been checked is a false positive of the same three kinds:
#              `outcomeVariance` and `predictiveCovariance` are FIELDS of
#              `Core/Moments.lean`'s own structure; `driftVariance` is a binder inside
#              `def effectiveSize`; `genotypeVarianceHWE` is attributed to
#              `Portability.AncestrySpecificPower` by a regex that cannot see a
#              `_root_.` declaration or an `open ... renaming`.  Held against the
#              corpus at `62bbadb`, all 34 are unreachable THERE TOO, in a tree that
#              compiled.  A gate at 34 false positives is worse than no gate.
#
#              THE MEASUREMENT THAT DOES WORK IS A DIFF, not a threshold, and it is
#              `necklace-B`'s: build the pre-change tree, compute the unresolved-name
#              set for every module in both, and report only what the change ADDED.
#              The false positives are identical in both trees and cancel exactly.
#              That needs a base revision, which makes it a reviewer's instrument
#              rather than a guard's -- `field-proofs` is the precedent for shelling
#              out to git, and the honest place for this is beside it rather than
#              inside a rule whose zero is supposed to mean something.
#
# EVERY VIOLATION IS A NAMED EXCEPTION OR IT IS NOT A VIOLATION ANYONE HAS THOUGHT
# ABOUT.  `LAYER_PENDING` below carries one sentence per outstanding edge saying what
# the edge is made of and what repair retires it.  An edge NOT in that table is
# reported harder than one in it, because an unlisted edge is one nobody has argued
# for.  The table is not a budget: every entry in it still counts as a violation and
# the budget is 0.  What the sentence buys is that the next person does not re-derive
# the analysis, and that an edge cannot be added silently -- adding one means writing
# down why.
#
# CALIBRATION.  Both counted rules have been run against a second tree -- the corpus at
# `62bbadb`, the state before this release's import work, reachable with
# `DESCENT_CORPUS=<checkout> --only layers` -- and they disagree with the run against
# the corpus today in the way each is supposed to.  ORDER reports 27 cross-layer edges
# there against 14 here, so it is measuring something that moved.  REACHABLE reports
# ZERO there against 31 here, which is the control that matters: a rule that has never
# been silent is indistinguishable from a rule that is always on, and this one was
# silent on a whole corpus one release ago.  The 31 are not a discovery about old code.
# They are this release's import repairs, each of which deleted a chain some unrelated
# file was resolving a name through, and every one of them is a file that will not
# compile.
#
# THE UNRANKED DIRECTORIES.  `Blindness`, `Conditionals`, `Pangenome`, `Spectral` and
# `Meta` have no rank in the contract, so ORDER cannot speak about their 98 edges and
# does not pretend to.  They are listed in `LAYER_UNRANKED` with the reason each is
# unranked, and the guard PRINTS their edge census every run so the exclusion is
# visible rather than silent.  Ranking them is a decision about what the corpus is,
# not a decision a guard may make on its own.
#
# A DIRECTORY IN NEITHER TABLE IS ITSELF A FINDING, and that rule is the difference
# between a named exception and an allowlist.  `Descent/Meta/` appeared during the week
# this guard was written; with only a skip-list of four names it would have been
# unranked, unexplained and unmentioned, and the guard would have gone on reporting a
# clean order over a directory nobody had placed.  Adding a top-level directory now
# means writing one sentence about where it sits.

LAYER_ORDER = ("Core", "Foundations", "Coalescent", "PopGen", "Portability",
               "Decision", "Program")
LAYER_RANK = {name: i for i, name in enumerate(LAYER_ORDER)}

# Why each of these is unranked, and what ranking it would have to settle.  A guard
# that skipped them without saying so would report a clean order over half the tree.
LAYER_UNRANKED = {
    "Blindness":
        "It states what a family of models CANNOT distinguish, so it is written "
        "against whatever layer's objects are being shown indistinguishable; it has "
        "edges to Core, Foundations, Coalescent, PopGen, Portability and Spectral, "
        "and ranking it means first deciding whether an impossibility result sits "
        "with the objects it is about or below all of them.",
    "Conditionals":
        "Conditional-law geometry used by Spectral and Portability and reaching back "
        "into Blindness; it is the one directory whose heaviest edge (12 to Blindness) "
        "runs to another unranked directory, so its rank cannot be decided before "
        "Blindness's is.",
    "Pangenome":
        "Three modules and one edge, to Coalescent. It is joined to the corpus by its "
        "own table of contents and by almost nothing else, which is the finding "
        "`shape-components` reports; ranking it is premature while it is an island.",
    "Meta":
        "Not in the order: it is the corpus's machinery about itself, written in the "
        "corpus's own language and importing only Lean and Batteries. A rank would "
        "permit it to import the bottom of the order and the point is that it imports "
        "none of it, so its separation is enforced by the META rule below instead. "
        "That rule is asymmetric on purpose. Nothing here may import a proof module, "
        "ever; a proof module may import the VOCABULARY modules named in "
        "`LAYER_META_VOCABULARY`, which add commands for writing a gap down and add no "
        "constant anything could cite, and may import no auditor.",
    "Spectral":
        "Frequency-band and pencil machinery that both PopGen and Portability consume, "
        "and that consumes Blindness and Conditionals in turn. It is a genuine "
        "cross-cutting layer and the honest options are to rank it beside Foundations "
        "or to split it, neither of which a guard decides.",
}

# One sentence per outstanding cross-layer edge: what the edge is MADE OF, and the
# repair that retires it.  Keys are `(importer, imported)` module names.  Every entry
# still counts as a violation; see the section header.
LAYER_PENDING = {
    ("Descent.PopGen.DemographicCapacity",
     "Descent.Portability.PCCorrectability.ImitationCapacity"):
        "`traceWindowBudgetClass`, `imitable_within_traceWindowBudget`, "
        "`pcCorrectabilityMargin` and `demographicSpike`. These ARE about correcting a "
        "score across populations and are correctly placed; the file states a PopGen "
        "capacity theorem in terms of them, so the consumer moves UP rather than the "
        "definitions moving down.",
    ("Descent.PopGen.GeneticArchitectureDiscovery",
     "Descent.Portability.AncestrySpecificPower"):
        "Twenty-two uses of `Portability.genotypeVarianceHWE`, which is Hardy-Weinberg "
        "genotype variance and contains no transport at all. Extract it downward -- "
        "Core or PopGen -- and this edge and two others go with it.",
    ("Descent.PopGen.GeneticArchitectureDiscovery",
     "Descent.Portability.BayesianPGSTheory"):
        "`jamesSteinMSE` and `optimalShrinkage`: shrinkage-estimator facts about one "
        "population, in Portability because the Bayesian PGS chapter was written "
        "there. They belong at or below PopGen.",
    ("Descent.PopGen.GeneticArchitectureDiscovery",
     "Descent.Portability.MechanisticPortabilityWitnesses"):
        "`mechanisticPortabilityRatio` and `sigmaTagCausalSourceAt` ARE about "
        "transport and are correctly placed. This edge inverts because a PopGen file "
        "states an architecture theorem in terms of them, so here the consumer moves "
        "UP rather than the definition moving down.",
    ("Descent.PopGen.HumanDemography", "Descent.Portability.PortabilityDrift"):
        "`fstFromGenerations` and `coalescentTau` are demography and coalescent time "
        "-- single-population quantities with no score being carried anywhere -- "
        "housed in the drift chapter because that is where the drift chapter was "
        "written.",
    ("Descent.PopGen.LDDecayTheory", "Descent.Portability.PortabilityDrift"):
        "Unfolds `Portability.ibdRecurrenceStep` and `islandFstMultiplicativeStep` "
        "against its own `driftLDStep`. The identity-by-descent recurrence and the "
        "island-model F_ST step are statements about one population's allele "
        "frequencies over generations; nothing in them is about transport.",
    # The five `PopulationGeneticsFoundations` files below arrived together and for one
    # reason: the chain that used to carry these names ran out of the directory and back
    # in, and cutting it left five files naming declarations they could not reach. The
    # imports are the repair for THAT, and they make a dependency that was always there
    # visible for the first time.
    ("Descent.PopGen.PopulationGeneticsFoundations.CoalescentTheory",
     "Descent.Portability.PortabilityDrift"):
        "`Portability.coalescentTau`: coalescent time for a pair of demes, which is a "
        "PopGen quantity housed in the drift chapter.",
    ("Descent.PopGen.PopulationGeneticsFoundations.FstDerivationFromDrift",
     "Descent.Portability.PortabilityDrift"):
        "`Portability.hetMutationFloor`: the mutation-drift heterozygosity floor for "
        "one closed population. Same extraction.",
    ("Descent.PopGen.PopulationGeneticsFoundations.MigrationDriftFoundations",
     "Descent.Portability.PortabilityDrift"):
        "`Portability.effectiveSymmetricMigration` and "
        "`fstMigrationDriftEquilibrium`: island-model migration-drift balance, single "
        "population set, no score carried anywhere.",
    ("Descent.PopGen.PopulationGeneticsFoundations.TransientFstDerivation",
     "Descent.Portability.PortabilityDrift"):
        "`Portability.hudsonFstFromCoalescenceTimes`: Hudson's F_ST from coalescence "
        "times, which is the definition this directory exists to derive.",
    ("Descent.PopGen.PopulationGeneticsFoundations.WrightFStatistics",
     "Descent.Portability.PortabilityDrift"):
        "`Portability.pairwiseFstFromBranches`: pairwise F_ST off a tree. Same "
        "extraction as the four above; one move of the drift recurrences down into "
        "PopGen retires all five edges and `LDDecayTheory`'s as well.",
    ("Descent.PopGen.PolygenicArchitecture", "Descent.Decision.CertificateGrading"):
        "Reads `FinitePrior.mean` and the atom-modulus lemmas. The certificate "
        "machinery is decision-theoretic and correctly placed; the polygenic INSTANCE "
        "of it is what sits in the wrong layer, so this repair moves a theorem up.",
    ("Descent.PopGen.PolygenicArchitecture", "Descent.Decision.TransportedMinimax"):
        "Same file and same repair: the minimax entropy exponents it names are "
        "Decision's, and the architecture statement consuming them is the thing in "
        "the wrong place.",
    ("Descent.PopGen.SelectionArchitecture", "Descent.Portability.AncestrySpecificPower"):
        "`fisherInformation`, `ncp` and `effectiveFisherInformation` are study-design "
        "quantities for a single cohort. Same extraction as "
        "`GeneticArchitectureDiscovery`.",
    ("Descent.PopGen.StandardizedGenotypeMoments",
     "Descent.Portability.AncestrySpecificPower"):
        "`Portability.genotypeVarianceHWE` again, six times. One extraction retires "
        "this edge, and two more above it.",
    ("Descent.Portability.MetricSpecificPortability.PrecisionRecall",
     "Descent.Program.OpenQuestions"):
        "`Program.f1Score`. This import was WRITTEN rather than found: the file named "
        "`f1Score` and reached it through `R2Decomposition -> PopGen.LDDecayTheory -> "
        "Program.OpenQuestions` until that chain was cut. An F1 formula is a "
        "classifier metric with no programme content; move the definition into "
        "Portability and the edge goes.",
    ("Descent.Portability.PGSCalibrationTheory.CalibrationVsDiscrimination",
     "Descent.Program.Conclusions"):
        "`BinaryPopulation`, `populationAUC` and `populationAUC_strictMono_invariant`: "
        "a measure-theoretic AUC apparatus housed in the narrative module. Also "
        "written rather than found -- the names arrived along a fifteen-module path "
        "that no longer exists.",
    ("Descent.Portability.PGSCalibrationTheory.RecalibrationMethods",
     "Descent.Program.Conclusions"):
        "The same three names and the same repair; this file reaches them on its own "
        "now rather than through a sibling that happened to be earlier in a chain.",
    ("Descent.Portability.PortabilityDrift.Definitions", "Descent.Program.Conclusions"):
        "This file names NOTHING from `Conclusions`. It is a carrier: "
        "`PortabilityDrift.PresentDayMoments`, further down the same chain, names "
        "`brierBernoulliRisk`, `bernoulliKLReal` and `exactBrierRiskOfCalibrated` and "
        "reaches them only through here. Interim repair is to move the import to the "
        "file that uses the names; the real one is to move the Bernoulli losses out "
        "of the narrative module.",
}

# The self-auditing directory.  See META in the header.
LAYER_META = "Meta"

# The modules under `Descent/Meta/` a proof module MAY import: the ones that add
# SYNTAX and read nothing.  `Informal` supplies `TODO`, `informal_definition`,
# `informal_lemma` and `@[withdrawn]`; `Semiformal` supplies `semiformal_result`.
# Both import `Lean.Elab.Command` and nothing else, both record into an environment
# extension, and neither adds a constant to the environment -- so a proof module that
# imports one gains a way to WRITE DOWN a gap and no way to cite one.
#
# Enumerated, not derived.  A path-shaped test ("anything not named `*Lint*`") would
# admit the next auditor somebody files under a neutral name, and the whole value of
# this rule is that widening it has to be a deliberate edit somebody argues for.
LAYER_META_VOCABULARY = {
    "Descent.Meta.Informal",
    "Descent.Meta.Semiformal",
}

LAYER_QUALIFIED = re.compile(r"\b([A-Z][A-Za-z0-9]*)\.([A-Za-z_][A-Za-z0-9_'!?]*)")
LAYER_DECL = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)")


def _layer_of(mod: str):
    """`Descent.PopGen.DGP` -> `PopGen`; the root and anything else -> `None`."""
    parts = mod.split(".")
    return parts[1] if len(parts) > 1 and parts[0] == "Descent" else None


def _layer_graph():
    """`(raw sources, the whole import graph, the tables of contents in it)`.

    THE GRAPH IS NOT PRUNED, and that is the difference between this guard and the
    shape ones.  `_shape_graph_without_toc` deletes heads at both ends because a head
    declares nothing and its edges are what `lake build` needs to reach the tree
    rather than what a proof rests on -- right for depth, wrong here twice over.
    `Descent.PopGen.LDDecayTheory -> Descent.Portability.PortabilityDrift` is an
    import of another layer's head and it is exactly as much a cross-layer dependency
    as an import of a module inside it; deleting the head end hides it.  And Lean
    resolves names through heads like any other import, so a reachability rule run on
    a pruned graph reports sixty modules as naming declarations they cannot see when
    they see them perfectly well.

    What IS skipped is edges whose SOURCE is a table of contents: `Descent/PopGen.lean`
    importing every module under `Descent/PopGen/` is the `heads` contract being
    satisfied, and `Descent.lean` importing the eleven heads is the build entry point.
    Neither is a dependency anything rests on.  `_shape_is_toc` decides what a head is,
    by the `heads` contract; a second answer to that question here is the failure this
    file's own header records.
    """
    raw, _code, graph, decls, _arch = _shape_corpus()
    return raw, graph, {m for m in graph if _shape_is_toc(m, graph, decls)}


def _layer_reachable(graph, start):
    seen, stack = {start}, [start]
    while stack:
        for dep in graph.get(stack.pop(), ()):
            if dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return seen


def run_layers() -> int:
    raw, graph, toc = _layer_graph()
    if not graph:
        print("layers guard CANNOT RUN: no Lean modules found under "
              f"{CORPUS / 'Descent'}")
        return 1

    order, core, narrative, meta, census = [], [], [], [], collections.Counter()

    for mod in sorted(graph):
        if mod in toc:
            continue
        src = _layer_of(mod)
        for dep in sorted(graph[mod]):
            dst = _layer_of(dep)
            if src is None or dst is None or src == dst:
                continue
            if src in LAYER_RANK and dst in LAYER_RANK:
                if LAYER_RANK[dst] > LAYER_RANK[src]:
                    order.append((mod, dep))
            else:
                census[(src, dst)] += 1
            if src == "Core":
                core.append((mod, dep))
            if dst == "Program":
                narrative.append((mod, dep))
            if (src == LAYER_META) != (dst == LAYER_META):
                # A proof module importing named `Descent/Meta/` VOCABULARY is not a
                # violation; every other crossing, in either direction, is.  See META.
                if not (dst == LAYER_META and dep in LAYER_META_VOCABULARY):
                    meta.append((mod, dep))

    # A top-level directory that is neither ranked nor explained.  See the header: this
    # is what stops `LAYER_UNRANKED` from being an allowlist that grows by accident.
    unplaced = sorted({d for d in (_layer_of(m) for m in graph)
                       if d and d not in LAYER_RANK and d not in LAYER_UNRANKED})

    # REACHABLE.  Only qualified names whose head is a top-level directory are
    # checked: `Program.f1Score` is a claim about a module, `Finset.sum_congr` and
    # `h.altFreq` are not.  Comments are stripped first, because a docstring is
    # allowed to name a declaration the file does not import -- that is what a
    # cross-reference IS.
    declared_in = {}
    for mod, text in raw.items():
        layer = _layer_of(mod)
        if layer is None:
            continue
        for name in LAYER_DECL.findall(text):
            declared_in.setdefault((layer, name), set()).add(mod)

    unreachable = []
    for mod in sorted(graph):
        if mod in toc:
            continue
        src = _layer_of(mod)
        text = raw.get(mod)
        if src is None or text is None:
            continue
        body = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", text, flags=re.S))
        closure = None
        for layer, name in sorted(set(LAYER_QUALIFIED.findall(body))):
            if layer == src or (layer not in LAYER_UNRANKED
                                and layer not in LAYER_RANK):
                continue
            homes = declared_in.get((layer, name))
            if not homes:
                continue
            if closure is None:
                closure = _layer_reachable(graph, mod)
            if not homes & closure:
                unreachable.append(
                    f"{mod} names {layer}.{name}, defined in "
                    f"{', '.join(sorted(homes))}, which it does not reach")

    stale = sorted(e for e in LAYER_PENDING
                   if e not in set(order) | set(core) | set(narrative))

    bad = []
    edges = sorted(set(order) | set(core) | set(narrative) | set(meta))
    if edges:
        listed = [e for e in edges if e in LAYER_PENDING]
        unlisted = [e for e in edges if e not in LAYER_PENDING]
        bad.append(f"cross-layer import edges: {len(edges)}, budget 0")
        for mod, dep in edges:
            rules = ("order " if (mod, dep) in order else "") + \
                    ("core " if (mod, dep) in core else "") + \
                    ("narrative " if (mod, dep) in narrative else "") + \
                    ("meta" if (mod, dep) in meta else "")
            bad.append(f"    {mod}")
            bad.append(f"      -> {dep}   [{rules.strip().replace(' ', '+')}]")
            reason = LAYER_PENDING.get((mod, dep))
            if reason:
                bad.append(f"      {reason}")
            else:
                bad.append("      NOT IN `LAYER_PENDING`: nobody has written down what "
                           "this edge is made of. Either name the declarations it "
                           "carries and the repair that retires it, or delete the "
                           "import -- an unargued cross-layer edge is the one shape "
                           "this guard exists to stop appearing.")
        bad.append(f"    ({len(listed)} argued for in `LAYER_PENDING`, "
                   f"{len(unlisted)} not)")
    if unreachable:
        bad.append(f"qualified names outside the importer's closure: "
                   f"{len(unreachable)}, budget 0; import the module that DEFINES the "
                   f"name, because the chain it currently arrives through belongs to "
                   f"another file and can be cut without warning")
        bad.extend("    " + x for x in sorted(unreachable))
    if unplaced:
        bad.append(f"top-level directories in neither `LAYER_ORDER` nor "
                   f"`LAYER_UNRANKED`: {len(unplaced)}, budget 0; give it a rank in "
                   f"the order or a sentence in `LAYER_UNRANKED` saying why it has "
                   f"none -- an unplaced directory is a piece of the corpus this "
                   f"guard silently reports as clean")
        bad.extend("    " + x for x in unplaced)
    if stale:
        bad.append(f"`LAYER_PENDING` entries whose edge no longer exists: {len(stale)}, "
                   f"budget 0; delete the entry -- a repaired edge described as "
                   f"outstanding is worse than no description")
        bad.extend(f"    {m} -> {d}" for m, d in stale)

    print(f"unranked-directory edges, not counted: {sum(census.values())} across "
          f"{len(census)} directory pairs. The contract ranks {len(LAYER_ORDER)} "
          f"directories and these {len(LAYER_UNRANKED)} have no rank:")
    for name in sorted(LAYER_UNRANKED):
        print(f"    {name}: {LAYER_UNRANKED[name]}")
    for (a, b), n in sorted(census.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"    {a} -> {b}: {n}")

    if bad:
        for line in bad:
            print(line)
        print(f"layers guard FAILS. The declared order is "
              f"{' < '.join(LAYER_ORDER)}, and an edge that runs the other way is a "
              f"lower layer that cannot be read, moved or rewritten without the "
              f"higher one -- which is the whole of what a layer buys.")
        return 1

    print(f"layers guard passes: {sum(len(v) for v in graph.values())} import edge(s) "
          f"over {len(graph)} modules, none running up the order "
          f"{' < '.join(LAYER_ORDER)}, none leaving `Descent/Core/`, none reaching "
          f"`Descent/Program/` from outside it, none reaching a `Descent/Meta/` "
          f"auditor or leaving `Descent/Meta/` at all, and every qualified "
          f"cross-directory name "
          f"inside its importer's closure.")
    return 0


# ======================================================================================
# DISPATCHER
# ======================================================================================

# The guards, in the order a reader should want them.  Cheap and broadly-scoped
# first, so a run that is going to fail says the most useful thing soonest.
#
# `gated` is whether a guard participates in the default run.  `field-proofs` is
# the only one that does not: it reads `origin/main` over git, and it has known
# false positives that make its raw count a diagnostic rather than a verdict.
#
# The signature column is not decoration.  `laundering` and `wiring` take their
# own flags, so `--only laundering --family F1` has to reach them; the rest take
# nothing and are called with no arguments.
def run_heads() -> int:
    """Every module under `Descent/X/` must be imported by `Descent/X.lean`.

    The root file used to import 171 modules directly, because a module the build
    never reaches is not clean, it is UNBUILT -- `ResonanceSpectrum` failed all
    day on a missing import while every whole-corpus build reported zero errors.
    The remedy was to name orphans in the root by hand, and a hand-maintained
    list has the same failure mode as no list, one lapse later.  The root's own
    comment recorded the near-miss: four `BundleRigidity` modules were reachable
    only transitively and `DeploymentCeiling` was not reachable at all.

    So the root names eleven heads and this guard reads the directories off disk.
    A new module is either in its head or the build says which one is not, and
    nobody has to remember anything.

    A head is also required to contain no declarations.  A table of contents that
    states a theorem is a module pretending to be a table of contents, and the
    next reader has no way to know which it is without opening it.
    """
    import os as _os
    import re as _re

    root = _os.path.dirname(_os.path.dirname(
        _os.path.dirname(_os.path.abspath(__file__))))
    lean = _os.path.join(root, "Descent")
    decl = _re.compile(r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|"
                       r"noncomputable\s+)*(?:def|abbrev|theorem|lemma|structure|"
                       r"inductive|instance|class)\s")
    missing, stray, declaring = [], [], []

    for entry in sorted(_os.listdir(lean)):
        d = _os.path.join(lean, entry)
        if not _os.path.isdir(d):
            continue
        head = _os.path.join(root, "Descent", entry + ".lean")
        if not _os.path.exists(head):
            missing.append(f"Descent/{entry}.lean does not exist")
            continue
        text = open(head, encoding="utf-8", errors="ignore").read()
        imported = set(_re.findall(r"(?m)^import\s+(\S+)$", text))
        # `lean_sources` AND NOT A FIFTH HAND-ROLLED WALK. The one this replaced
        # swept up AppleDouble `._X.lean` resource forks -- macOS `tar` writes
        # one beside every file it archives, and the sync script extracts them
        # into the shared checkout -- and asked the head to import
        # `Descent.Spectral.._CirculationDefect`, a module name no file can have.
        # 271 of this guard's findings were that, i.e. all but one, and the
        # false ones read exactly like the true one. The comment on
        # `lean_sources` says one place decides what counts as a corpus file
        # precisely because a walk that forgets is indistinguishable from a walk
        # that is right.
        on_disk = {
            str(p.relative_to(root)).replace(_os.sep, ".")[:-len(".lean")]
            for p in lean_sources(Path(d))
        }
        for m in sorted(on_disk - imported):
            missing.append(f"Descent/{entry}.lean does not import {m}")
        for m in sorted(imported - on_disk):
            stray.append(f"Descent/{entry}.lean imports {m}, which is not under it")
        body = _re.sub(r"/-.*?-/", " ", text, flags=_re.S)
        if decl.search(body):
            declaring.append(f"Descent/{entry}.lean declares something; a head is a "
                             f"table of contents")

    for line in missing + stray + declaring:
        print(f"  {line}")
    total = len(missing) + len(stray) + len(declaring)
    if total:
        print(f"heads guard FAILS: {total} problem(s); a head must be exactly its "
              f"directory, and nothing else")
        return 1
    print("heads guard: every directory head imports exactly its own modules")
    return 0


GUARDS = {
    "heads":           dict(fn=run_heads,           gated=True,  takes_argv=False),
    "style":           dict(fn=run_style,           gated=True,  takes_argv=False),
    "identifications": dict(fn=run_identifications, gated=True,  takes_argv=False),
    "duplication":     dict(fn=run_duplication,     gated=True,  takes_argv=False),
    "mathlib":         dict(fn=run_mathlib,         gated=True,  takes_argv=False),
    "laundering":      dict(fn=run_laundering,      gated=True,  takes_argv=True),
    "regimes":         dict(fn=run_regimes,         gated=True,  takes_argv=False),
    "closure":         dict(fn=run_closure,         gated=True,  takes_argv=False),
    "wiring":          dict(fn=run_wiring,          gated=True,  takes_argv=True),
    "conventions":     dict(fn=run_conventions,     gated=True,  takes_argv=False),
    # `ledger` is DIAGNOSTIC for one commit only, and for one reason, recorded
    # here so it is not forgotten: it currently reports seven docstring
    # citations to `simcov/battery_bulk19.py` and `simcov/battery_bulk20.py`,
    # whose results were never committed.  Those are true findings -- six
    # definitions assert an empirical status against evidence that does not
    # exist in the repository -- and the fix is to land the results, which is
    # GATED.  The condition this entry set for itself -- flip when
    # `battery_bulk19_results.json` and `battery_bulk20_results.json` land -- is met:
    # both files are committed, the seven citations they blocked resolve, and the
    # guard's gated rules are at zero.  It ran diagnostic for exactly as long as its
    # stated reason lasted, which is the only thing that separates a ratchet from a
    # permanent exemption.
    #
    # Its `REPORTED, NOT GATED` section still names seven citations that reach a
    # battery emitting numbers and calling `record()` nowhere.  Those are outstanding
    # and they do NOT gate: the repair is a `record()` call in three battery scripts
    # and a rerun, not a change here.  That category is the next thing to flip.
    "ledger":          dict(fn=run_ledger,          gated=True,  takes_argv=False),
    # GATED, where `ledger` is not, and the difference is the population.  This
    # one reads seven files' worth of declarations at depth 0-1, small enough to
    # hold at zero by hand; `ledger` reads 2164 and reports its sharpest rules
    # because a budget pinned to their count would be worse than none.
    "core-empirics":   dict(fn=run_core_empirics,   gated=True,  takes_argv=False),
    "field-proofs":    dict(fn=run_field_proofs,    gated=True , takes_argv=False),
    # THE SHAPE GUARDS. One is gated and four are DIAGNOSTIC, for the reason the
    # `ledger` entry above records: each of the four reports true findings whose
    # fixes are in flight, and gating them today breaks the build for everyone while
    # the repair lands. The budgets are the budgets and they do not move. What flips
    # each one is named on its line; run `--only <name>` for the outstanding count,
    # which is also the work list.
    #
    # The counts quoted below were true when written and every one of them has moved
    # since, in both directions -- `shape-components` went UP when a new subsystem
    # arrived as an island, which is the recurrence these guards exist to catch,
    # happening while they were being written. Read the guard, not the comment.
    #
    # `shape-depth`: GATED, flipped from diagnostic once it reached the limit. The
    # audit measured 37 on a chain of 38 modules; the chain repairs brought it to
    # exactly 12.
    #
    # THERE IS NO HEADROOM, and that is deliberate rather than an oversight. One
    # import added to the wrong module fails this, which is the whole reason to gate
    # it now rather than after it has drifted back: the depth has been repaired
    # before and lost again, and a limit set above the current value is a licence to
    # regress to it. If a module legitimately needs a thirteenth rung, the fix is
    # not to raise `SHAPE_DEPTH_LIMIT` -- it is that some link on the chain the
    # guard prints is importing a file rather than a dependency, and `shape-chains`
    # will usually name it.
    "shape-depth":     dict(fn=run_shape_depth,      gated=True,  takes_argv=False),
    # `shape-chains`: flip when no module's only internal import is a sibling it
    # names nothing from. Measured 38 when the audit asked for this, six of them
    # consecutive files in `PopGen/PopulationGeneticsFoundations`; 28 as the repair
    # lands. Each line of the output names the module the file should have imported.
    "shape-chains":    dict(fn=run_shape_chains,     gated=True , takes_argv=False),
    # `shape-components`: flip when every module lies in the corpus's one weak
    # component. `Pangenome`'s island closed while this was being written, and a new
    # `Descent/Meta/` arrived as one on the same day -- which is the whole case for
    # the guard: the previous two islands were each found by an audit and fixed by
    # hand, and the third was caught within hours by a check. Three singletons also
    # remain: `BundleRigidity/LinearSCM`, `BundleRigidity/Operator` and
    # `Spectral/ResonanceSpectrum`, each importing nothing from the corpus and
    # imported by nothing in it.
    "shape-components": dict(fn=run_shape_components, gated=True , takes_argv=False),
    # `shape-spine`: flip when cross-module theorem reuse reaches 20% and the corpus
    # states 80 theorems joining `PopGenParameters` to a deployed metric. Both are
    # far off -- just under 12%, and 19 -- and the second is the sharper number:
    # all nineteen are in `Core/Moments.lean`, so the spine exists and is one file
    # long. This is the one of the five that no amount of moving imports around
    # will fix; it needs theorems that do not exist yet.
    "shape-spine":     dict(fn=run_shape_spine,      gated=True , takes_argv=False),
    # GATED, alone among the five, because its count is already zero:
    # `deployedR2FromIsland` was deleted while these guards were being written and
    # nothing has taken its place. Calibrated against a fixture carrying that pair,
    # since a guard that has only ever reported zero has not been shown to fire.
    "shape-routes":    dict(fn=run_shape_routes,     gated=True,  takes_argv=False),
    # DIAGNOSTIC for the reason the `ledger` entry above records, and the outstanding
    # findings are two different things that flip it at two different times.
    #
    # ORDER/CORE/NARRATIVE/META: 19 cross-layer edges, every one argued for by name in
    # `LAYER_PENDING`, and every one a real inversion whose repair is content moving
    # between directories. Flip when that table is empty. It was 27 one release ago;
    # the ones that went were not fixed by moving anything, they were imports carrying
    # Mathlib or the programme narrative and naming nothing from what they imported.
    #
    # REACHABLE: 0, and read that zero narrowly -- it covers qualified cross-directory
    # names and not the unqualified ones, which on the one commit where both were
    # counted outnumbered them fourteen to one. The rule's own comment says why the
    # obvious widening is not here and what instrument does cover it.
    #
    # It was 17 and the history is the point rather than the number. Each is a file
    # naming a declaration it does not reach, which means it does not compile, and
    # every one arrived this release from an import repair -- the count against
    # `62bbadb` is zero. The fix is one import line per file, naming the module that
    # DEFINES the name; `PopulationGeneticsFoundations` has already had five such lines
    # land and they are the five newest entries in `LAYER_PENDING`.
    #
    # WHEN REACHABLE IS BACK AT ZERO IT SHOULD BE SPLIT OUT AND GATED ON ITS OWN rather
    # than waiting on `LAYER_PENDING`. It is the only rule in this file that has been
    # demonstrated silent on a whole corpus and nonzero on another, and holding a
    # calibrated rule hostage to an uncalibrated one is how a gate never lands.
    "layers":          dict(fn=run_layers,           gated=True , takes_argv=False),
}


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)

    ap = argparse.ArgumentParser(
        prog="check.py",
        description="Code validation for the proof corpus (source-text half).",
        epilog="Flags after `--only NAME` are passed to that guard.",
    )
    ap.add_argument("--only", metavar="NAME",
                    help="run one guard (see --list); remaining flags go to it")
    ap.add_argument("--list", action="store_true", help="list the guards and exit")
    args, rest = ap.parse_known_args(argv)

    if args.list:
        width = max(len(n) for n in GUARDS)
        for name, spec in GUARDS.items():
            print(f"  {name:{width}s}  {'gated' if spec['gated'] else 'diagnostic'}")
        return 0

    if args.only:
        if args.only not in GUARDS:
            print(f"unknown guard {args.only!r}; --list shows them all",
                  file=sys.stderr)
            return 2
        selected = [args.only]
    else:
        if rest:
            # Guard-specific flags are meaningless without --only: there is no
            # sensible way to route `--family` when every guard is running and
            # only one understands it.  Silently ignoring them would be worse.
            print(f"unrecognised arguments {rest} -- pass them after --only NAME",
                  file=sys.stderr)
            return 2
        selected = [n for n, s in GUARDS.items() if s["gated"]]

    # A single-guard run prints exactly what that guard printed when it was its
    # own script, with no banner and no trailing verdict.  Callers parse this
    # output by line offset -- `cluster-lean-build.sh` does `sed -n '3,20p'` on
    # the laundering summary -- and a decorative header silently shifts every
    # one of those windows onto the wrong lines.
    if len(selected) == 1:
        spec = GUARDS[selected[0]]
        return 1 if (spec["fn"](rest) if spec["takes_argv"] else spec["fn"]()) else 0

    failures = []
    for name in selected:
        spec = GUARDS[name]
        print(f"\n{'=' * 78}\n== {name}\n{'=' * 78}")
        # A guard that raises is a failing guard, not a failing RUN.  Letting the
        # exception escape aborted the sweep at the first crash, so every guard
        # after it never ran and the output ended in a traceback that looked like
        # a tooling problem rather than a corpus one.  Worse, a caller piping
        # this through `tail` saw the pipeline's exit status and read the whole
        # thing as a pass.  Each guard is now isolated: the crash is reported
        # against that guard, and the remaining guards still run.
        try:
            code = spec["fn"](rest) if spec["takes_argv"] else spec["fn"]()
        except Exception as exc:  # noqa: BLE001 -- a guard may fail any way it likes
            traceback.print_exc()
            print(f"GUARD CRASHED: {name}: {exc}")
            failures.append(name)
            continue
        if code:
            failures.append(name)

    print(f"\n{'=' * 78}")
    if failures:
        # Name every failing guard, not just the first.  A run that stops at the
        # first failure trains a reader to fix one thing and re-run, which is how
        # a six-guard sweep turns into six round trips.
        print(f"FAIL: {len(failures)} of {len(selected)} guard(s) failed: "
              f"{', '.join(failures)}")
        return 1
    print(f"PASS: {len(selected)} guard(s) passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
