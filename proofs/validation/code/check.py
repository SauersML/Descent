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

    python3 proofs/validation/code/check.py

Run one guard:

    python3 proofs/validation/code/check.py --only laundering
    python3 proofs/validation/code/check.py --only laundering --strict
    python3 proofs/validation/code/check.py --list

Exit is nonzero if any guard that ran fails.  Guard-specific flags go after the
guard name; `--only laundering --json out.json` reaches the laundering guard.

THE GUARDS, and what each one catches:

  style           mathlib-style policy: copyright header, module docstring,
                  import placement, line length, snake_case theorem names,
                  `↦` over `=>`, and documentation that narrates development
                  history rather than mathematics.
  identifications structural guards over the corpus: admissions (`sorry` is
                  reported, `admit` is forbidden), convention drift, equilibria
                  with no dynamic, duplicate bodies, and the budget ratchets.
  laundering      a valid proof of a weaker, conditional, vacuous or circular
                  statement advertised under the intended theorem's name.
  regimes         external theorem packaging in production structures: a
                  scientific conclusion accepted from a caller and re-exported
                  by field projection.
  closure         a Calibrator module outside the root import closure, which
                  `lake build Calibrator` cannot validate and so cannot fail on.
  wiring          an upstream-arc module with no biological dependent: a result
                  adjacent to the corpus rather than wired into it.
  field-proofs    theorems whose ENTIRE proof is a structure-field projection,
                  measured on origin/main rather than the worktree.  DIAGNOSTIC,
                  not a gate: it has known false positives and never fails the
                  run.  It is excluded from the default set because it shells
                  out to git and reads a remote ref.

WHY ONE FILE.  These seven were seven scripts in three directories, and the cost
was not tidiness.  Three of them independently re-derived "which files are the
corpus" and the three answers disagreed; one walked `proofs/Calibrator/` and
could not see `proofs/Calibrator.lean`, the corpus root, which is a SIBLING of
that directory rather than a child.  Two definitions were deleted as unreferenced
on the strength of that blind spot.  There is now exactly one `REPO`, one
`PROOFS`, and one place to look.

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
# proofs/validation/code/check.py, so parents[3] is the repository root.
REPO = Path(__file__).resolve().parents[3]

# GNOMON_CORPUS points every guard at a different tree, and exists so the guards
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
# Unset, this is `<repo>/proofs` and nothing changes.
PROOFS = Path(os.environ.get("GNOMON_CORPUS") or (REPO / "proofs"))

# What findings are reported relative to.  It must track the tree actually
# scanned: `relative_to` RAISES on a path outside its argument, so a guard
# reporting relative to REPO aborts outright on any corpus outside the
# repository -- which is every fixture.
CORPUS_BASE = PROOFS.parent


def lean_sources(root: Path) -> list:
    """Every Lean source under `root`, in a stable order, excluding junk.

    One place decides what counts as a corpus file, because the alternative is
    what this replaced: four separate `rglob("*.lean")` walks, exactly one of
    which skipped AppleDouble `._*` files.  Those are resource forks written by
    macOS tar and by some copy tools; they are not UTF-8, they are not Lean, and
    a walk that includes them either crashes on decode or reports findings for a
    file nobody wrote.  Dotfiles are excluded for the same reason -- editor swap
    files and `.#` locks are not corpus.
    """
    return sorted(
        path
        for path in root.rglob("*.lean")
        if not any(part.startswith(".") for part in path.parts)
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
    for path in lean_sources(PROOFS):
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
# Was `proofs/validation/code/check.py`.
#
# Check repository Lean sources against the local mathlib style policy.
# ======================================================================================

# The header is checked for SHAPE, not for a particular name.  Pinning the
# author made the rule reject every file a second contributor wrote, and the only
# way to satisfy it was to rewrite someone else's attribution -- which is worse
# than the defect it was guarding against.  What matters is that the block is
# present, is the mathlib form, and names somebody.
STYLE_COPYRIGHT_HEADER = re.compile(
    r"\A/-\n"
    r"Copyright \(c\) \d{4} [^\n]+\. All rights reserved\.\n"
    r"Released under Apache 2\.0 license as described in the file LICENSE\.\n"
    r"Authors: [^\n]+\n"
    r"-/\n"
)


def style_lean_files() -> list[Path]:
    """Return source-controlled Lean-shaped files, excluding macOS resource forks."""
    # The lakefile is corpus for style purposes but sits beside `proofs/`
    # rather than inside it, and a fixture tree has none.
    files = [f for f in [CORPUS_BASE / "lakefile.lean"] if f.is_file()]
    files.extend(
        path for path in lean_sources(PROOFS)
    )
    return sorted(files)


def style_line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def style_check_file(path: Path) -> list[str]:
    source = path.read_text()
    rel = path.relative_to(CORPUS_BASE)
    errors: list[str] = []

    if not STYLE_COPYRIGHT_HEADER.match(source):
        errors.append(f"{rel}:1: missing or nonstandard copyright header")

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
        # The header block is five lines: `/-`, three body lines, `-/`.
        expected_first_import = 6
        if import_lines[0] != expected_first_import:
            errors.append(
                f"{rel}:{import_lines[0]}: imports must immediately follow the copyright header"
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
# Was `proofs/validation/code/check.py`.  Its full header, which carries the
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
#    (a) WRONG ROOT. A scan walking `proofs/Calibrator/` cannot see
#        `proofs/Calibrator.lean`, the corpus root, which is a SIBLING of that
#        directory rather than a child. `decaySlope` was deleted as having "no use
#        anywhere"; its only consumer was a theorem in the root. `LDDecayMechanism`
#        was then deleted for having "lost its only consumer" -- the second
#        deletion inheriting the first's blind spot. The file list built below
#        includes `Calibrator.lean` explicitly for exactly this reason; do not
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
#    result whose name hides what it rests on (3p). Each count is pinned at what
#    was measured and ratchets down, so the corpus cannot acquire new ones.
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
# Guards 5-7 are the subject of `Calibrator.DriftRegime`, which proves that 6 and 7
# are impossibilities rather than oversights.

# Was `os.path.join(os.path.dirname(__file__), "..", "proofs")` when this guard
# lived in `scripts/`.  It is now derived from the one `PROOFS` above, which is
# the point of the merge: three guards used to re-derive this and disagree.
IDENT_ROOT = str(PROOFS)

# Every budget is 0. Nothing is grandfathered: a screen that permits N existing
# instances of the defect it names is a screen that has agreed to the defect,
# and "it was already there" is not a standard. A count above 0 fails the build.
CONVENTION_SITE_BUDGET = 0          # ploidy/coalescent constants restated inline
ISOLATED_MODULE_BUDGET = 0          # modules no theorem cross-relates to another
UNDECLARED_BUDGET = 0               # empirical defs with no status marker
UNRELATED_BUDGET = 0                # same-quantity siblings no theorem relates
MISSING_ARG_BUDGET = 0              # signatures omitting a dependency of the named quantity
CONFLATION_BUDGET = 0               # one formula under names from different concept families
CONVENTION_DECL_BUDGET = 0          # composable quantities with no declared convention
OVERCLAIM_BUDGET = 0                # untested definitions whose docstring claims exactness
EQUILIBRIUM_BUDGET = 0              # equilibria stipulated as a closed form, never derived
DUPLICATE_BODY_BUDGET = 0           # one body under two names, tied by nothing
REGIME_DECL_BUDGET = 0              # drift regimes baked into a body instead of a hypothesis
UNDERDELIVERY_BUDGET = 0            # docstring attributes an identity the signature does not prove
INHERITED_VALIDATION_BUDGET = None  # VALIDATED inherited from a sibling identity; pin on first run
VACUOUS_VALIDATION_BUDGET = None    # VALIDATED with no recorded power; pin on first run
LAUNDERED_PROP_BUDGET = 0           # named propositions only ever assumed, never established
UNWITNESSED_BUNDLE_BUDGET = 0       # assumption bundles no concrete construction satisfies
INSTANCE_LAUNDERING_BUDGET = 0      # supplied fields turned into silently-binding instances
UNCONDITIONAL_NAME_BUDGET = 0       # conditional results named as though unconditional
DOMAIN_NAMED_ARITHMETIC_BUDGET = 0  # genetics in the name, free reals in the goal

# THE RECORD THE ZEROING WOULD OTHERWISE HAVE DESTROYED.
#
# Seven of the budgets above were not always 0. They were pinned at a MEASURED
# count and ratcheted downwards, and the guard's own header still describes that
# discipline: each count "pinned at what was measured", so "the corpus cannot
# acquire new ones". Those numbers were the measurement. Setting them all to 0
# in a single edit enforces the right standard and destroys the record at the
# same time, and without the record nobody can read a later run: 7 unwitnessed
# bundles is excellent progress from 38 and a bad regression from 0, and the
# number alone does not say which.
#
# So the standard is 0 and the history is kept here. Each entry is the last value
# the budget carried before the zeroing, and the commit that set it.
#
# Two of the seven have since been genuinely cleared to 0 -- LAUNDERED_PROP from
# 16, UNCONDITIONAL_NAME from 35. That is only visible because the old numbers
# are written down.
LAST_PINNED_BEFORE_ZEROING = {
    "ISOLATED_MODULE_BUDGET":         (14, "ee0302c8", "2026-08-01"),
    "UNRELATED_BUDGET":               (20, "c1881cb4", "2026-08-01"),
    "LAUNDERED_PROP_BUDGET":          (16, "cfcff551", "2026-08-03"),
    "UNWITNESSED_BUNDLE_BUDGET":      (38, "cfcff551", "2026-08-03"),
    "INSTANCE_LAUNDERING_BUDGET":     (2,  "cfcff551", "2026-08-03"),
    "UNCONDITIONAL_NAME_BUDGET":      (35, "cfcff551", "2026-08-03"),
    "DOMAIN_NAMED_ARITHMETIC_BUDGET": (90, "12e5ce63", "2026-08-03"),
}
# CONVENTION_SITE_BUDGET and ISOLATED_MODULE_BUDGET have a longer history worth
# keeping, because it is the evidence that a 0 here is reachable rather than
# rhetorical. Convention sites were ratcheted 101, 100, 99, 93, 86, 79, 77, 76,
# 43, 37, 29, 15, 7, 0 across fourteen commits on 2026-08-01, each decrement made
# after the count had actually reached it, and the guard passed at 0. Isolated
# modules went 23, 22, 21, 19, 17, 15, 14 over the same day and passed at 14.
# Both have since regressed, which is what the screens are for.

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
    literally `end Calibrator`. That is only one of several correct ways to
    close the namespace: `end Calibrator.CertificateGrading` closes
    `namespace Calibrator.CertificateGrading`, and a matched inner `end Foo`
    followed by `end Calibrator` is equally correct. Both were reported as
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

def ident_preceding_docstring(lines, i):
    """The whole `/-- ... -/` block attached to the declaration on line `i`.

    The status may be declared anywhere in a docstring, and these run to forty
    lines, so a fixed lookback window reports a declared status as missing and
    invites a second, contradictory marker next to the first. The block is
    delimited, so read the delimiters."""
    j = i - 1
    while j >= 0 and (not lines[j].strip() or lines[j].lstrip().startswith("@[")):
        j -= 1
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

def ident_lean_files():
    return (glob.glob(os.path.join(IDENT_ROOT, "Calibrator", "*.lean")) +
            glob.glob(os.path.join(IDENT_ROOT, "Calibrator", "*", "*.lean")) +
            [os.path.join(IDENT_ROOT, "Calibrator.lean")])

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
            (r"(?m)^\s*(?:syntax|macro|macro_rules|elab|elab_rules|initialize|builtin_initialize|run_cmd|run_tac)\b",
             "installs custom syntax, elaboration, or initialization code"),
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
            # `local instance : Fact (2 ≤ 2) := ⟨by decide⟩` in Calibrator.lean
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
    defpat = re.compile(r'^(?:noncomputable )?def ([A-Za-z_0-9\'.]+)(.*?)(?=\n(?:/-|@\[|theorem |noncomputable |def |abbrev |structure |section |end |namespace ))', re.S | re.M)
    # A convention restatement is a 2 or a 4 adjacent to a population-genetic
    # parameter: 2 Ne, 4 Ne mu, 2 p (1 - p). The 2 in a Gaussian density or in
    # a quadratic expansion is not a ploidy convention, and tying it to `ploidy`
    # would be wrong, so the pattern requires the neighbouring symbol.
    POP = r"(?:Ne|N|N_b|N₀|N₁|mu|μ|m|m_rate|m_into|mig|p|p0|p₁|p₂|p_bar|maf|fst|freq|theta|θ|sigma_sq)"
    mult = re.compile(r"(?<![\^A-Za-z_0-9.])[24]\s*\*\s*(?:\([^)]*\)|[A-Za-z_0-9.]*\.)?" + POP + r"\b"
                      r"|/\s*\(\s*[24]\s*\*\s*(?:[A-Za-z_0-9.]*\.)?" + POP + r"\b"
                      r"|\b(?:[A-Za-z_0-9]+\.)?" + POP + r"\s*\*\s*[24]\b")
    # Definitions that a Conventions theorem relates back to `ploidy` or to a
    # derived primitive are not loose restatements: their constant is forced.
    tied = set()
    for f in ident_lean_files():
        if not f.endswith("Conventions.lean"):
            continue
        conv = ident_strip_comments(open(f).read())
        for b in re.split(r"\n(?=theorem )", conv):
            if not b.startswith("theorem"):
                continue
            stmt = b.split(":=", 1)[0]
            tied.update(re.findall(r"[A-Za-z_][A-Za-z_0-9']*", stmt))

    sites = 0
    for f in ident_lean_files():
        if f.endswith("Conventions.lean"):
            continue
        src = ident_strip_comments(open(f).read())
        for m in defpat.finditer(src):
            body = m.group(2)
            body = body.split(":=", 1)[1] if ":=" in body else ""
            body = re.sub(r'\^\s*[0-9]+', '', body)
            if mult.search(body) and m.group(1).split(".")[-1] not in tied:
                sites += 1
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
    DOMAIN = re.compile(r"fst|drift|selection|herit|linkage|allele|geno|migrat|coalesc|mutation|"
                        r"epistat|domin|recomb|ancestr|spike|admix|haplo|polygenic|prevalence|"
                        r"liability|penetrance|pgs|gwas|singleton|winners|power|ncp|effect", re.I)
    DOMAIN_CASED = re.compile(r"^ld|(?:^|[a-z0-9])LD(?=[A-Z_]|$)")
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
            if "Empirical status:" not in ident_preceding_docstring(raw, i):
                undeclared.append(f"{os.path.relpath(f, IDENT_ROOT)}: `{short}` has no Empirical status")
    if len(undeclared) > UNDECLARED_BUDGET:
        bad.append(f"definitions making an empirical claim without an Empirical status marker: "
                   f"{len(undeclared)}, budget {UNDECLARED_BUDGET}")
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
            norm = re.sub(r"[A-Za-z_][A-Za-z_0-9₀-₉'.]*",
                          lambda t: "V" if t.group(0) in bound else t.group(0), body)
            if not re.search(r"[0-9]|[A-Za-z_]{3,}", norm.replace("V", "")):
                continue
            groups.setdefault(norm, []).append((mod, name.split(".")[-1]))
    all_stmts = []
    for f in ident_lean_files():
        for b in re.split(r"\n(?=@\[simp\]\s*\n?theorem |theorem |private theorem )",
                          ident_strip_comments(open(f).read())):
            if re.match(r"(?:@\[simp\]\s*)?(?:private )?theorem ", b) and ":=" in b:
                all_stmts.append(b.split(":=", 1)[0])
    # A definition tied to a shared primitive in Conventions is related in the
    # stronger sense: its whole group is pinned to one object rather than to
    # each other pairwise. Credit that, or the metric penalises exactly the
    # refactor it exists to encourage.
    primitives = set()
    for f in ident_lean_files():
        if not f.endswith("Conventions.lean"):
            continue
        for m in re.finditer(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)",
                             ident_strip_comments(open(f).read()), re.M):
            primitives.add(m.group(1).split(".")[-1])

    unrelated = 0
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
                unrelated += 1
    if unrelated > UNRELATED_BUDGET:
        bad.append(f"same-quantity definitions never related to a sibling by any theorem: "
                   f"{unrelated}, budget {UNRELATED_BUDGET}")

    # 3d. Missing-argument screen. Six of the eleven falsified definitions failed
    #     the same way: the signature omits an argument the named quantity is
    #     known to depend on. No constant repairs such a definition, and the
    #     defect is visible statically, without any simulation. Each entry is a
    #     name pattern together with the arguments that quantity must depend on.
    PREVALENCE_FREE = {"populationAUC"}   # rank definition, prevalence-free by construction
    REQUIRED_ARGS = [
        (r"power",            [r"alpha", r"z_?alpha", r"threshold", r"level"],
         "statistical power depends on the significance threshold"),
        (r"auc",              [r"prev", r"k\b", r"pi\b", r"baseRate"],
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
    ]
    missing = []
    for f in ident_lean_files():
        body_all = ident_strip_comments(open(f).read())
        for m in re.finditer(r"^(?:noncomputable )?def ([A-Za-z_0-9'.]+)([^:]*):", body_all, re.M):
            name, args = m.group(1).split(".")[-1], m.group(2)
            if name in PREVALENCE_FREE or re.search(r"gaussian|interval|approximation", name, re.I):
                continue   # name declares the model it is exact for, or is a wrapper
            for pat, needed, why in REQUIRED_ARGS:
                if not re.search(pat, name, re.I):
                    continue
                if not any(re.search(a, args, re.I) for a in needed):
                    missing.append(f"{os.path.relpath(f, IDENT_ROOT)}: `{name}` takes no "
                                   f"{needed[0]}-like argument; {why}")
    if len(missing) > MISSING_ARG_BUDGET:
        bad.append(f"definitions omitting an argument the named quantity depends on: "
                   f"{len(missing)}, budget {MISSING_ARG_BUDGET}")
        bad.extend("    " + x for x in missing)

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
    if len(overclaim) > OVERCLAIM_BUDGET:
        bad.append(f"untested definitions whose docstring claims exactness: "
                   f"{len(overclaim)}, budget {OVERCLAIM_BUDGET}")
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
    if len(undeclared_conv) > CONVENTION_DECL_BUDGET:
        bad.append(f"definitions taking an ambiguity-prone quantity with no declared "
                   f"convention: {len(undeclared_conv)}, budget {CONVENTION_DECL_BUDGET}")
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
    if len(conflated) > CONFLATION_BUDGET:
        bad.append(f"definitions sharing one formula across concept families with no Denotes "
                   f"declaration: {len(conflated)}, budget {CONFLATION_BUDGET}")
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
            if any(o != short and names_an_equilibrium(o) and
                   re.search(r"\b" + re.escape(o) + r"\b", body) for o in allnames):
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
    if len(stipulated) > EQUILIBRIUM_BUDGET:
        bad.append(f"equilibrium definitions with no theorem deriving them as the fixed point "
                   f"of a process in the same file: {len(stipulated)}, budget {EQUILIBRIUM_BUDGET}; "
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
            norm = alpha_normal(args, body)
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
                        re.findall(r"^import (Calibrator\.[\w.]+)", open(f).read(), re.M)]

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
                # and as `agreement`, and `UnifiedBiology` does the same as
                # `persistentTransition` and `contextMatchQuality`. Both were
                # invisible while the five CROSS-file pairings of those very
                # definitions were reported. A check that reports the weaker
                # instance and hides the stronger one produces a count people
                # trust, which is worse than no count.
                #
                # Only an entry paired with itself is skipped now.
                if fa == fb and na == nb and la == lb:
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
    if len(duplicates) > DUPLICATE_BODY_BUDGET:
        bad.append(f"alpha-equivalent definition bodies tied by neither a call nor a theorem: "
                   f"{len(duplicates)}, budget {DUPLICATE_BODY_BUDGET}; make one call the "
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
    #     which data-generating process it assumes. `Calibrator.DriftRegime`
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
    if len(regimeless) > REGIME_DECL_BUDGET:
        bad.append(f"definitions encoding a drift regime with no declared Regime: "
                   f"{len(regimeless)}, budget {REGIME_DECL_BUDGET}; name the "
                   f"data-generating assumption, see Calibrator.DriftRegime")
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

    def attributed_identity(doc):
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
            if any(re.search(p, s, re.I) for p in ATTRIBUTION):
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
            if delivers_identity(goal_of(header_of(block))):
                continue
            claim = attributed_identity(doc)
            if claim:
                underdelivered.append(
                    f"{os.path.relpath(f, IDENT_ROOT)}:{raw[:m.start()].count(chr(10)) + 1}: "
                    f"`{name}` claims an identity its conclusion does not state: "
                    f"\"{claim}\"")
    if len(underdelivered) > UNDERDELIVERY_BUDGET:
        bad.append(f"docstrings attributing an identity the statement does not deliver: "
                   f"{len(underdelivered)}, budget {UNDERDELIVERY_BUDGET}; state the "
                   f"identity in the conclusion, or stop claiming it in the prose")
        bad.extend("    " + x for x in underdelivered)

    # 3k. Validation inherited from a sibling identity. Over-determination
    #     detects divergence between independently written formulas and is
    #     provably blind to a premise they share
    #     (`Calibrator.DriftRegime.crossChecks_blind_to_retention`): every identity
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
    #     Reported, not enforced, until the count is measured once and pinned:
    #     these two guards are retroactive over twenty existing VALIDATED tags,
    #     and failing the build on all of them at once would be noise rather than
    #     signal. Pin INHERITED_VALIDATION_BUDGET to the first reported count and
    #     ratchet it down, exactly as CONVENTION_SITE_BUDGET was.
    if INHERITED_VALIDATION_BUDGET is None:
        for x in inherited[:10]:
            print(f"  advisory (inherited validation): {x}")
    elif len(inherited) > INHERITED_VALIDATION_BUDGET:
        bad.append(f"VALIDATED tags justified by a sibling identity rather than a measurement: "
                   f"{len(inherited)}, budget {INHERITED_VALIDATION_BUDGET}")
        bad.extend("    " + x for x in inherited)

    # 3l. Validation with no power. `neutralAFBenchmarkRatio` was recorded as
    #     validated to 3.2 percent. The design was symmetric, so both sides of the
    #     ratio collapsed to ~1 and the test could not have failed;
    #     `Calibrator.DriftRegime.symmetric_design_has_no_power` proves that on any
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
            nums = [float(x) for x in re.findall(r"\d+\.\d+", power.group(1))]
            if len(nums) < 2:
                powerless.append(f"{os.path.relpath(f, IDENT_ROOT)}: a Power clause names fewer than "
                                 f"two predicted values, so no span is declared")
            elif max(nums) - min(nums) <= 0.05 * max(abs(max(nums)), 1.0):
                powerless.append(f"{os.path.relpath(f, IDENT_ROOT)}: a Power clause declares a span of "
                                 f"only {max(nums) - min(nums):.4f}; a near-constant prediction "
                                 f"cannot reject a wrong functional form")
    if VACUOUS_VALIDATION_BUDGET is None:
        for x in powerless[:12]:
            print(f"  advisory (validation power unstated): {x}")
    elif len(powerless) > VACUOUS_VALIDATION_BUDGET:
        bad.append(f"VALIDATED tags whose design had no recorded power: {len(powerless)}, "
                   f"budget {VACUOUS_VALIDATION_BUDGET}; record the spread of the prediction "
                   f"across the design, see Calibrator.DriftRegime")
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
    if len(laundered) > LAUNDERED_PROP_BUDGET:
        bad.append("named propositions only ever assumed, never established: %d, budget %d; "
                   "prove one concrete object satisfies it, or admit it with `sorry` so the "
                   "debt is enumerable" % (len(laundered), LAUNDERED_PROP_BUDGET))
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
    if len(unwitnessed) > UNWITNESSED_BUNDLE_BUDGET:
        bad.append("hypothesis bundles no construction ever satisfies: %d, budget %d; "
                   "build one concrete instance, or the theorems over it are vacuous"
                   % (len(unwitnessed), UNWITNESSED_BUNDLE_BUDGET))
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
    if len(laundered_inst) > INSTANCE_LAUNDERING_BUDGET:
        bad.append("supplied hypotheses installed as typeclass instances: %d, budget %d; "
                   "pass the fact explicitly so the dependency stays visible in the signature"
                   % (len(laundered_inst), INSTANCE_LAUNDERING_BUDGET))
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
    if len(misnamed) > UNCONDITIONAL_NAME_BUDGET:
        bad.append("conditional results named as though unconditional: %d, budget %d; "
                   "name the assumption in the theorem or declare `Assumes:` in its docstring"
                   % (len(misnamed), UNCONDITIONAL_NAME_BUDGET))
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
        r"portab|drift|heritab|genetic|genom|(?<!in)variant|locus|loci|allele|pgs|"
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

    domain_named_arithmetic = []
    for tname, stmt in global_theorems:
        if not DOMAIN_WORD.search(tname):
            continue
        goal = goal_of(statement_of(full_decl.get(tname, stmt)))
        if set(re.findall(IDENT, goal)) & corpus_vocab:
            continue
        domain_named_arithmetic.append(
            "`%s` names genetics but its goal mentions no constant this corpus "
            "defines" % tname)
    if DOMAIN_NAMED_ARITHMETIC_BUDGET is None:
        print(f"  advisory (genetics-asserting names on domain-free statements): "
              f"{len(domain_named_arithmetic)}")
        for x in domain_named_arithmetic[:12]:
            print(f"    {x}")
    elif len(domain_named_arithmetic) > DOMAIN_NAMED_ARITHMETIC_BUDGET:
        bad.append("genetics-asserting names on domain-free statements: %d, budget %d; "
                   "either state the theorem about a defined quantity or name it for "
                   "the arithmetic it does"
                   % (len(domain_named_arithmetic), DOMAIN_NAMED_ARITHMETIC_BUDGET))
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
        for imp in re.findall(r"^import (Calibrator[A-Za-z.]*)", raw, re.M):
            if not os.path.exists(os.path.join(IDENT_ROOT, imp.replace(".", "/") + ".lean")):
                bad.append(f"{rel}: imports {imp}, which does not exist")

    # 4. semantic isolation. A module that no theorem ever relates to another
    #    module cannot be contradicted by anything: a false definition inside it
    #    is consistent with the whole corpus. This is the condition that let two
    #    falsified identifications survive review, so the count is ratcheted.
    owner = {}
    for f in ident_lean_files():
        mod = os.path.basename(f)[:-5]
        for m in re.finditer(r"^(?:noncomputable )?(?:def|abbrev|structure) ([A-Za-z_0-9'.]+)",
                             ident_strip_comments(open(f).read()), re.M):
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
    if len(isolated) > ISOLATED_MODULE_BUDGET:
        bad.append(f"semantically isolated modules rose to {len(isolated)}, budget "
                   f"{ISOLATED_MODULE_BUDGET}: {', '.join(isolated)}; relate the new "
                   f"module's quantities to an existing one so it can be contradicted")

    if sites > CONVENTION_SITE_BUDGET:
        bad.append(f"convention restatement sites rose to {sites}, budget {CONVENTION_SITE_BUDGET}; "
                   f"relate the new constant to `ploidy` in Conventions.lean instead of inlining it")

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
        # A count means nothing without the count it is being compared to. Seven
        # of these screens were pinned at a measured number and then zeroed in one
        # edit; printing the old numbers next to the failures is what stops a
        # reader mistaking progress for regression, or the reverse.
        print("\nPREVIOUSLY PINNED (budget is now 0 for all; nothing is grandfathered)\n")
        for name, (was, commit, when) in sorted(LAST_PINNED_BEFORE_ZEROING.items()):
            print(f"  {name:32s} was {was:3d}  pinned {commit} {when}")
        return 1
    print(f"structural guards pass: convention sites {sites}/{CONVENTION_SITE_BUDGET}, "
          f"undeclared {len(undeclared)}/{UNDECLARED_BUDGET}, conventions {len(undeclared_conv)}/{CONVENTION_DECL_BUDGET}, "
          f"unrelated {unrelated}/{UNRELATED_BUDGET}, "
          f"stipulated equilibria {len(stipulated)}/{EQUILIBRIUM_BUDGET}, "
          f"duplicate bodies {len(duplicates)}/{DUPLICATE_BODY_BUDGET}, "
          f"isolated modules {len(isolated)}/{ISOLATED_MODULE_BUDGET}, "
          f"admissions {len(admissions)} (reported, not trusted)")
    return 0


# ======================================================================================
# GUARD: laundering -- proof of a weaker statement under the right name
#
# Was `proofs/validation/code/check.py`.  Its full header, which defines the standard
# and enumerates every family this guard detects, is reproduced immediately below.
# ======================================================================================

# Ban proof laundering: a valid Lean proof of a weaker, conditional, vacuous, or
# circular statement presented as the intended theorem.
#
# WHAT THIS IS NOT.  It is not a kernel check.  The kernel is not being fooled in any
# of the patterns below; every one of them typechecks.  `proofs/validation/code/check.py`
# guards the source text and `proofs/validation/code/Check.lean` guards the
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
# `proofs/validation/code/check.py` -- and it is deliberate.
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
#     F3   typeclass laundering: nonstandard class, `Fact`, `Nonempty`, `Inhabited`, or
#          a `letI`/`haveI`-installed instance standing in for a proof.
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
#     proofs/validation/code/check.py                  # whole corpus, human report
#     proofs/validation/code/check.py --severity fatal # only the fatal families
#     proofs/validation/code/check.py --json out.json  # machine-readable
#     proofs/validation/code/check.py path/to/File.lean ...
#
# Exit status is 1 if any FATAL or CONDITIONAL finding survives.  There is deliberately
# NO SUPPRESSION FILE.  A ledger of accepted laundering is how a corpus normalises it;
# if a finding is wrong, fix the detector and say why in this docstring.
#
# LIMITS, stated so a clean report is not over-read.  This is a source-text analysis: it
# sees what was typed, not what the elaborator produced.  It cannot see premises
# introduced by `export`ed instances from an import, a `Fact` synthesised at elaboration
# time, or a definition unfolded to something other than its written form.  The
# environment-level companion, `proofs/validation/code/Check.lean`, walks
# the fully elaborated telescope of every `Calibrator` declaration and is authoritative
# where the two disagree.  Run both.

FATAL, CONDITIONAL, FIDELITY = "FATAL", "CONDITIONAL", "FIDELITY"
SEVERITY_ORDER = {FATAL: 0, CONDITIONAL: 1, FIDELITY: 2}

# WHAT GATES, AND WHY IT IS NOT EVERYTHING.
#
# FATAL gates.  Those families are laundering proper: the declaration does not prove
# what its name says, and no amount of context makes that acceptable.
#
# CONDITIONAL does not gate by default, and this is a deliberate line rather than a
# concession.  A theorem of the form `(hx : 0 < x) : f x < f (x + 1)` has a Prop-valued
# premise and is ordinary mathematics; so does every theorem quantified over a model
# class that the corpus proves nonempty.  Gating on those would make the guard
# permanently red, and a permanently red guard is read as broken and then ignored --
# which is how the patterns it exists to catch get in.  The CONDITIONAL count is
# printed as a LEDGER on every run: it is the honest size of what this corpus assumes,
# it is meant to be read, and it is meant to go down.
#
# `--strict` gates on CONDITIONAL as well.  That is the standard the corpus is aiming
# at, and the flag exists so the aim is checkable rather than aspirational.
EXIT_ON = {FATAL}

FAMILY_SEVERITY = {
    "F1": FATAL, "F1b": FATAL, "F4": FATAL, "F7": FATAL, "F8": FATAL,
    "F9": FATAL, "F11": FATAL, "F24": FATAL,
    "F2": CONDITIONAL, "F3": CONDITIONAL, "F16": CONDITIONAL,
    "F19": CONDITIONAL, "F23": CONDITIONAL, "F22": FIDELITY, "F16s": FIDELITY,
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
    "F16s": "side condition on free variables (not laundering)",
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
        dm = re.search(r"/--(.*?)-/\s*$", pre, re.S)
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


def is_prop_type(ty: str, prop_aliases: set[str], prop_structs: set[str]) -> bool:
    """Whether a binder type is a PROPOSITION (a hypothesis), as opposed to data.

    `(f : α → Prop)` is data -- an abstract predicate parameter, reported separately.
    `(h : ∀ x, f x)` is a proposition.  The discriminator is the head, not the presence
    of the token `Prop`.
    """
    t = norm(ty)
    if not t:
        return False
    if re.search(r"(→|->)\s*Prop$", t) or t == "Prop":
        return False          # predicate-valued data, not an assumption
    if any(t.startswith(k + " ") or t == k for k in LOGIC) or t.startswith("¬"):
        return True
    d = depths(t)
    for op in REL + LOGIC:
        for k in range(len(t) - len(op) + 1):
            if t[k : k + len(op)] == op and d[k] == 0:
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
    return [b for b in d.binders if is_prop_type(b.type, c.prop_aliases, c.prop_structs)]


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
                        is_prop_type(b.type, c.prop_aliases, c.prop_structs):
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
                            if is_prop_type(x.type, c.prop_aliases, c.prop_structs)]
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
                        if not is_prop_type(fld.type, c.prop_aliases, c.prop_structs):
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
            fam = "F16" if substantive else "F16s"
            if b.kind in ("implicit", "instance", "strict") or b.inherited:
                add("F19", f"hidden premise `{b.kind}{' (section variable)' if b.inherited else ''}"
                           f" {b.name} : {_clip(b.type)}`")
            elif substantive:
                add("F16", f"premise `{b.name} : {_clip(b.type)}` assumes a fact about "
                           f"{', '.join(sorted(mentions)[:3])}")
            else:
                add("F16s", f"side condition `{b.name} : {_clip(b.type)}`")

        # F3 -- typeclass laundering.
        for b in d.binders:
            if b.kind != "instance":
                continue
            head = re.match(r"([A-Za-z_][\w.']*)", norm(b.type))
            if not head:
                continue
            base = head.group(1).split(".")[-1]
            if base in ASSUMPTION_CLASSES or (
                base in c.struct_fields and base not in STANDARD_CLASSES
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
                          if is_prop_type(b.type, c.prop_aliases, c.prop_structs))
            if not guarded:
                add("F21", f"conclusion divides by `{den}`, which no premise shows is "
                           f"nonzero; `x / 0 = 0` in Lean, so the claim is silently true "
                           f"wherever `{den}` vanishes")
                break

        # F17 -- name inflation on a conditional statement.
        if INFLATED.search(d.name) and (hyps or any(
                b.kind == "instance" and
                re.match(r"([A-Za-z_][\w.']*)", norm(b.type)) and
                re.match(r"([A-Za-z_][\w.']*)", norm(b.type)).group(1).split(".")[-1]
                not in STANDARD_CLASSES
                for b in d.binders)):
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
            if re.match(r"(Empty|PEmpty|Fin 0)\b", t):
                add("F10", f"quantifies over the empty type `{t}`")
            # `{n : ℕ // 0 < n}` ascribes the bound variable, so `\w+\s*//` never
            # matched a real subtype -- only the rarer `{n // p n}` spelling.
            sm = re.match(r"\{[^/]*//\s*(.+)\}$", t)
            if sm:
                base = _head_ident(t)
                add("F12", f"domain is the subtype `{_clip(t)}`; "
                           f"no `Nonempty` for it is proved in-corpus"
                    if base not in c.inhabited else
                    f"domain is the subtype `{_clip(t)}`")

    if d.kind in ("def", "abbrev"):
        # F8 -- definitional weakening.
        if norm(d.conclusion) == "Prop" and norm(d.body) in ("True", "trivial", "⊤"):
            add("F8", "target property is defined as `True`")
        # F2 -- Prop alias with a theorem-like name and no inhabitant.
        if norm(d.conclusion) == "Prop" and THEOREMISH.search(d.name):
            if d.name.split(".")[-1] not in proved_props:
                add("F2", "Prop named like a theorem, with no proof of it in-corpus")
        # F7 -- conclusion-by-definition.
        if norm(d.conclusion) == "Prop":
            parts = _top_conjuncts(d.body)
            if len(parts) > 1:
                for p in parts:
                    # No leading `\b`: the telling word is usually INSIDE a camelCase
                    # identifier (`isCalibrated`, `hasPortability`), where no boundary
                    # precedes it.
                    if re.search(r"(?i)(correct|desired|conclusion|holds|valid|"
                                 r"calibrat|portab|identif|sound|complete)", p):
                        add("F7", f"predicate `{d.name}` has the advertised conclusion "
                                  f"as a conjunct: `{_clip(p)}`")
                        break
        # F13 -- range advertised as canonical.
        if re.search(r"\.range\b|Set\.image\b", d.body) and re.search(
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


def check_files(c: Corpus) -> list[Finding]:
    """Whole-file syntax that bypasses trust, and dead concrete constructions."""
    out: list[Finding] = []
    seen_files = {d.file for d in c.decls}
    for rel in sorted(seen_files):
        src = (CORPUS_BASE / rel).read_text(encoding="utf-8", errors="replace")  # abs rel is a no-op
        m = mask(src)
        for pat, fam, msg in [
            (r"\bnative_decide\b", "F24", "`native_decide` moves the compiler into the "
                                          "trusted base"),
            (r"^\s*(unsafe|opaque)\s+", "F24", "unsafe/opaque declaration"),
            (r"^\s*(macro|elab|syntax|macro_rules|elab_rules)\b", "F24",
             "custom syntax or elaborator"),
            (r"@\[implemented_by", "F24", "compiled implementation substituted for the "
                                          "definition"),
            (r"^\s*(letI|haveI)\b", "F3", "instance installed locally; the obligation "
                                          "moves to whoever supplied its argument"),
            (r"#print axioms", "F24_INFO", "handled by the F18 pass below"),
        ]:
            for mo in re.finditer(pat, m, re.M):
                if fam == "F24_INFO":
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
    ap.add_argument("--severity", choices=["fatal", "conditional", "all"],
                    default="all")
    ap.add_argument("--json", metavar="PATH")
    ap.add_argument("--summary", action="store_true",
                    help="counts per family and per file only")
    ap.add_argument("--family", action="append",
                    help="restrict to one family, e.g. --family F1")
    ap.add_argument("--strict", action="store_true",
                    help="also fail on CONDITIONAL findings (the target standard: no "
                         "unresolved premise anywhere in the corpus)")
    args = ap.parse_args(argv)

    if args.paths:
        files = [Path(p).resolve() for p in args.paths]
    else:
        files = lean_sources(PROOFS)
    files = [f for f in files if f.is_file()]

    corpus = build_corpus(files)
    findings = analyse(corpus)

    keep = {"fatal": {FATAL}, "conditional": {FATAL, CONDITIONAL},
            "all": {FATAL, CONDITIONAL, FIDELITY}}[args.severity]
    findings = [f for f in findings if f.severity in keep]
    if args.family:
        findings = [f for f in findings if f.family in set(args.family)]

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

    gate = EXIT_ON | ({CONDITIONAL} if args.strict else set())
    n_gated = sum(1 for f in findings if f.severity in gate)
    if n_gated:
        print(f"\nFAIL: {n_gated} finding(s) at or above the gating severity "
              f"({'FATAL+CONDITIONAL' if args.strict else 'FATAL'}).")
    else:
        print(f"\nPASS: no findings at the gating severity "
              f"({'FATAL+CONDITIONAL' if args.strict else 'FATAL'}). "
              f"The CONDITIONAL ledger above is still debt, not absolution.")
    return 1 if n_gated else 0


# ======================================================================================
# GUARD: regimes -- no external theorem packaging in production structures
#
# Was `proofs/validation/code/check.py`.
#
# Model data and genuine algebraic laws may live in structures.  A scientific or
# analytic conclusion may not be accepted from a caller and then re-exported by
# field projection.  This check guards the concrete anti-patterns removed from the
# Calibrator corpus and rejects bare `Prop` switches, which carry no mathematical
# content at all.
#
# Lean compilation remains the proof check.  This guard is an architectural check
# that prevents the old `AssumedTheorem.result` interface from returning under a
# new edit.
# ======================================================================================

REGIMES_SOURCE_ROOT = PROOFS / "Calibrator"

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
# `Calibrator.BundleRigidity.DeploymentCeiling`: state the input as a TYPED HYPOTHESIS of
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
# GUARD: closure -- every Calibrator module is in the root import closure
#
# Was `proofs/validation/code/check.py`.
#
# `lake build Calibrator` can only validate modules reachable from
# `proofs/Calibrator.lean`.  This guard compares that transitive closure with the
# source tree, so adding an unimported module cannot produce a false-green root
# build.
# ======================================================================================

CLOSURE_ROOT = PROOFS / "Calibrator.lean"
CLOSURE_IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")


def closure_module_path(module):
    return PROOFS / (module.replace(".", "/") + ".lean")


def closure_direct_imports(path):
    imports = set()
    for line in read_source(path).splitlines():
        match = CLOSURE_IMPORT.match(line)
        if match is not None:
            imports.add(match.group(1))
    return imports


def closure_calibrator_sources():
    modules = {
        path
        for path in lean_sources(PROOFS / "Calibrator")
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
    sources = closure_calibrator_sources()
    closure = closure_root_closure()
    absent = sorted(path.relative_to(CORPUS_BASE) for path in sources - closure)
    print(f"CALIBRATOR_SOURCES\t{len(sources)}")
    print(f"ROOT_CLOSURE\t{len(closure & sources)}")
    for path in absent:
        print(f"MODULE_ABSENT\t{path}")
    if absent:
        return 1
    return 0


# ======================================================================================
# GUARD: wiring -- is a result wired into the biology, or only adjacent to it
#
# Was `proofs/validation/code/check.py`.  Its full header is reproduced
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
# Run:  python3 proofs/validation/code/check.py
#       python3 proofs/validation/code/check.py --json

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
    "Condensation",
    "CondensationUnification",
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
    out = {}
    for dirpath, _, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                with open(p, encoding="utf-8") as fh:
                    out[p] = fh.read()
    return out


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

    here = os.path.dirname(os.path.abspath(__file__))
    calibrator = str(PROOFS / "Calibrator")
    if not os.path.isdir(calibrator):
        print(f"cannot find {calibrator}", file=sys.stderr)
        return 2

    files = wiring_load(calibrator)
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
        width = max(len(s) for s in report)
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
# Was `proofs/validation/code/check.py`.  Its full header, including the calibration
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
    by = collections.Counter(h[0].replace("proofs/Calibrator/","") for h in hits)
    for f,c in by.most_common(): print(f"  {c:3}  {f}")
    print()
    for f,ln,name,p,ow in sorted(hits, key=lambda r:(r[0],r[1])):
        print(f"{f.replace('proofs/Calibrator/','')}:{ln}")
        print(f"    theorem {name}")
        print(f"    proof := {p}      [field of {', '.join(ow)}]")
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
# own flags, so `--only laundering --strict` has to reach them; the rest take
# nothing and are called with no arguments.
GUARDS = {
    "style":           dict(fn=run_style,           gated=True,  takes_argv=False),
    "identifications": dict(fn=run_identifications, gated=True,  takes_argv=False),
    "laundering":      dict(fn=run_laundering,      gated=True,  takes_argv=True),
    "regimes":         dict(fn=run_regimes,         gated=True,  takes_argv=False),
    "closure":         dict(fn=run_closure,         gated=True,  takes_argv=False),
    "wiring":          dict(fn=run_wiring,          gated=True,  takes_argv=True),
    "field-proofs":    dict(fn=run_field_proofs,    gated=False, takes_argv=False),
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
            print(f"unknown guard {args.only!r}; --list shows the seven",
                  file=sys.stderr)
            return 2
        selected = [args.only]
    else:
        if rest:
            # Guard-specific flags are meaningless without --only: there is no
            # sensible way to route `--strict` when six guards are running and
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
