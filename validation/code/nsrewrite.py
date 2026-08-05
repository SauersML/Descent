#!/usr/bin/env python3
"""Move one directory into its own namespace, and qualify every reference to it.

WHY A TOOL AND NOT AN EDIT.  Giving `Descent/PopGen/` the namespace
`Descent.PopGen` is one line per file.  What makes it a project rather than a
line is the other side: 1,376 declarations change their full name at once, and
every use of them elsewhere in the corpus must acquire the `PopGen.` prefix or
stop resolving.  Done by hand that is thousands of edits with no way to check
coverage; done by regex over the whole file it corrupts prose, field names and
local binders.

WHAT THIS DOES.  For a directory D:

  1. Rewrites `namespace Descent` -> `namespace Descent.D` and the matching
     `end Descent` -> `end Descent.D` in every file under `Descent/D/`.
  2. In every file OUTSIDE D, prefixes each reference to a name D defines with
     `D.`, skipping comments, string literals, already-qualified occurrences and
     import lines.

Step 2 is safe in one direction and not the other.  A reference that SHOULD have
been qualified and was not simply fails to resolve, and the compiler names it --
Lean does not silently pick a different `neiFst`.  A reference that should NOT
have been qualified is the hazard, so the tool refuses to touch three classes of
name and reports them for a human:

  * names that are also STRUCTURE FIELDS somewhere (`{ ratio := ... }` would
    become `{ Core.ratio := ... }`, which is not a field update),
  * names that are also BOUND LOCALLY somewhere (`intro sum`, `fun risk =>`),
  * names shorter than four characters, which are overwhelmingly locals.

Those are the 27 duplicate short names the flat namespace has been hiding, and
they are meant to be looked at rather than moved.

    python3 validation/code/nsrewrite.py --report          # incoming reference census
    python3 validation/code/nsrewrite.py --dir Decision    # dry run: what would change
    python3 validation/code/nsrewrite.py --dir Decision --write
"""

from __future__ import annotations

import argparse
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nsmap  # noqa: E402

ROOT = nsmap.ROOT
LEAN_ROOT = nsmap.LEAN_ROOT

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?₀-₉]*")

# `structure ... where` fields and `deriving`-free anonymous-constructor keys.
FIELD = re.compile(r"^\s{1,}([a-z][A-Za-z0-9_'₀-₉]*)\s*:(?!=)")
# Binder forms that introduce a local of the given name.
BINDER = re.compile(
    r"(?:^|[\s(⟨,])(?:fun|λ|intro|intros|obtain|rintro|set|let|have|use|∀|∃|Σ|Π)\s+"
    r"([a-zA-Z_][A-Za-z0-9_'₀-₉]*)")
ASSIGN = re.compile(r"([a-zA-Z_][A-Za-z0-9_'₀-₉]*)\s*:=")

MIN_SAFE_LEN = 4


def all_files():
    out = []
    for dirpath, _, filenames in os.walk(LEAN_ROOT):
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                out.append(os.path.join(dirpath, fn))
    root = os.path.join(ROOT, "Descent.lean")
    if os.path.exists(root):
        out.append(root)
    return sorted(out)


def files_of(directory: str):
    """Paths under `Descent/<directory>/`."""
    return [p for p in all_files()
            if p != os.path.join(ROOT, "Descent.lean")
            and os.path.relpath(p, LEAN_ROOT).split(os.sep)[0] == directory]


def files_outside(directory: str):
    """Every other .lean file, the root file included -- it is the biggest caller."""
    inside = set(files_of(directory))
    return [p for p in all_files() if p not in inside]


def spans(text: str):
    """Yield (start, end, kind) for every comment and string literal.

    Lean block comments nest, so a depth counter is required: `/- /- -/ -/` ends
    once, and a non-nesting scan would leave the rest of the file marked as code
    when it is comment, or the reverse.
    """
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            yield (i, j, "comment")
            i = j
        elif c == "-" and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            yield (i, j, "comment")
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            yield (i, min(j + 1, n), "string")
            i = j + 1
        else:
            i += 1


def code_mask(text: str):
    """A bytearray parallel to `text`: 1 where the character is code."""
    mask = bytearray(b"\x01" * len(text))
    for a, b, _kind in spans(text):
        for k in range(a, min(b, len(text))):
            mask[k] = 0
    return mask


def risky_names(paths):
    """Names that must not be mechanically prefixed, with the reason."""
    risky: dict[str, str] = {}
    for path in paths:
        with open(path, encoding="utf-8", errors="ignore") as fh:
            text = fh.read()
        stripped = nsmap.strip_comments(text)
        for line in stripped.split("\n"):
            m = FIELD.match(line)
            if m:
                risky.setdefault(m.group(1), "structure field")
        for m in BINDER.finditer(stripped):
            risky.setdefault(m.group(1), "local binder")
        for m in ASSIGN.finditer(stripped):
            risky.setdefault(m.group(1), "assignment key")
    return risky


def defined_in(directory: str, table):
    """Short names defined under `Descent/<directory>/`."""
    names = set()
    for mod, decls in table.items():
        if nsmap.directory_of(mod) == directory:
            names |= {short for _full, short, _kind, _line in decls}
    return names


def qualify(text: str, names: set[str], prefix: str) -> tuple[str, int]:
    """Prefix bare occurrences of `names` with `prefix.`, code positions only."""
    mask = code_mask(text)
    out, last, hits = [], 0, 0
    for m in IDENT.finditer(text):
        a, b = m.span()
        if not mask[a]:
            continue
        if m.group(0) not in names:
            continue
        if a and text[a - 1] in "._":          # already qualified, or part of a name
            continue
        if b < len(text) and text[b] == ".":   # `neiFst.foo` is a projection chain
            pass                               # still ours: `PopGen.neiFst.foo`
        line_start = text.rfind("\n", 0, a) + 1
        if text.startswith("import ", line_start) or text.startswith("open ", line_start):
            continue
        out.append(text[last:a])
        out.append(prefix + "." + m.group(0))
        last = b
        hits += 1
    out.append(text[last:])
    return "".join(out), hits


def rewrite_namespace(text: str, directory: str) -> str:
    """`namespace Descent` -> `namespace Descent.D`, and its matching `end`.

    Only the OUTERMOST `namespace Descent` is moved.  A file that already nests a
    second namespace inside it keeps that nesting: `Descent.PopGen.ScoreMoments`
    is the right name for a group inside a group.
    """
    lines = text.split("\n")
    depth, opened_at = 0, None
    for i, line in enumerate(lines):
        if nsmap.NAMESPACE.match(line):
            if depth == 0 and line.strip() == "namespace Descent":
                opened_at = i
                lines[i] = f"namespace Descent.{directory}"
            depth += 1
        elif nsmap.SECTION.match(line):
            depth += 1
        elif nsmap.END.match(line):
            depth -= 1
            if depth == 0 and opened_at is not None:
                lines[i] = f"end Descent.{directory}"
                opened_at = None
    return "\n".join(lines)


def report(table):
    """How much work each directory's move is, measured before doing any of it.

    The order to move them in is cheapest-first: a directory nothing refers to
    costs one line per file, and one that 150 modules refer to is where a
    mistake in the qualifier is expensive.
    """
    cache = {}
    for path in all_files():
        with open(path, encoding="utf-8", errors="ignore") as fh:
            text = fh.read()
        cache[path] = (text, code_mask(text))

    print("incoming references   (uses of a directory's names from outside it)")
    for d in nsmap.DIRECTORIES:
        names = defined_in(d, table)
        if not names:
            continue
        hits, mods = 0, set()
        for path, (text, mask) in cache.items():
            if nsmap.directory_of(nsmap.module_of(path)) == d:
                continue
            local = sum(1 for m in IDENT.finditer(text)
                        if mask[m.start()] and m.group(0) in names
                        and not (m.start() and text[m.start() - 1] in "._"))
            if local:
                hits += local
                mods.add(nsmap.module_of(path))
        print(f"  {d:14s} {len(names):5d} names  {hits:6d} uses  in {len(mods):4d} modules")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--report", action="store_true")
    ap.add_argument("--dir")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()

    table = nsmap.load()

    if args.report:
        report(table)
        return 0

    if not args.dir:
        ap.print_help()
        return 2

    d = args.dir
    names = defined_in(d, table)
    if not names:
        print(f"no declarations under Descent/{d}/", file=sys.stderr)
        return 2

    outside = files_outside(d)
    risky = risky_names(all_files())
    skipped = {n: risky[n] for n in sorted(names) if n in risky}
    skipped.update({n: "too short" for n in names if len(n) < MIN_SAFE_LEN})
    movable = {n for n in names if n not in skipped}

    print(f"Descent/{d}/: {len(names)} names, {len(movable)} safe to prefix, "
          f"{len(skipped)} held back")
    for n, why in sorted(skipped.items()):
        print(f"    hold  {n}  ({why})")

    changed = 0
    for path in outside:
        with open(path, encoding="utf-8", errors="ignore") as fh:
            text = fh.read()
        new, hits = qualify(text, movable, d)
        if hits:
            changed += 1
            print(f"    {hits:5d}  {nsmap.module_of(path)}")
            if args.write:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(new)
    for path in files_of(d):
        with open(path, encoding="utf-8", errors="ignore") as fh:
            text = fh.read()
        new = rewrite_namespace(text, d)
        if new != text and args.write:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(new)
    print(f"{changed} modules reference Descent/{d}/"
          f"{'' if args.write else '   (dry run; pass --write)'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
