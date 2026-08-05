#!/usr/bin/env python3
"""Namespace inventory: what each declaration's FULL name actually is.

WHY THIS EXISTS.  `architecture.py` counts declarations by SHORT name, which is
the right unit for its questions (is this defined twice? is it referenced?) and
the wrong unit for the question this file asks: does the name a declaration
carries say where it lives?

The corpus's rule is that a directory is a namespace.  `Descent/Coalescent/`
obeys it -- every file there opens `namespace Descent` then `namespace
Coalescent`, so `Descent.Coalescent.pairDistinct` names its own home.  Nothing
else does: 6,267 declarations sit in a flat `Descent`, so a short name must be
globally unique BY HAND, and one concept acquires five names because no second
module may reuse the first's.

This module reads the namespace stack -- `namespace`/`end` and `section`/`end`
tracked together, since they share the `end` keyword and only a stack tells them
apart -- and reports:

    python3 validation/code/nsmap.py               # per-directory mismatch census
    python3 validation/code/nsmap.py --duplicates  # short names defined twice
    python3 validation/code/nsmap.py --module M    # every declaration in one module
    python3 validation/code/nsmap.py --json        # the whole table, for tools

It is a MEASUREMENT, not a gate.  The gate is `architecture.py`; this is what a
rewrite of the namespaces consults to know what it is moving and what will
collide when it lands.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEAN_ROOT = os.path.join(ROOT, "Descent")

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(def|abbrev|theorem|lemma|structure|inductive|instance|class|opaque|axiom)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)")
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.'₀-₉]*)\s*$")
SECTION = re.compile(r"^section\b")
END = re.compile(r"^end\b\s*([A-Za-z_][A-Za-z0-9_.'₀-₉]*)?\s*$")

# The directories that are meant to be namespaces.  `Descent/Core/` is listed so
# the census can say which of its files already comply; the root file has no
# directory and is exempt.
DIRECTORIES = [
    "Blindness", "Coalescent", "Conditionals", "Core", "Decision",
    "Foundations", "Pangenome", "PopGen", "Portability", "Program", "Spectral",
]


def strip_comments(text: str) -> str:
    """Remove block comments (docstrings included) and line comments.

    Namespace commands never appear in prose, but `end` does -- and a file that
    says "end of section" in a docstring would otherwise pop a namespace off the
    stack and mislabel every declaration after it.
    """
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def module_of(path: str) -> str:
    return os.path.relpath(path, ROOT)[:-len(".lean")].replace(os.sep, ".")


def directory_of(mod: str) -> str | None:
    """`Descent.PopGen.DGP` -> `PopGen`; the root file -> None."""
    parts = mod.split(".")
    return parts[1] if len(parts) >= 3 and parts[0] == "Descent" else None


def scan(path: str):
    """Return (module, [(full name, short name, kind, line)])."""
    with open(path, encoding="utf-8", errors="ignore") as fh:
        text = strip_comments(fh.read())
    stack: list[str | None] = []          # None marks a `section`
    found = []
    for lineno, line in enumerate(text.split("\n"), 1):
        m = NAMESPACE.match(line)
        if m:
            stack.append(m.group(1))
            continue
        if SECTION.match(line):
            stack.append(None)
            continue
        if END.match(line):
            if stack:
                stack.pop()
            continue
        m = DECL.match(line)
        if m:
            prefix = ".".join(n for n in stack if n)
            short = m.group(2).split(".")[-1]
            # A declaration may itself carry a dotted prefix (`Foo.bar`); that
            # prefix is part of the full name but not of the namespace.
            own = m.group(2)
            full = f"{prefix}.{own}" if prefix else own
            found.append((full, short, m.group(1), lineno))
    return module_of(path), found


def load() -> dict[str, list]:
    table = {}
    for dirpath, _, filenames in os.walk(LEAN_ROOT):
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                mod, decls = scan(os.path.join(dirpath, fn))
                table[mod] = decls
    root = os.path.join(ROOT, "Descent.lean")
    if os.path.exists(root):
        mod, decls = scan(root)
        table["Descent"] = decls
    return table


def expected_namespace(mod: str) -> str | None:
    d = directory_of(mod)
    return f"Descent.{d}" if d else None


def census(table):
    """Per-directory: how many declarations name their own home."""
    rows = collections.defaultdict(lambda: [0, 0])
    for mod, decls in table.items():
        want = expected_namespace(mod)
        if want is None:
            continue
        d = directory_of(mod)
        for full, _short, _kind, _line in decls:
            rows[d][1] += 1
            if full.startswith(want + "."):
                rows[d][0] += 1
    return rows


def duplicates(table):
    """Short name -> the modules that define it, where that is more than one.

    Two modules defining the same short name is not by itself a defect: it is
    exactly what a namespace is for.  It IS a defect while the namespace is flat,
    because then the two are the same full name and one of them wins silently --
    and it is a defect for the extraction tools, which key on the short name and
    die with `KeyError` when the same key arrives twice with different bodies.
    """
    by_short = collections.defaultdict(list)
    for mod, decls in table.items():
        for full, short, kind, line in decls:
            by_short[short].append((mod, full, kind, line))
    return {s: v for s, v in by_short.items() if len({m for m, _, _, _ in v}) > 1}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--duplicates", action="store_true",
                    help="list short names defined in more than one module")
    ap.add_argument("--collisions", action="store_true",
                    help="list short names whose FULL names collide (the real defect)")
    ap.add_argument("--module", help="list every declaration in one module")
    ap.add_argument("--json", action="store_true", help="dump the whole table")
    args = ap.parse_args()

    table = load()

    if args.json:
        json.dump(table, sys.stdout, indent=1)
        return 0

    if args.module:
        for full, short, kind, line in table.get(args.module, []):
            print(f"{line:5d}  {kind:9s} {full}")
        return 0

    if args.duplicates or args.collisions:
        dups = duplicates(table)
        for short in sorted(dups):
            entries = dups[short]
            fulls = {f for _, f, _, _ in entries}
            if args.collisions and len(fulls) > 1:
                continue          # distinct full names: the namespace did its job
            print(f"{short}  ({len(entries)} definitions"
                  f"{', SAME full name' if len(fulls) == 1 else ''})")
            for mod, full, kind, line in sorted(entries):
                print(f"    {mod}:{line}  {kind} {full}")
        print(f"\n{len(dups)} short names defined in more than one module")
        return 0

    rows = census(table)
    total_ok = total = 0
    print("namespace census   (declarations whose full name names their directory)")
    for d in DIRECTORIES:
        ok, n = rows.get(d, [0, 0])
        total_ok += ok
        total += n
        pct = 100.0 * ok / n if n else 100.0
        flag = "OK" if ok == n else ""
        print(f"  {d:14s} {ok:5d} / {n:5d}  {pct:5.1f}%  {flag}")
    pct = 100.0 * total_ok / total if total else 100.0
    print(f"  {'TOTAL':14s} {total_ok:5d} / {total:5d}  {pct:5.1f}%")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
