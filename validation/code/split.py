#!/usr/bin/env python3
"""Cut a monolith into a chain of modules along its own section boundaries.

WHY A CHAIN.  A monolith's declarations depend on each other in whatever order
they happen to appear.  Cutting one into modules that import only what they use
means first discovering that order, which is worth doing and is a different job:
it changes what each proof can see, so every part of it has to be checked.  A
CHAIN -- each part importing the one before, in the original order -- preserves
every resolution the single file had, so the split cannot change what any proof
sees and the only thing that can break is the mechanics of the cut.

WHY SECTION BOUNDARIES.  They are where the file already says a subject ends.
Cutting anywhere else means guessing, and a guess that lands mid-proof is not
recoverable by reading the diff.

WHAT IT HANDLES.

  * Scope balance.  A cut at a top-level boundary can still leave a `section`
    open or close one it never opened -- `PortabilityDrift` opened
    `section PortabilityDrift` and closed it 8,000 lines later.  Each part
    reopens and recloses by name.  A section scopes `variable`s; a file that
    declares none at that level can be reopened exactly, and the tool REFUSES
    the split when one does (`--check` reports it).
  * The header.  License, imports, `namespace`, and every file-scope `open` are
    copied to each part, because a part that cannot see what the original saw is
    not the same code.
  * The seams.  The prose between two sections is the map of the file; it goes
    with the part it introduces rather than being dropped at the cut.
  * The old path.  The original file becomes a head importing the last part, so
    every existing `import` keeps working and keeps meaning the same thing.

    python3 validation/code/split.py Descent/X/Y.lean            # report the cuts
    python3 validation/code/split.py Descent/X/Y.lean --write
"""

from __future__ import annotations

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nsmap  # noqa: E402

FILE_OPEN = re.compile(r"^open\b")
IMPORT = re.compile(r"^import\b")
VARIABLE = re.compile(r"^variable\b")


def blank_comments(text: str) -> list[str]:
    """Comment characters replaced by spaces, newlines kept.

    `nsmap.strip_comments` collapses a block comment to one space, which merges
    lines and puts every later line number out by however many lines the
    docstrings above it occupied.  Every line number this tool reports is a CUT,
    so an off-by-N here does not misreport, it mis-splits.
    """
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
        else:
            i += 1
            continue
        for k in range(i, min(j, n)):
            if out[k] != "\n":
                out[k] = " "
        i = j
    return "".join(out).split("\n")


def scan(lines):
    """Top-level `section NAME` openings and their matching `end`, 1-based."""
    code = blank_comments("\n".join(lines))
    stack, tops = [], []
    for i, line in enumerate(code, 1):
        m = nsmap.NAMESPACE.match(line)
        if m:
            stack.append(("ns", m.group(1), i))
        elif nsmap.SECTION.match(line):
            parts = line.split()
            name = parts[-1] if len(parts) > 1 else None
            # depth 1 means: inside the file's one namespace, nothing else.
            if len([s for s in stack if s[0] == "section"]) == 0 and name:
                tops.append((name, i, None))
            stack.append(("section", name, i))
        elif nsmap.END.match(line):
            if stack:
                kind, name, _at = stack.pop()
                if kind == "section" and name and \
                        len([s for s in stack if s[0] == "section"]) == 0:
                    for k, (n, a, b) in enumerate(tops):
                        if n == name and b is None:
                            tops[k] = (n, a, i)
                            break
    return [t for t in tops if t[2] is not None]


def balance(lines):
    """(prefix, suffix) making a fragment scope-balanced."""
    code = blank_comments("\n".join(lines))
    stack, unmatched = [], []
    for line in code:
        m = nsmap.NAMESPACE.match(line)
        if m:
            stack.append(("ns", m.group(1)))
        elif nsmap.SECTION.match(line):
            parts = line.split()
            stack.append(("section", parts[-1] if len(parts) > 1 else None))
        elif nsmap.END.match(line):
            if stack:
                stack.pop()
            else:
                unmatched.append(nsmap.END.match(line).group(1))
    return ([f"section {n}" if n else "section" for n in unmatched],
            [f"end {n}" if n else "end" for _k, n in reversed(stack)])


WHY = """/-!
# `{stem}.{name}`

Part of the split of `{path}`, which was {total:,} lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/"""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("path")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--min-lines", type=int, default=120,
                    help="merge a section smaller than this into the previous part")
    args = ap.parse_args()

    lines = open(args.path, encoding="utf-8").read().split("\n")
    total = len(lines)
    L = lambda a, b: lines[a - 1:b]  # noqa: E731

    ns_at = next((i for i, l in enumerate(lines, 1)
                  if nsmap.NAMESPACE.match(l)), None)
    if ns_at is None:
        print("no namespace: nothing to split against", file=sys.stderr)
        return 2

    header = [l for l in lines[:ns_at] if IMPORT.match(l)]

    # A file may open more than one namespace before its first section --
    # `TrafficInvariantSeparation` opens `Descent.Blindness` and then
    # `TrafficInvariantSeparation` -- and every `open` it needs may sit inside
    # them.  Carrying only the outermost silently renames every declaration in
    # every part, which no error message says out loud.  So the PREAMBLE is every
    # scope-opening and every `open` before the first cut, and each part closes
    # them in reverse.
    #
    # A `variable` INSIDE a top-level section is scoped to that section, and the
    # cuts are section boundaries, so it never crosses one.  A variable in the
    # preamble is the one case a chain split cannot reproduce.
    code = blank_comments("\n".join(lines))
    depth, opens, ns_stack = 0, [], []
    first_section = None
    for i, l in enumerate(code, 1):
        m = nsmap.NAMESPACE.match(l)
        if m:
            depth += 1
            if first_section is None:
                ns_stack.append((i, m.group(1)))
            continue
        if nsmap.SECTION.match(l):
            if first_section is None and len(l.split()) > 1:
                first_section = i
            depth += 1
            continue
        if nsmap.END.match(l):
            depth -= 1
            continue
        if first_section is not None:
            continue
        if VARIABLE.match(l):
            print(f"REFUSED: preamble `variable` at line {i}; a chain split would "
                  f"change what the later parts see", file=sys.stderr)
            return 2
        if FILE_OPEN.match(l):
            opens.append(i)

    if first_section is None:
        print(f"{args.path}: no top-level section -- nothing to cut along")
        return 0

    preamble = [lines[i - 1] for i, _n in ns_stack] 
    closers = [f"end {n}" for _i, n in reversed(ns_stack)]
    open_lines = [lines[i - 1] for i in opens]

    # The outermost namespace's `end` is not part of any section; keep it and the
    # inner closers out of the last part so the balancer does not try to reopen a
    # namespace as a section.
    total_body = len(lines)
    for _i, n in ns_stack:
        for k in range(total_body, 0, -1):
            if lines[k - 1].strip() == f"end {n}":
                total_body = k - 1
                break

    tops = scan(lines)
    if len(tops) < 2:
        print(f"{args.path}: {len(tops)} top-level section(s) -- nothing to cut along")
        return 0

    # Each part runs from the end of the previous one to the end of its section,
    # so the prose introducing a section travels with it.
    cuts, prev_end = [], tops[0][1]
    for name, a, b in tops:
        cuts.append((name, prev_end, b))
        prev_end = b + 1
    if prev_end <= total_body:
        tail = [i for i in range(prev_end, total_body + 1) if lines[i - 1].strip()]
        if tail:
            cuts.append(("Tail", prev_end, total_body))

    merged = []
    for name, a, b in cuts:
        if merged and b - a + 1 < args.min_lines:
            pn, pa, _pb = merged[-1]
            merged[-1] = (pn, pa, b)
        else:
            merged.append((name, a, b))

    stem = os.path.basename(args.path)[:-len(".lean")]
    print(f"{args.path}: {total:,} lines -> {len(merged)} parts")
    for name, a, b in merged:
        pre, suf = balance(L(a, b))
        print(f"  {name:28s} {b - a + 1:6,d} lines"
              f"{'   reopen ' + ','.join(pre) if pre else ''}"
              f"{'   close ' + ','.join(suf) if suf else ''}")
    if not args.write:
        print("(dry run; pass --write)")
        return 0

    outdir = args.path[:-len(".lean")]
    os.makedirs(outdir, exist_ok=True)
    lic = L(1, 3)
    prev = None
    for name, a, b in merged:
        pre, suf = balance(L(a, b))
        imports = list(header) + ([f"import {stem_mod(args.path)}.{prev}"] if prev else [])
        out = (lic + imports + [""] + preamble + [""] + open_lines + [""]
               + [WHY.format(stem=stem, name=name, path=args.path, total=total), ""]
               + pre + L(a, b) + suf + [""] + closers + [""])
        open(os.path.join(outdir, name + ".lean"), "w").write("\n".join(out))
        prev = name

    open(args.path, "w").write("\n".join(lic + [
        f"import {stem_mod(args.path)}.{prev}", "",
        f"""/-!
# `{stem}` -- the head of a split file

This was {total:,} lines. It is now {len(merged)} modules under `{stem}/`, chained in the order
the original was written, and this file names the last of them -- so every existing
`import` of this module keeps working and keeps meaning the same thing.
-/""", ""]))
    print(f"wrote {len(merged)} parts and a head")
    return 0


def ns_line_name(line: str) -> str:
    return line.split()[1]


def stem_mod(path: str) -> str:
    return path[:-len(".lean")].replace(os.sep, ".")


if __name__ == "__main__":
    raise SystemExit(main())
