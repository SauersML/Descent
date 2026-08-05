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
have been qualified is the hazard, because `Core.ratio := 0` is not a field
update and `fun Core.risk =>` is not a binder: those are syntax errors, and a
hundred of them at once is not a signal, it is a wall.  So the tool decides by
POSITION, not by name -- a declaration head, a binder keyword, a `foo := ..`
field key, an indented `foo : T` field declaration -- and additionally holds
back, PER FILE, any name that file binds itself.

The per-file part matters.  An earlier version held a name back everywhere it
was bound anywhere, which retired `Phi`, `variance`, `scoreVariance`,
`prevalence` and `dot` from the rewrite entirely; those are the `Foundations`
kernel names the rest of the corpus calls most.  That a proof somewhere binds
`variance` says nothing about whether a different file's `variance` is a global.

What survives the holds is the real duplicate-short-name set -- `witness`,
`risk`, `zero`, `modulus`, `nonempty`, `cosPart`/`sinPart` -- which the flat
namespace has been hiding and which is meant to be looked at, not moved.

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

# `structure ... where` fields.
FIELD = re.compile(r"^\s{1,}([a-z][A-Za-z0-9_'₀-₉]*)\s*:(?!=)")
# `fun x y =>`, `intro h`, `∀ a b, ..` -- a RUN of names, not just the first.
# Written as a NEGATED character class rather than a repeated group: the
# obvious `(?:ident\s*)+:` form backtracks exponentially on a long line with no
# colon, and this corpus has 9,000-line files full of them.
BINDER = re.compile(
    r"(?:^|[\s(⟨,])(?:fun|λ|intro|intros|obtain|rintro|set|let|have|∀|∃|Σ|Π)"
    r"[ \t]+([^,:=(){}⟨⟩\n]{0,80})")
# `(Ne μ : ℝ)`, `{α : Type}` -- every explicit binder group, same reasoning.
PAREN_BINDER = re.compile(r"[(\{⦃]([^():{}\n]{0,80}):(?!=)")
NAMES = re.compile(r"[a-zA-Z_][A-Za-z0-9_'₀-₉]*")


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


def bound_locally(text: str) -> set[str]:
    """Names this FILE binds -- as a local, a field, or its own declaration.

    A name is held back per FILE, not corpus-wide.  The first version of this
    held a name back everywhere it was ever bound anywhere, which retired
    `Phi`, `variance`, `scoreVariance`, `prevalence` and `dot` from the rewrite
    entirely -- and those are exactly the `Foundations` kernel names the rest of
    the corpus calls most.  A name bound in one proof says nothing about
    whether a different file's use of it is a global.

    Within a file, though, the hold is right and cheap: if a proof here binds
    `variance`, then some uses of `variance` in this file are that local, and
    telling them apart needs scope tracking rather than position.  Those files
    are named in the report and qualified by hand.
    """
    stripped = nsmap.strip_comments(text)
    names = set()
    for line in stripped.split("\n"):
        m = FIELD.match(line)
        if m:
            names.add(m.group(1))
        m = nsmap.DECL.match(line)
        if m:
            names.add(m.group(2).split(".")[-1])
    for rx in (BINDER, PAREN_BINDER):
        for m in rx.finditer(stripped):
            names.update(NAMES.findall(m.group(1)))
    return names


# Positions at which an identifier is being INTRODUCED rather than used.
_DECL_KEYWORD = re.compile(
    r"(?:^|\s)(?:def|abbrev|theorem|lemma|structure|inductive|instance|class|opaque|"
    r"axiom|namespace|end|open|export|section|variable|attribute|universe|"
    r"fun|λ|intro|intros|rintro|obtain|rcases|let|have|set|"
    r"deriving|where|with)\s*$")


def introduces(text: str, a: int, b: int) -> bool:
    """Is the identifier at [a,b) a binding occurrence rather than a use?

    Three shapes, each of which a blanket prefix would turn into a syntax error
    rather than a resolution failure -- so unlike a missed qualification they
    cannot be left to the compiler to find one at a time:

      * a declaration head or binder keyword immediately before it,
      * `foo := ...` opening a line or following `{` / `,` -- a structure
        instance field, which names a FIELD and not a global,
      * `  foo : T` at an indent with no `:=` -- a structure field declaration.
    """
    line_start = text.rfind("\n", 0, a) + 1
    pre = text[line_start:a]
    post = text[b:]
    if _DECL_KEYWORD.search(pre):
        return True
    if post.lstrip(" ").startswith(":="):
        stripped = pre.rstrip()
        if stripped == "" or stripped[-1] in "{,|" or stripped.endswith("with"):
            return True
    if pre.strip() == "" and pre.startswith(" "):
        rest = post.lstrip(" ")
        if rest.startswith(":") and not rest.startswith(":="):
            return True
    return False


def namespace_tokens(directory: str) -> set[str]:
    """Namespace segments a directory introduces, which references must qualify.

    A declaration is not the only thing a move renames.  `Descent/Decision/`
    holds `namespace Descent.CertificateGrading` and, inside `Descent.Decision`,
    `namespace Problem`; both become `Descent.Decision.<X>`, and every
    `CertificateGrading.foo` or `Problem.bar` written elsewhere has to gain the
    same `Decision.` prefix that the bare names do.  Missing this leaves the
    directory's SUB-namespaces unreachable while its plain declarations resolve,
    which is a confusing half-migration rather than a clean failure.
    """
    tokens = set()
    for path in files_of(directory):
        with open(path, encoding="utf-8", errors="ignore") as fh:
            text = nsmap.strip_comments(fh.read())
        stack: list[str | None] = []
        for line in text.split("\n"):
            m = nsmap.NAMESPACE.match(line)
            if m:
                name = m.group(1)
                if not stack:
                    # `namespace Descent.CertificateGrading`: the tail is ours.
                    if name.startswith("Descent.") and name != f"Descent.{directory}":
                        tokens.add(name[len("Descent."):].split(".")[0])
                else:
                    tokens.add(name.split(".")[0])
                stack.append(name)
            elif nsmap.SECTION.match(line):
                stack.append(None)
            elif nsmap.END.match(line) and stack:
                stack.pop()
    return tokens - {directory, "Descent"}


def ambiguous_tokens() -> set[str]:
    """Namespace segments more than one directory introduces.

    `ProbeBlindness` is opened under both `Blindness/` and `Decision/`.  A
    mechanical prefix would send every `ProbeBlindness.` in the corpus to
    whichever directory moved last, including the ones inside the other
    directory that already resolve.  Those are qualified by hand.
    """
    seen = collections.Counter()
    for d in nsmap.DIRECTORIES:
        for t in namespace_tokens(d):
            seen[t] += 1
    return {t for t, n in seen.items() if n > 1}


def defined_in(directory: str, table):
    """Short names defined under `Descent/<directory>/`."""
    names = set()
    for mod, decls in table.items():
        if nsmap.directory_of(mod) == directory:
            names |= {short for _full, short, _kind, _line in decls}
    return names


def qualify(text: str, names: set[str], prefix: str,
            tokens: set[str] = frozenset()) -> tuple[str, int, set[str]]:
    """Prefix bare uses of `names` with `prefix.`; return (text, hits, held).

    `tokens` are namespace segments, prefixed only where they are USED as a
    prefix (`Problem.value`), never where they stand alone -- a bare `Problem`
    is a type name that the declaration pass already covers or does not own.

    `held` is the subset this file binds locally, which is left alone and
    reported so the file can be qualified by hand.
    """
    held = names & bound_locally(text)
    movable = names - held
    mask = code_mask(text)
    out, last, hits = [], 0, 0
    for m in IDENT.finditer(text):
        a, b = m.span()
        if not mask[a]:
            continue
        if m.group(0) not in movable:
            if not (m.group(0) in tokens and b < len(text) and text[b] == "."):
                continue
        if a and (text[a - 1] in "._" or text[a - 1].isalnum()):
            continue                            # already qualified, or mid-name
        if introduces(text, a, b):
            continue
        line_start = text.rfind("\n", 0, a) + 1
        if text.startswith(("import ", "open ", "export ", "namespace ", "end "),
                           line_start):
            continue
        out.append(text[last:a])
        out.append(prefix + "." + m.group(0))
        last = b
        hits += 1
    out.append(text[last:])
    return "".join(out), hits, held


def rewrite_namespace(text: str, directory: str) -> str:
    """`namespace Descent` -> `namespace Descent.D`, and its matching `end`.

    Only the OUTERMOST `namespace Descent` is moved.  A file that already nests a
    second namespace inside it keeps that nesting: `Descent.PopGen.ScoreMoments`
    is the right name for a group inside a group.
    """
    lines = text.split("\n")
    depth, opened_name = 0, None
    for i, line in enumerate(lines):
        m = nsmap.NAMESPACE.match(line)
        if m:
            if depth == 0:
                old = m.group(1)
                if old == "Descent":
                    opened_name = f"Descent.{directory}"
                elif old.startswith("Descent.") and old != f"Descent.{directory}":
                    # `namespace Descent.CertificateGrading` -- a module-named
                    # group that never acquired its directory.  Keep the group,
                    # put the directory above it.
                    opened_name = f"Descent.{directory}.{old[len('Descent.'):]}"
                if opened_name:
                    lines[i] = f"namespace {opened_name}"
            depth += 1
        elif nsmap.SECTION.match(line):
            depth += 1
        elif nsmap.END.match(line):
            depth -= 1
            if depth == 0 and opened_name is not None:
                lines[i] = f"end {opened_name}"
                opened_name = None
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
    ambiguous = ambiguous_tokens()
    tokens = namespace_tokens(d) - ambiguous
    print(f"Descent/{d}/: {len(names)} names, {len(tokens)} sub-namespaces")
    for t in sorted(namespace_tokens(d) & ambiguous):
        print(f"    hold  namespace {t}  (opened under more than one directory)")

    changed, all_held = 0, collections.defaultdict(set)
    for path in outside:
        with open(path, encoding="utf-8", errors="ignore") as fh:
            text = fh.read()
        new, hits, held = qualify(text, names, d, tokens)
        for n in held:
            all_held[n].add(nsmap.module_of(path))
        if hits:
            changed += 1
            print(f"    {hits:5d}  {nsmap.module_of(path)}")
            if args.write:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(new)
    for n in sorted(all_held):
        mods = sorted(all_held[n])
        print(f"    hold  {d}.{n}  bound locally in {len(mods)} module(s): "
              f"{', '.join(mods[:3])}{' ...' if len(mods) > 3 else ''}")
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
