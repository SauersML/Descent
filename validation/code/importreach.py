#!/usr/bin/env python3
"""Whether dropping an import would make a module unable to see a name it uses.

    python3 validation/code/importreach.py drop Descent.Program.OpenQuestions
    python3 validation/code/importreach.py unused
    python3 validation/code/importreach.py layers

WHY THIS EXISTS, AND WHAT IT DELIBERATELY WILL NOT DO

The corpus has 133 modules whose entire `Descent` import list is one entry --
their predecessor in a chain -- and an import DAG 37 deep.  Cutting a chain link
needs an answer to one question: after the cut, can this module still SEE every
`Descent` name its body mentions?

`#min_imports` answers that properly, from the elaborated environment, and it is
the right tool.  It is unavailable whenever the cluster is down, and it is also
a full elaboration of the corpus, so a cheap static screen that says "these cuts
are obviously safe, these need the compiler" is worth having in front of it.

THIS IS A SCREEN, NOT A PROOF.  It reads source text, and source text does not
show:

  * instances, which are found by typeclass resolution and never named;
  * `simp` lemmas, which change what `simp` closes without appearing in a proof;
  * notation and macros, which are consumed during parsing;
  * `export`ed names, which reach a module under a shorter spelling;
  * anything a tactic finds by search -- `aesop`, `positivity`, `norm_num`
    extensions, `gcongr` lemmas, `fun_prop`.

So `unused` reports CANDIDATES.  A candidate is safe to act on only once the
five cases above have been checked for the specific module being cut, which is
what `drop` reports on: it names the modules that would go out of reach, so a
reader can decide rather than being told.

The rule this file exists to respect: A MEASUREMENT THAT CANNOT REPORT ITS OWN
LIMITS WILL BE READ AS THOUGH IT HAD NONE.
"""

from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
IMPORT_RE = re.compile(r"^import\s+(\S+)", re.M)
# A declaration head.  Deliberately anchored at column zero: an indented `def`
# inside a `where` block is not a name another module can refer to.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|inductive|class|instance|axiom|opaque)\s+"
    r"([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)",
    re.M,
)
# Names that are too short or too common to attribute to a module by text match.
# A false ATTRIBUTION makes a cut look unsafe, which is the safe direction, so
# this list is short on purpose.
NOISE = {"value", "map", "comp", "id", "sum", "product", "ratio", "share", "witness"}

# The layer order the corpus is adopting.  A module may import its own layer and
# any layer below it, and nothing above.
#
# The four directories at rank 4 are SIBLINGS, not a sub-order: `Portability`,
# `Spectral`, `Blindness` and `Conditionals` are four subsystems over the same
# population-genetic base, and none is built on another.  Giving them one rank
# says an import between them is not a layer violation -- it may still be a
# coupling worth removing, but it is a different finding and this file does not
# make it.  `Pangenome` sits with them because it is a fifth such subsystem.
#
# Enforcement belongs in `assert_not_exists` at the head of each file, where a
# violation is a build error at the file that commits it.  This mode exists
# because that enforcement needs a compiler and the ordering can be measured
# without one -- and because the direct-violation count is the number that says
# how much work the enforcement is, which is much smaller than it looks.
LAYERS = {
    "Core": 0,
    "Foundations": 1,
    "Coalescent": 2,
    "PopGen": 3,
    "Portability": 4,
    "Spectral": 4,
    "Blindness": 4,
    "Conditionals": 4,
    "Pangenome": 4,
    "Decision": 5,
    "Program": 6,
}


def layer_of(mod: str) -> int | None:
    parts = mod.split(".")
    return LAYERS.get(parts[1]) if len(parts) > 1 else None


def modules() -> dict[str, str]:
    """Module name -> source text, for every .lean file under Descent/."""
    out = {}
    for base, _dirs, files in os.walk(os.path.join(ROOT, "Descent")):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            out[os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")] = open(
                p, encoding="utf-8", errors="ignore"
            ).read()
    root = os.path.join(ROOT, "Descent.lean")
    if os.path.exists(root):
        out["Descent"] = open(root, encoding="utf-8", errors="ignore").read()
    return out


def imports_of(src: str) -> list[str]:
    return [m for m in IMPORT_RE.findall(src) if m.startswith("Descent")]


def declares(src: str) -> set[str]:
    """The bare names a module introduces, last component only.

    Last component because a use site writes `fstFromFlow`, not
    `Descent.Core.fstFromFlow`, whenever the namespace is open -- which it
    usually is.  Matching on the last component over-attributes rather than
    under-attributes, and over-attribution makes a cut look unsafe.
    """
    return {n.split(".")[-1] for n in DECL_RE.findall(src)} - NOISE


def reachable(mod: str, edges: dict[str, list[str]], skip: tuple[str, str] | None = None) -> set[str]:
    """Transitive import closure of `mod`, optionally with one edge removed."""
    seen, stack = set(), [mod]
    while stack:
        m = stack.pop()
        for dep in edges.get(m, []):
            if skip == (m, dep) or dep in seen:
                continue
            seen.add(dep)
            stack.append(dep)
    return seen


def uses(src: str, names: set[str]) -> set[str]:
    """Which of `names` the source text mentions outside comments and strings."""
    stripped = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    stripped = re.sub(r"--[^\n]*", " ", stripped)
    stripped = re.sub(r"^import\s+\S+", " ", stripped, flags=re.M)
    tokens = set(re.findall(r"[A-Za-z_][\w']*", stripped))
    return names & tokens


def main() -> int:
    if len(sys.argv) < 2 or sys.argv[1] not in ("drop", "unused", "layers"):
        print(__doc__)
        return 2

    src = modules()
    edges = {m: imports_of(s) for m, s in src.items()}
    decl = {m: declares(s) for m, s in src.items()}

    if sys.argv[1] == "layers":
        direct: list[tuple[str, str]] = []
        for m in sorted(edges):
            lm = layer_of(m)
            if lm is None:
                continue
            for dep in edges[m]:
                ld = layer_of(dep)
                if ld is not None and ld > lm:
                    direct.append((m, dep))
        # Transitive, for the size of the shadow each direct violation casts.
        trans = 0
        for m in edges:
            lm = layer_of(m)
            if lm is None:
                continue
            for dep in reachable(m, edges):
                ld = layer_of(dep)
                if ld is not None and ld > lm:
                    trans += 1
        depth: dict[str, int] = {}

        def d(mod: str, stack: tuple[str, ...] = ()) -> int:
            if mod in depth:
                return depth[mod]
            if mod in stack:
                return 0
            depth[mod] = 0
            depth[mod] = max([d(i, stack + (mod,)) + 1 for i in edges.get(mod, [])] + [0])
            return depth[mod]

        for mod in edges:
            d(mod)
        chains = [m for m, deps in edges.items() if len(deps) == 1]
        print(f"DAG depth {max(depth.values())}; {len(chains)} of {len(edges)} modules "
              f"import exactly one Descent module")
        print(f"{len(direct)} DIRECT layer-order violation(s), casting {trans} transitive one(s).")
        print("These are the import lines that have to change; the transitive count is")
        print("what they cost, and it is why the direct list is the one to work from.\n")
        by_pair: dict[tuple[str, str], list[str]] = {}
        for m, dep in direct:
            by_pair.setdefault((m.split(".")[1], dep.split(".")[1]), []).append(f"{m} -> {dep}")
        for (a, b), rows in sorted(by_pair.items(), key=lambda kv: -len(kv[1])):
            print(f"  {a} (rank {LAYERS[a]}) imports {b} (rank {LAYERS[b]}) -- {len(rows)}")
            for r in sorted(rows):
                print(f"      {r}")
        return 1 if direct else 0

    if sys.argv[1] == "drop":
        if len(sys.argv) < 3:
            print("drop needs a module name")
            return 2
        target = sys.argv[2]
        importers = [m for m, deps in edges.items() if target in deps]
        print(f"{target}: {len(importers)} direct importer(s)\n")
        safe, unsafe = [], []
        for m in sorted(importers):
            before = reachable(m, edges)
            after = reachable(m, edges, skip=(m, target))
            lost_mods = before - after
            lost_names: set[str] = set()
            for lm in lost_mods:
                lost_names |= decl.get(lm, set())
            needed = uses(src[m], lost_names)
            if needed:
                unsafe.append((m, sorted(needed)[:8], len(lost_mods)))
            else:
                safe.append((m, len(lost_mods)))
        print(f"SAFE TO CUT ({len(safe)}) -- no mentioned name goes out of reach:")
        for m, n in safe:
            print(f"    {m}   (loses reach to {n} module(s), uses none of them)")
        print(f"\nNEEDS THE COMPILER ({len(unsafe)}) -- would lose a name the body mentions:")
        for m, names, n in unsafe:
            print(f"    {m}   (loses {n} module(s); mentions {', '.join(names)})")
        print(
            "\nREMINDER: 'safe' here means no NAME goes out of reach.  Instances, simp\n"
            "lemmas, notation, exports and tactic-search lemmas are invisible to this\n"
            "screen.  Check those before cutting."
        )
        return 0

    # unused: every import whose module contributes no mentioned name.
    rows = []
    for m in sorted(edges):
        for dep in edges[m]:
            before = reachable(m, edges)
            after = reachable(m, edges, skip=(m, dep))
            lost: set[str] = set()
            for lm in before - after:
                lost |= decl.get(lm, set())
            if not uses(src[m], lost):
                rows.append((m, dep, len(before - after)))
    print(f"{len(rows)} import(s) contribute no mentioned name (CANDIDATES, not verdicts):\n")
    for m, dep, n in rows:
        print(f"    {m}\n        drop `import {dep}`  (loses reach to {n} module(s))")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
