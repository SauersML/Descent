"""Name-collision scan, run against RAW declarations.

This deliberately does not use the shared definition table, or any table keyed
by name.  A dictionary keyed by fully-qualified name CANNOT REPRESENT a name
collision: the second declaration overwrites the first, and the count of
colliding names is identically zero by construction.  Adopting the shared
parser took this project's homonym count from 1 to 0 for exactly that reason,
and the one it lost was a genuine duplicate declaration
(`effectCorrelationStabilizing`, since renamed in 17dc297e).

So this scan reads declaration headers straight out of the Lean sources and
groups by the name a reader would see, tracking `namespace` (which changes a
name) separately from `section` (which does not).  It is the one check in this
directory that must never be folded into the shared table.
"""

from __future__ import annotations

import json
import re
from collections import defaultdict
from pathlib import Path

from paths import CALIBRATOR as CAL, require, ARTIFACTS as ART

require(CAL, "proofs/Calibrator")

DEF = re.compile(
    r"^(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*"
    r"(def|abbrev|structure|inductive)\s+([A-Za-z_][A-Za-z0-9_.'₀-₉]*)")
NS_OPEN = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
NS_END = re.compile(r"^end\b\s*([A-Za-z_][A-Za-z0-9_.']*)?")
SEC_OPEN = re.compile(r"^section\b\s*([A-Za-z_][A-Za-z0-9_.']*)?")


def scan_file(path: Path):
    """Yield (fully_qualified_name, short, line, private, kind)."""
    ns: list[str] = []
    opened: list[str] = []  # stack entries: "ns:<name>" or "sec:<name>"
    for i, line in enumerate(path.read_text(encoding="utf-8").split("\n"), 1):
        m = NS_OPEN.match(line)
        if m:
            ns.append(m.group(1))
            opened.append("ns:" + m.group(1))
            continue
        m = SEC_OPEN.match(line)
        if m:
            opened.append("sec:" + (m.group(1) or ""))
            continue
        m = NS_END.match(line)
        if m:
            if opened:
                kind = opened.pop()
                if kind.startswith("ns:") and ns:
                    ns.pop()
            continue
        m = DEF.match(line)
        if m:
            short = m.group(2)
            fq = ".".join(ns + [short]) if ns else short
            yield fq, short, i, line.strip().startswith("private"), m.group(1)


def run():
    sites = defaultdict(list)
    for p in sorted(CAL.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        for fq, short, line, priv, kind in scan_file(p):
            sites[fq].append({"file": str(p.relative_to(CAL.parent)), "line": line,
                              "short": short, "private": priv, "kind": kind})
    collisions = {fq: v for fq, v in sites.items() if len(v) > 1}
    # a collision between two private declarations in different files is legal
    real = {fq: v for fq, v in collisions.items()
            if sum(1 for x in v if not x["private"]) > 1}
    return {"declarations": sum(len(v) for v in sites.values()),
            "distinct_names": len(sites),
            "colliding_names": collisions,
            "colliding_public": real}


def main():
    r = run()
    (ART / "results_homonyms.json").write_text(
        json.dumps(r, indent=1, ensure_ascii=False))
    print("HOMONYM SCAN (raw declarations, no name-keyed table)")
    print(f"  declarations read        : {r['declarations']}")
    print(f"  distinct qualified names : {r['distinct_names']}")
    print(f"  names declared twice+    : {len(r['colliding_names'])}")
    print(f"  ...with >1 non-private   : {len(r['colliding_public'])}")
    print()
    for fq, v in sorted(r["colliding_public"].items()):
        print(f"  !! {fq}")
        for x in v:
            print(f"       {x['file']}:{x['line']}  {'private ' if x['private'] else ''}{x['kind']}")
    if not r["colliding_public"]:
        print("  no public name declared more than once")
        return 0
    # Exit non-zero so this can gate a commit or a CI step.  A duplicate
    # fully-qualified declaration does not compile, and it has been
    # reintroduced by a multi-stage refactor whose later stage was authored
    # against a pre-rename copy of the file -- which no amount of renaming
    # prevents, but a guard run before pushing does.
    print()
    print("  FAIL: a fully-qualified name is declared more than once. Lean will")
    print("  reject this. If a rename already fixed it once, check whether a")
    print("  later stage of an in-flight refactor was authored before the fix.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main() or 0)
