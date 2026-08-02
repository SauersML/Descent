"""Simulation-coverage report over proofs/Calibrator.

Answers: which definitions have actually been checked against an independent
ground truth, and which are asserted but never tested?

A definition counts as COVERED if its name appears in one of the validation
scripts in this directory (each of which quotes the Lean source it transcribes).
Everything else is UNCOVERED -- machine-checked, and empirically unexamined.
"""
from __future__ import annotations

import collections
import pathlib
import re
import sys

HEAD_RE = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)")


def all_defs(root):
    defs = []
    for path in sorted(pathlib.Path(root).rglob("*.lean")):
        for i, line in enumerate(path.read_text(errors="ignore").splitlines()):
            m = HEAD_RE.match(line.strip())
            if m:
                defs.append((m.group(1), path.name))
    return defs


def tested_names(script_dir):
    names = set()
    for p in pathlib.Path(script_dir).glob("*.py"):
        txt = p.read_text(errors="ignore")
        # names appear as lean_<Name>, "<Name>", or Spec("<Name>"
        for m in re.finditer(r"lean_([A-Za-z_][\w']*)", txt):
            names.add(m.group(1))
        for m in re.finditer(r"[\"']([a-z][A-Za-z0-9_']{4,})[\"']", txt):
            names.add(m.group(1))
    return names


def main(root, scripts):
    defs = all_defs(root)
    tested = tested_names(scripts)
    by_file = collections.defaultdict(lambda: [0, 0])
    covered, uncovered = [], []
    for name, f in defs:
        base = name.split(".")[-1]
        hit = base in tested or name in tested
        by_file[f][0] += 1
        if hit:
            by_file[f][1] += 1
            covered.append(name)
        else:
            uncovered.append((name, f))

    total = len(defs)
    print(f"definitions: {total}   covered by a validation script: {len(covered)}"
          f"   ({100*len(covered)/total:.1f}%)\n")
    print("coverage by file (files with >=8 definitions):")
    print(f"{'file':<44} {'defs':>5} {'cov':>5} {'%':>6}")
    for f, (n, c) in sorted(by_file.items(), key=lambda kv: -kv[1][0]):
        if n < 8:
            continue
        print(f"{f:<44} {n:5d} {c:5d} {100*c/n:5.0f}%")

    print("\nlargest wholly-untested files:")
    zero = [(f, n) for f, (n, c) in by_file.items() if c == 0 and n >= 8]
    for f, n in sorted(zero, key=lambda kv: -kv[1])[:12]:
        print(f"   {f:<44} {n:5d} definitions, none tested")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "Calibrator",
         sys.argv[2] if len(sys.argv) > 2 else "validation/popgen_defs")
