"""Find docstrings that claim more than their theorem proves.

WHY

A Lean theorem cannot be false. Its docstring can, and the docstring is what a
reader takes away. The gap between them is the one defect class the kernel
cannot catch, and it is the same class as proof laundering: the statement is
sound, the claim attached to it is not.

Two shapes are checkable from the sources alone.

EQUIVALENCE CLAIMED, ONE DIRECTION PROVED

A docstring saying "exactly when", "if and only if", "precisely when" or
"necessary and sufficient", attached to a statement with no `↔`.  Sometimes the
converse sits in an adjacent theorem and the package really is an equivalence,
so this reports rather than accuses -- but each entry has to be checked, because
the honest version is cheap:

    constantConditional_driftDefect_zero  said the defect vanishes "exactly
    when" the conditional does not drift, and proved only that a constant
    conditional has zero defect.  The converse needed six lines and a positivity
    hypothesis that turned out to matter: an ancestry of weight zero contributes
    nothing to the defect and its conditional is unconstrained.

ORDER CLAIMED, INSTANCE PROVED

A docstring asserting a general ordering -- "more X means more Y" -- attached to
a closed numeric instance.  The failure mode is real and was found here by
external review: a resolution/defect co-monotonicity claim held along nested
information filtrations and failed for unrelated predictors, with a two-bit
counterexample.  See `MetricSpecificPortability.lean`, where the counterexample
is now formalised beside the nested statement.

WHAT TO DO WITH AN ENTRY

Three honest repairs, in order of preference: prove the converse; weaken the
docstring to what the statement says; or formalise the counterexample that shows
the general reading is false. The third is the most valuable, because it stops
the claim being re-made.

    python3 overclaim_gap.py             # counts and entries
    python3 overclaim_gap.py --file NAME # one module
"""

from __future__ import annotations

import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve()
CORPUS = HERE.parents[3] / "Calibrator"

PAIR = re.compile(
    r"/--((?:.|\n)*?)-/\s*\n(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+"
    r"([A-Za-z0-9_']+)((?:.|\n)*?):=", re.M)

IFF = re.compile(
    r"if and only if|exactly when|precisely when|necessary and sufficient",
    re.I)


def scan() -> list[tuple[str, str, str]]:
    out: list[tuple[str, str, str]] = []
    for f in sorted(CORPUS.rglob("*.lean")):
        txt = f.read_text(encoding="utf-8")
        names = set(re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z0-9_']+)",
            txt, re.M))
        for m in PAIR.finditer(txt):
            doc, name, stmt = m.group(1), m.group(2), m.group(3)
            if "↔" in stmt:
                continue
            hit = IFF.search(doc)
            if not hit:
                continue
            # A converse stated nearby, by the corpus's own naming habit.
            stem = name.split("_")[0]
            converse = any(
                other != name and other.startswith(stem)
                and ("_of_" in other or other.endswith("_converse"))
                for other in names)
            note = hit.group(0).lower() + (
                "  (converse may be adjacent)" if converse else "")
            out.append((name, f.relative_to(CORPUS).as_posix(), note))
    return out


def main(argv: list[str]) -> int:
    if not CORPUS.is_dir():
        print(f"corpus not found at {CORPUS}", file=sys.stderr)
        return 2
    rows = scan()
    print(f"{len(rows)} one-directional theorems whose docstring claims an "
          f"equivalence")

    if "--file" in argv:
        want = argv[argv.index("--file") + 1]
        rows = [r for r in rows if want in r[1]]
        print(f"{len(rows)} of those are in {want}")
    else:
        print()
        by_file = collections.Counter(f for _, f, _ in rows)
        for f, c in by_file.most_common(12):
            print(f"  {c:4d}  {f}")
    print()
    for name, f, note in rows:
        print(f"  {name:54s} {note:38s} {f}")
    print()
    print("Reports, does not accuse: the converse is sometimes an adjacent")
    print("theorem and the package really is an equivalence. Each entry still")
    print("has to be read, because a docstring is what a reader takes away.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
