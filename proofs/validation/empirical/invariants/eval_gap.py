"""List real-valued definitions that no theorem evaluates in closed form.

WHY THIS EXISTS SEPARATELY FROM `worklist_triage.py`

`worklist_triage.py` is exact but needs `coverage.json`, `unreachable.json` and
`results_theorems.json`, which come from a full `check_theorems` run.  That run
is a cluster job.  This script needs nothing but the `.lean` sources, so it can
be run while editing, and it answers the one question that decides whether a
definition is worth a theorem:

    is there any theorem whose conclusion equates this definition, applied to
    arguments, to an expression that mentions no other definition?

Such a theorem is an EXACT EVALUATION.  It is the only shape that survives the
eight failure modes catalogued in `worklist_triage.py`, because it fixes the
body at a point rather than fixing a property the body shares with its wrong
neighbours.  Everything else -- invariance, one-sided bound, vanishing
criterion, decay direction, cross-identity, fixed point -- leaves a family of
bodies satisfying it.

WHAT IT IS NOT

An approximation, deliberately biased toward reporting too much:

  * it reads text, not elaborated terms, so a definition evaluated through an
    abbreviation or a structure projection is reported as unevaluated;
  * a definition can be legitimately covered by `check_ranges` or by a
    simulation without any exact-evaluation theorem, and this script does not
    know that;
  * a cross-identity to an ALREADY-PINNED definition does pin the second one.
    This script counts it as unevaluated, which is the safe direction: the pin
    is then stated directly rather than resting on a chain.

So treat the output as candidates. `worklist_triage.py` decides.

    python3 eval_gap.py                  # counts, and the worst files
    python3 eval_gap.py --list           # every candidate
    python3 eval_gap.py --file NAME      # candidates in one module
"""

from __future__ import annotations

import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve()
CORPUS = HERE.parents[3] / "Calibrator"

DEF_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?def\s+([a-z][A-Za-z0-9_']*)((?:.|\n)*?):=", re.M)
THM_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s", re.M)
# `name applied-to-things = rhs`, with no comparison operator in between so that
# `f x ≤ g y = ...` does not read as an evaluation of `f`.
#
# The name pattern used to require four characters, so `ppv` and `qst` could
# never be recognised as pinned however many theorems evaluated them. Both were
# carrying a reference evaluation and being reported as open work.
NAME_RE = re.compile(r"\b([a-z][A-Za-z0-9_']*)\b")
COMPARISON = "<>≤≥≠"


def real_defs() -> dict[str, tuple[pathlib.Path, str]]:
    out: dict[str, tuple[pathlib.Path, str]] = {}
    for f in sorted(CORPUS.rglob("*.lean")):
        txt = f.read_text(encoding="utf-8")
        for m in DEF_RE.finditer(txt):
            sig = m.group(2)
            if len(sig) > 600:
                continue
            out[m.group(1)] = (f, sig.rstrip().rsplit(":", 1)[-1].strip())
    return out


def theorem_heads() -> list[str]:
    heads = []
    for f in sorted(CORPUS.rglob("*.lean")):
        txt = f.read_text(encoding="utf-8")
        idx = [m.start() for m in THM_RE.finditer(txt)]
        idx.append(len(txt))
        for a, b in zip(idx, idx[1:]):
            heads.append(re.split(r":=\s*(?:by\b|\n)", txt[a:b])[0])
    return heads


def evaluated(defs: dict) -> set[str]:
    """Names appearing on the left of an equation whose right side names no definition.

    Scanning per equals-sign rather than per name matters.  The earlier version
    matched `name ... = rhs` in one pass, so the regex consumed the whole line
    starting from the FIRST lowercase token -- which for `@[simp] theorem f_mk ...`
    is `simp`.  Every `@[simp]`-tagged evaluation was therefore invisible, and the
    definitions they pinned were reported as open work.
    """
    seen: set[str] = set()
    for head in theorem_heads():
        # A statement that WRAPS puts its definition on one line and its `=` on the
        # next, so the per-line scan below misses it entirely.  When the whole head
        # contains exactly one `=` there are no hypothesis equalities to confuse the
        # leftmost-name rule, so the joined head can be scanned directly.
        joined = " ".join(head.split())
        lines = head.split("\n")
        if joined.count("=") - joined.count(":=") - joined.count("==") == 1:
            lines = lines + [joined]
        for line in lines:
            for pos, ch in enumerate(line):
                if ch != "=":
                    continue
                if pos and line[pos - 1] in COMPARISON + ":!":
                    continue
                if pos + 1 < len(line) and line[pos + 1] == "=":
                    continue
                lhs, rhs = line[:pos], line[pos + 1:]
                if any(c in lhs for c in COMPARISON):
                    continue
                if any(d in rhs for d in defs):
                    continue
                # Only the leftmost definition name counts: it is the head of the
                # applied expression.  `hweGenotypeVariance gaussianKurtosisMaf = 1/3`
                # pins the variance, not the argument it is evaluated at.
                for name in NAME_RE.findall(lhs):
                    if name in defs:
                        seen.add(name)
                        break
    return seen


def main(argv: list[str]) -> int:
    if not CORPUS.is_dir():
        print(f"corpus not found at {CORPUS}", file=sys.stderr)
        return 2
    defs = real_defs()
    real = {n for n, (_, rt) in defs.items() if rt == "ℝ"}
    gap = sorted(real - evaluated(defs))

    want = None
    if "--file" in argv:
        want = argv[argv.index("--file") + 1]
        gap = [n for n in gap if want in defs[n][0].name]

    print(f"{len(real)} real-valued definitions, "
          f"{len(gap)} with no exact-evaluation theorem")
    if want is None:
        print()
        by_file = collections.Counter(
            defs[n][0].relative_to(CORPUS).as_posix() for n in gap)
        for f, c in by_file.most_common(15):
            print(f"  {c:4d}  {f}")
    if "--list" in argv or want is not None:
        print()
        for n in gap:
            print(f"  {n:48s} {defs[n][0].relative_to(CORPUS).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
