#!/usr/bin/env python3
"""Structural guard: is a result wired into the biology, or only adjacent to it?

The condition this enforces is the team lead's, and it is deliberately not a
style rule:

    A result is wired in when removing it breaks something biological.

That is testable. For a Lean corpus it means: some module outside the upstream
arc must *reference a declaration* of the arc module. Import edges alone do not
count -- a module can import another and use nothing from it, and the import
graph then records an intention rather than a dependency. Conversely a shared
vocabulary does not count either: two modules can both talk about allele
frequencies while neither depends on the other, which is the "two corpora that
agree" failure this script exists to detect.

WHAT IT MEASURES

For every module in ARC, collect its declared names, then count references to
those names from modules outside ARC, with docstrings and comments stripped so
that a mention in prose is not scored as a dependency. A module with zero
genuine cross-boundary references is UNWIRED however many files import it.

WHY THE COMMENT-STRIPPING MATTERS

The corpus's house style cites sibling theorems in docstrings extensively. Those
citations are how a reader navigates, and they are exactly what makes an
unwired module look wired. Stripping them is the whole point of the measurement.

KNOWN PARSE HAZARD, HANDLED

Lean keywords can follow a `def`-like token in constructs this regex does not
model, which yields phantom declarations named `in`, `at`, `with`. Those match
everywhere and manufacture false dependencies. Short and reserved names are
therefore dropped; an earlier version of this script reported six spurious
dependents of HiddenConeAmbiguity, all of them the keyword `in`.

Run:  python3 proofs/validation/wiring/check_wiring.py
      python3 proofs/validation/wiring/check_wiring.py --json
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

# The upstream arc: modules whose content is mathematics about coordinate laws,
# designs and limits rather than about genotypes, phenotypes or study design.
ARC = {
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
RESERVED = {
    "in", "at", "with", "fun", "by", "do", "then", "else", "from",
    "have", "show", "let", "this", "where", "deriving", "extends",
}
MIN_NAME_LEN = 4

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|structure|class|abbrev|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)",
    re.M,
)


def strip_comments(text: str) -> str:
    """Remove Lean block comments/docstrings and line comments.

    Block comments do not nest in this corpus in practice, and a non-greedy
    match is correct for that case.
    """
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def load(root: str) -> dict[str, str]:
    out = {}
    for dirpath, _, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                with open(p, encoding="utf-8") as fh:
                    out[p] = fh.read()
    return out


def stem(path: str) -> str:
    return os.path.basename(path)[:-5]


def declarations(text: str) -> set[str]:
    names = set()
    for m in DECL.finditer(text):
        n = m.group(1)
        if n in RESERVED or len(n) < MIN_NAME_LEN:
            continue
        names.add(n)
    return names


def analyze(files: dict[str, str]) -> dict:
    decls = {}
    for p, t in files.items():
        s = stem(p)
        if s in ARC:
            decls[s] = declarations(t)

    bodies = {}
    for p, t in files.items():
        s = stem(p)
        if s not in ARC:
            bodies[s] = strip_comments(t)

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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true", help="emit machine-readable output")
    ap.add_argument(
        "--require",
        nargs="*",
        default=[],
        help="modules that MUST be wired; exit nonzero if any is not",
    )
    args = ap.parse_args()

    here = os.path.dirname(os.path.abspath(__file__))
    calibrator = os.path.normpath(os.path.join(here, "..", "..", "Calibrator"))
    if not os.path.isdir(calibrator):
        print(f"cannot find {calibrator}", file=sys.stderr)
        return 2

    files = load(calibrator)
    report = analyze(files)

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


if __name__ == "__main__":
    raise SystemExit(main())
