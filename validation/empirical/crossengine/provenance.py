#!/usr/bin/env python3
"""Engine provenance of empirical verdicts -- the gate-eligible half.

    python3 provenance.py            # exit 1 on any GATING finding
    python3 provenance.py --all      # also list the DIAGNOSTIC findings

The simulations in this directory can never be a required check: their verdicts
are statistical, so at any sample size they carry a false-failure rate.  This
script is the deterministic consequence of them.  It reads the committed
`results.json` and the Lean sources, and it is fast, dependency-free and pinned
to no line number.

Two kinds of finding:

GATING -- a claim that cross-engine measurement showed to be
    RESTRICTED has silently dropped its restriction.  `results.json` records
    which claims were rejected on which cells; if such a definition's docstring
    goes back to reading as an unrestricted validation, the corpus has lost a
    fact it paid for.  This is a real defect and it fails deterministically.

DIAGNOSTIC (not gating) -- a definition claiming VALIDATED whose provenance
    shows only coalescent engines, i.e. it has never met a forward simulator.
    That is the normal state of most of this corpus today, so it is reported
    and not gated; gating it would fail on ~77 definitions from day one, which
    is a survey, not a check.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent


def find_repo_root(start: pathlib.Path) -> pathlib.Path:
    for p in [start, *start.parents]:
        if (p / "Descent").is_dir() and (p / "lakefile.lean").is_file():
            return p
    raise SystemExit("could not locate the repository root above " + str(start))


ROOT = find_repo_root(HERE)

# `noncomputable def NAME`, `def NAME`, `abbrev NAME`.  Anchored on the NAME,
# never on a line number: definitions in this corpus move every few minutes.
def_re_cache: dict[str, re.Pattern] = {}


def def_pattern(name: str) -> re.Pattern:
    if name not in def_re_cache:
        def_re_cache[name] = re.compile(
            r"^(?:noncomputable\s+)?(?:def|abbrev)\s+" + re.escape(name)
            + r"\b", re.M)
    return def_re_cache[name]


def docstring_of(text: str, name: str):
    """The `/-- ... -/` block immediately preceding `def name`, or None."""
    m = def_pattern(name).search(text)
    if not m:
        return None
    head = text[:m.start()]
    close = head.rfind("-/")
    if close < 0:
        return None
    # Everything between the last `/--` before that close and the close itself.
    open_ = head.rfind("/--", 0, close)
    if open_ < 0:
        return None
    between = head[close + 2:]
    # The docstring must be adjacent: only whitespace may separate it from the
    # definition, otherwise we have picked up an unrelated earlier comment.
    if between.strip():
        return None
    return head[open_ + 3:close]


UNRESTRICTED_VALIDATED = re.compile(
    r"Empirical status:\s*\*\*VALIDATED\*\*", re.I)


def check(results_path: pathlib.Path, show_all: bool) -> int:
    if not results_path.exists():
        print(f"no results at {results_path}; nothing to check", file=sys.stderr)
        return 0
    doc = json.loads(results_path.read_text())
    gating, diagnostic = [], []

    for key, s in doc.get("claims", {}).items():
        lean = ROOT / s["lean_file"]
        if not lean.exists():
            gating.append(f"{key}: {s['lean_file']} does not exist")
            continue
        text = lean.read_text(errors="ignore")
        name = s["def_name"]
        if not def_pattern(name).search(text):
            gating.append(
                f"{key}: definition `{name}` is gone from {s['lean_file']}; "
                "the cross-engine result that restricts it now describes "
                "nothing. Re-point or delete the claim in claims.py.")
            continue
        doc_txt = docstring_of(text, name)

        restricted = bool(s.get("cells_corpus_rejected"))
        if restricted:
            if doc_txt is None:
                gating.append(
                    f"{key}: `{name}` was rejected by forward simulation on "
                    f"{len(s['cells_corpus_rejected'])} cells but now carries "
                    "no docstring at all, so the restriction is unrecorded.")
                continue
            if UNRESTRICTED_VALIDATED.search(doc_txt):
                worst = max(s["cells_corpus_rejected"],
                            key=lambda c: abs(c["sems"]))
                gating.append(
                    f"{key}: `{name}` reads as unrestricted **VALIDATED**, but "
                    f"forward simulation rejects it on cell {worst['cell']!r} "
                    f"({worst['engine']}) at {abs(worst['sems']):.0f} sems "
                    f"(measured {worst['measured']:.4g} against "
                    f"{worst['corpus']:.4g}). The restriction has been dropped.")
            if "crossengine" not in doc_txt:
                gating.append(
                    f"{key}: `{name}` is restricted by cross-engine "
                    "measurement, but its docstring no longer cites "
                    "`validation/empirical/crossengine/`, so a reader "
                    "cannot find the evidence for the restriction.")

        kinds = set(s.get("engine_kinds", []))
        if doc_txt and UNRESTRICTED_VALIDATED.search(doc_txt) \
                and "forward" not in kinds:
            diagnostic.append(
                f"{key}: `{name}` claims VALIDATED on {sorted(kinds)} engines "
                "only; no forward simulator has ever seen it.")

    for f in gating:
        print("GATING: " + f)
    if show_all or not gating:
        for f in diagnostic:
            print("DIAGNOSTIC: " + f)
    print(f"\ncrossengine provenance: {len(gating)} gating, "
          f"{len(diagnostic)} diagnostic")
    return 1 if gating else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", default=str(HERE / "results.json"))
    ap.add_argument("--all", action="store_true")
    a = ap.parse_args()
    return check(pathlib.Path(a.results), a.all)


if __name__ == "__main__":
    raise SystemExit(main())
