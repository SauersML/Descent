"""Mutation-test the guard calibration: if a guard goes blind, does anyone notice?

    python3 validation/code/mutate_guards.py

STATUS: DIAGNOSTIC.  Not a CI step -- it runs `test_check.py` once per guard,
so it is roughly ten times the cost of the gated calibration.  Run it when a
guard is added, renamed, or substantially rewritten.

WHAT IT ASKS, AND WHY IT IS A DIFFERENT QUESTION.  `test_check.py` plants
defects in fixture corpora and asserts each is reported.  That establishes the
suite catches those defects; it does not establish WHICH guard caught them.  A
guard whose planted defects are also reported by a neighbour looks calibrated
and is not: it could stop working entirely and the calibration would stay
green.

So: neuter each `run_<guard>()` in `check.py` -- make it return 0 immediately,
emitting no findings -- and re-run `test_check.py` against the unmodified
fixtures.  A guard whose calibration still passes while the guard reports
nothing is UNCALIBRATED.

This found exactly one on 2026-08-04: `mathlib`, the guard that proves the
corpus does not duplicate Mathlib, could be silenced entirely with no effect on
`test_check.py`.  `check.mathlib_root()` had honoured `DESCENT_MATHLIB` "so the
guard can be calibrated against a fixture tree" since it was written -- the
hook was built and the calibration was never attached to it.  `calibrate_mathlib()`
in test_check.py now covers it, and this file is what proves that coverage is
real rather than nominal.

The mutation is applied to a throwaway copy; nothing here edits the checkout.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent.parent
CHECK_REL = "validation/code/check.py"
TEST_REL = "validation/code/test_check.py"

# Kept in step with check.py's GUARDS dict; a name that stops resolving is
# reported rather than skipped silently, because a guard renamed out of this
# list is exactly the case this file exists to catch.
GUARDS = ["style", "identifications", "laundering", "regimes", "closure",
          "wiring", "duplication", "mathlib", "conventions"]


def sh(argv, cwd, timeout=1800):
    try:
        p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True,
                           timeout=timeout)
        return p.returncode
    except subprocess.TimeoutExpired:
        return "TIMEOUT"


def stage(td: Path) -> Path:
    root = td / "tree"
    shutil.copytree(REPO / "proofs", root / "proofs", symlinks=True,
                    ignore=shutil.ignore_patterns("__pycache__"))
    return root


def neuter(root: Path, guard: str) -> bool:
    path = root / CHECK_REL
    src = path.read_text(encoding="utf-8")
    m = re.search(rf"^(def run_{guard}\([^)]*\)[^:]*:)$", src, re.M)
    if not m:
        return False
    path.write_text(
        src[:m.end()] + "\n    return 0  # NEUTERED BY mutate_guards.py"
        + src[m.end():], encoding="utf-8")
    return True


def main() -> int:
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        base = stage(td)
        base_rc = sh([sys.executable, TEST_REL], base)
        print(f"baseline test_check.py on unmodified check.py: rc={base_rc}")
        if base_rc != 0:
            print("  Baseline is not green, so nothing below is interpretable: "
                  "a calibration that already fails will 'fail' for every "
                  "mutation regardless of coverage.")
            return 1

        print(f"\n{'guard':<18} {'test_check.py':<14} verdict")
        print("-" * 78)
        blind, missing = [], []
        for guard in GUARDS:
            shutil.rmtree(base)
            base = stage(td)
            if not neuter(base, guard):
                missing.append(guard)
                print(f"{guard:<18} {'-':<14} run_{guard}() not found -- renamed?")
                continue
            rc = sh([sys.executable, TEST_REL], base)
            if rc == 0:
                blind.append(guard)
                note = "UNCALIBRATED: guard silenced, calibration still green"
            else:
                note = "covered (calibration fails when the guard goes blind)"
            print(f"{guard:<18} rc={str(rc):<11} {note}")

        covered = len(GUARDS) - len(blind) - len(missing)
        print(f"\n{covered} of {len(GUARDS)} guards are covered by test_check.py")
        if blind:
            print(f"UNCALIBRATED: {blind}")
        if missing:
            print(f"NOT FOUND (rename this file's GUARDS list): {missing}")
        return 1 if (blind or missing) else 0


if __name__ == "__main__":
    raise SystemExit(main())
