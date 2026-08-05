#!/usr/bin/env python3
"""Calibration for `provenance.py`, in BOTH directions.

    python3 test_provenance.py

Deterministic, dependency-free, a fraction of a second.  A check that has never
been shown to fail is not a check, and a check that fires on a clean tree is
noise; this asserts both halves against the committed `results.json`:

  * on the tree as committed, zero gating findings;
  * with the restriction removed from a definition the cross-engine run
    rejected, exactly one gating finding naming that definition.

The mutation is applied to a COPY of the Lean source under a temporary
directory laid out like the repository, so the working tree is never edited --
this repository is shared between concurrent sessions and a test that writes to
tracked files corrupts whatever else is running.
"""

from __future__ import annotations

import json
import pathlib
import shutil
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import provenance                                  # noqa: E402

RESULTS = HERE / "results.json"


def run_against(root: pathlib.Path) -> tuple[int, list[str]]:
    """Run the check with `provenance.ROOT` pointed at `root`."""
    saved = provenance.ROOT
    provenance.ROOT = root
    out = []
    real_print = print
    try:
        import builtins
        builtins.print = lambda *a, **k: out.append(" ".join(str(x) for x in a))
        rc = provenance.check(RESULTS, True)
    finally:
        import builtins
        builtins.print = real_print
        provenance.ROOT = saved
    return rc, out


def stage(root: pathlib.Path, files: set[str]) -> None:
    for rel in files:
        dst = root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(provenance.ROOT / rel, dst)


def main() -> int:
    if not RESULTS.exists():
        print("no committed results.json; nothing to calibrate against")
        return 0
    doc = json.loads(RESULTS.read_text())
    claims = doc["claims"]
    files = {s["lean_file"] for s in claims.values()}
    failures = []
    mutated_count = 0

    with tempfile.TemporaryDirectory() as td:
        clean = pathlib.Path(td) / "clean"
        (clean / "proofs" / "Calibrator").mkdir(parents=True)
        stage(clean, files)

        rc, out = run_against(clean)
        if rc != 0:
            failures.append(
                "the tree as committed produces gating findings, so the check "
                "fires on a clean tree:\n    " + "\n    ".join(out))

        # Drop the restriction from every claim the run rejected, one at a time.
        restricted = {k: s for k, s in claims.items()
                      if s.get("cells_corpus_rejected")}
        if not restricted:
            failures.append(
                "results.json records no rejected claim, so the failing "
                "direction cannot be calibrated at all")
        for key, s in restricted.items():
            dirty = pathlib.Path(td) / ("dirty_" + key)
            (dirty / "proofs" / "Calibrator").mkdir(parents=True)
            stage(dirty, files)
            path = dirty / s["lean_file"]
            text = path.read_text()
            # Restore the unrestricted status header the corpus used to carry.
            mutated = text.replace("Empirical status: **VALIDATED IN THE",
                                   "Empirical status: **VALIDATED** IN THE")
            if mutated == text:
                # This claim's docstring does not use that phrasing; skip it
                # rather than pretend a mutation was applied.
                continue
            path.write_text(mutated)
            mutated_count += 1
            rc, out = run_against(dirty)
            if rc == 0:
                failures.append(
                    f"dropping the restriction on {key} produced NO gating "
                    "finding: the check cannot detect the defect it exists for")
            elif not any(s["def_name"] in line for line in out):
                failures.append(
                    f"dropping the restriction on {key} fired, but no finding "
                    f"names `{s['def_name']}`")

    # A test that skipped every mutation would report success having exercised
    # nothing.  Require that the failing direction was actually driven.
    if mutated_count == 0:
        failures.append(
            "no mutation was applied to any restricted claim, so the failing "
            "direction was never exercised and this test proves nothing")

    for f in failures:
        print("CALIBRATION FAILURE: " + f)
    print(f"provenance calibration: {len(failures)} failure(s), "
          f"{mutated_count} mutation(s) exercised")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
