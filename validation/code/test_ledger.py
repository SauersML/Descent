#!/usr/bin/env python3
"""Calibration for the `ledger` guard, in BOTH directions.

    python3 validation/code/test_ledger.py

A guard with no calibration is a guard nobody can quote. This one is calibrated
the way `test_check.py` calibrates the laundering detector: against planted
inputs whose correct answer is known before the run, and in both directions,
because a detector that never fires and a detector that always fires are equally
useless and look identical from a passing build.

WHAT IS PLANTED, and what each case is for:

  CLEAN. A ledger and a corpus that agree, with every citation resolvable and
  every agreement competed. Must produce zero findings at gating severity. This
  is the direction that usually goes untested, and it is the one that catches a
  guard which has quietly started failing on everything.

  A PLANTED WRONG FORMULA must be reported. A definition whose docstring claims
  VALIDATED while every ledger record for it says FALSIFIED is the drift this
  guard exists for, and it must appear in the reported list.

  A PLANTED IDENTITY must be recorded as UNINFORMATIVE, not as a MATCH. This is
  the single most important case: `driftVariance`, `haplotypeHomozygosity` and
  `multiTraitEffectiveSampleSize` were all banked as validations off an oracle
  algebraically pinned to the body, and the emitter is supposed to make that
  structurally impossible. The test drives `simcov/ledger.py` on a synthetic
  results file carrying a MATCH with no competitor and asserts the emitted
  verdict is UNINFORMATIVE.

  A HAND-EDITED LEDGER must fail. The competitor gate lives in the emitter, so
  the one way to bank an uncompeted agreement is to edit `ledger.json` directly.
  That must be a build failure, or the gate is advisory.

  A DANGLING CITATION must fail, and a STALE citation must fail.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
# validation/code/, so two levels up is the repository root. The corpus used to
# sit under a `proofs/` directory and no longer does; this resolved through that
# segment and reported the ledger ABSENT rather than failing to find it, which
# is the quiet way for a test to stop testing anything.
REPO = HERE.parent.parent
SIMCOV = REPO / "validation" / "empirical" / "simcov"

FAILURES: list[str] = []


def expect(label: str, ok: bool, detail: str = "") -> None:
    print(("  PASS  " if ok else "  FAIL  ") + label + (
        "" if ok else "\n          " + detail))
    if not ok:
        FAILURES.append(label)


# ---------------------------------------------------------------------------
# 1. the emitter's competitor gate, driven on planted results
# ---------------------------------------------------------------------------

def emit(results: dict, name: str = "plant") -> dict:
    """Run simcov/ledger.py over one planted results file and read it back."""
    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, "battery_%s_results.json" % name), "w") as fh:
            json.dump(results, fh)
        # A source file, so freshness has something to hash and compare.
        with open(os.path.join(d, "battery_%s.py" % name), "w") as fh:
            fh.write("# planted\n")
        os.utime(os.path.join(d, "battery_%s.py" % name), (1, 1))
        out = os.path.join(d, "ledger.json")
        proc = subprocess.run(
            [sys.executable, str(SIMCOV / "ledger.py"), d, "-o", out],
            capture_output=True, text=True)
        if proc.returncode != 0:
            raise RuntimeError(proc.stderr or proc.stdout)
        return json.loads(Path(out).read_text())


def cell(lean: float, truth: float, sem: float) -> dict:
    return dict(design="d%g" % lean, lean=lean, truth=truth, sem=sem,
                sems_off=abs(lean - truth) / sem, rel_err=0.0)


def row(name: str, source: str, verdict: str) -> dict:
    return dict(name=name, source=source, verdict=verdict, note="", regime="r",
                worst=dict(sems_off=1.0), cells=[cell(1, 1, 1), cell(2, 2, 1)])


def test_emitter_gate() -> None:
    print("\nemitter: the competitor gate is structural, not remembered")

    led = emit([row("plantedIdentity", "p*(1-p)*f", "MATCH")])
    rec = [r for r in led["records"] if r["role"] == "corpus"]
    expect("a MATCH with NO competitor is emitted as UNINFORMATIVE",
           len(rec) == 1 and rec[0]["verdict"] == "UNINFORMATIVE",
           "got %s" % [r["verdict"] for r in rec])
    expect("and the downgrade carries its reason",
           bool(rec and rec[0].get("downgraded_because")),
           "no downgraded_because recorded")

    led = emit([row("plantedReal", "a + d*(1-2*p)", "MATCH"),
                row("plantedReal [competing]", "a + d*(1-p)", "FALSIFIED")])
    rec = [r for r in led["records"] if r["role"] == "corpus"]
    expect("a MATCH WITH a rejected competitor survives as MATCH",
           len(rec) == 1 and rec[0]["verdict"] == "MATCH",
           "got %s" % [r["verdict"] for r in rec])
    expect("and the rejected competitor is counted",
           bool(rec and rec[0]["competitors_rejected"] == 1),
           "got %s" % [r.get("competitors_rejected") for r in rec])

    led = emit([row("plantedBoth", "x", "MATCH"),
                row("plantedBoth [competing]", "y", "MATCH")])
    rec = [r for r in led["records"] if r["role"] == "corpus"]
    expect("a MATCH whose competitor ALSO matched is UNINFORMATIVE",
           len(rec) == 1 and rec[0]["verdict"] == "UNINFORMATIVE",
           "got %s" % [r["verdict"] for r in rec])

    led = emit([row("plantedWrong", "z", "FALSIFIED")])
    rec = [r for r in led["records"] if r["role"] == "corpus"]
    expect("a FALSIFIED verdict is NOT downgraded by the gate",
           len(rec) == 1 and rec[0]["verdict"] == "FALSIFIED",
           "got %s" % [r["verdict"] for r in rec])

    # A competitor recorded under a name of the author's choosing, as
    # `equalVarianceGaussianAUC [factor 2 dropped]` is for
    # `equalVarianceGaussianAUCFromSignalVariance`.
    led = emit([row("plantedPrefixed", "u", "MATCH"),
                row("plantedPref [competing]", "v", "FALSIFIED")])
    rec = [r for r in led["records"] if r["role"] == "corpus"]
    expect("a competitor named by a shared prefix is still associated",
           len(rec) == 1 and rec[0]["verdict"] == "MATCH",
           "got %s; prefix association failed"
           % [r["verdict"] for r in rec])


# ---------------------------------------------------------------------------
# 2. the guard, on planted corpus + ledger pairs
# ---------------------------------------------------------------------------

CLEAN_DEF = '''/-
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
-/
namespace Descent

/-- A planted definition.

    Empirical status: **VALIDATED** (`simcov/battery_plant.py`). -/
noncomputable def plantedClean (p : Real) : Real := p

end Descent
'''


def run_guard(lean_src: str, ledger: dict) -> tuple[int, str]:
    """Run check.py's ledger guard against a planted corpus and ledger."""
    with tempfile.TemporaryDirectory() as d:
        proofs = Path(d) / "proofs"
        (proofs / "Descent").mkdir(parents=True)
        (proofs / "Descent" / "Planted.lean").write_text(lean_src)
        (proofs / "Descent.lean").write_text("import Descent.Planted\n")
        led_dir = proofs / "validation" / "empirical" / "simcov"
        led_dir.mkdir(parents=True)
        (led_dir / "ledger.json").write_text(json.dumps(ledger))
        env = dict(os.environ, DESCENT_CORPUS=str(proofs))
        proc = subprocess.run(
            [sys.executable, str(HERE / "check.py"), "--only", "ledger"],
            capture_output=True, text=True, env=env)
        return proc.returncode, proc.stdout + proc.stderr


def ledger_with(**over) -> dict:
    rec = dict(declaration="plantedClean", against=None, battery="plant",
               battery_sha="deadbeef", role="corpus", tag="", source="p",
               verdict_raw="MATCH", verdict="MATCH", downgraded_because=None,
               competitors_carried=1, competitors_rejected=1,
               worst_sems=1.0, cells=2,
               freshness="OK (results not older than source)",
               regime="planted", note="")
    rec.update(over)
    return dict(schema_version=1, records=[rec])


def test_guard() -> None:
    print("\nguard: clean input is silent, each planted defect is reported")

    rc, out = run_guard(CLEAN_DEF, ledger_with())
    expect("a clean corpus and ledger produce ZERO findings",
           rc == 0 and "budget 0" not in out,
           "rc=%d\n%s" % (rc, out.strip()[:600]))
    expect("and the guard says what it checked",
           "ledger guard passes" in out, out.strip()[:300])

    rc, out = run_guard(CLEAN_DEF, ledger_with(competitors_rejected=0))
    expect("a HAND-EDITED uncompeted agreement fails the build",
           rc == 1 and "no competing formula rejected" in out,
           "rc=%d\n%s" % (rc, out.strip()[:600]))

    rc, out = run_guard(CLEAN_DEF, ledger_with(freshness="STALE (source newer than results)"))
    expect("a citation to a STALE battery fails the build",
           rc == 1 and "stale" in out.lower(),
           "rc=%d\n%s" % (rc, out.strip()[:600]))

    rc, out = run_guard(CLEAN_DEF, ledger_with(battery="somethingelse"))
    expect("a citation the ledger has never seen fails the build",
           rc == 1 and "never seen" in out,
           "rc=%d\n%s" % (rc, out.strip()[:600]))

    both = ledger_with()
    both["records"].append(dict(both["records"][0],
                                battery="plant2", verdict="FALSIFIED",
                                verdict_raw="FALSIFIED"))
    rc, out = run_guard(CLEAN_DEF, both)
    expect("contradictory verdicts with no adjudication fail the build",
           rc == 1 and "no adjudication" in out,
           "rc=%d\n%s" % (rc, out.strip()[:600]))

    both["adjudications"] = {"plantedClean": {"authoritative": "plant",
                                              "reason": ["planted"]}}
    rc, out = run_guard(CLEAN_DEF, both)
    expect("and an adjudication clears exactly that finding",
           rc == 0, "rc=%d\n%s" % (rc, out.strip()[:600]))

    # A planted wrong formula: docstring claims agreement, evidence disagrees.
    wrong = ledger_with(verdict="FALSIFIED", verdict_raw="FALSIFIED")
    rc, out = run_guard(CLEAN_DEF, wrong)
    expect("a docstring asserting VALIDATED against a FALSIFIED record is "
           "REPORTED",
           "REPORTED, NOT GATED" in out and "plantedClean" in out,
           "rc=%d\n%s" % (rc, out.strip()[:600]))


def main() -> int:
    if not (SIMCOV / "ledger.py").exists():
        print("test_ledger: %s is absent" % (SIMCOV / "ledger.py"))
        return 2
    test_emitter_gate()
    test_guard()
    print()
    if FAILURES:
        print("test_ledger: %d calibration case(s) FAILED: %s"
              % (len(FAILURES), "; ".join(FAILURES)))
        return 1
    print("test_ledger: all calibration cases pass -- the emitter downgrades an "
          "uncompeted agreement, the guard is silent on clean input, and each "
          "planted defect is reported")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
