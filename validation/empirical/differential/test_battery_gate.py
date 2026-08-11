#!/usr/bin/env python3
"""CALIBRATION of the differential battery's GATE, in both directions.

    python3 validation/empirical/differential/test_battery_gate.py

`test_identity_gate.py` and `test_roundtrip.py` calibrate two families of CHECK.
Nothing calibrated `run.py` itself -- the code that decides, from a table of
per-check results, whether the battery passed.  That code was calibrated in
practice at exactly one boundary: a check whose EVERY grid point raised was
reported.  A check evaluable at one of fifteen points was not, and neither was
an instrument that compared nothing at all.

Measured before the fix, driving the real `run.main()` with `checks.CHECKS`
perturbed:

    14/15 grid points raise, survivor at index 0   -> verdict AGREE, rc 0
    14/15 grid points raise, survivor at index 14  -> verdict AGREE, rc 0
    15/15 grid points raise                        -> verdict ERROR, rc 1
    extraction table emptied                       -> cross-check compared 0
                                                      definitions, totality
                                                      audit visited 0 points,
                                                      neither said so

So this asserts, over the REAL check list:

  NEGATIVE  the unperturbed battery returns 0, and a perturbation that leaves
            every point evaluable does not trip the new failure.
  POSITIVE  a check that loses part of its grid fails, whichever end survives;
            a check that loses all of it fails; an instrument that measured
            nothing fails.

The partial-grid probes are placed at BOTH ends of the victim's grid.  Several
checks in `checks.py` carry a `canfail_clause` saying in words that their
discrimination lives at one end of the grid -- `coalFst-exact-split`'s says the
check cannot discriminate at all for `t << Ne` -- so a probe that only ever
removed the head would certify the instrument over the half where the loss is
harmless.

Stdlib only, no Lean, no build; it does import the generated table through
`run.py`, so it runs after `emit.py` exactly as the battery does.
"""

from __future__ import annotations

import copy
import json
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import checks                                                    # noqa: E402
import run                                                       # noqa: E402

REAL = list(checks.CHECKS)
# A check with a wide grid and a documented end-dependence, so that losing part
# of the grid is a real loss rather than a bookkeeping one.
VICTIM = "coalFst-exact-split"

FAILURES = []


def expect(condition, message):
    if not condition:
        FAILURES.append(message)
    print(f"  {'ok  ' if condition else 'FAIL'}  {message}")


def _run(check_list):
    """Run the real gate over `check_list`; return (rc, results dict)."""
    saved = checks.CHECKS
    saved_argv = sys.argv
    handle, path = tempfile.mkstemp(suffix=".json")
    os.close(handle)
    try:
        checks.CHECKS = check_list
        sys.argv = ["run.py", "--json", path]
        try:
            rc = run.main()
        except SystemExit as exc:
            rc = exc.code
        with open(path) as fh:
            return rc, json.load(fh)
    finally:
        checks.CHECKS = saved
        sys.argv = saved_argv
        os.unlink(path)


def _only_at(base, keep_index):
    """`base`, but the corpus side raises at every grid point except one."""
    clone = copy.copy(base)
    clone.id = f"{base.id}-CALIB-survivor-{keep_index}"
    lean0 = base.lean
    grid = base.grid

    def lean(D, **params):
        if grid.index(params) != keep_index:
            raise ZeroDivisionError(
                "planted by test_battery_gate.py: body undefined here")
        return lean0(D, **params)

    clone.lean = lean
    return clone


def _never(base):
    """`base`, but the corpus side raises at every grid point."""
    clone = copy.copy(base)
    clone.id = f"{base.id}-CALIB-no-survivor"

    def lean(D, **params):
        raise ZeroDivisionError(
            "planted by test_battery_gate.py: body undefined everywhere")

    clone.lean = lean
    return clone


def substitute(victim, replacement):
    return [replacement if c.id == victim else c for c in REAL]


def main():
    base = next((c for c in REAL if c.id == VICTIM), None)
    if base is None:
        print(f"FAIL: the victim check {VICTIM!r} is gone from checks.py; "
              f"re-point this calibration at another wide-grid check rather "
              f"than deleting it.")
        return 1
    n = len(base.grid)

    print("CALIBRATION: the unperturbed battery is the baseline")
    rc, out = _run(REAL)
    expect(rc == 0, f"the real battery returns 0 (got {rc}); nothing below "
                    f"means anything until it does")
    stray = {cid: c["n_grid_errors"] for cid, c in out["checks"].items()
             if c["n_grid_errors"]}
    expect(not stray,
           f"no check in the real battery has an errored grid point (got {stray})")

    print()
    print("CALIBRATION: a check that loses part of its grid must fail")
    for keep in (0, n - 1):
        rc, out = _run(substitute(VICTIM, _only_at(base, keep)))
        row = out["checks"][f"{VICTIM}-CALIB-survivor-{keep}"]
        where = "HEAD" if keep == 0 else "TAIL"
        expect(rc != 0,
               f"{where}: a check evaluable at only grid point {keep} of {n} "
               f"fails the gate (rc={rc}, verdict={row['verdict']}, "
               f"{row['n_grid_errors']} of {row['n_grid']} points raised)")
        expect(row["n_grid_errors"] == n - 1,
               f"{where}: the results file records {row['n_grid_errors']} "
               f"errored points, expected {n - 1}")

    print()
    print("CALIBRATION: a check that loses ALL of its grid must fail")
    rc, out = _run(substitute(VICTIM, _never(base)))
    row = out["checks"][f"{VICTIM}-CALIB-no-survivor"]
    expect(rc != 0 and row["verdict"] == "ERROR",
           f"a check evaluable at no grid point fails the gate as ERROR "
           f"(rc={rc}, verdict={row['verdict']})")

    print()
    print("CALIBRATION: an instrument that compared nothing must fail")
    # The cross-check and the totality audit both report a COUNT and were gated
    # only on the disagreements inside it -- zero when the two translators agree
    # everywhere, and equally zero when there was nothing to compare. Emptying
    # the extraction table is the state extract/ was actually in.
    saved_cross, saved_totality = run._cross_validate, run._crossvalidate_points
    try:
        run._cross_validate = lambda D, used: {
            "method": "planted by test_battery_gate.py: compared nothing",
            "n_definitions_compared": 0, "n_arg_tuples": 0,
            "n_agree_all_points": 0, "agree": {},
            "quarantined_disagreements": [], "unresolved_disagreements": [],
            "not_comparable": {},
        }
        rc, _ = _run(REAL)
        expect(rc != 0,
               f"a cross-check that compared 0 definitions fails the gate "
               f"(rc={rc})")
    finally:
        run._cross_validate = saved_cross

    try:
        run._crossvalidate_points = lambda: {}
        rc, out = _run(REAL)
        expect(out["contract_totality"]["points_checked"] == 0,
               "the planted empty point set really does empty the totality "
               "audit, as the case requires")
        expect(rc != 0,
               f"a totality audit that visited 0 points fails the gate "
               f"(rc={rc})")
    finally:
        run._crossvalidate_points = saved_totality

    print()
    if FAILURES:
        print(f"FAIL: {len(FAILURES)} calibration assertion(s) failed")
        for message in FAILURES:
            print(f"  {message}")
        return 1
    print("PASS: the differential battery's gate is calibrated in both "
          "directions -- a clean battery passes, a check that loses its grid "
          "at either end fails, and an instrument that compared nothing fails.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
