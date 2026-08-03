#!/usr/bin/env python3
"""Environment preflight. Computes nothing; fails loudly and specifically.

Run before sweep_inlined.py or dgp_batch.py. Exits non-zero with a precise
reason if those scripts cannot do what they claim, so that a failure is
diagnosed rather than worked around.

Written for Python 3.6.8 with numpy only.
"""

import json
import os
import shutil
import sys
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.normpath(os.path.join(HERE, "..", "..", "extract"))

problems = []
notes = []


def check(label, ok, detail):
    line = "  [%s] %s" % ("OK " if ok else "FAIL", label)
    if detail:
        line += " -- " + str(detail)
    print(line)
    if not ok:
        problems.append(label + ": " + str(detail))


print("PREFLIGHT")
print("  python %s" % sys.version.split()[0])

# --- 1. numpy --------------------------------------------------------------
try:
    import numpy as np
    check("numpy imports", True, "version " + np.__version__)
except Exception as exc:
    check("numpy imports", False, exc)
    np = None

# --- 2. the extract directory ---------------------------------------------
check("extract directory exists", os.path.isdir(EXTRACT), EXTRACT)

# --- 3. stale bytecode -----------------------------------------------------
# A __pycache__ entry older than the module it caches can serve the previous
# version of a regenerated file, and the symptom is indistinguishable from
# "the fix was never applied". Delete rather than diagnose.
pyc = os.path.join(EXTRACT, "__pycache__")
if os.path.isdir(pyc):
    try:
        shutil.rmtree(pyc)
        notes.append("removed stale __pycache__ in extract/")
        print("  [OK ] cleared extract/__pycache__ before importing")
    except Exception as exc:
        check("clear extract/__pycache__", False, exc)

# --- 4. the generated callables -------------------------------------------
if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

lean_defs = None
try:
    import lean_defs
    check("lean_defs imports", True, lean_defs.__file__)
except SyntaxError as exc:
    check("lean_defs imports", False,
          "SYNTAX ERROR -- generated code is not Python 3.6 compatible: %s" % exc)
except Exception as exc:
    check("lean_defs imports", False, "%s: %s" % (type(exc).__name__, exc))

try:
    import lean_rt  # noqa: F401
    check("lean_rt imports", True, "total-arithmetic runtime present")
except Exception as exc:
    check("lean_rt imports", False, "%s: %s" % (type(exc).__name__, exc))

# --- 5. defs.json ----------------------------------------------------------
defs_path = os.path.join(EXTRACT, "defs.json")
table = None
try:
    fh = open(defs_path)
    table = json.load(fh)
    fh.close()
    check("defs.json loads", True, "%d entries" % len(table))
except Exception as exc:
    check("defs.json loads", False, "%s: %s" % (type(exc).__name__, exc))

# --- 6. a callable actually evaluates -------------------------------------
# coalFst t Ne = t/(t+2Ne); at t=100, Ne=1000 that is exactly 1/21.
if lean_defs is not None:
    try:
        fn = getattr(lean_defs, "coalFst", None) or getattr(
            lean_defs, "Calibrator_coalFst", None)
        if fn is None:
            check("a known callable is present", False,
                  "neither coalFst nor Calibrator_coalFst found in lean_defs")
        else:
            got = fn(100.0, 1000.0)
            want = 100.0 / (100.0 + 2000.0)
            ok = abs(got - want) < 1e-12
            check("coalFst(100,1000) == 1/21", ok,
                  "got %r, want %r" % (got, want))
    except Exception:
        check("a known callable evaluates", False, traceback.format_exc(limit=3))

# --- 7. api (only dgp_batch.py needs it) ----------------------------------
try:
    import api
    n = len(api.definition_table())
    check("api imports (needed by dgp_batch.py only)", True, "%d definitions" % n)
    try:
        st = api.staleness()
        check("api.staleness() clean", not st, st if st else "clean")
    except AttributeError:
        notes.append("api.staleness() absent; snapshot coherence unverified")
        print("  [    ] api.staleness() not present in this build (not fatal)")
except SyntaxError as exc:
    check("api imports (needed by dgp_batch.py only)", False,
          "SYNTAX ERROR -- api.py is not Python 3.6 compatible: %s. "
          "sweep_inlined.py does NOT need api and should still run." % exc)
except Exception as exc:
    check("api imports (needed by dgp_batch.py only)", False,
          "%s: %s" % (type(exc).__name__, exc))

print("")
if problems:
    print("PREFLIGHT FAILED -- %d problem(s):" % len(problems))
    for p in problems:
        print("  * " + p)
    print("")
    print("Send this output back rather than working around it. If only the")
    print("api import failed, sweep_inlined.py is still runnable; dgp_batch.py")
    print("is not.")
    sys.exit(1)

print("PREFLIGHT PASSED")
for n_ in notes:
    print("  note: " + n_)
sys.exit(0)
