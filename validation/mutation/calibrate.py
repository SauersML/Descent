#!/usr/bin/env python3.12
"""Repair the probe files against the maxErrors truncation.

Lean stops reporting after `maxErrors` (default 100) messages and emits a
line-0 error saying so.  Every mutant past that point in a file with many
failures produced NO error line, and a span-based "no error here" test read
that as "this mutant compiled".  In the first run 24 of 101 probe files hit the
cap, so both the one-at-a-time and the all-at-once counts were inflated.

The calibration did not catch it because all three calibration probes sat at the
TOP of every file, where truncation cannot reach them.  A calibration placed
where the failure mode cannot reach it is not a calibration.  So this adds:

  * `set_option maxErrors` high enough that truncation does not occur, and
  * a TAIL calibration -- a mutant that MUST fail, placed at the END of the
    file.  If it is ever reported clean, that file was truncated and its whole
    result is void.
  * an AUTOIMPLICIT calibration -- a declaration referring to an undeclared
    name, which compiles under `autoImplicit` and fails without it.  `lake env
    lean` does NOT apply the library's `leanOptions`, so moving off `lake build`
    to lift the message cap silently turned `autoImplicit` back ON, and a
    dropped binder came back as a fresh implicit variable rather than an error.
    If this probe is ever reported clean, the run had autoImplicit and its whole
    result is void.
"""
import pathlib
import sys

TAIL = """
-- {g} CALIB-TAIL
example (zzt : Nat) : 1 < zzt := by omega
-- {g} CALIB-AUTOIMPLICIT
example : zzUndeclaredNameForCalibration = zzUndeclaredNameForCalibration := rfl
"""

for p in sorted(pathlib.Path(sys.argv[1]).glob("TProbe*.lean")):
    guard = sys.argv[2]
    t = p.read_text()
    if "set_option maxErrors" in t:
        continue
    lines = t.split("\n")
    out = []
    for ln in lines:
        out.append(ln)
        if ln.startswith("import "):
            out.append("set_option maxErrors 1000000")
    p.write_text("\n".join(out) + TAIL.format(g=guard))
print("PATCHED", len(list(pathlib.Path(sys.argv[1]).glob("TProbe*.lean"))))
