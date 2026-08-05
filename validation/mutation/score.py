#!/usr/bin/env python3.12
"""Score a mutation sweep, with truncation made self-reporting.

Handles BOTH message formats: lake writes `error: <path>:l:c:`, a direct
`lake env lean` writes `<path>:l:c: error:`.  Getting this wrong is not
hypothetical -- an anchored `^proofs/` regex is what made the vacuity pass
report every theorem as vacuous on its first run.

A file is VOID if it carries the `maximum number of errors` message, or if its
CALIB-TAIL probe -- a mutant that must fail, placed at the very end -- is scored
clean.  The tail calibration exists because the first version of this sweep put
all its calibration at the TOP of each file, where Lean's 100-message cap could
never reach it, so the instrument certified itself on the only region that was
never at risk.
"""
import re
import pathlib
import sys

BUILD = pathlib.Path(sys.argv[1]).read_text(errors="replace")
PROBEDIR = pathlib.Path(sys.argv[2])
MARK = sys.argv[3]            # "MUT" or "ALLMUT"
LABEL = sys.argv[4]           # "DROPPABLE" or "UNCONDITIONAL"

errs, truncated = {}, set()
for m in re.finditer(
        r"(?:error: )?Descent/(TProbe\d+)\.lean:(\d+):\d+:(?: error)?", BUILD):
    errs.setdefault(m.group(1), set()).add(int(m.group(2)))
for m in re.finditer(
        r"Descent/(TProbe\d+)\.lean:\d+:\d+:.*maximum number of errors", BUILD):
    truncated.add(m.group(1))
for m in re.finditer(
        r"(TProbe\d+)\.lean:0:0: maximum number of errors", BUILD):
    truncated.add(m.group(1))

tot = hit = 0
cd = cn = cf = ct = ca = 0
nfiles = void = 0
rows = []
for p in sorted(PROBEDIR.glob("TProbe*.lean")):
    nfiles += 1
    lines = p.read_text().split("\n")
    e = errs.get(p.stem, set())
    marks = []
    for i, ln in enumerate(lines):
        for tag, key in (("CD", "CALIB-DROPPABLE"), ("CN", "CALIB-NEEDED"),
                         ("CF", "CALIB-FRESH"), ("CT", "CALIB-TAIL"),
                         ("CA", "CALIB-AUTOIMPLICIT")):
            if key in ln:
                marks.append((i + 2, tag, None))
                break
        else:
            if f" {MARK} " in ln:
                marks.append((i + 2, "M", ln.split()))
    clean_of = {}
    for k, (start, tag, payload) in enumerate(marks):
        end = marks[k + 1][0] - 2 if k + 1 < len(marks) else len(lines)
        clean_of[k] = not any(start <= x <= end for x in e)
    tailclean = any(clean_of[k] for k, (_, t, _) in enumerate(marks)
                    if t in ("CT", "CA"))
    if p.stem in truncated or tailclean:
        void += 1
        continue
    for k, (start, tag, payload) in enumerate(marks):
        c = clean_of[k]
        if tag == "CD":
            cd += c
        elif tag == "CN":
            cn += c
        elif tag == "CF":
            cf += not c
        elif tag == "CT":
            ct += not c
        elif tag == "CA":
            ca += not c
        else:
            tot += 1
            if c:
                hit += 1
                _, _, _, mod, thm, binder, srcline = payload
                rows.append(f"{LABEL}\t{mod}\t{thm}\t{binder}\t"
                            f"{mod.split('.')[-1]}.lean:{srcline}")

for r in sorted(rows):
    print(r)
good = nfiles - void
print(f"PROBE_FILES\t{nfiles}")
print(f"VOID_FILES\t{void}\t(truncated or tail-calibration clean; must be 0)")
print(f"CALIB_DROPPABLE_COMPILED\t{cd}/{good}\t(must equal {good})")
print(f"CALIB_NEEDED_FALSE_POS\t{cn}/{good}\t(must equal 0)")
print(f"CALIB_FRESH_ERRORS\t{cf}/{good}\t(must equal {good})")
print(f"CALIB_TAIL_FAILED\t{ct}/{good}\t(must equal {good})")
print(f"CALIB_AUTOIMPLICIT_OFF\t{ca}/{good}\t(must equal {good})")
print(f"MUTANTS\t{tot}")
print(f"{LABEL}_TOTAL\t{hit}")
