"""An explicit name list to replace the regex in popgen_defs/coverage.py.

That script decides coverage by scanning its own sources for any quoted
lowercase identifier of five or more characters:

    re.finditer(r"[\"']([a-z][A-Za-z0-9_']{4,})[\"']", txt)

which matches every string literal of that shape -- filenames, column headers,
verdict strings, dict keys -- not only definition names.  The resulting figure
is an upper bound with approximate membership, and it has been quoted as a
floor.

This script produces the list that regex was reaching for: names that actually
exist as definitions in the canonical table, partitioned by how strong the
evidence of use is.  It does not modify popgen_defs/coverage.py -- that script
is someone else's and may be relied on.  It prints a list to paste, and the
delta, so the correction can be made by whoever owns it.

    python3 validation/extract/popgen_names.py

Expect the number to come DOWN.  That is the right direction for a figure that
has been quoted as a floor.
"""
from __future__ import annotations

import collections
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import api                                                # noqa: E402

PROOFS = HERE.parent.parent
SCRIPTS = PROOFS / "validation" / "popgen_defs"

# The pattern currently in use, reproduced exactly so the delta is honest.
LOOSE = re.compile(r"[\"']([a-z][A-Za-z0-9_']{4,})[\"']")
# Explicit transcription markers: a name written as `lean_<name>` is a
# deliberate statement that this Python function transcribes that definition.
EXPLICIT = re.compile(r"lean_([A-Za-z_][\w']*)")
# A bare identifier used as code, not as a string.  Weaker than `lean_` but far
# stronger than a quoted literal: it means the name was CALLED or referenced.
CODEISH = re.compile(r"(?<![\"'\w.])([a-z][A-Za-z0-9_']{4,})\s*\(")


def main():
    api.refresh()
    table = api.definition_table()
    by_short = collections.defaultdict(list)
    for n in table:
        by_short[n.split(".")[-1]].append(n)

    loose, explicit, codeish = set(), set(), set()
    files = sorted(SCRIPTS.glob("*.py"))
    for p in files:
        txt = p.read_text(errors="ignore")
        loose |= {m.group(1) for m in LOOSE.finditer(txt)}
        explicit |= {m.group(1) for m in EXPLICIT.finditer(txt)}
        codeish |= {m.group(1) for m in CODEISH.finditer(txt)}

    real = set(by_short)
    loose_real = loose & real
    loose_bogus = loose - real
    explicit_real = explicit & real
    codeish_real = codeish & real

    print("=" * 74)
    print("popgen_defs/coverage.py -- what its regex actually matches")
    print("=" * 74)
    print(f"scripts scanned                        : {len(files)}")
    print(f"tokens the regex matches               : {len(loose)}")
    print(f"  of those, real definition names      : {len(loose_real)}")
    print(f"  of those, NOT definition names       : {len(loose_bogus)}"
          f"   <- string literals counted as coverage")
    print()
    print(f"names written as `lean_<name>` (explicit transcription): "
          f"{len(explicit_real)}")
    print(f"names appearing as called identifiers                  : "
          f"{len(codeish_real)}")

    strong = sorted(explicit_real | codeish_real)
    print(f"\nUNION of the two strong forms                          : "
          f"{len(strong)}")

    total = len(table)
    print(f"\ncorpus definitions: {total}")
    print(f"  regex figure    : {len(loose_real)}/{total} = "
          f"{100*len(loose_real)/total:.1f}%   (current, loose)")
    print(f"  explicit figure : {len(strong)}/{total} = "
          f"{100*len(strong)/total:.1f}%   (name actually used as code)")

    print("\nsample of what the regex counts that is NOT a definition:")
    for tok in sorted(loose_bogus)[:25]:
        print(f"    {tok!r}")

    print("\nEXPLICIT LIST -- paste this in place of the regex:")
    print("SIMULATED = {")
    for n in strong:
        fq = by_short[n]
        print(f"    {n!r},"
              + (f"   # {fq[0]}" if len(fq) == 1 else f"   # AMBIGUOUS {fq}"))
    print("}")

    amb = [n for n in strong if len(by_short[n]) > 1]
    if amb:
        print(f"\n{len(amb)} of these are ambiguous short names and should be "
              "keyed fully-qualified:")
        for n in amb:
            print(f"    {n} -> {by_short[n]}")

    out = {"loose_matches": sorted(loose), "loose_real": sorted(loose_real),
           "loose_bogus": sorted(loose_bogus), "explicit": sorted(explicit_real),
           "codeish": sorted(codeish_real), "recommended": strong,
           "ambiguous": amb, "corpus_total": total}
    (HERE / "popgen_names.json").write_text(json.dumps(out, indent=1))
    print(f"\nwritten: {HERE / 'popgen_names.json'}")


if __name__ == "__main__":
    main()
