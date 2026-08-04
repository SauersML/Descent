"""Find definitions this harness has already measured but never marked.

Ten definitions turned up in one pass sitting exactly here: measured with power
in batteries 2 and 7, results written to the battery JSON, and no status marker
ever added. That is the same failure as a marker with no measurement behind it,
pointing the other way. The screen counts them as owed, so the coverage figure
understates what has been established, and a reader of the definition sees
UNTESTED beside a quantity checked to a fraction of a sem.

This scan cross-references every battery result file against the inventory and
reports definitions that were measured and are still marked UNTESTED. It is
cheaper than any new simulation: the work is done, only the bookkeeping is
missing.

Names are matched loosely, because a battery record's `name` is prose written
for a human -- "coalFst [tight]", "pgsVariance [linkage equilibrium]",
"ldsrExpectedBetaSq [slope = h2/M]". Every identifier-shaped token in the record
name is tried against the inventory, and hits are reported with the verdict and
the worst cell so a human can confirm before landing anything. Nothing is
written automatically: a marker is a claim, and claims get read before they are
made.
"""
import glob
import json
import os
import re
import sys

SIMCOV = sys.argv[1] if len(sys.argv) > 1 else "."
INV = sys.argv[2] if len(sys.argv) > 2 else "inventory.json"

MEASURED_VERDICTS = {"MATCH", "FALSIFIED"}
TOKEN = re.compile(r"[A-Za-z_][A-Za-z_0-9']{3,}")


def main():
    inv = {r["short"]: r for r in json.load(open(INV))}
    untested = {n for n, r in inv.items() if r["status"] == "UNTESTED"}

    found = {}
    for path in sorted(glob.glob(os.path.join(SIMCOV, "battery_*_results.json"))):
        try:
            recs = json.load(open(path))
        except Exception:
            continue
        if isinstance(recs, dict):
            recs = [v for v in recs.values() if isinstance(v, dict)]
        for rec in recs:
            if not isinstance(rec, dict):
                continue          # some result files store bare lists of rows
            v = str(rec.get("verdict", ""))
            if v.split(" ")[0] not in MEASURED_VERDICTS:
                continue
            for tok in TOKEN.findall(str(rec.get("name", ""))):
                if tok not in untested:
                    continue
                w = rec.get("worst") or {}
                sems = w.get("sems_off")
                prev = found.get(tok)
                entry = (os.path.basename(path), v, sems, rec.get("name"))
                # keep the record with the tightest agreement
                if prev is None or (isinstance(sems, (int, float))
                                    and isinstance(prev[2], (int, float))
                                    and sems < prev[2]):
                    found[tok] = entry

    print("definitions measured in a battery and still marked UNTESTED: %d\n"
          % len(found))
    print("  %-40s %-11s %9s  %s" % ("definition", "verdict", "worst sems",
                                     "battery record"))
    for name in sorted(found):
        f, v, sems, recname = found[name]
        s = "%9.2f" % sems if isinstance(sems, (int, float)) else "        -"
        print("  %-40s %-11s %s  %s" % (name, v.split(" ")[0], s, recname[:44]))
        print("      %s  (%s)" % (inv[name]["file"].split("/")[-1], f))

    print("\nNothing is written by this scan. A status marker is a claim, and a")
    print("claim gets read before it is made: several of these will be records")
    print("whose design was later found wrong, and those must stay UNTESTED.")


if __name__ == "__main__":
    main()
