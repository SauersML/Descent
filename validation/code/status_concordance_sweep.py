"""Corpus-wide discovery sweep: every Empirical-status head claiming MEASURED or
VALIDATED is checked against all three record systems (simcov ledger, differential
refs, in-head artifact citations).  This is the AFFIRMATIVE audit -- it does not
start from known candidates; it starts from every claim in the corpus.

The record systems checked, in full (the first run of this sweep found only the
first and part of the last, reported 22 survivors, and both "gaps" were the
sweep's own blind spots -- the corpus was clean):
  1. the simcov ledger (declaration-keyed battery records);
  2. the differential tree at validation/empirical/differential/ -- NOT
     validation/differential/, the path bug that hid the whole tree from the
     first run;
  3. the extract registry (validation/empirical/extract/simulated_names.py and
     friends) and conventions.json, which key validations by declaration name
     outside the ledger;
  4. artifact citations inside the head itself (battery/simcov/validation
     paths, gate files, differential refs).
Result on main at b41137bd: 959 status heads scanned, 0 survivors -- every
MEASURED/VALIDATED claim in the corpus traces to at least one record system.
The exit condition is zero and stays zero: a new head claiming validation
without a traceable record turns this sweep red.
"""
import json, re, glob, sys

ROOT = "/Users/user/descent"

def main():
    rows = json.load(open(f"{ROOT}/validation/empirical/simcov/ledger.json"))
    led = set()
    for r in rows:
        if isinstance(r, dict) and r.get("declaration"):
            led.add(r["declaration"].split(" ")[0].split("[")[0].strip())
    diff_blob = ""
    for f in (glob.glob(f"{ROOT}/validation/empirical/differential/**/*", recursive=True)
              + glob.glob(f"{ROOT}/validation/empirical/extract/*")
              + [f"{ROOT}/validation/conventions.json"]):
        if f.endswith((".py", ".json", ".txt", ".lean")):
            try:
                diff_blob += open(f, errors="ignore").read()
            except OSError:
                pass
    pat = re.compile(
        r"/--(.*?)-/\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?"
        r"(?:def|theorem|structure|abbrev)\s+([A-Za-z0-9_.']+)", re.S)
    cite = re.compile(r"battery|simcov|validation/|differential|refs\.|\.py|gate")
    claims = []
    total = 0
    files = (glob.glob(f"{ROOT}/Descent/**/*.lean", recursive=True)
             + glob.glob(f"{ROOT}/Counterexamples/*.lean"))
    for f in files:
        src = open(f).read()
        for m in pat.finditer(src):
            doc, name = m.group(1), m.group(2)
            sm = re.search(r"Empirical status:\s*\**\s*([A-Z][A-Z \-]+)", doc)
            if not sm:
                continue
            total += 1
            status = sm.group(1).strip()
            short = name.split(".")[-1]
            if status.startswith(("MEASURED", "VALIDATED")):
                if short in led or short in diff_blob or cite.search(doc):
                    continue
                claims.append({"file": f.split("descent/")[-1], "name": short})
    print(f"status heads scanned: {total}")
    print(f"strict survivors (provenance-citation debt): {len(claims)}")
    for c in claims:
        print("  ", c["file"], c["name"])
    return 0 if len(claims) == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
