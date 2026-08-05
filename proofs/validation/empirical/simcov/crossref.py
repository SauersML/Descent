"""Cross-reference every battery_*_results.json against inventory.json.

Coverage here is a docstring property: inventory.py counts a def as MEASURED iff
its own `Empirical status:` line says VALIDATED/FALSIFIED/MEASURED/TESTED.  The
batteries run ahead of the docstrings, so a def can carry a real verdict and
still read UNTESTED.

The batteries record a competing formula for a def under the SAME def name with
a bracketed tag and a DIFFERENT `source` string.  Classifying by tag text is
guesswork (118 distinct tags, some regime labels, some competitors), so this
splits on `source`: rows sharing the bare-name row's source are readings of the
corpus body, rows with any other source are competitors.  That makes the identity
gate mechanical -- a corpus MATCH is only worth something if some competitor on
the same battery was rejected.
"""
import glob
import json
import os
import re
import sys

D = sys.argv[1] if len(sys.argv) > 1 else "."
inv = json.load(open(os.path.join(D, "inventory.json")))
by_short = {}
for r in inv:
    by_short.setdefault(r["short"], []).append(r)

MEASURED_STATES = {"VALIDATED", "FALSIFIED", "MEASURED", "TESTED"}
REAL = {"FALSIFIED", "REFUTED", "MATCH", "VALIDATED"}

rows_by_short = {}
for path in sorted(glob.glob(os.path.join(D, "battery_*_results.json"))):
    bat = os.path.basename(path)[len("battery_"):-len("_results.json")]
    rows = json.load(open(path))
    if isinstance(rows, dict):
        rows = rows.get("results", [])
    for row in rows:
        if not isinstance(row, dict) or not row.get("name"):
            continue
        raw = row["name"].strip()
        short = re.split(r"[ \[(]", raw)[0].split(".")[-1]
        if not short:
            continue
        tag = raw[len(short):].strip()
        rows_by_short.setdefault(short, []).append({
            "battery": bat, "raw": raw, "tag": tag, "bare": not tag,
            "verdict": str(row.get("verdict", "?")),
            "note": (row.get("note") or "")[:300],
            "regime": (row.get("regime") or "")[:260],
            "source": (row.get("source") or "").strip(),
            "span": row.get("span"),
            "worst_sems": (row.get("worst") or {}).get("sems_off"),
            "ncells": len(row.get("cells") or []),
        })


def head(v):
    v = v.upper()
    for w in ("FALSIFIED", "REFUTED", "VOID", "NO POWER", "LEAD",
              "SELF-TEST", "MATCH", "VALIDATED", "CONVENTION", "REGIME"):
        if w in v:
            return w
    return (v.split() or ["?"])[0]


report = {}
for short, rows in rows_by_short.items():
    canon = set(r["source"] for r in rows if r["bare"])
    corpus = [r for r in rows if r["source"] in canon] if canon else rows
    comp = [r for r in rows if r["source"] not in canon] if canon else []
    heads = set(head(r["verdict"]) for r in corpus)
    real = heads & REAL
    # identity gate: a MATCH is only informative if a competitor on the same
    # battery was rejected.
    gated = set()
    for r in corpus:
        if head(r["verdict"]) != "MATCH":
            continue
        if any(c["battery"] == r["battery"] and head(c["verdict"]) in
               ("FALSIFIED", "REFUTED") for c in comp):
            gated.add(r["battery"])
    report[short] = dict(corpus=corpus, comp=comp, heads=heads, real=real,
                         gated=gated, no_canon=not canon)

cat = {"conflict": [], "writeback_gated": [], "writeback_falsified": [],
       "worthless_match": [], "nonverdict": [], "already": [], "orphan": []}
for short, rep in sorted(report.items()):
    recs = by_short.get(short)
    if not recs:
        cat["orphan"].append((short, None, rep))
        continue
    rec = recs[0]
    doc_measured = bool(set(rec["states"]) & MEASURED_STATES)
    e = (short, rec, rep)
    real = rep["real"]
    if len(real & {"FALSIFIED", "REFUTED"}) and len(real & {"MATCH", "VALIDATED"}):
        cat["conflict"].append(e)
    elif doc_measured:
        cat["already"].append(e)
    elif real & {"FALSIFIED", "REFUTED"}:
        cat["writeback_falsified"].append(e)
    elif real & {"MATCH", "VALIDATED"}:
        (cat["writeback_gated"] if rep["gated"] else
         cat["worthless_match"]).append(e)
    else:
        cat["nonverdict"].append(e)


def dump(rows, ind="   "):
    for r in rows:
        print("%s[%s]%s %s | span=%s worst_sems=%s cells=%d | src=%s"
              % (ind, r["battery"], "" if r["bare"] else " " + r["tag"][:60],
                 r["verdict"], r["span"], r["worst_sems"], r["ncells"],
                 r["source"][:70]))
        if r["note"]:
            print(ind + "     note: " + r["note"])


ORDER = ["conflict", "worthless_match", "writeback_falsified",
         "writeback_gated", "nonverdict", "already", "orphan"]
print("defs with battery rows: %d" % len(report))
print("  " + "  ".join("%s=%d" % (k, len(cat[k])) for k in ORDER))
for k in ORDER:
    print("\n" + "#" * 78 + "\n### %s: %d\n" % (k.upper(), len(cat[k])) + "#" * 78)
    for short, rec, rep in cat[k]:
        if rec is None:
            print("\n%s  <NOT IN INVENTORY>" % short)
        else:
            print("\n%s  (%s:%d)  doc=%s states=%s  gate=%s"
                  % (short, os.path.basename(rec["file"]), rec["line"],
                     rec["status"], rec["states"],
                     "PASS(" + ",".join(sorted(rep["gated"])) + ")"
                     if rep["gated"] else "none"))
        print("  corpus rows:")
        dump(rep["corpus"])
        if rep["comp"]:
            print("  competitors: " + ", ".join(
                "%s:%s" % (c["battery"], head(c["verdict"])) for c in rep["comp"]))

emp = [r for r in inv if r["empirical_claim"]]
nonclaim = [r for r in emp if "NOT AN EMPIRICAL CLAIM" in (r.get("doc") or "")]
ncids = set(id(r) for r in nonclaim)
measurable = [r for r in emp if id(r) not in ncids]
noverdict = [r for r in measurable
             if r["short"] not in report
             and not (set(r["states"]) & MEASURED_STATES)]
print("\n" + "#" * 78)
print("### NO BATTERY ROW AND NO DOC VERDICT: %d  (measurable=%d, screened=%d,"
      " declared-nonclaim=%d)"
      % (len(noverdict), len(measurable), len(emp), len(nonclaim)))
print("#" * 78)
byfile = {}
for r in noverdict:
    byfile.setdefault(os.path.basename(r["file"]), []).append(r)
for f, rs in sorted(byfile.items(), key=lambda kv: -len(kv[1])):
    print("\n-- %s (%d)" % (f, len(rs)))
    for r in rs:
        print("   %-44s L%-6d status=%s" % (r["short"], r["line"], r["status"]))
json.dump({k: [(s, (rec or {}).get("file"), (rec or {}).get("line"))
               for s, rec, _ in v] for k, v in cat.items()},
          open("crossref_cat.json", "w"), indent=1)
json.dump([[r["short"], r["file"], r["line"]] for r in noverdict],
          open("crossref_noverdict.json", "w"), indent=1)
