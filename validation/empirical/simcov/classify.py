"""Classify the untested surface by the ORACLE each definition needs.

Getting coverage to 100% one bespoke simulation at a time does not finish. The
only way through 251 definitions is to notice that they are not 251 independent
problems: most are compositions of a handful of primitives, and one simulation
that validates a primitive validates every composition of it evaluated on the
same run.

So the classes here are chosen by oracle, not by topic:

  COMPOSITION  the body is built only from definitions already measured. Testing
               the composed formula end-to-end against the same simulated ground
               truth is a real measurement, not inheritance -- the composition
               can be wrong where every part is right.
  SCALAR       a closed-form real expression in scalar arguments. Needs a
               ground truth, but a single popgen or Monte Carlo design usually
               covers a whole family.
  LINALG       matrices, vectors, Finset sums. Testable against random matrices
               and simulated genotypes; one design covers many.
  STRUCTURE    witnesses, literal constants, structure fields, index helpers.
               These are not empirical claims at all. An UNTESTED marker on
               `![1, 1]` is noise, and the honest fix is to stop screening them
               as claims rather than to invent a measurement for them.
  BESPOKE      everything else: needs its own design.
"""
import json
import re
import sys

INV = sys.argv[1] if len(sys.argv) > 1 else "inventory.json"

MEASURED = {"VALIDATED", "FALSIFIED", "MEASURED", "TESTED"}

recs = json.load(open(INV))
by_name = {r["short"]: r for r in recs}
measured_names = {r["short"] for r in recs if r["status"] in MEASURED}

# also treat as measured anything whose docstring cites the simcov harness
for r in recs:
    if "simcov" in (r.get("doc") or ""):
        measured_names.add(r["short"])

untested = [r for r in recs if r["empirical_claim"] and r["status"] == "UNTESTED"]

STRUCTURE = re.compile(
    r"^\s*!?\[|^\s*!!\[|^\s*\{|:=\s*$|^\s*fun\s+\w+\s*↦\s*if|"
    r"^\s*\d+\s*$|^\s*rfl\s*$|Fin\.|Matrix\.of|^\s*⟨")
LINALG = re.compile(r"mulVec|dotProduct|∑|Matrix|Finset|⁻¹\.|Fin \d|‖|frobenius|"
                    r"transpose|diagonal|eigen", re.I)
SCALAR = re.compile(r"[-+*/^]|Real\.(exp|log|sqrt)|\d")

IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")
KEYWORDS = {"let", "in", "if", "then", "else", "fun", "Real", "exp", "log",
            "sqrt", "pi", "Finset", "univ", "sum", "Matrix", "Fin", "true",
            "false", "abs", "max", "min", "this", "m", "p", "x", "t", "i", "j"}


def refs(body):
    return {w for w in IDENT.findall(body)
            if w in by_name and w not in KEYWORDS}


buckets = {"COMPOSITION": [], "SCALAR": [], "LINALG": [], "STRUCTURE": [],
           "BESPOKE": []}

for r in untested:
    body = (r["body"] or "").strip()
    dependencies = refs(body)
    if not body or STRUCTURE.match(body):
        buckets["STRUCTURE"].append(r)
    elif dependencies and dependencies <= measured_names:
        buckets["COMPOSITION"].append(r)
    elif LINALG.search(body):
        buckets["LINALG"].append(r)
    elif SCALAR.search(body):
        buckets["SCALAR"].append(r)
    else:
        buckets["BESPOKE"].append(r)

print("untested empirical-claim definitions: %d\n" % len(untested))
for k in ("STRUCTURE", "COMPOSITION", "SCALAR", "LINALG", "BESPOKE"):
    print("%-12s %4d" % (k, len(buckets[k])))

print("\n--- STRUCTURE (not empirical claims; screen should not count them) ---")
for r in buckets["STRUCTURE"][:40]:
    print("  %-44s %s" % (r["short"], r["file"].split("/")[-1]))

print("\n--- COMPOSITION (validated primitives, composition untested) ---")
for r in buckets["COMPOSITION"][:40]:
    print("  %-44s %s" % (r["short"], r["file"].split("/")[-1]))

import collections
print("\n--- SCALAR by file ---")
for f, n in collections.Counter(
        r["file"].split("/")[-1] for r in buckets["SCALAR"]).most_common(15):
    print("  %4d  %s" % (n, f))
print("\n--- LINALG by file ---")
for f, n in collections.Counter(
        r["file"].split("/")[-1] for r in buckets["LINALG"]).most_common(15):
    print("  %4d  %s" % (n, f))

json.dump({k: [r["short"] for r in v] for k, v in buckets.items()},
          open("classified.json", "w"), indent=1)
