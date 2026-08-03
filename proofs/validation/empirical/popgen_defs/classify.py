"""Classify every Calibrator definition by whether simulation CAN test it.

"100% simulation coverage" over all 859 definitions is not the right target,
because most of them cannot be falsified by simulation even in principle.  This
splits them into classes so the achievable target is explicit:

  TESTABLE       a closed-form numeric claim about a quantity with an
                 independent ground truth.  This is the class that should reach
                 100%.
  COMPOSITIONAL  defined purely by applying other definitions.  Correct iff its
                 parts are; covered transitively, no separate oracle needed.
  TAUTOLOGICAL   a sum/difference of its own named arguments (e.g.
                 `observedMeanShift = prevalenceShift + environmentalShift +
                 geneticShift`).  True by construction; nothing to falsify.
  STRUCTURAL     projections, accessors, record builders, Prop-valued
                 predicates, and indexed families -- not numeric claims.

Only TESTABLE has a meaningful denominator.
"""
from __future__ import annotations

import collections
import json
import pathlib
import re
import sys


def _lean_sources(_r):
    # `rglob` under Calibrator/ does NOT reach `proofs/Calibrator.lean`, the corpus
    # ROOT, which sits one level above it. A scan blind to the root reported
    # `decaySlope` unreferenced; it was deleted, and `LDDecayMechanism` was then
    # deleted for having lost its only consumer. Both consumers were in the root.
    # `lean_parse.build` carries this `extra` idiom -- keep every scanner in step.
    _r = pathlib.Path(_r)
    _fs = sorted(_r.rglob("*.lean"))
    _x = _r.parent / (_r.name + ".lean")
    if _x.exists():
        _fs.append(_x)
    return _fs


HEAD = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)")


def load(root):
    defs = []
    for path in _lean_sources(pathlib.Path(root)):
        lines = path.read_text(errors="ignore").splitlines()
        i = 0
        while i < len(lines):
            if not HEAD.match(lines[i].strip()):
                i += 1
                continue
            start, chunk = i, [lines[i].rstrip()]
            i += 1
            while i < len(lines):
                s = lines[i]
                if not s.strip():
                    break
                if re.match(r"^(noncomputable\s+)?(def|theorem|lemma|structure|"
                            r"instance|/--|namespace|end|section|@\[)", s.strip()):
                    break
                chunk.append(s.rstrip())
                i += 1
            joined = " ".join(c.strip() for c in chunk)
            if ":=" not in joined:
                continue
            name = HEAD.match(joined).group(1)
            head, body = joined.split(":=", 1)
            defs.append(dict(name=name, sig=head, body=body.strip(),
                             file=path.name, line=start + 1))
    return defs


def classify(d, all_names):
    body, sig = d["body"], d["sig"]

    # Prop-valued or record-valued: not a numeric claim
    if re.search(r":\s*Prop\b", sig) or "where" in body[:80]:
        return "STRUCTURAL"
    if re.match(r"^\{.*with", body) or body.startswith("⟨"):
        return "STRUCTURAL"
    # a bare projection: `m.field`
    if re.fullmatch(r"[a-zA-Z_][\w.']*", body):
        return "STRUCTURAL"
    # indexed family / matrix / submodule valued
    if re.search(r"Matrix|Submodule|Finset|Measure|Fin \w+ →", sig):
        return "STRUCTURAL"

    # arguments named in the signature
    args = set(re.findall(r"[^\W\d][\w']*", sig.split(":")[0])) if ":" in sig else set()
    toks = set(re.findall(r"[^\W\d][\w']*", body))

    # tautological: body is only additions/subtractions of its own arguments
    if toks and toks.issubset(args) and re.fullmatch(r"[\w\s.'+\-()]+", body):
        if "+" in body or "-" in body:
            return "TAUTOLOGICAL"

    # compositional: body invokes other definitions and nothing else numeric
    called = {t for t in toks if t in all_names and t != d["name"].split(".")[-1]}
    if called and not re.search(r"\d", body.replace("2", "").replace("1", "")):
        if not re.search(r"Real\.(exp|log|sqrt)", body):
            return "COMPOSITIONAL"

    return "TESTABLE"


def tested_names(script_dir):
    names = set()
    for p in pathlib.Path(script_dir).glob("*.py"):
        txt = p.read_text(errors="ignore")
        for m in re.finditer(r"lean_([A-Za-z_][\w']*)", txt):
            names.add(m.group(1))
        for m in re.finditer(r"[\"']([a-z][A-Za-z0-9_']{4,})[\"']", txt):
            names.add(m.group(1))
    return names


def main(root, scripts):
    defs = load(root)
    all_names = {d["name"].split(".")[-1] for d in defs}
    tested = tested_names(scripts)

    counts = collections.Counter()
    testable_untested = []
    for d in defs:
        c = classify(d, all_names)
        d["class"] = c
        counts[c] += 1
        base = d["name"].split(".")[-1]
        d["tested"] = base in tested or d["name"] in tested
        if c == "TESTABLE" and not d["tested"]:
            testable_untested.append(d)

    total = len(defs)
    testable = counts["TESTABLE"]
    tested_testable = testable - len(testable_untested)
    print(f"total definitions: {total}")
    for c, n in counts.most_common():
        print(f"  {c:<14} {n:5d}  ({100*n/total:4.1f}%)")
    print(f"\nTESTABLE covered: {tested_testable}/{testable} "
          f"({100*tested_testable/max(testable,1):.1f}%)")
    print(f"remaining to reach 100% of TESTABLE: {len(testable_untested)}\n")

    byfile = collections.Counter(d["file"] for d in testable_untested)
    print("untested TESTABLE definitions, by file:")
    for f, n in byfile.most_common(14):
        print(f"  {f:<44} {n:4d}")

    with open("classify.json", "w") as fh:
        json.dump([{k: d[k] for k in ("name", "file", "line", "class", "tested")}
                   for d in defs], fh, indent=1)
    print("\nfull classification written to classify.json")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "Calibrator",
         sys.argv[2] if len(sys.argv) > 2 else "validation/popgen_defs")
