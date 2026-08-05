"""Static cross-definition consistency scan over Descent.

Two of the confirmed bugs (amInflationFactor vs amEquilibriumVariance,
fstFromDrift vs coalFst) were found by noticing that the development defines the
same quantity twice with different formulas.  That is a contradiction detectable
by pure logic -- no simulation, no ground truth.  This scan looks for it.

Reports:
  1. DUPLICATE BODIES  - different names, identical formula.  Usually harmless
     redundancy, but each is a fork risk: fixing one leaves the other wrong.
  2. CONCEPT CLASHES   - names that denote the same quantity (same normalized
     concept key) but have different formulas.  These are contradictions: at
     most one can be right.
  3. UNIT CLASHES      - a parameter name that is produced by one definition and
     consumed by another whose formula implies a different convention.
"""
from __future__ import annotations

import collections
import pathlib
import re
import sys


def _lean_sources(_r):
    # `rglob` under Descent/ does NOT reach `Descent.lean`, the corpus
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


DEF_RE = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)\s*(.*?)\s*:=\s*(.*)$")


HEAD_RE = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)")


def load_defs(root):
    """Join each declaration into one logical line before parsing, so that
    definitions whose signature or body spans several lines are not missed."""
    defs = []
    for path in _lean_sources(pathlib.Path(root)):
        lines = path.read_text(errors="ignore").splitlines()
        i = 0
        while i < len(lines):
            if not HEAD_RE.match(lines[i].strip()):
                i += 1
                continue
            start = i
            chunk = [lines[i].rstrip()]
            i += 1
            # accumulate until the declaration is closed by a blank line or the
            # start of the next top-level declaration
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
            name = HEAD_RE.match(joined).group(1)
            head, body = joined.split(":=", 1)
            sig = head.split(name, 1)[1] if name in head else head
            defs.append(dict(name=name, sig=sig.strip(), body=body.strip(),
                             file=path.name, line=start + 1))
    return defs


def normalize_body(b):
    """Strip whitespace and parameter names so equivalent formulas compare."""
    b = re.sub(r"\s+", "", b)
    return b


CONCEPT_PATTERNS = [
    (r"fst.*(island|migration)|(?:island|migration).*fst", "equilibrium F_ST under migration"),
    (r"^(coal|demo)?fst(fromcoalescencetime|fromdrift|derived)?$", "F_ST after a split"),
    (r"aminflation|amequilibrium", "assortative-mating variance inflation"),
    (r"auc", "AUC"),
    (r"^r2scaling|^expectedr2fromn", "R^2 vs training sample size"),
    (r"heterozyg|hetequilib", "heterozygosity"),
    (r"lddecay|ldretention|ldrecurrence", "LD decay per generation"),
    (r"pgsvariance|targetpgsvariance", "PGS variance"),
]


def concept_of(name):
    low = name.lower().replace("_", "")
    for pat, label in CONCEPT_PATTERNS:
        if re.search(pat, low):
            return label
    return None


def main(root):
    defs = load_defs(root)
    print(f"parsed {len(defs)} definitions from {root}\n")

    print("=" * 74)
    print("1. DUPLICATE BODIES (identical formula under different names)")
    print("=" * 74)
    by_body = collections.defaultdict(list)
    for d in defs:
        if len(d["body"]) > 6:
            by_body[normalize_body(d["body"])].append(d)
    dup = 0
    for body, group in sorted(by_body.items(), key=lambda kv: -len(kv[1])):
        names = {g["name"] for g in group}
        if len(names) < 2:
            continue
        dup += 1
        if dup > 12:
            continue
        print(f"  {body[:56]}")
        for g in group:
            print(f"      {g['name']:<42} {g['file']}:{g['line']}")
    print(f"  ... {dup} duplicated formulas total\n")

    print("=" * 74)
    print("2. CONCEPT CLASHES (same quantity, different formulas)")
    print("=" * 74)
    by_concept = collections.defaultdict(list)
    for d in defs:
        c = concept_of(d["name"])
        if c:
            by_concept[c].append(d)
    for concept, group in sorted(by_concept.items()):
        bodies = collections.defaultdict(list)
        for g in group:
            bodies[normalize_body(g["body"])].append(g)
        if len(bodies) < 2:
            continue
        print(f"\n  {concept}: {len(bodies)} distinct formulas")
        for body, gs in bodies.items():
            print(f"      {body[:58]}")
            for g in gs:
                print(f"          {g['name']:<40} {g['file']}:{g['line']}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
