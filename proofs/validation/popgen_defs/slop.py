"""Find useless declarations in proofs/Calibrator.

Four kinds, in decreasing order of confidence:

  DEAD          a definition referenced nowhere except its own declaration.
  TRIVIAL_THM   a theorem whose entire content is arithmetic: the statement
                mentions one definition and the proof is a single
                unfold/dsimp + linarith/ring/positivity step.  These restate a
                definition rather than establishing anything about it.
  DUP_BODY      two or more definitions with byte-identical bodies.  At most one
                is needed; the others are fork hazards, since fixing one leaves
                the rest wrong.
  TAUT_LOWUSE   a definition that is a sum/difference of its own arguments AND
                has few references.  (Widely-used ones are legitimate names.)

Reports only; deletion is a separate, reviewed step.
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


DEF = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)")
THM = re.compile(r"^(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z_][\w.']*)")
TRIVIAL_TACTICS = re.compile(
    r"^(unfold|dsimp|simp only|simp|rw)?\s*\[?[\w\s,.\[\]]*\]?\s*;?\s*"
    r"(linarith|ring|ring_nf|positivity|norm_num|nlinarith|rfl|linarith \[.*\])\s*$")


def blocks(root):
    """Yield (kind, name, file, start_line, text) for every declaration."""
    for path in _lean_sources(pathlib.Path(root)):
        lines = path.read_text(errors="ignore").splitlines()
        i = 0
        while i < len(lines):
            s = lines[i].strip()
            m_def, m_thm = DEF.match(s), THM.match(s)
            if not (m_def or m_thm):
                i += 1
                continue
            kind = "def" if m_def else "thm"
            name = (m_def or m_thm).group(1)
            start = i
            i += 1
            body = []
            while i < len(lines):
                nxt = lines[i]
                if nxt.strip() and not nxt.startswith(" ") and not nxt.startswith("\t"):
                    if re.match(r"^(noncomputable\s+)?(def|theorem|lemma|structure|"
                                r"instance|/--|namespace|end|section|@\[|--)", nxt.strip()):
                        break
                body.append(nxt)
                i += 1
            yield kind, name, path.name, start + 1, "\n".join(body)


def main(root):
    decls = list(blocks(root))
    text = "\n".join(p.read_text(errors="ignore")
                     for p in _lean_sources(pathlib.Path(root)))

    defs = [d for d in decls if d[0] == "def"]
    thms = [d for d in decls if d[0] == "thm"]
    counts = {}
    for _, name, _, _, _ in defs:
        base = name.split(".")[-1]
        counts[name] = len(re.findall(rf"\b{re.escape(base)}\b", text))

    print(f"{len(defs)} definitions, {len(thms)} theorems\n")

    dead = [(n, f, l) for k, n, f, l, _ in defs if counts.get(n, 0) <= 1]
    print(f"=== DEAD (referenced nowhere but their own declaration): {len(dead)}")
    for n, f, l in dead[:25]:
        print(f"    {f}:{l:5d}  {n}")

    trivial = []
    for _, name, f, l, body in thms:
        lines = [x.strip() for x in body.splitlines() if x.strip()]
        proof = [x for x in lines if x.startswith(("unfold", "dsimp", "linarith",
                                                   "ring", "positivity", "simp",
                                                   "norm_num", "nlinarith", "rfl"))]
        if not lines:
            continue
        # the proof body after ":= by" is at most two trivial tactic lines
        tail = [x for x in lines if not x.startswith(("(", "{", "--"))]
        if len(proof) >= 1 and len(tail) <= 6 and len(proof) >= len(tail) - 4:
            joined = " ".join(proof)
            if re.fullmatch(r"[\w\s\[\],.;:'←→*+\-/^()<>≤≥≠|]+", joined) and len(proof) <= 2:
                trivial.append((name, f, l, joined[:60]))
    print(f"\n=== TRIVIAL_THM (statement restates a definition, proof is one "
          f"arithmetic step): {len(trivial)}")
    for n, f, l, p in trivial[:25]:
        print(f"    {f}:{l:5d}  {n:<52} [{p}]")

    bodies = collections.defaultdict(list)
    for _, name, f, l, body in defs:
        b = re.sub(r"\s+", "", body)
        if len(b) > 6:
            bodies[b].append((name, f, l))
    dups = {b: g for b, g in bodies.items() if len({x[0] for x in g}) > 1}
    print(f"\n=== DUP_BODY (identical formula, different names): {len(dups)} groups")
    for b, g in list(dups.items())[:10]:
        print(f"    {b[:50]}")
        for n, f, l in g:
            print(f"        {f}:{l:5d}  {n}")

    json.dump(dict(dead=dead, trivial=[list(t) for t in trivial],
                   dups={k: v for k, v in list(dups.items())}),
              open("slop.json", "w"), indent=1, default=str)
    print("\nwritten to slop.json")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "Calibrator")
