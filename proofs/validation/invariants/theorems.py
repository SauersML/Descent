"""Parse theorem statements into checkable properties.

The corpus contains roughly 1500 theorems and they are the largest untapped
source of discriminating checks in it.  Each one is a property that the
definitions it mentions must satisfy -- `simpleFst p₁ p₂ = simpleFst p₂ p₁`,
`coalFst t₁ Ne < coalFst t₂ Ne` under `t₁ < t₂`, `0 ≤ neiFst H_T H_S ∧
neiFst H_T H_S ≤ 1` under `H_S ≤ H_T`.  Evaluating them numerically needs no
external reference and no invented claim, because the claim is the author's
and Lean has already proved it.

WHAT THIS DOES AND DOES NOT ESTABLISH.  Lean has no `sorry`s, so a theorem
cannot be false; checking it numerically cannot discover a corpus defect.  What
it can do is DISCRIMINATE BODIES: perturb the definition and the theorem
breaks.  That makes it coverage in the falsifiability sense -- a wrong body
would have been caught -- but it is INTERNAL CONSISTENCY, not validation
against the world.  Two definitions can satisfy every identity between them and
both be wrong about biology.  The reporting keeps the two kinds of evidence in
separate columns for exactly that reason.

A numeric failure here therefore indicts this checker, never the corpus: a
mis-transcribed body, a hypothesis outside the arithmetic fragment, or a
sampled point the hypotheses were supposed to exclude.
"""
from __future__ import annotations

import pathlib
import re


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


CAL = pathlib.Path(__file__).resolve().parents[2] / "Calibrator"

HEAD = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([\w.'₀-₉]+)")
SCALAR = {"ℝ", "ℕ"}


def _split_binders(text):
    """Split a theorem head into binder groups and the conclusion.

    Walks the text tracking bracket depth so a `:` inside a binder is not
    mistaken for the one that introduces the conclusion.
    """
    groups, depth, start = [], 0, None
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in "({[":
            if depth == 0:
                start = i
            depth += 1
        elif ch in ")}]":
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(text[start:i + 1])
                start = None
        elif ch == ":" and depth == 0:
            return groups, text[i + 1:]
        i += 1
    return groups, ""


def parse_statement(block):
    """Return a dict describing one theorem, or None if it is not usable."""
    m = HEAD.match(block)
    if not m:
        return None
    name = m.group(1)
    head = block.split(":= by")[0]
    head = head.split(":=\n")[0]
    head = head[m.end():]
    groups, concl = _split_binders(head)
    if not concl.strip():
        return None
    variables, hypotheses = [], []
    for g in groups:
        inner = g[1:-1]
        implicit = g[0] in "{["
        if ":" not in inner:
            continue
        lhs, rhs = inner.split(":", 1)
        rhs = rhs.strip()
        if rhs in SCALAR:
            for nm in lhs.split():
                variables.append((nm, rhs, implicit))
        else:
            hypotheses.append(rhs)
    return dict(name=name, variables=variables, hypotheses=hypotheses,
                conclusion=" ".join(concl.split()))


def all_theorems():
    out = []
    for p in _lean_sources(CAL):
        text = p.read_text(errors="ignore")
        blocks = re.split(r"\n(?=(?:@\[[^\]]*\]\n)?(?:theorem|lemma)\s)", text)
        for b in blocks:
            st = parse_statement(b)
            if st:
                st["module"] = p.stem
                st["path"] = str(p.relative_to(CAL.parent.parent))
                st["line"] = text[:text.index(b)].count("\n") + 1 if b in text else 0
                out.append(st)
    return out


DEFCALL = re.compile(r"\b([a-z][\w'₀-₉]*)\b")


def definitions_mentioned(st, known):
    """Which known definitions does this theorem's conclusion mention?

    The CONCLUSION only.  A definition appearing solely in a hypothesis is not
    constrained by the theorem, so perturbing it need not break anything and
    counting it as covered would be false.
    """
    names = set(DEFCALL.findall(st["conclusion"]))
    bound = {v for v, _, _ in st["variables"]}
    return sorted(n for n in names if n in known and n not in bound)
