"""Admissible input boxes, derived from the corpus rather than assumed.

The box for a definition's arguments comes, in priority order, from
  1. hypotheses of theorems that mention the definition (`0 < Ne`, `p < 1`, ...),
     as mined by `lean_parse.py`;
  2. the declared kind of the quantity (probability, frequency, F_ST, ...)
     inferred from the argument name;
  3. a conservative default.

A box is what makes a check falsifiable: it is the set of inputs over which an
invariant is asserted, so a wrong body can be caught by exhibiting a point in it.
"""
from __future__ import annotations

import random
import re

UNIT_NAMES = re.compile(
    r"^(p|q|p[₀-₉0-9]|q[₀-₉0-9]|freq\w*|prob\w*|prevalence|fst\w*|f_?st\w*|rg|r2|h2|"
    r"\w*Freq|\w*Prob|\w*Fst|\w*R2|\w*H2|\w*Ratio|\w*Rate|\w*Fraction|\w*Share|"
    r"\w*Prevalence|\w*Correlation|\w*Heritability|alpha|beta|rho|tau|m|mu|epsilon)$",
    re.I)
COUNT_NAMES = re.compile(r"^(n|N|m|Ne|N₀|N₁|nEff|nSource|nTarget|\w*Size|\w*Count|"
                         r"\w*Samples?|t|gen\w*|generations?)$")

# (lo, hi, open_lo, open_hi)
DEFAULT_BOX = (0.05, 3.0)


def _num(tok):
    try:
        return float(eval(tok, {"__builtins__": {}}))       # numeric literal only
    except Exception:
        return None


HYP_RE = re.compile(r"^\s*(-?[\d./]+|\w[\w'₀-₉]*)\s*(<|≤|>|≥)\s*(-?[\d./]+|\w[\w'₀-₉]*)\s*$")


def box_for(d):
    """Return {argname: (lo, hi)} for the explicit real arguments of a def."""
    args = [n for a in d["args"] if not a["implicit"] and a["type"] in ("ℝ", "ℕ")
            for n in a["names"]]
    nat = {n for a in d["args"] if a["type"] == "ℕ" for n in a["names"]}
    box = {}
    for n in args:
        if n in nat:
            box[n] = (1.0, 20.0)
        elif UNIT_NAMES.match(n):
            box[n] = (0.02, 0.98)
        elif COUNT_NAMES.match(n):
            box[n] = (1.0, 1000.0)
        else:
            box[n] = DEFAULT_BOX

    for h in d.get("constraints", {}).get("hypotheses", []):
        m = HYP_RE.match(h)
        if not m:
            continue
        a, op, b = m.groups()
        va, vb = _num(a), _num(b)
        if vb is None and va is not None and b in box:          # c < x
            lo, hi = box[b]
            box[b] = (max(lo, va + (1e-3 if op in "<" else 0.0)), hi)
        elif va is None and vb is not None and a in box:        # x < c
            lo, hi = box[a]
            box[a] = (lo, min(hi, vb - (1e-3 if op in "<" else 0.0)))
    # repair degenerate boxes
    for n, (lo, hi) in box.items():
        if not (hi > lo):
            box[n] = (lo, lo + 1.0)
    return box


def sample(box, rng: random.Random):
    return {n: rng.uniform(lo, hi) for n, (lo, hi) in box.items()}


def corners(box, limit=32):
    """Deterministic corner + midpoint points of the box."""
    names = list(box)
    pts = [{n: (box[n][0] + box[n][1]) / 2 for n in names}]
    for k in range(min(limit, 1 << max(len(names), 1))):
        pt = {}
        for j, n in enumerate(names):
            lo, hi = box[n]
            eps = (hi - lo) * 1e-6
            pt[n] = lo + eps if (k >> j) & 1 else hi - eps
        pts.append(pt)
    return pts


def declared_range(d):
    """The range the definition's own docstring/name and its theorems assert."""
    c = d.get("constraints", {})
    lo = c.get("range_lo", c.get("declared_lo"))
    hi = c.get("range_hi", c.get("declared_hi"))
    kind = c.get("declared_kind")
    src = "theorem" if ("range_lo" in c or "range_hi" in c) else (
        "docstring/name" if kind else None)
    return lo, hi, kind, src
