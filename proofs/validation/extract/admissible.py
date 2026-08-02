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

# Names that carry a unit-interval convention throughout this corpus.  Matched
# as a substring, because the corpus writes `h2_true`, `avg_r2_tag`, `fstTarget`.
UNIT_NAMES = re.compile(
    r"(^p$|^q$|^p[₀-₉0-9']?$|^q[₀-₉0-9']?$|freq|prob|prevalence|fst|"
    r"\br2\b|r2|h2|heritab|rg\b|ratio|rate|fraction|share|proportion|"
    r"correlation|sens|spec|auc|power|accuracy|coverage|retention|portab)", re.I)
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


def hypothesis_predicates(d):
    """Mined theorem hypotheses, compiled into Python predicates over the args.

    These are the conditions under which the corpus itself asserts things about
    the definition; sampling outside them produces false accusations, so the
    admissible set is the box intersected with these.
    """
    import translate
    preds, texts, dropped = [], [], []
    argnames = {translate.pyname(n) for a in d["args"] for n in a["names"]}
    for h in d.get("constraints", {}).get("hypotheses", []):
        try:
            stmts, ret = translate.translate_body(h)
        except Exception:                                        # noqa: BLE001
            dropped.append(h)
            continue
        if stmts:
            dropped.append(h)
            continue
        src = "\n".join(stmts + [f"__r = {ret}"])
        used = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", ret)) - {"_rt"}
        if not used or not used <= argnames:
            dropped.append(h)          # constrains something we do not model
            continue
        try:
            code = compile(src, "<hyp>", "exec")
        except SyntaxError:
            dropped.append(h)
            continue
        preds.append(code)
        texts.append(h)
    return preds, texts, dropped


def satisfies(preds, pt):
    import lean_rt as _rt
    for code in preds:
        ns = dict(pt)
        ns["_rt"] = _rt
        try:
            exec(code, {"__builtins__": {}}, ns)
        except Exception:                                        # noqa: BLE001
            return False
        if ns.get("__r") is not True:
            return False
    return True


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
    """Bounds on the definition's value, each with its own provenance.

    A bound proved by a theorem is authoritative; a bound merely implied by the
    docstring or by the quantity's name is a conjecture.  They must never be
    conflated: a violated conjecture is a lead, a violated theorem is a defect.
    """
    c = d.get("constraints", {})
    kind = c.get("declared_kind")
    if "range_lo" in c:
        lo, src_lo = c["range_lo"], "theorem"
    else:
        lo, src_lo = c.get("declared_lo"), ("docstring/name" if kind else None)
    if "range_hi" in c:
        hi, src_hi = c["range_hi"], "theorem"
    else:
        hi, src_hi = c.get("declared_hi"), ("docstring/name" if kind else None)
    return lo, hi, kind, src_lo, src_hi


# ------------------------------------------------------------ structures

FIELD_HYP = re.compile(r"^\s*(-?[\d./]+|\w[\w'\u2080-\u2089]*)\s*(<|\u2264|>|\u2265)"
                       r"\s*(-?[\d./]+|\w[\w'\u2080-\u2089]*)\s*$")


def struct_value(sdecl, rng):
    """An admissible inhabitant of a Lean structure, as a dict of its ℝ/ℕ fields.

    The structure's own Prop fields are its stated invariants (`0 < varY`,
    `varCondE ≤ varYhat`); they are enforced here so that the sampled witness is
    actually admissible and a range violation downstream means something.
    """
    real = [f["name"] for f in sdecl["fields"] if f["type"] in ("\u211d", "\u2115")]
    props = [f["type"] for f in sdecl["fields"] if f["type"] not in ("\u211d", "\u2115")]
    val = {n: rng.uniform(0.05, 1.0) for n in real}
    for _ in range(6):                       # fixed-point repair of the invariants
        changed = False
        for h in props:
            m = FIELD_HYP.match(h)
            if not m:
                continue
            a, op, b = m.groups()
            if a in val and b in val:
                lo, hi = (a, b) if op in ("<", "\u2264") else (b, a)
                if val[lo] > val[hi]:
                    val[lo], val[hi] = val[hi], val[lo]
                    changed = True
            elif b in val and _num(a) is not None and val[b] <= _num(a):
                val[b] = _num(a) + 0.1
                changed = True
            elif a in val and _num(b) is not None and val[a] >= _num(b):
                val[a] = _num(b) - 0.1
                changed = True
        if not changed:
            break
    return val
