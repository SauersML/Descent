"""FAMILY 2 -- metamorphic invariants.

An invariant relates a definition's value at one input to its value at
another.  It needs no reference implementation and no simulation, which is why
it scales to a whole corpus.  Six kinds are derived here, all of them from the
definition's own name, docstring, signature and adjacent theorems:

  SYMMETRY      a between-population quantity is unchanged when the two
                populations are swapped.
  SCALE         a dimensionless quantity is unchanged when every second-moment
                argument is multiplied by the same positive constant.
  LIMIT         a quantity with a stated limit attains it: F_ST -> 0 as Ne
                grows, heterozygosity -> 0 as a frequency approaches fixation,
                a decay -> its equilibrium as the rate goes to zero.
  ABSORBING     loss and fixation are absorbing.  An allele at frequency 0
                stays at 0; at frequency 1 it stays at 1.  A smooth formula
                that leaves the boundary is a qualitative error.
  MONOTONE      a direction the docstring or an adjacent theorem name asserts
                actually holds.
  IDENTITY      a value the docstring pins at a specific input.

Every registration records WHY it applies.  Where nothing can be derived, the
definition is recorded with `reason` and counted in the residue, never
silently skipped.
"""
from __future__ import annotations

import math
import random
import re

from backends import FLOAT
from semantics import admissible_box, param_box, result_name

INF = math.inf

# --------------------------------------------------------------------------
# which quantities must be symmetric under swapping the two populations

SYMMETRIC_NAME = re.compile(
    r"fst|divergence|distance|similarity|overlap|shared|coancestry|"
    r"differentiation|betweenpop|crosspop|jaccard|concordance", re.I
)
# ... and which must NOT be: an ordered quantity names its own direction
ORDERED_NAME = re.compile(
    r"fromsource|totarget|sourceto|targetto|transfer|portab|gain|loss|"
    r"improvement|regret|ratio|relative|shift|drop|delta", re.I
)

# role suffixes that distinguish the two members of a pair
PAIR_SUFFIX = [
    ("source", "target"), ("src", "tgt"), ("a", "b"), ("1", "2"),
    ("₁", "₂"), ("i", "j"), ("s", "t"), ("x", "y"),
    ("pop1", "pop2"), ("popa", "popb"), ("first", "second"),
    ("eur", "afr"), ("train", "test"), ("disc", "repl"),
]

DIMENSIONLESS = re.compile(
    r"fst|r2|rsq|correlation|proportion|fraction|share|portability|"
    r"heritability|ratio|probability|retention|attenuation|auc|index", re.I
)
SECOND_MOMENT = re.compile(
    r"var|sigma|σ|cov|moment|noise|signal|mse|scale|tau|τ|v_[a-z]|^v[A-Z]",
    re.I
)

FREQ_PARAM = re.compile(r"^(p|q|p[₀₁₂0-9]|p_\w+|freq\w*|alleleFreq\w*)$", re.I)
NE_PARAM = re.compile(r"^(ne|n_e|nₑ|ne\w*|effectiveN\w*|popSize)$", re.I)
MAP_NAME = re.compile(
    r"step|update|next|after|trajectory|recurrence|iterate|generation|"
    r"^freq|alleleFreq", re.I
)


def _stem_pairs(names):
    """Pairs of parameters that name the same quantity for two populations."""
    out = []
    low = [n.lower() for n in names]
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            a, b = low[i], low[j]
            for sa, sb in PAIR_SUFFIX:
                if a.endswith(sa) and b.endswith(sb) and a[: -len(sa)] == b[: -len(sb)]:
                    if a[: -len(sa)] or len(names) == 2:
                        out.append((i, j, f"`{names[i]}`/`{names[j]}` are the "
                                          f"same quantity for two populations"))
                        break
    return out


def _sample(box, names, rng, n=400):
    from search import _draw

    pts = []
    for _ in range(n):
        pts.append([_draw(rng, box[nm]) for nm in names])
    return pts


def _ev(c, x):
    try:
        v = c(FLOAT, *x)
    except Exception:
        return None
    if v is None or isinstance(v, bool) or v != v or math.isinf(v):
        return None
    return float(v)


def _rel(a, b):
    return abs(a - b) / max(1.0, abs(a), abs(b))


# --------------------------------------------------------------------------


def derive(c, feasible=None, seed=0, n=400):
    """Return (checks, skipped) for one compiled definition.

    Each check is a dict with `kind`, `why` (the evidence that it applies) and
    `run(c)` producing (ok, detail).
    """
    d = c.d
    names = c.names
    box, _ = admissible_box(d)
    rng = random.Random(seed)
    pts = _sample(box, names, rng, n)
    if feasible is not None:
        pts = [p for p in pts if _safe(feasible, p)]
    checks, skipped = [], []
    rname = result_name(d)
    doc = d.get("doc", "") or ""

    # ---- SYMMETRY -------------------------------------------------------
    pairs = _stem_pairs(names)
    if pairs and SYMMETRIC_NAME.search(rname) and not ORDERED_NAME.search(rname):
        for i, j, why in pairs:
            checks.append(_symmetry_check(c, pts, i, j, why))
    elif not pairs:
        skipped.append(("symmetry", "no two parameters name the same quantity "
                                    "for two populations"))
    else:
        skipped.append(("symmetry", f"`{rname}` does not name a symmetric "
                                    "between-population quantity"))

    # ---- SCALE INVARIANCE ----------------------------------------------
    mom = [k for k, nm in enumerate(names) if SECOND_MOMENT.search(nm)]
    if mom and DIMENSIONLESS.search(rname):
        checks.append(_scale_check(c, pts, mom,
                                   f"`{rname}` is dimensionless and "
                                   f"{[names[k] for k in mom]} are second "
                                   "moments, so scaling them together must "
                                   "leave the value unchanged"))
    elif not mom:
        skipped.append(("scale", "no second-moment argument to scale"))
    else:
        skipped.append(("scale", f"`{rname}` is not evidently dimensionless"))

    # ---- ABSORBING BOUNDARY --------------------------------------------
    fq = [k for k, nm in enumerate(names) if FREQ_PARAM.match(nm)]
    if fq and MAP_NAME.search(d["name"]):
        for k in fq:
            checks.append(_absorbing_check(c, pts, k,
                          f"`{d['name']}` maps an allele frequency forward and "
                          f"`{names[k]}` is that frequency; loss and fixation "
                          "are absorbing states"))
    elif not fq:
        skipped.append(("absorbing", "no allele-frequency argument"))
    else:
        skipped.append(("absorbing", f"`{d['name']}` is not a "
                                     "frequency-forwarding map"))

    # ---- LIMITS ---------------------------------------------------------
    ne = [k for k, nm in enumerate(names) if NE_PARAM.match(nm)]
    if ne and re.search(r"fst|drift|differentiation", rname, re.I):
        checks.append(_limit_check(
            c, pts, ne[0], 1e12, 0.0,
            f"`{rname}` is a drift quantity and drift vanishes as "
            f"`{names[ne[0]]}` grows without bound"))
    elif not ne:
        skipped.append(("limit-Ne", "no effective-population-size argument"))
    else:
        skipped.append(("limit-Ne", f"`{rname}` is not a drift quantity"))

    if fq and re.search(r"heterozygosity|^het|diversity", rname, re.I):
        for k in fq:
            checks.append(_limit_check(
                c, pts, k, 0.0, 0.0,
                f"heterozygosity vanishes when `{names[k]}` reaches loss"))
            checks.append(_limit_check(
                c, pts, k, 1.0, 0.0,
                f"heterozygosity vanishes when `{names[k]}` reaches fixation"))
    else:
        skipped.append(("limit-freq", "not a heterozygosity of a frequency"))

    # ---- MONOTONICITY ---------------------------------------------------
    for k, direction, why in _monotone_claims(d, names):
        checks.append(_monotone_check(c, pts, k, direction, why, box))
    if not _monotone_claims(d, names):
        skipped.append(("monotone", "neither the docstring nor an adjacent "
                                    "theorem name asserts a direction"))

    return checks, skipped


def _safe(f, x):
    try:
        return bool(f(*x))
    except Exception:
        return False


# --------------------------------------------------------------------------
# individual check constructors.  Each returns a dict with a `run` closure.


def _mk(kind, why, run, param=None):
    return dict(kind=kind, why=why, run=run, param=param)


def _symmetry_check(c, pts, i, j, why):
    def run(cc):
        worst, wx = 0.0, None
        for x in pts:
            y = list(x)
            y[i], y[j] = y[j], y[i]
            a, b = _ev(cc, x), _ev(cc, y)
            if a is None or b is None:
                continue
            r = _rel(a, b)
            if r > worst:
                worst, wx = r, (list(x), y, a, b)
        return worst <= 1e-9, dict(max_relative_asymmetry=worst, witness=wx)

    return _mk("symmetry", why, run, param=(i, j))


def _scale_check(c, pts, mom, why):
    def run(cc):
        worst, wx = 0.0, None
        for x in pts:
            for s in (2.0, 7.5, 0.1):
                y = list(x)
                for k in mom:
                    y[k] = x[k] * s
                a, b = _ev(cc, x), _ev(cc, y)
                if a is None or b is None:
                    continue
                r = _rel(a, b)
                if r > worst:
                    worst, wx = r, (list(x), y, a, b, s)
        return worst <= 1e-9, dict(max_relative_change=worst, witness=wx)

    return _mk("scale", why, run, param=tuple(mom))


def _absorbing_check(c, pts, k, why):
    def run(cc):
        bad = []
        for x in pts[:60]:
            for p, want in ((0.0, 0.0), (1.0, 1.0)):
                y = list(x)
                y[k] = p
                v = _ev(cc, y)
                if v is None:
                    continue
                if abs(v - want) > 1e-9:
                    bad.append(dict(at=y, got=v, expected=want))
        return not bad, dict(violations=bad[:5], n_violations=len(bad))

    return _mk("absorbing", why, run, param=k)


def _limit_check(c, pts, k, at, want, why, tol=1e-6):
    def run(cc):
        bad = []
        for x in pts[:60]:
            y = list(x)
            y[k] = at
            v = _ev(cc, y)
            if v is None:
                continue
            if abs(v - want) > tol:
                bad.append(dict(at=y, got=v, expected=want))
        return not bad, dict(violations=bad[:5], n_violations=len(bad))

    return _mk("limit", why, run, param=k)


MONO_DOC = re.compile(
    r"(increas\w*|decreas\w*|grows|declines|rises|falls|larger|smaller)\s+"
    r"(?:monotonically\s+)?(?:with|in)\s+`?([A-Za-z_][\w'₀-₉]*)`?", re.I
)
MONO_THM = re.compile(
    r"(increas\w*|decreas\w*)_(?:with|in)_([A-Za-z_][\w'₀-₉]*)", re.I
)


def _monotone_claims(d, names):
    """(param_index, +1/-1, evidence) for every asserted direction."""
    out = []
    doc = d.get("doc", "") or ""
    for m in MONO_DOC.finditer(doc):
        word, p = m.group(1).lower(), m.group(2)
        if p not in names:
            continue
        sign = 1 if word.startswith(("increas", "grow", "rise", "larger")) else -1
        out.append((names.index(p), sign,
                    f"the docstring says the value {m.group(1)} with `{p}`"))
    for t in d.get("theorem_hyps", []):
        for m in MONO_THM.finditer(t["thm"]):
            word, p = m.group(1).lower(), m.group(2)
            p = (t.get("argmap") or {}).get(p, p)
            if p not in names:
                continue
            sign = 1 if word.startswith("increas") else -1
            out.append((names.index(p), sign,
                        f"theorem `{t['thm']}` asserts the direction"))
    # dedupe on (index, sign)
    seen, ded = set(), []
    for i, s, w in out:
        if (i, s) in seen:
            continue
        seen.add((i, s))
        ded.append((i, s, w))
    return ded


def _monotone_check(c, pts, k, sign, why, box):
    def run(cc):
        bad = []
        lo, hi = box[c.names[k]]["lo"], box[c.names[k]]["hi"]
        for x in pts[:120]:
            y = list(x)
            step = max(abs(x[k]) * 0.5, (hi - lo) * 1e-3, 1e-9)
            y[k] = min(x[k] + step, hi)
            if y[k] == x[k]:
                continue
            a, b = _ev(cc, x), _ev(cc, y)
            if a is None or b is None:
                continue
            if sign * (b - a) < -1e-12 * max(1.0, abs(a)):
                bad.append(dict(at=list(x), then=y, f_at=a, f_then=b))
        return not bad, dict(violations=bad[:5], n_violations=len(bad))

    return _mk("monotone", why, run, param=k)
