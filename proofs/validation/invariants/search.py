"""Box search: witness hunting (floats) and containment proving (intervals).

`maximize` is a witness hunter -- it returns a concrete input point, which is
what a defect report needs.  It can MISS a thin escape, so a negative result
from it is NOT a proof and is reported as `inconclusive`, never as `pass`.

`prove_contained` is the other half: sound interval branch-and-bound.  When it
succeeds, no point of the box escapes, and that IS a proof.  When it exhausts
its budget it returns `inconclusive` too.  Only these two, plus the SMT
backend, may ever emit a verdict; nothing here upgrades silence to safety.
"""
from __future__ import annotations

import math
import random

from backends import FLOAT, INTERVAL, Iv

INF = math.inf


def _draw(rng, spec):
    lo, hi, sc = spec["lo"], spec["hi"], spec["scale"]
    lo = max(lo, -1e12)
    hi = min(hi, 1e12)
    if sc == "nat":
        return float(rng.randint(int(max(0, lo)), int(min(hi, 10000))))
    if sc == "log" and lo > 0:
        return math.exp(rng.uniform(math.log(lo), math.log(hi)))
    if sc == "log1p" and lo >= 0:
        return math.expm1(rng.uniform(0.0, math.log1p(hi)))
    return rng.uniform(lo, hi)


def _corners(box, names, cap=4096):
    """Corners plus edge midpoints -- escapes cluster at domain boundaries."""
    pts = [[]]
    for n in names:
        s = box[n]
        lo, hi = max(s["lo"], -1e12), min(s["hi"], 1e12)
        vals = [lo, hi, 0.5 * (lo + hi)]
        if lo < 0 < hi:
            vals.append(0.0)
        # just inside the boundary: open-interval domains escape near the edge
        w = hi - lo
        vals += [lo + 1e-9 * w, hi - 1e-9 * w, lo + 1e-4 * w, hi - 1e-4 * w]
        nxt = []
        for p in pts:
            for v in vals:
                nxt.append(p + [v])
        pts = nxt
        if len(pts) > cap:
            pts = random.Random(0).sample(pts, cap)
    return pts


def maximize(f, box, names, budget=20000, seed=0):
    """Maximize f over the box.  Returns (best_value, best_point).

    Random draws on the declared measure, then boundary enumeration, then a
    shrinking pattern search from the incumbent.
    """
    rng = random.Random(seed)
    best, bestx = -INF, None

    def ev(x):
        try:
            v = f(*x)
        except (ValueError, OverflowError, ZeroDivisionError, TypeError):
            return None
        if isinstance(v, bool) or v is None:
            return None
        if isinstance(v, complex) or v != v:  # NaN
            return None
        return float(v)

    for x in _corners(box, names):
        v = ev(x)
        if v is not None and v > best:
            best, bestx = v, list(x)
    for _ in range(budget):
        x = [_draw(rng, box[n]) for n in names]
        v = ev(x)
        if v is not None and v > best:
            best, bestx = v, x
    if bestx is None:
        return -INF, None
    # pattern search, multiplicative then additive steps, clipped to the box
    x = list(bestx)
    for scale in (0.5, 0.2, 0.05, 0.01, 3e-3, 1e-3, 3e-4, 1e-4, 1e-5, 1e-6, 1e-7):
        improved = True
        while improved:
            improved = False
            for i, n in enumerate(names):
                s = box[n]
                w = min(s["hi"], 1e12) - max(s["lo"], -1e12)
                for step in (scale * w, -scale * w):
                    y = list(x)
                    y[i] = min(max(y[i] + step, s["lo"]), s["hi"])
                    if s["scale"] == "nat":
                        y[i] = float(round(y[i]))
                    if y[i] == x[i]:
                        continue
                    v = ev(y)
                    if v is not None and v > best + 1e-15:
                        best, x, improved = v, y, True
    return best, x


def prove_contained(fiv, box, names, lo, hi, max_boxes=3000):
    """Interval branch-and-bound proof that f(box) is inside [lo, hi].

    Returns 'proved', 'refuted' (with a witness sub-box), or 'inconclusive'.
    """
    root = [Iv(max(box[n]["lo"], -1e12), min(box[n]["hi"], 1e12)) for n in names]
    stack = [root]
    used = 0
    worst = None
    while stack and used < max_boxes:
        b = stack.pop()
        used += 1
        try:
            r = fiv(*b)
        except (ValueError, OverflowError, ZeroDivisionError, TypeError):
            return "inconclusive", None, used
        if not isinstance(r, Iv):
            r = Iv(float(r), float(r))
        if r.lo >= lo - 1e-12 and r.hi <= hi + 1e-12:
            continue
        # split the widest coordinate
        widths = [bb.hi - bb.lo for bb in b]
        w = max(widths)
        if w <= 1e-9 or not math.isfinite(w):
            worst = (b, r)
            continue
        i = widths.index(w)
        mid = 0.5 * (b[i].lo + b[i].hi)
        l = list(b)
        rr = list(b)
        l[i] = Iv(b[i].lo, mid)
        rr[i] = Iv(mid, b[i].hi)
        stack.append(l)
        stack.append(rr)
    if not stack and worst is None:
        return "proved", None, used
    return "inconclusive", worst, used
