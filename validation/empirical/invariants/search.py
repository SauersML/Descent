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
        if s["scale"] == "nat":
            # a ℕ argument may only take integer values.  Without this a
            # "witness" like `k = 1e-05` for a founder count is reported, and
            # it is not a point Lean can even form.
            vals = sorted({float(round(v)) for v in vals if v >= 0})
        nxt = []
        for p in pts:
            for v in vals:
                nxt.append(p + [v])
        pts = nxt
        if len(pts) > cap:
            pts = random.Random(0).sample(pts, cap)
    return pts


def maximize(f, box, names, budget=20000, seed=0, feasible=None):
    """Maximize f over the box, subject to `feasible(*x)`.

    `feasible` carries the RELATIONAL hypotheses the author stated in adjacent
    theorems (`H_S <= H_T`, Cauchy-Schwarz on an LD covariance, ...).  Without
    it the search reports every such definition as broken at a point the author
    already excluded.  Returns (best_value, best_point).

    Random draws on the declared measure, then boundary enumeration, then a
    shrinking pattern search from the incumbent.
    """
    rng = random.Random(seed)
    best, bestx = -INF, None

    def ev(x):
        if feasible is not None:
            try:
                if not feasible(*x):
                    return None
            except Exception:
                return None
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

    Returns 'proved' or 'inconclusive'.  THERE IS NO 'refuted' VERDICT and
    there never was: this routine is SOUND, not complete.  An interval
    evaluation that straddles the bound may do so because the body really
    escapes, or because interval arithmetic over-approximated it, and those
    two are indistinguishable here -- so a box it cannot close is returned as
    `inconclusive` with the worst sub-box, never as a refutation.  Refuting a
    bound needs a concrete witness, which is `maximize`'s job.

    The docstring used to promise 'refuted'.  Nothing in production read it --
    `check_ranges` branches only on 'proved' -- but a NEW caller written from
    this docstring gets a branch that is silently dead, and its counts then
    look like measurements.  That happened on 2026-08-02: a vacuity sweep
    classified 0 of 137 definitions as able to violate their bound, which read
    as a dramatic finding and was an artefact of a branch that cannot be
    taken.  The positive control that caught it -- force an absurd bound of
    [0.499, 0.5001], on which essentially every definition must escape, and
    check that SOMETHING is refuted -- returned 0 of 120, which is the shape
    of a check that cannot fire rather than one that found nothing.
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
