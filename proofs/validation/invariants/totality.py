"""Totality artifacts: where Lean's junk values become WRONG domain values.

Mathlib totalises partial operations -- `x / 0 = 0`, `Real.log 0 = 0`,
`Real.sqrt x = 0` for `x < 0`, `x ^ (n : ℤ)` at `x = 0`.  A checking tool must
therefore not raise where Lean returns 0, or it manufactures defects that do
not exist.

That is only half the contract.  Totality explains why the expression does not
error; it says nothing about whether the resulting value is defensible.  When

  * the point is ATTAINABLE inside the definition's own admissible box, and
  * the modelled quantity has a defined limit there, and
  * the junk value differs from that limit,

the definition returns a wrong value at a point people care about, silently,
and no type error will ever reveal it.  That is a defect, and a more serious
one than an unbounded range: an unbounded range is usually a missing
hypothesis, this is a wrong answer inside the domain.

The worked example is `equalVarianceGaussianAUCFromExplainedR2`:
`Phi (Real.sqrt (r2 / (2 * (1 - r2))))` at `r2 = 1` divides by zero, so the
argument is 0 instead of +infinity and a perfectly predictive score is assigned
an AUC of 0.5 -- chance discrimination.

Finding these needs the exact points where a junk branch fires.  Sampling will
essentially never land on one, because they are a measure-zero set.  So the
backend is instrumented to record the value of every guard (every divisor,
every `log` and `sqrt` argument) at each evaluation, and the scan looks for
guards that CHANGE SIGN along a coordinate and bisects to the crossing.  That
lands exactly on the junk point rather than near it.
"""
from __future__ import annotations

import math

from backends import FloatBackend

INF = math.inf


class TracingBackend(FloatBackend):
    """FloatBackend that records every partiality guard it evaluates.

    `guards` accumulates `(kind, value)`; a junk branch fired iff some guard
    is at or past its threshold (a zero divisor, a nonpositive `log`, a
    negative `sqrt`).
    """

    def __init__(self):
        self.guards = []

    def reset(self):
        self.guards = []

    # -- the partial operations, each recording its guard -------------------

    def div(self, a, b):
        self.guards.append(("div", b))
        return 0.0 if b == 0 else a / b

    def log(self, x):
        self.guards.append(("log", x))
        return 0.0 if x == 0 else math.log(abs(x))

    def sqrt(self, x):
        self.guards.append(("sqrt", x))
        return math.sqrt(x) if x >= 0 else 0.0

    def rpow(self, a, b):
        self.guards.append(("rpow", a))
        return FloatBackend.rpow(a, b)

    def pow(self, a, b):
        if isinstance(b, float) and b.is_integer() and int(b) < 0:
            self.guards.append(("inv", a))
        return FloatBackend.pow(a, b)

    # everything else is inherited unchanged

    def fired(self):
        """Did a junk branch actually trigger at the last evaluation?"""
        for kind, v in self.guards:
            if kind in ("div", "inv") and v == 0:
                return kind
            if kind == "log" and v == 0:
                return kind
            if kind == "sqrt" and v < 0:
                return kind
            if kind == "rpow" and v <= 0:
                return kind
        return None


def _eval(c, tb, x):
    tb.reset()
    try:
        v = c(tb, *x)
    except Exception:
        return None, []
    if v is None or isinstance(v, bool) or v != v:
        return None, list(tb.guards)
    return float(v), list(tb.guards)


def _plain(c, x):
    from backends import FLOAT

    try:
        v = c(FLOAT, *x)
    except Exception:
        return None
    if v is None or isinstance(v, bool) or v != v:
        return None
    return float(v)


def _crossings(c, tb, x, k, lo, hi, n=48):
    """Values of coordinate k where some guard crosses its threshold.

    Returns bracketing pairs (a, b, guard_index) for bisection.
    """
    out = []
    xs = [lo + (hi - lo) * i / (n - 1.0) for i in range(n)]
    prev_g, prev_t = None, None
    for t in xs:
        y = list(x)
        y[k] = t
        _, g = _eval(c, tb, y)
        if prev_g is not None and len(g) == len(prev_g):
            for j, ((kind, a), (kind2, b)) in enumerate(zip(prev_g, g)):
                if kind != kind2:
                    continue
                # the threshold is 0 for every guard kind we track
                if (a < 0) != (b < 0) or a == 0 or b == 0:
                    out.append((prev_t, t, j))
        prev_g, prev_t = g, t
    return out


def _bisect(c, tb, x, k, a, b, j, iters=60):
    """Drive guard j to its zero by bisection on coordinate k."""
    def guard(t):
        y = list(x)
        y[k] = t
        _, g = _eval(c, tb, y)
        return g[j][1] if j < len(g) else None

    ga, gb = guard(a), guard(b)
    if ga is None or gb is None:
        return None
    if ga == 0:
        return a
    if gb == 0:
        return b
    if (ga < 0) == (gb < 0):
        return None
    for _ in range(iters):
        m = 0.5 * (a + b)
        gm = guard(m)
        if gm is None:
            return None
        if gm == 0:
            return m
        if (gm < 0) == (ga < 0):
            a, ga = m, gm
        else:
            b, gb = m, gm
    return 0.5 * (a + b)


def _limit(c, x, k, t, side, box_lo, box_hi):
    """One-sided limit of f along coordinate k as it approaches t.

    Returns (limit, converged).  `converged` is False when the sequence is not
    settling, in which case there is no defined limit to compare against and
    nothing is reported.
    """
    vals = []
    for d in (1e-3, 1e-4, 1e-5, 1e-6, 1e-7):
        step = d * max(1.0, abs(t))
        u = t + side * step
        if u < box_lo or u > box_hi:
            return None, False
        y = list(x)
        y[k] = u
        v = _plain(c, y)
        if v is None:
            return None, False
        vals.append(v)
    # settling: successive differences shrinking towards the last value
    d1 = abs(vals[-1] - vals[-2])
    d0 = abs(vals[-3] - vals[-4])
    if not math.isfinite(vals[-1]):
        return vals[-1], True  # a genuine pole; defined as an extended limit
    if d1 <= 0.25 * d0 + 1e-12 or d1 <= 1e-9 * max(1.0, abs(vals[-1])):
        return vals[-1], True
    # not settling: extrapolate only if the trend is clearly divergent
    if abs(vals[-1]) > 10 * abs(vals[0]) and abs(vals[-1]) > 1e6:
        return math.copysign(INF, vals[-1]), True
    return None, False


def scan(c, box, names, pts, max_report=6):
    """Find attainable junk points whose value contradicts the limit.

    Returns a list of findings, each with the exact input point, the junk
    branch that fired, the value returned, and the limit it should have had.
    """
    tb = TracingBackend()
    findings = []
    seen = set()
    for x in pts[:25]:
        for k, nm in enumerate(names):
            lo, hi = box[nm]["lo"], box[nm]["hi"]
            if not (math.isfinite(lo) and math.isfinite(hi)) or hi <= lo:
                continue
            for a, b, j in _crossings(c, tb, x, k, lo, hi):
                t = _bisect(c, tb, x, k, a, b, j)
                if t is None or not (lo <= t <= hi):
                    continue
                y = list(x)
                y[k] = t
                val, _ = _eval(c, tb, y)
                kind = tb.fired()
                if kind is None or val is None:
                    continue
                key = (k, round(t, 9))
                if key in seen:
                    continue
                seen.add(key)
                left, okl = _limit(c, x, k, t, -1.0, lo, hi)
                right, okr = _limit(c, x, k, t, +1.0, lo, hi)
                lim, why = None, None
                if okl and okr and left is not None and right is not None:
                    if _close(left, right):
                        lim, why = left, "two-sided limit"
                elif okl and left is not None and t >= hi - 1e-12:
                    lim, why = left, "limit from inside the box (upper edge)"
                elif okr and right is not None and t <= lo + 1e-12:
                    lim, why = right, "limit from inside the box (lower edge)"
                if lim is None or _close(lim, val):
                    continue
                finite = math.isfinite(lim)
                # A junk value of 0 where the limit DIVERGES to +infinity is
                # not a neutral choice: it returns the smallest possible value
                # where the truth is the largest.  `stabilizingNsFromObserved
                # Correlation` reports NO selection at the correlation where
                # selection is infinitely strong.  Weaker than a wrong finite
                # answer -- there is no right finite answer to return -- but
                # much worse than an arbitrary one, because it inverts the
                # direction any downstream comparison will see.
                inverted = (not finite) and lim > 0 and val <= 0
                findings.append(dict(
                    point={n: v for n, v in zip(names, y)},
                    coordinate=nm, at=t, junk_branch=kind,
                    value=val, limit=lim, limit_kind=why,
                    klass=("wrong-finite-value" if finite else
                           "direction-inverted" if inverted else
                           "singularity"),
                    severity_note=(
                        "the quantity has a finite limit here and the "
                        "definition returns something else -- a wrong value "
                        "inside the domain"
                        if finite else
                        "the limit diverges to +infinity and the definition "
                        "returns 0, the opposite extreme; there is no right "
                        "finite answer, but this one inverts the direction"
                        if inverted else
                        "the limit is infinite, so the quantity is genuinely "
                        "undefined here and the junk value is a modelling "
                        "choice"),
                ))
                if len(findings) >= max_report:
                    return findings
    return findings


def _close(a, b):
    if a is None or b is None:
        return False
    if math.isinf(a) or math.isinf(b):
        return a == b
    return abs(a - b) <= 1e-6 * max(1.0, abs(a), abs(b))
