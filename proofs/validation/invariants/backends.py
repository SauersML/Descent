"""Evaluation backends for transpiled Lean bodies.

One transpilation, three semantics:

  `FloatBackend`    ordinary IEEE evaluation, for sampling and local search.
  `IntervalBackend` sound outward-rounded interval arithmetic, for PROOFS of
                    range containment (an interval result inside the range is
                    a proof for the whole box; only an escaping interval is
                    inconclusive and must be refined).
  `Z3Backend`       real-arithmetic terms for SMT, exact for the polynomial /
                    rational fragment.

Lean's junk-value conventions are reproduced exactly, because the whole point
is to test what is written:  `x / 0 = 0`, `Real.sqrt x = 0` for `x < 0`,
`Real.log x = 0` for `x <= 0`.  A checker that silently used NaN instead would
miss escapes that the Lean semantics genuinely produces.
"""
from __future__ import annotations

import math


# --------------------------------------------------------------- float


class FloatBackend:
    name = "float"
    pi = math.pi
    e = math.e

    @staticmethod
    def div(a, b):
        return 0.0 if b == 0 else a / b  # Lean: x / 0 = 0

    @staticmethod
    def sqrt(x):
        return math.sqrt(x) if x >= 0 else 0.0  # Lean: Real.sqrt of neg = 0

    @staticmethod
    def exp(x):
        try:
            return math.exp(x)
        except OverflowError:
            return math.inf

    @staticmethod
    def log(x):
        # Mathlib defines Real.log through |x|, so Real.log (-x) = Real.log x,
        # and only Real.log 0 is the junk value 0.  Returning 0 for every
        # nonpositive argument -- which this did before -- is a DIFFERENT
        # function from the one the corpus is written against.
        return 0.0 if x == 0 else math.log(abs(x))

    @staticmethod
    def logb(b, x):
        return FloatBackend.div(FloatBackend.log(x), FloatBackend.log(b))

    @staticmethod
    def Phi(x):
        """Standard normal CDF -- Calibrator/Probability.lean:487 `Phi`."""
        return 0.5 * math.erfc(-x / math.sqrt(2.0))

    @staticmethod
    def phi(x):
        return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)

    @staticmethod
    def probit(p):
        """Inverse standard normal CDF (Acklam), junk value 0 outside (0,1)."""
        if not 0.0 < p < 1.0:
            return 0.0
        a = [-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02,
             1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00]
        bq = [-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02,
              6.680131188771972e+01, -1.328068155288572e+01]
        c = [-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00,
             -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00]
        dd = [7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00,
              3.754408661907416e+00]
        pl = 0.02425
        if p < pl:
            q = math.sqrt(-2 * math.log(p))
            return (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / \
                   ((((dd[0]*q+dd[1])*q+dd[2])*q+dd[3])*q+1)
        if p > 1 - pl:
            q = math.sqrt(-2 * math.log(1 - p))
            return -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / \
                    ((((dd[0]*q+dd[1])*q+dd[2])*q+dd[3])*q+1)
        q = p - 0.5
        r = q * q
        return (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q / \
               (((((bq[0]*r+bq[1])*r+bq[2])*r+bq[3])*r+bq[4])*r+1)

    sin = staticmethod(math.sin)
    cos = staticmethod(math.cos)
    tanh = staticmethod(math.tanh)
    atan = staticmethod(math.atan)

    @staticmethod
    def pow(a, b):
        if isinstance(b, float) and b.is_integer():
            n = int(b)
            if n >= 0:
                return a ** n
            return FloatBackend.div(1.0, a ** (-n))
        return FloatBackend.rpow(a, b)

    @staticmethod
    def rpow(a, b):
        # Real.rpow is defined via the complex exponential and taken real
        # part, so a negative base does NOT give a junk value: it gives
        # exp(log|a| * b) * cos(pi * b).
        if a == 0:
            return 1.0 if b == 0 else 0.0
        try:
            if a > 0:
                return math.exp(b * math.log(a))
            return math.exp(b * math.log(-a)) * math.cos(b * math.pi)
        except OverflowError:
            return math.inf

    mx = staticmethod(max)
    mn = staticmethod(min)
    absv = staticmethod(abs)

    @staticmethod
    def ite(c, a, b):
        return a if c else b

    @staticmethod
    def cmp(a, op, b):
        return {"<": a < b, ">": a > b, "<=": a <= b, ">=": a >= b,
                "==": a == b, "!=": a != b}[op]

    land = staticmethod(lambda a, b: a and b)
    lor = staticmethod(lambda a, b: a or b)


# --------------------------------------------------------------- interval

INF = math.inf


class Iv:
    """Closed interval [lo, hi]; `nan` marks a value we cannot bound."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = lo
        self.hi = lo if hi is None else hi

    def __repr__(self):
        return f"[{self.lo:.6g}, {self.hi:.6g}]"

    def __add__(self, o):
        o = iv(o)
        return Iv(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return Iv(-self.hi, -self.lo)

    def __sub__(self, o):
        return self + (-iv(o))

    def __rsub__(self, o):
        return iv(o) + (-self)

    def __mul__(self, o):
        o = iv(o)
        c = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        c = [x for x in c if not math.isnan(x)]
        return Iv(min(c), max(c)) if c else Iv(-INF, INF)

    __rmul__ = __mul__

    def contains(self, x):
        return self.lo <= x <= self.hi

    def straddles_zero(self):
        return self.lo <= 0 <= self.hi


def iv(x):
    return x if isinstance(x, Iv) else Iv(float(x), float(x))


class IntervalBackend:
    """Outward-rounded interval arithmetic honouring Lean's junk values."""

    name = "interval"
    pi = Iv(math.pi, math.pi)
    e = Iv(math.e, math.e)

    @staticmethod
    def div(a, b):
        a, b = iv(a), iv(b)
        if b.straddles_zero():
            # Lean's x/0 = 0 means the result set is the union of the ordinary
            # quotient over b != 0 with {0}; that is unbounded unless b is a
            # point at 0.
            if b.lo == 0 and b.hi == 0:
                return Iv(0.0, 0.0)
            return Iv(-INF, INF)
        return a * Iv(1.0 / b.hi, 1.0 / b.lo)

    @staticmethod
    def sqrt(x):
        x = iv(x)
        lo = math.sqrt(x.lo) if x.lo >= 0 else 0.0
        hi = math.sqrt(x.hi) if x.hi >= 0 else 0.0
        return Iv(min(lo, 0.0) if x.lo < 0 else lo, hi)

    @staticmethod
    def exp(x):
        x = iv(x)
        return Iv(math.exp(x.lo) if x.lo > -700 else 0.0,
                  math.exp(x.hi) if x.hi < 700 else INF)

    @staticmethod
    def log(x):
        x = iv(x)
        if x.lo > 0:
            return Iv(math.log(x.lo), math.log(x.hi))
        if x.hi < 0:  # log|x| is DECREASING in x on the negative axis
            return Iv(math.log(-x.hi), math.log(-x.lo))
        # the interval straddles zero: log|x| is unbounded below, and the
        # single point x = 0 contributes the junk value 0
        top = max(math.log(abs(x.lo)) if x.lo != 0 else -INF,
                  math.log(abs(x.hi)) if x.hi != 0 else -INF, 0.0)
        return Iv(-INF, top)

    @staticmethod
    def logb(b, x):
        return IntervalBackend.div(IntervalBackend.log(x), IntervalBackend.log(b))

    @staticmethod
    def Phi(x):
        x = iv(x)
        return Iv(FloatBackend.Phi(x.lo), FloatBackend.Phi(x.hi))

    @staticmethod
    def phi(x):
        x = iv(x)
        if x.straddles_zero():
            return Iv(min(FloatBackend.phi(x.lo), FloatBackend.phi(x.hi)),
                      FloatBackend.phi(0.0))
        return Iv(min(FloatBackend.phi(x.lo), FloatBackend.phi(x.hi)),
                  max(FloatBackend.phi(x.lo), FloatBackend.phi(x.hi)))

    @staticmethod
    def probit(p):
        p = iv(p)
        if p.lo <= 0.0 or p.hi >= 1.0:
            return Iv(-INF, INF)
        return Iv(FloatBackend.probit(p.lo), FloatBackend.probit(p.hi))

    @staticmethod
    def sin(x):
        return Iv(-1.0, 1.0)

    @staticmethod
    def cos(x):
        return Iv(-1.0, 1.0)

    @staticmethod
    def tanh(x):
        x = iv(x)
        return Iv(math.tanh(x.lo), math.tanh(x.hi))

    @staticmethod
    def atan(x):
        x = iv(x)
        return Iv(math.atan(x.lo), math.atan(x.hi))

    @staticmethod
    def pow(a, b):
        a, b = iv(a), iv(b)
        if b.lo == b.hi and float(b.lo).is_integer():
            n = int(b.lo)
            if n == 0:
                return Iv(1.0, 1.0)
            if n > 0:
                if n % 2 == 0:
                    if a.straddles_zero():
                        return Iv(0.0, max(a.lo ** n, a.hi ** n))
                    m = min(abs(a.lo), abs(a.hi)) ** n
                    return Iv(m, max(a.lo ** n, a.hi ** n))
                return Iv(a.lo ** n, a.hi ** n)
            return IntervalBackend.div(Iv(1.0, 1.0), IntervalBackend.pow(a, Iv(-n)))
        return IntervalBackend.rpow(a, b)

    @staticmethod
    def rpow(a, b):
        a, b = iv(a), iv(b)
        if a.lo <= 0:
            return Iv(-INF, INF)  # junk-value region; give up soundly
        return IntervalBackend.exp(b * IntervalBackend.log(a))

    @staticmethod
    def mx(a, b):
        a, b = iv(a), iv(b)
        return Iv(max(a.lo, b.lo), max(a.hi, b.hi))

    @staticmethod
    def mn(a, b):
        a, b = iv(a), iv(b)
        return Iv(min(a.lo, b.lo), min(a.hi, b.hi))

    @staticmethod
    def absv(a):
        a = iv(a)
        if a.straddles_zero():
            return Iv(0.0, max(-a.lo, a.hi))
        return Iv(min(abs(a.lo), abs(a.hi)), max(abs(a.lo), abs(a.hi)))

    @staticmethod
    def cmp(a, op, b):
        """Three-valued: True, False, or None when the branch is undecided."""
        a, b = iv(a), iv(b)
        lt = a.hi < b.lo
        ge = a.lo >= b.hi
        table = {"<": (lt, ge), ">": (b.hi < a.lo, b.lo >= a.hi),
                 "<=": (a.hi <= b.lo, a.lo > b.hi),
                 ">=": (a.lo >= b.hi, a.hi < b.lo)}
        if op in table:
            t, f = table[op]
            return True if t else (False if f else None)
        return None

    @staticmethod
    def ite(c, a, b):
        if c is True:
            return iv(a)
        if c is False:
            return iv(b)
        return Iv(
            min(iv(a).lo, iv(b).lo), max(iv(a).hi, iv(b).hi)
        )

    @staticmethod
    def land(a, b):
        if a is False or b is False:
            return False
        if a is True and b is True:
            return True
        return None

    @staticmethod
    def lor(a, b):
        if a is True or b is True:
            return True
        if a is False and b is False:
            return False
        return None


class TolerantBackend(FloatBackend):
    """FloatBackend whose comparisons carry a floating-point tolerance.

    Theorem statements are exact over the reals: `simpleFst p p = 0`, or
    `coalFst t1 Ne < coalFst t2 Ne`.  Evaluated in double precision, an exact
    `==` is essentially never true and a strict `<` fails on ties that the
    reals do not have.  Checking a proved theorem with exact float comparisons
    reports failures that are entirely artifacts of rounding.
    """

    name = "tolerant"
    REL = 1e-9

    @staticmethod
    def cmp(a, op, b):
        # A comparison involving a value double precision cannot represent is
        # not evidence about a statement that is exact over the reals.
        # `gradeCertifiedRisk (gradeCertifiedSampleSize eps K c) K c = eps` is
        # an identity, but at c = 7.4e-06 the intermediate `eps ^ (-K/c)` is
        # about 10^31000 and overflows to inf, after which every comparison is
        # meaningless. Returning None makes the point UNDECIDED and it is
        # skipped, rather than counted as a proved theorem failing -- which is
        # what produced this checker's one and only disagreement.
        if not (math.isfinite(a) and math.isfinite(b)):
            return None
        tol = TolerantBackend.REL * max(1.0, abs(a), abs(b))
        if op == "==":
            return abs(a - b) <= tol
        if op == "!=":
            return abs(a - b) > tol
        if op == "<":
            return a < b + tol
        if op == "<=":
            return a <= b + tol
        if op == ">":
            return a > b - tol
        if op == ">=":
            return a >= b - tol
        raise ValueError(op)


class StrictBackend(FloatBackend):
    """FloatBackend for evaluating HYPOTHESES, with margins that SHRINK.

    Tolerance has a direction and getting it backwards is not conservative.
    `TolerantBackend` reads `a < b` as `a < b + tol` so that a proved
    conclusion is not failed on rounding.  Applying that same rule to a
    HYPOTHESIS admits points the theorem excludes: `m1 < m2` was accepted with
    m1 fractionally GREATER than m2, and the conclusion -- which genuinely
    depends on the ordering -- then failed, and the failure was reported
    against the checker rather than against the sampler.

    So hypotheses are evaluated here, where every margin makes the admissible
    set smaller, and conclusions are evaluated in `TolerantBackend`, where
    every margin makes the accepted set larger.  Points near a hypothesis
    boundary are simply not sampled.
    """

    name = "strict"
    REL = 1e-6

    @staticmethod
    def cmp(a, op, b):
        # Same rule on the hypothesis side, and here it shrinks the admissible
        # set as everything else in this backend does: a point whose
        # hypothesis cannot be evaluated in double precision is not sampled.
        if not (math.isfinite(a) and math.isfinite(b)):
            return None
        tol = StrictBackend.REL * max(1.0, abs(a), abs(b))
        if op == "==":
            return abs(a - b) <= 1e-12 * max(1.0, abs(a), abs(b))
        if op == "!=":
            return abs(a - b) > tol
        if op == "<":
            return a < b - tol
        if op == "<=":
            return a <= b - 0.0
        if op == ">":
            return a > b + tol
        if op == ">=":
            return a >= b + 0.0
        raise ValueError(op)


FLOAT = FloatBackend
TOLERANT = TolerantBackend
STRICT = StrictBackend
INTERVAL = IntervalBackend
