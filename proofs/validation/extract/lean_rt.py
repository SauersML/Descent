"""Lean/Mathlib-faithful runtime for extracted definitions.

Mathlib's real operations are *total*: they are given junk-but-defined values
outside their mathematical domain.  Hand transcription into Python routinely
gets this wrong (Python raises where Lean returns 0), and the difference is
exactly where a definition's edge-case behaviour lives.  These shims reproduce
Mathlib's conventions:

    x / 0        = 0            (`div_zero`)
    x⁻¹ at 0     = 0            (`inv_zero`)
    Real.log 0   = 0            (`Real.log_zero`)
    Real.log x   = log |x|      (`Real.log_neg_eq_log`)
    Real.sqrt x  = 0 for x < 0  (`Real.sqrt_eq_zero_of_nonpos`)
    x ^ (n : ℕ)  = monoid pow, 0 ^ 0 = 1
    x ^ (y : ℝ)  = Real.rpow    (0 ^ y = 0 for y ≠ 0; x < 0 uses exp/cos branch)
"""
from __future__ import annotations

import math

pi = math.pi


def rdiv(a, b):
    return 0.0 if b == 0 else a / b


def rinv(a):
    return 0.0 if a == 0 else 1.0 / a


def rlog(x):
    return 0.0 if x == 0 else math.log(abs(x))


def rsqrt(x):
    return 0.0 if x <= 0 else math.sqrt(x)


def rexp(x):
    return math.exp(x)


def lpow(a, b):
    """`^` with Mathlib semantics, dispatching on whether the exponent is a
    natural/integer literal (monoid pow) or a real (rpow)."""
    if isinstance(b, int) or (isinstance(b, float) and b.is_integer()):
        n = int(b)
        if a == 0:
            return 1.0 if n == 0 else (0.0 if n > 0 else 0.0)  # 0⁻ⁿ = 0 in Lean
        return float(a) ** n
    # Real.rpow
    if a == 0:
        return 0.0
    if a > 0:
        return math.exp(math.log(a) * b)
    return math.exp(math.log(-a) * b) * math.cos(b * math.pi)


def _proj(obj, fld):
    """Structure projection `x.fld` / anonymous-constructor projection `x.1`."""
    if fld.isdigit():
        return obj[int(fld) - 1]
    if isinstance(obj, dict):
        return obj[fld]
    return getattr(obj, fld)


# trig / hyperbolic, passed straight through
exp, log, sqrt = rexp, rlog, rsqrt
cos, sin, tan = math.cos, math.sin, math.tan
cosh, sinh, tanh = math.cosh, math.sinh, math.tanh
arctan, arcsin, arccos = math.atan, math.asin, math.acos


def rmax(a, b):
    return a if a >= b else b


def rmin(a, b):
    return a if a <= b else b


def rabs(a):
    return abs(a)


def Phi(x):
    """Standard normal CDF.

    NUMERIC STAND-IN.  The corpus defines
        Calibrator.Phi : ℝ → ℝ := ProbabilityTheory.cdf (gaussianReal 0 1)
    which is measure-theoretic and has no arithmetic body to extract.  This is
    the erf form of the same function, accurate to ~1e-16 relative.  It is
    mathematically equal to the Lean definition, but it was NOT derived from the
    Lean source, so a disagreement in a definition that routes through it can be
    a defect in that definition OR a mismatch with the intended Phi.  Anything
    depending on it is flagged `numeric_standins` in classes.json.
    """
    return 0.5 * math.erfc(-x / math.sqrt(2.0))


def logb(b, x):
    return rdiv(rlog(x), rlog(b))
