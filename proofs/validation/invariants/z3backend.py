"""SMT backend: decide range containment instead of sampling for it.

A sampling negative is not a proof.  An SMT negative is.  For the polynomial
and rational fragment -- which is most of this corpus -- z3's nonlinear real
arithmetic decides `is there a point in the box where the body leaves its
range?` outright, so `inconclusive` becomes `proved` or a witness.

Lean's junk values are modelled exactly, as branches rather than as side
conditions:  `a / b` is `If(b == 0, 0, a/b)`, and `Real.sqrt x` introduces a
fresh variable `s` with `s >= 0 and (x >= 0 -> s*s == x) and (x < 0 -> s == 0)`.
Encoding them as preconditions instead would quietly drop exactly the points
where the interesting defects live.

TRANSCENDENTALS ARE NOT MODELLED.  `exp`, `log`, `Phi` and friends have no
decidable theory here, and inventing an axiomatisation would produce verdicts
that look like proofs and are not.  A definition using them is reported
`unsupported`, and the sampling backend remains its only evidence.

`Phi` in particular: the `extract` agent's numeric `Phi` is an erf form that is
mathematically equal to the corpus's measure-theoretic definition but NOT
derived from it.  Modelling it here would mean proving things about a stand-in
while appearing to prove them about the corpus.
"""
from __future__ import annotations

import math

try:
    import z3

    HAVE_Z3 = True
except Exception:  # pragma: no cover - z3 is optional by design
    z3 = None
    HAVE_Z3 = False


class Unsupported(Exception):
    """The body leaves the decidable fragment."""


class Z3Backend:
    """Emits z3 real terms; collects side constraints for `sqrt`."""

    name = "z3"

    def __init__(self):
        self.aux = []          # extra assertions (sqrt definitions)
        self._n = 0
        self.pi = math.pi
        self.e = math.e

    def _fresh(self, tag):
        self._n += 1
        return z3.Real(f"_{tag}{self._n}")

    # -- total arithmetic --------------------------------------------------

    def div(self, a, b):
        return z3.If(b == 0, z3.RealVal(0), a / b)

    def sqrt(self, x):
        s = self._fresh("sqrt")
        self.aux.append(z3.And(s >= 0,
                               z3.Implies(x >= 0, s * s == x),
                               z3.Implies(x < 0, s == 0)))
        return s

    def pow(self, a, b):
        if isinstance(b, float) and b.is_integer():
            n = int(b)
            if n == 0:
                return z3.RealVal(1)
            if n > 0:
                r = a
                for _ in range(n - 1):
                    r = r * a
                return r
            return self.div(z3.RealVal(1), self.pow(a, float(-n)))
        raise Unsupported("non-integer exponent")

    def rpow(self, a, b):
        raise Unsupported("Real.rpow")

    def mx(self, a, b):
        return z3.If(a >= b, a, b)

    def mn(self, a, b):
        return z3.If(a <= b, a, b)

    def absv(self, a):
        return z3.If(a >= 0, a, -a)

    def ite(self, c, a, b):
        return z3.If(c, a, b)

    def cmp(self, a, op, b):
        return {"<": a < b, ">": a > b, "<=": a <= b, ">=": a >= b,
                "==": a == b, "!=": a != b}[op]

    def land(self, a, b):
        return z3.And(a, b)

    def lor(self, a, b):
        return z3.Or(a, b)

    # -- everything transcendental is refused, loudly ----------------------

    def _no(self, *_a, **_k):
        raise Unsupported("transcendental function")

    exp = log = logb = sin = cos = tanh = atan = Phi = phi = probit = _no


def decide_range(c, box, names, lo, hi, timeout_ms=10000):
    """Is there a point in `box` where `c` leaves `[lo, hi]`?

    Returns (verdict, witness, detail) with verdict in
    {'proved', 'escape', 'unknown', 'unsupported', 'no-z3'}.

    'proved' means UNSAT of the escape condition over the whole box: a proof,
    not a sample.
    """
    if not HAVE_Z3:
        return "no-z3", None, "z3 is not installed; sampling only"
    b = Z3Backend()
    vs = {n: z3.Real(n) for n in names}
    try:
        body = c(b, *[vs[n] for n in names])
    except Unsupported as e:
        return "unsupported", None, str(e)
    except Exception as e:
        return "unsupported", None, f"{type(e).__name__}: {e}"

    s = z3.Solver()
    s.set("timeout", timeout_ms)
    for a in b.aux:
        s.add(a)
    for n in names:
        blo, bhi = box[n]["lo"], box[n]["hi"]
        if math.isfinite(blo):
            s.add(vs[n] >= z3.RealVal(blo))
        if math.isfinite(bhi):
            s.add(vs[n] <= z3.RealVal(bhi))
    esc = []
    if math.isfinite(lo):
        esc.append(body < z3.RealVal(lo))
    if math.isfinite(hi):
        esc.append(body > z3.RealVal(hi))
    if not esc:
        return "unsupported", None, "no finite bound to check"
    s.add(z3.Or(*esc))

    r = s.check()
    if r == z3.unsat:
        return "proved", None, "no point of the box leaves the range (UNSAT)"
    if r == z3.sat:
        m = s.model()
        w = {}
        for n in names:
            try:
                w[n] = float(m.eval(vs[n], model_completion=True).as_fraction())
            except Exception:
                w[n] = None
        return "escape", w, "witness from the model"
    return "unknown", None, f"solver returned {r}"
