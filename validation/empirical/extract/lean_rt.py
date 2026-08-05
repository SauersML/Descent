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


def _is_vec(x):
    return isinstance(x, (list, tuple))


def rdiv(a, b):
    if _is_vec(a) or _is_vec(b):
        if _is_vec(a) and _is_vec(b):
            return [rdiv(x, y) for x, y in zip(a, b)]
        if _is_vec(a):
            return [rdiv(x, b) for x in a]
        return [rdiv(a, y) for y in b]
    return 0.0 if b == 0 else a / b


def rinv(a):
    """Lean `a⁻¹`, at whatever type `a` has.

    Scalars: `x⁻¹ = 0` at `x = 0`, which is Mathlib's junk value and not an
    error.

    A SQUARE NESTED TABLE IS A MATRIX, and `M⁻¹` is `Matrix.nonsing_inv`, not a
    reciprocal of each entry and not `1.0 / M`. This used to reach the scalar
    path and raise "unsupported operand type(s) for /: 'float' and 'VecFn'",
    which took out the whole cone above `sourceERMWeights` -- twenty-one
    definitions including `r2FromSourceWeights`, both source-weight Brier
    variants and the Gaussian AUC, none of which has anything wrong with it.

    A singular matrix inverts to ZERO, matching `Matrix.nonsing_inv_apply_not_
    isUnit`. That is not a defensive fallback: the corpus states the consequence
    as `sourceERMWeights_at_singular_covariance_is_junk`, "a rank-deficient
    design reports predict-nothing rather than not-identified", so returning
    zero here is what makes that theorem checkable rather than merely stated.

    A flat table is a `Pi` type, whose `Inv` instance IS pointwise.
    """
    if isinstance(a, (list, tuple)):
        n = len(a)
        if n and all(isinstance(r, (list, tuple)) and len(r) == n for r in a):
            return _matrix_inv(a)
        return VecFn(rinv(x) for x in a)
    return 0.0 if a == 0 else 1.0 / a


def _matrix_inv(M):
    """Gauss-Jordan inverse of a square table; the zero matrix if singular."""
    n = len(M)
    aug = [[float(x) for x in row] + [1.0 if i == j else 0.0 for j in range(n)]
           for i, row in enumerate(M)]
    for c in range(n):
        piv = max(range(c, n), key=lambda r: abs(aug[r][c]))
        if abs(aug[piv][c]) < 1e-12:
            # Singular to working precision. Mathlib's inverse here is 0, and
            # a caller that goes on to `mulVec` it gets the zero vector, which
            # is the documented "predict nothing" outcome.
            return VecFn(VecFn(0.0 for _ in range(n)) for _ in range(n))
        aug[c], aug[piv] = aug[piv], aug[c]
        d = aug[c][c]
        aug[c] = [x / d for x in aug[c]]
        for r in range(n):
            if r == c:
                continue
            f = aug[r][c]
            if f:
                aug[r] = [x - f * y for x, y in zip(aug[r], aug[c])]
    return VecFn(VecFn(row[n:]) for row in aug)


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


# Mathlib matrix/vector methods reachable by dot notation.  Populated below,
# after the functions exist.
_MATRIX_METHODS = {}


def _proj(obj, fld):
    """Structure projection `x.fld` / anonymous-constructor projection `x.1`."""
    if fld.isdigit():
        return obj[int(fld) - 1]
    if isinstance(obj, (list, tuple)) and fld in _MATRIX_METHODS:
        # `(m.sigmaTag P).mulVec wS`: the base is an EXPRESSION, not a binder,
        # so the translator could not tell at parse time that it is a matrix and
        # emitted a projection.  At runtime the value is right here and it is a
        # sequence, so the method is Mathlib's, not a field lookup.  This is a
        # dispatch on an observed value, not a guess: a dict-valued structure
        # still takes the field path below.
        fn = _MATRIX_METHODS[fld]
        return lambda *a: fn(obj, *a)
    if isinstance(obj, dict):
        if fld not in obj:
            why = (obj.get("__uninhabited__") or {}).get(fld)
            if why:
                raise KeyError(
                    f"field {fld!r} was deliberately left uninhabited: {why}. "
                    "This definition reads a field whose Lean type this "
                    "harness does not model, so there is no honest value to "
                    "give it.")
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
        Descent.Phi : ℝ → ℝ := ProbabilityTheory.cdf (gaussianReal 0 1)
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


# ------------------------------------------------- elementwise arithmetic
#
# `Fin n → ℝ` and `Matrix (Fin p) (Fin q) ℝ` arguments arrive as Python
# sequences, and Lean writes ordinary `+`, `-`, `*` on them (`Sig_S - Sig_T` is
# matrix subtraction).  Python lists do not subtract, so generated code for a
# definition with vector arguments routes arithmetic through these instead.
# Scalar-only definitions are NOT routed through them and are byte-identical to
# before, so this cannot perturb anything that already worked.



def add(a, b):
    if _is_vec(a) and _is_vec(b):
        return [add(x, y) for x, y in zip(a, b)]
    if _is_vec(a):
        return [add(x, b) for x in a]
    if _is_vec(b):
        return [add(a, y) for y in b]
    return a + b


def sub(a, b):
    if _is_vec(a) and _is_vec(b):
        return [sub(x, y) for x, y in zip(a, b)]
    if _is_vec(a):
        return [sub(x, b) for x in a]
    if _is_vec(b):
        return [sub(a, y) for y in b]
    return a - b


def mul(a, b):
    if _is_vec(a) and _is_vec(b):
        return [mul(x, y) for x, y in zip(a, b)]
    if _is_vec(a):
        return [mul(x, b) for x in a]
    if _is_vec(b):
        return [mul(a, y) for y in b]
    return a * b


def neg(a):
    return [neg(x) for x in a] if _is_vec(a) else -a


# ------------------------------------------- inhabitants of function types
#
# A Lean value of type `Fin n → ℝ` is read in TWO different ways by the code
# this package generates:
#
#   * as a table, when the argument was declared `Fin n → ℝ` -- the translator
#     emits `v[int(i)]`, and `∑ i, v i` needs `len(v)`;
#   * as a function, when the same value arrives as a structure FIELD -- the
#     translator emits `_rt._proj(s, 'v')(i)`, because from inside a body a
#     projection is just an expression that gets applied.
#
# Handing out two different Python values for the one Lean value is what broke
# this before: `admissible.struct_value` gave function-typed fields a lambda,
# which has no length, so `∑ j, spectrum.weight j` could not run, and gave
# `Pop → Matrix …` fields a *dict* (it read the head `Pop` as a structure name),
# so `m.directCausal P` raised "'dict' object is not callable".  VecFn is ONE
# value that answers both readings, so a field and an argument of the same Lean
# type behave identically and cannot disagree.
#
# Out-of-range indexing RAISES.  It must: silently clamping or wrapping would
# turn "this definition was evaluated at an index its argument does not have"
# into a plausible number, and that number would become evidence.


def _ix(k, n, who):
    if isinstance(k, bool) or not isinstance(k, (int, float)):
        raise TypeError(f"{who}: index {k!r} is not a finite-type index; "
                        "refusing to invent one")
    i = int(k)
    if not 0 <= i < n:
        raise IndexError(f"{who}: index {i} outside 0..{n - 1}; the inhabitant "
                         "does not cover this point (widen the sampled "
                         "dimension rather than reading a wrapped entry)")
    return i


class VecFn(list):
    """A finite Lean function `ι → X`, usable as a table AND as a function.

    `v[i]` and `v(i)` are the same entry; `v(i, j)` walks two levels, which is
    how `M i j` for a `Matrix (Fin p) (Fin q) ℝ` field arrives.  Being a `list`
    subclass means `len`, iteration, `sum`, and the elementwise `add`/`sub`/
    `mul` above all work on it unchanged.
    """

    __slots__ = ()

    def __call__(self, *idx):
        v, rest = self, list(idx)
        while rest:
            if isinstance(v, (list, tuple)):
                v = v[_ix(rest.pop(0), len(v), "VecFn")]
                continue
            if callable(v):
                # `Fin atomCount → ℝ → ℝ`: a table OF functions.  The remaining
                # arguments belong to the function, not to the table.
                return v(*rest)
            raise TypeError(
                f"VecFn applied to {len(idx)} indices but ran out of "
                "dimensions; this value is not that many levels deep")
        return v

    # ---- ARITHMETIC IS ELEMENTWISE, NOT CONCATENATION.
    #
    # `VecFn` subclasses `list` to get `len`, iteration and indexing for free,
    # and inherited `list.__add__` with them -- so a translated body computing
    # Lean's `A + B` on two `Fin p -> R` vectors got a vector of length 2p, and
    # on two matrices a matrix with twice the rows.  Lean's `+` on `Pi` and on
    # `Matrix` is elementwise at every level; concatenation is not a thing it
    # can mean.
    #
    # It failed loudly only where a shape was checked downstream:
    # `crossCovariance` summed four `Matrix (Fin p) (Fin q)` terms into a 16x4
    # and two effect vectors into a length-8, and `mulVec` refused the pair --
    # sixteen definitions, `mechanisticPortabilityRatio` and both Brier
    # components among them, filed NOT-EXTRACTABLE for a shape the harness had
    # built itself. Where nothing checked a length it was worse than an error:
    # `sum` over a concatenation is the sum of both operands, so a body could
    # return a plausible wrong number instead of raising.
    #
    # `*` is deliberately NOT overridden. Mathlib's `*` on `Matrix` is matrix
    # multiplication and on `Pi` is elementwise, so a single operator cannot be
    # right for both; the translator emits the explicit `_rt.mul`/`_rt.mulVec`
    # helpers, and inherited `list.__mul__` raises `TypeError` on a float rather
    # than inventing an answer.

    def __add__(self, other):
        return _vec(add(self, other))

    __radd__ = __add__          # `sum(vs)` starts at the scalar 0; add() broadcasts it

    def __sub__(self, other):
        return _vec(sub(self, other))

    def __rsub__(self, other):
        return _vec(sub(other, self))

    def __neg__(self):
        return _vec(neg(self))

    def __repr__(self):
        return f"VecFn({list.__repr__(self)})"


def _vec(x):
    """Re-wrap a nested plain `list` as `VecFn`, so `v(i)` still works.

    `add`/`sub`/`neg` build plain lists. A plain list indexes but does not
    CALL, and a body that reads a summed field as `m.f P i` would raise
    "'list' object is not callable" -- so the wrapping is what makes the
    elementwise result usable in the same places the operands were.
    """
    if isinstance(x, (list, tuple)):
        return VecFn(_vec(e) for e in x)
    return x


def _register_matrix_methods():
    _MATRIX_METHODS.update({"mulVec": mulVec, "vecMul": vecMul,
                            "trace": lambda M: trace(M), "transpose": transpose,
                            "dotProduct": dotProduct})


def sumdim(idx, *lens):
    """The length a `∑` with an unannotated index ranges over.

    `∑ i, freq i` carries no dimension in its syntax; Lean recovers one by
    elaborating `i`'s type from `freq`'s domain.  The translator recovers it the
    same way, from every place the index is applied -- and passes ALL of them
    here so that they can be checked against each other at runtime.

    Disagreement RAISES.  If two things the index runs over have different
    lengths, then either the inference picked the wrong one or the caller passed
    mismatched arguments; in both cases the sum would silently run over the
    wrong range and return a number that looks fine.  That is exactly the
    failure mode this whole package exists to avoid, so it must be loud.
    """
    if not lens:
        raise ValueError(f"sum index {idx!r}: no dimension could be inferred")
    if len(set(lens)) != 1:
        raise ValueError(
            f"sum index {idx!r} ranges over values of DIFFERENT lengths "
            f"{lens}; the range is ambiguous and any choice would be a guess")
    return lens[0]


def transpose(M):
    """Mathlib `Matrix.transpose`."""
    M = [list(r) for r in M]
    if not M:
        return VecFn()
    if len({len(r) for r in M}) != 1:
        raise ValueError("transpose: rows have different lengths")
    return VecFn(VecFn(M[i][j] for i in range(len(M)))
                 for j in range(len(M[0])))


def dotProduct(u, v):
    """Mathlib `dotProduct u v = ∑ i, u i * v i`.

    Refuses on a length mismatch: Lean's version is typed `(Fin n → ℝ) → (Fin n
    → ℝ) → ℝ`, so unequal lengths mean the two arguments came from different
    dimensions and zipping them would silently compute a truncated sum.
    """
    u, v = list(u), list(v)
    if len(u) != len(v):
        raise ValueError(f"dotProduct: lengths {len(u)} and {len(v)} differ; "
                         "in Lean both live in `Fin n → ℝ` for one `n`")
    return sum(a * b for a, b in zip(u, v))


def mulVec(M, v):
    """Mathlib `Matrix.mulVec M v = fun i => ∑ j, M i j * v j`."""
    M = [list(r) for r in M]
    v = list(v)
    for r in M:
        if len(r) != len(v):
            raise ValueError(f"mulVec: matrix row width {len(r)} does not "
                             f"match vector length {len(v)}")
    return VecFn(sum(a * b for a, b in zip(r, v)) for r in M)


def vecMul(v, M):
    """Mathlib `Matrix.vecMul v M = fun j => ∑ i, v i * M i j`."""
    M = [list(r) for r in M]
    v = list(v)
    if len(M) != len(v):
        raise ValueError(f"vecMul: matrix has {len(M)} rows, vector has "
                         f"{len(v)} entries")
    return VecFn(sum(v[i] * M[i][j] for i in range(len(v)))
                 for j in range(len(M[0]) if M else 0))


def trace(M):
    """Mathlib `Matrix.trace M = ∑ i, M i i`.  Square matrices only."""
    M = [list(r) for r in M]
    for r in M:
        if len(r) != len(M):
            raise ValueError(f"trace: matrix is {len(M)}x{len(r)}, not square")
    return sum(M[i][i] for i in range(len(M)))


_register_matrix_methods()
