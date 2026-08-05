#!/usr/bin/env python3.12
"""Independent reproduction of the sigma_k quadrature table in
Descent/CondensationUnification.lean (ScaleSequence.doubly_exponential docstring):

    1.414, 3.742, 19.07, 294.1, 7.276e4, 4.699e9, 2.005e19

The corpus states these came from Gauss-Hermite with 200 nodes and that no script
reproduces them.  We reproduce them two independent ways:

  METHOD A (primary, EXACT): the normalized squaring flow
        X_0 = Z ~ N(0,1),   X_k = (X_{k-1}^2 - 1) / sigma_k,
        sigma_k^2 = Var(X_{k-1}^2) = E[X_{k-1}^4] - 1
  keeps every EVEN moment of every X_k a rational number, because sigma_k^2 is
  rational and only even powers of sigma_k ever appear:
        m_{2j}(X_k) = ( sum_i C(2j,i) (-1)^{2j-i} m_{2i}(X_{k-1}) ) / (sigma_k^2)^j
  So the whole table is computable in exact arithmetic with fractions.Fraction,
  with no quadrature and no error term at all.  E[Z^{2j}] = (2j-1)!!.

  METHOD B (the stated method): Gauss-Hermite quadrature in double precision,
  nodes from the orthonormal probabilists'-Hermite recurrence via interlacing
  bisection, weights w_i = 1 / sum_{k<n} pi_k(x_i)^2.  Run at several node counts
  so the floating-point degradation is visible.

Also tests the docstring's claim that the logarithms "double at each floor to four
significant figures".

stdlib only (no numpy/sympy on the cluster).
"""

import json
import math
import sys
from fractions import Fraction

# floors we want sigma_1 .. sigma_NFLOOR
NFLOOR = 7

CLAIMED = [1.414, 3.742, 19.07, 294.1, 7.276e4, 4.699e9, 2.005e19]


# --------------------------------------------------------------------------
# METHOD A: exact rational moment recursion
# --------------------------------------------------------------------------

def binom_table(nmax):
    C = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    for n in range(nmax + 1):
        C[n][0] = 1
        for k in range(1, n + 1):
            C[n][k] = C[n - 1][k - 1] + C[n - 1][k]
    return C


def exact_sigmas(nfloor):
    """Return [Fraction(sigma_k^2) for k=1..nfloor] exactly."""
    # J[k] = highest half-order of moments of X_k that we need.
    # need m4(X_{nfloor-1}) -> J[nfloor-1] = 2, and J[k-1] = 2*J[k]
    J = [0] * nfloor
    J[nfloor - 1] = 2
    for k in range(nfloor - 2, -1, -1):
        J[k] = 2 * J[k + 1]
    maxorder = 2 * J[0]
    C = binom_table(maxorder)

    # moments of X_0 = Z: m_{2j} = (2j-1)!!
    m = [Fraction(0)] * (J[0] + 1)
    m[0] = Fraction(1)
    for j in range(1, J[0] + 1):
        m[j] = m[j - 1] * (2 * j - 1)

    sig2 = []
    for k in range(1, nfloor + 1):
        s2 = m[2] - 1                      # sigma_k^2 = E[X_{k-1}^4] - 1
        sig2.append(s2)
        if k == nfloor:
            break
        # push moments forward to X_k, up to half-order J[k]
        Jk = J[k]
        newm = [Fraction(0)] * (Jk + 1)
        for j in range(Jk + 1):
            acc = Fraction(0)
            twoj = 2 * j
            for i in range(twoj + 1):
                term = C[twoj][i] * m[i]
                acc += term if (twoj - i) % 2 == 0 else -term
            newm[j] = acc / (s2 ** j)
        m = newm
    return sig2


# --------------------------------------------------------------------------
# METHOD B: Gauss-Hermite (probabilists', weight = standard normal density)
# --------------------------------------------------------------------------

def orthonormal_hermite(x, n):
    """Return list pi_0(x) .. pi_n(x) for the orthonormal probabilists' Hermite
    polynomials: x*pi_k = sqrt(k+1)*pi_{k+1} + sqrt(k)*pi_{k-1}."""
    p = [1.0]
    if n == 0:
        return p
    p.append(x)
    for k in range(1, n):
        p.append((x * p[k] - math.sqrt(k) * p[k - 1]) / math.sqrt(k + 1))
    return p


def _pi_n(x, n):
    pm, pc = 1.0, x
    if n == 0:
        return 1.0
    for k in range(1, n):
        pm, pc = pc, (x * pc - math.sqrt(k) * pm) / math.sqrt(k + 1)
    return pc


def gauss_hermite(n):
    """Nodes and weights for E[f(Z)], Z~N(0,1), via interlacing bisection."""
    roots = [0.0]  # roots of pi_1
    for k in range(2, n + 1):
        lim = math.sqrt(2.0 * k + 1.0) + 2.0
        bounds = [-lim] + roots + [lim]
        new = []
        for a, b in zip(bounds[:-1], bounds[1:]):
            fa, fb = _pi_n(a, k), _pi_n(b, k)
            if fa == 0.0:
                new.append(a)
                continue
            if fa * fb > 0:
                # widen once at the extremes; otherwise interlacing guarantees a sign change
                continue
            for _ in range(200):
                mid = 0.5 * (a + b)
                fm = _pi_n(mid, k)
                if fm == 0.0 or (b - a) < 1e-15 * max(1.0, abs(mid)):
                    break
                if fa * fm < 0:
                    b = mid
                else:
                    a, fa = mid, fm
            new.append(0.5 * (a + b))
        roots = new
    nodes = roots
    weights = []
    for x in nodes:
        p = orthonormal_hermite(x, n - 1)
        weights.append(1.0 / sum(v * v for v in p))
    return nodes, weights


def gh_sigmas(n, nfloor):
    """Run the flow at the quadrature nodes in double precision."""
    nodes, weights = gauss_hermite(n)
    xs = list(nodes)
    out = []
    for _ in range(nfloor):
        m4 = sum(w * x ** 4 for x, w in zip(xs, weights))
        m2 = sum(w * x ** 2 for x, w in zip(xs, weights))
        s2 = m4 - m2 * m2          # Var(X^2) with the empirical m2 (=1 in exact arith)
        out.append(s2)
        s = math.sqrt(abs(s2))
        xs = [(x * x - m2) / s for x in xs]
    return out


# --------------------------------------------------------------------------

def main():
    res = {"claimed": CLAIMED}

    # POSITIVE CONTROL: the two floors that are Lean theorems must come out exact.
    ctrl = exact_sigmas(2)
    res["positive_control"] = {
        "sigma1_sq": str(ctrl[0]), "sigma1_sq_expected": "2",
        "sigma2_sq": str(ctrl[1]), "sigma2_sq_expected": "14",
        "pass": ctrl[0] == Fraction(2) and ctrl[1] == Fraction(14),
    }
    gn, gw = gauss_hermite(64)
    gh_m4 = sum(w * x ** 4 for x, w in zip(gn, gw))
    gh_m2 = sum(w * x ** 2 for x, w in zip(gn, gw))
    res["positive_control"]["gh64_EZ2"] = gh_m2
    res["positive_control"]["gh64_EZ4"] = gh_m4

    sig2 = exact_sigmas(NFLOOR)
    exact = [math.sqrt(float(s)) for s in sig2]
    res["exact_sigma_sq_num_digits"] = [len(str(s.numerator)) for s in sig2]
    res["exact_sigma"] = exact
    res["exact_sigma_sq_first_two"] = [str(sig2[0]), str(sig2[1])]

    # agreement with the docstring, in significant figures
    agree = []
    for c, e in zip(CLAIMED, exact):
        rel = abs(c - e) / abs(e)
        agree.append({"claimed": c, "exact": e, "rel_err": rel,
                      "sig_figs_matching": (-math.log10(rel) if rel > 0 else 99)})
    res["agreement"] = agree

    # the "logarithms double at each floor" claim
    logs = [math.log(v) for v in exact]
    ratios = [logs[i + 1] / logs[i] for i in range(len(logs) - 1)]
    res["log_sigma"] = logs
    res["log_ratio_consecutive"] = ratios
    res["log_doubling_max_abs_dev_from_2"] = max(abs(r - 2.0) for r in ratios)

    # largest c admissible in exp(c*2^k) <= sigma_k, k=1..7
    cs = [logs[k - 1] / (2 ** k) for k in range(1, NFLOOR + 1)]
    res["growthRate_upper_bounds_per_floor"] = cs
    res["max_admissible_growthRate"] = min(cs)
    res["binding_floor"] = 1 + cs.index(min(cs))

    # Method B
    res["gauss_hermite"] = {}
    for n in (50, 100, 200, 400):
        try:
            g = gh_sigmas(n, NFLOOR)
            gs = [math.sqrt(abs(v)) for v in g]
            res["gauss_hermite"][str(n)] = {
                "sigma": gs,
                "rel_err_vs_exact": [abs(a - b) / b for a, b in zip(gs, exact)],
            }
        except Exception as exc:  # noqa: BLE001
            res["gauss_hermite"][str(n)] = {"error": repr(exc)}

    json.dump(res, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
