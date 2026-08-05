#!/usr/bin/env python3
"""Where exactly the width law's exponent parts company with an estimation metric.

For a scale family B_delta(lam) = (1/delta) psi(lam/delta) there are three different
"squared norms of a derivative with respect to delta", and they have three different
exponents.  Computed exactly, for several shapes, so the comparison is decided:

  U = int (dB/ddelta)^2 dlam                 unweighted L^2, what the width law measures
  F = int (dlog B/ddelta)^2 B dlam           the Fisher information of the density
  W = (1/4pi) int_{-pi}^{pi} (dlog f/ddelta)^2 dlam    the Whittle information (fixed band)

The width law's object is U.  The object that has to appear in a transported estimation
floor is W.  If they differ in exponent the identification is a category error.
"""

import json
import sys

import sympy as sp

d = sp.Symbol("delta", positive=True, real=True)
lam = sp.Symbol("lambda", real=True)  # real, not positive: see width_law.py


def shapes():
    return [
        ("gaussian", sp.exp(-lam ** 2 / (2 * d ** 2)) / (d * sp.sqrt(2 * sp.pi)), (-sp.oo, sp.oo)),
        ("lorentzian", d / (sp.pi * (d ** 2 + lam ** 2)), (-sp.oo, sp.oo)),
        ("asymmetric_gamma", lam * sp.exp(-lam / d) / d ** 2, (0, sp.oo)),
    ]


def expo(expr):
    return sp.simplify(sp.log(expr.subs(d, 2 * d) / expr) / sp.log(2))


def main():
    rows = []
    print("scale family B_delta(lam) = (1/delta) psi(lam/delta), exact:")
    print(f"{'shape':<18}{'U = int (dB/dd)^2':<28}{'exp':<6}"
          f"{'F = Fisher of the density':<30}{'exp':<6}")
    for name, B, (a, b) in shapes():
        U = sp.simplify(sp.integrate(sp.diff(B, d) ** 2, (lam, a, b)))
        score = sp.diff(sp.log(B), d)
        F = sp.simplify(sp.integrate(score ** 2 * B, (lam, a, b)))
        eU, eF = expo(U), expo(F)
        print(f"{name:<18}{str(U):<28}{str(eU):<6}{str(F):<30}{str(eF):<6}")
        rows.append(dict(shape=name, U=str(U), U_exponent=str(eU),
                         F=str(F), F_exponent=str(eF)))
    print("\n  U ~ delta^-3 : the width law's unweighted L^2 derivative norm")
    print("  F ~ delta^-2 : the Fisher information of the band read as a density")
    print("  W ~ delta^-1 : the Whittle information for a memory rate over a FIXED")
    print("                 frequency band (computed in width_law.py: exactly 1/(2delta))")
    print("\n  Three objects, three exponents. The width law measures the first;")
    print("  a transported estimation floor needs the third. Two powers of delta apart.")
    json.dump(rows, open(sys.argv[1], "w"), indent=1) if len(sys.argv) > 1 else None


if __name__ == "__main__":
    main()
