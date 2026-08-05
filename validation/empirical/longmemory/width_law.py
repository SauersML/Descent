#!/usr/bin/env python3
"""The width law, and whether its w^-3 is the same object as the metric's delta^-3.

Target: Descent/Decision/TransportedMinimax.lean, section "The width law".

Claims under test:
  (W1) for a spectral band of width w,  ||B||^2 = shape/w      -- shape-free exponent
  (W2)                                  ||dB||^2 = shape/w^3   -- shape-free exponent
  (W3) widthLaw_ratio: ||dB||^2 / ||B||^2 = 1/w^2 EXACTLY, with the shape constant
       cancelling, because the SAME `shape` field supplies both norms
  (W4) widthLaw_gives_longMemoryMetric: with eps^2 as the shape constant,
       ||dB||^2 = longMemoryMetric eps w = eps^2/w^3, so the exponent 3 in the conformal
       metric is derived rather than assumed.

Everything is done in exact symbolic arithmetic (sympy) so that the exponents and the ratio
constants are decided, not fitted.  A separate numerical arm re-derives the same exponents
by quadrature on a width sweep, as a check on the symbolic integration.

Bands are L^1-normalised to unit mass, B_w(lam) = (1/w) psi(lam/w), which is the only
normalisation under which W1 and W2 can both hold: it gives ||B||^2 = (int psi^2)/w and
||dB||^2 = (int psi'^2)/w^3.  Note already that the two shape constants are DIFFERENT
integrals of the same psi -- that is what W3 asserts to be equal.

The identification question is settled by computing, for a genuine spectral density family
f_delta(lam) = eps^2 g(lam; delta), three different objects and their delta exponents:
    A = int (d f / d lam)^2 dlam         -- the width law's derivative norm (frequency)
    P = int (d f / d delta)^2 dlam       -- L^2 parameter-derivative norm
    F = (1/4pi) int_{-pi}^{pi} (d log f / d delta)^2 dlam   -- the Whittle information
F is the object that has to appear in a transported estimation floor.  If A and F have
different delta exponents then the width law's 3 and the metric's 3 are not the same 3.
"""

import json
import sys

import sympy as sp

w, d, e, u = sp.symbols("w delta epsilon u", positive=True, real=True)
# lambda must be REAL, not positive: declaring it positive collapses Abs(lambda) to
# lambda and silently corrupts any shape defined with an absolute value (the triangular
# band). Caught by cross-check against coverage-closer's independent quadrature.
lam = sp.Symbol("lambda", real=True)


def band_shapes():
    """L^1-normalised bands of width w, as (name, expression, support)."""
    return [
        ("gaussian",
         sp.exp(-lam ** 2 / (2 * w ** 2)) / (w * sp.sqrt(2 * sp.pi)),
         (-sp.oo, sp.oo)),
        ("lorentzian",
         w / (sp.pi * (w ** 2 + lam ** 2)),
         (-sp.oo, sp.oo)),
        ("raised_cosine",
         (1 + sp.cos(2 * sp.pi * lam / w)) / w,
         (-w / 2, w / 2)),
        ("triangular",
         (1 - sp.Abs(lam) / w) / w,
         (-w, w)),
        ("asymmetric_gamma",
         lam * sp.exp(-lam / w) / w ** 2,
         (0, sp.oo)),
    ]


def analyse_bands():
    rows = []
    print("=== W1/W2/W3: band norms, exact ===")
    print(f"{'shape':<18}{'||B||^2':<22}{'||dB||^2':<24}{'ratio*w^2':<14}")
    for name, B, (a, b) in band_shapes():
        mass = sp.simplify(sp.integrate(B, (lam, a, b)))
        n2 = sp.simplify(sp.integrate(B ** 2, (lam, a, b)))
        dB = sp.diff(B, lam)
        g2 = sp.simplify(sp.integrate(dB ** 2, (lam, a, b)))
        ratio = sp.simplify(sp.simplify(g2 / n2) * w ** 2)
        # exponents, read off exactly
        pn = sp.simplify(sp.log(n2.subs(w, 2) / n2.subs(w, 1)) / sp.log(2))
        pg = sp.simplify(sp.log(g2.subs(w, 2) / g2.subs(w, 1)) / sp.log(2))
        print(f"{name:<18}{str(n2):<22}{str(g2):<24}{str(ratio):<14}")
        rows.append(dict(shape=name, mass=str(mass), normSq=str(n2), gradNormSq=str(g2),
                         normSq_exponent=str(pn), gradNormSq_exponent=str(pg),
                         ratio_times_w2=str(ratio),
                         ratio_times_w2_float=float(sp.N(ratio))))
    print("\n  exponents (exact):")
    for r in rows:
        print(f"    {r['shape']:<18} ||B||^2 ~ w^({r['normSq_exponent']})   "
              f"||dB||^2 ~ w^({r['gradNormSq_exponent']})")
    print("\n  ratio * w^2 as a number (W3 requires exactly 1 for every shape):")
    for r in rows:
        print(f"    {r['shape']:<18}{r['ratio_times_w2_float']:.6f}")

    # the rectangular band, handled separately: its derivative is a pair of deltas
    print("\n  rectangular band: ||B||^2 = 1/w exactly; dB/dlam is a pair of Dirac deltas,")
    print("  so ||dB||^2 = +infinity.  The canonical band shape does not satisfy W2 at all.")
    rect = dict(shape="rectangular", normSq="1/w", gradNormSq="+oo",
                normSq_exponent="-1", gradNormSq_exponent="undefined",
                ratio_times_w2="+oo", ratio_times_w2_float=float("inf"))
    rows.append(rect)
    return rows


def analyse_identification():
    """Three objects on one spectral family, and their delta exponents."""
    print("\n=== W4: is the width law's 3 the metric's 3? ===")
    # Ornstein-Uhlenbeck / Lorentzian spectral density: the family whose memory rate is delta
    f = e ** 2 / (d ** 2 + lam ** 2)
    A = sp.simplify(sp.integrate(sp.diff(f, lam) ** 2, (lam, -sp.oo, sp.oo)))
    P = sp.simplify(sp.integrate(sp.diff(f, d) ** 2, (lam, -sp.oo, sp.oo)))
    logf = sp.log(f)
    F = sp.simplify(sp.integrate(sp.diff(logf, d) ** 2, (lam, -sp.pi, sp.pi)) / (4 * sp.pi))
    F_small = sp.simplify(sp.limit(F * d, d, 0))  # leading behaviour as delta -> 0

    def expo(expr, sym):
        return sp.simplify(sp.log(expr.subs(sym, 2 * sym) / expr) / sp.log(2))

    out = {}
    for name, expr in (("A = int (df/dlam)^2  [width law, frequency derivative]", A),
                       ("P = int (df/ddelta)^2 [L2 parameter derivative]", P),
                       ("F = Whittle information for delta over a FIXED band", F)):
        print(f"\n  {name}")
        print(f"    exact: {sp.simplify(expr)}")
        try:
            print(f"    delta exponent: {expo(expr, d)}")
            print(f"    eps   exponent: {expo(expr, e)}")
            out[name] = dict(expr=str(sp.simplify(expr)),
                             delta_exponent=str(expo(expr, d)),
                             eps_exponent=str(expo(expr, e)))
        except Exception as ex:  # F is not a pure power
            print(f"    not a pure power in delta; leading behaviour as delta->0: "
                  f"{F_small}/delta")
            out[name] = dict(expr=str(sp.simplify(expr)),
                             delta_exponent="not a pure power; ~ %s/delta as delta->0"
                                            % sp.simplify(F_small),
                             eps_exponent="0")
    print(f"\n  Whittle information leading term as delta -> 0:  {F_small}/delta")
    out["F_leading"] = str(F_small)
    return out


def numeric_check():
    """Independent quadrature check of the symbolic exponents, on a width sweep."""
    import numpy as np
    from scipy.integrate import quad
    print("\n=== numeric cross-check of the exponents (quadrature, width sweep) ===")
    shapes = {
        "gaussian": (lambda x, W: np.exp(-x ** 2 / (2 * W ** 2)) / (W * np.sqrt(2 * np.pi)),
                     lambda x, W: -x * np.exp(-x ** 2 / (2 * W ** 2)) / (W ** 3 * np.sqrt(2 * np.pi)),
                     30.0),
        "lorentzian": (lambda x, W: W / (np.pi * (W ** 2 + x ** 2)),
                       lambda x, W: -2 * W * x / (np.pi * (W ** 2 + x ** 2) ** 2),
                       4000.0),
        "asymmetric_gamma": (lambda x, W: x * np.exp(-x / W) / W ** 2 if x > 0 else 0.0,
                             lambda x, W: (np.exp(-x / W) / W ** 2 - x * np.exp(-x / W) / W ** 3) if x > 0 else 0.0,
                             60.0),
    }
    res = {}
    ws = np.array([0.25, 0.5, 1.0, 2.0, 4.0])
    for name, (B, dB, lim) in shapes.items():
        n2, g2 = [], []
        for W in ws:
            n2.append(quad(lambda x: B(x, W) ** 2, -lim * W, lim * W, limit=400)[0])
            g2.append(quad(lambda x: dB(x, W) ** 2, -lim * W, lim * W, limit=400)[0])
        pn = np.polyfit(np.log(ws), np.log(n2), 1)[0]
        pg = np.polyfit(np.log(ws), np.log(g2), 1)[0]
        ratio = np.array(g2) / np.array(n2) * ws ** 2
        print(f"  {name:<18} ||B||^2 ~ w^{pn:+.9f}   ||dB||^2 ~ w^{pg:+.9f}   "
              f"ratio*w^2 = {ratio.mean():.6f} (spread {ratio.std():.2e})")
        res[name] = dict(normSq_exponent=float(pn), gradNormSq_exponent=float(pg),
                         ratio_times_w2=float(ratio.mean()))
    # rectangular: show the derivative norm diverging under grid refinement
    print("\n  rectangular band, ||dB||^2 by finite differences as the grid refines:")
    div = []
    for npt in (1000, 4000, 16000, 64000):
        x = np.linspace(-1.5, 1.5, npt)
        dx = x[1] - x[0]
        Bv = np.where(np.abs(x) <= 0.5, 1.0, 0.0)
        g = np.gradient(Bv, dx)
        val = float(np.trapezoid(g ** 2, x))
        div.append(dict(npoints=npt, value=val))
        print(f"    n={npt:<7} ||dB||^2 = {val:.4e}")
    print("    diverges linearly in the grid resolution, as a pair of deltas must.")
    res["rectangular_divergence"] = div
    return res


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else None
    bands = analyse_bands()
    ident = analyse_identification()
    num = numeric_check()
    if out:
        json.dump(dict(bands=bands, identification=ident, numeric=num), open(out, "w"), indent=1)
        print("\nwrote", out)


if __name__ == "__main__":
    main()
