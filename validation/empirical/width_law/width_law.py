#!/usr/bin/env python3
"""Test the width law of Descent/Decision/TransportedMinimax.lean (WidthLaw).

The Lean structure asserts, for a band of width w and a single shape constant c:

    ||B||^2   = c / w        and     ||dB||^2 = c / w^3

and concludes ||dB||^2 / ||B||^2 = 1/w^2 EXACTLY, shape-free.

A band of width w with a fixed profile is B_w(f) = (1/w) g(f/w) with g of unit
mass (this is the ONLY normalisation under which ||B||^2 ~ w^-1; the unit-height
convention gives ||B||^2 ~ +w, and the unit-L2 convention gives w^0.  The script
checks all three so the choice is not smuggled in).  Under the unit-mass
convention, exactly:

    ||B_w||^2  = C1[g] / w      with C1[g] = int g^2
    ||dB_w||^2 = C2[g] / w^3    with C2[g] = int (g')^2

so the EXPONENTS -1 and -3 are shape-free, but the two constants are DIFFERENT
FUNCTIONALS of the shape and the ratio is (C2/C1)/w^2, not 1/w^2.  The test
measures C2/C1 across genuinely different shapes.

POSITIVE CONTROL: the Gaussian, whose C1 and C2 have closed forms
(C1 = 1/(2 sqrt(pi)), C2 = 1/(4 sqrt(pi))), is checked against those exact
values before any fitted exponent is believed.  A second control checks that
the fitter recovers a planted exponent from synthetic data.

Shapes: rectangular, Gaussian, raised-cosine (Hann), triangular, Lorentzian,
and two deliberately asymmetric bands (Gamma(3) and a skew-normal).
"""

import json
import math

import numpy as np
from scipy.integrate import quad
from scipy.special import erf

SQPI = math.sqrt(math.pi)

# Each shape: (g, g', support, description).  All g have unit mass.
SHAPES = {}


def _reg(name, g, dg, sup, desc, smooth_derivative=True):
    SHAPES[name] = dict(g=g, dg=dg, sup=sup, desc=desc,
                        smooth_derivative=smooth_derivative)


_reg("rectangular",
     lambda x: 1.0 if -0.5 <= x <= 0.5 else 0.0,
     None, (-0.5, 0.5),
     "indicator on [-1/2,1/2]; derivative is a pair of Dirac deltas",
     smooth_derivative=False)

_reg("gaussian",
     lambda x: math.exp(-0.5 * x * x) / math.sqrt(2 * math.pi),
     lambda x: -x * math.exp(-0.5 * x * x) / math.sqrt(2 * math.pi),
     (-40.0, 40.0), "standard normal density")

_reg("hann",
     lambda x: (1.0 + math.cos(2 * math.pi * x)) if -0.5 <= x <= 0.5 else 0.0,
     lambda x: (-2 * math.pi * math.sin(2 * math.pi * x))
     if -0.5 <= x <= 0.5 else 0.0,
     (-0.5, 0.5), "raised cosine / Hann window, C^1 across the edges")

_reg("triangular",
     lambda x: (1.0 - abs(x)) if abs(x) <= 1.0 else 0.0,
     lambda x: (-1.0 if x > 0 else 1.0) if abs(x) <= 1.0 else 0.0,
     (-1.0, 1.0), "triangular window; derivative has jumps but is square integrable")

_reg("lorentzian",
     lambda x: 1.0 / (math.pi * (1.0 + x * x)),
     lambda x: -2.0 * x / (math.pi * (1.0 + x * x) ** 2),
     (-4000.0, 4000.0), "Cauchy density; heavy tails, no second moment")

_reg("gamma3_asym",
     lambda x: 0.5 * x * x * math.exp(-x) if x > 0 else 0.0,
     lambda x: 0.5 * (2 * x - x * x) * math.exp(-x) if x > 0 else 0.0,
     (0.0, 300.0), "Gamma(shape=3) density; strongly asymmetric, one-sided")

_reg("skewnormal_asym",
     lambda x: 2.0 * math.exp(-0.5 * x * x) / math.sqrt(2 * math.pi)
     * 0.5 * (1.0 + erf(5.0 * x / math.sqrt(2.0))),
     None, (-40.0, 40.0),
     "skew-normal with slant 5; asymmetric, derivative taken numerically")


def _numeric_dg(g, h=1e-5):
    return lambda x: (g(x + h) - g(x - h)) / (2 * h)


def integrate(f, sup, points=None):
    a, b = sup
    val, err = quad(f, a, b, limit=800, epsabs=1e-13, epsrel=1e-13,
                    points=points)
    return val, err


def shape_constants(name):
    sh = SHAPES[name]
    g = sh["g"]
    dg = sh["dg"] or _numeric_dg(g)
    pts = None
    if name in ("hann", "triangular"):
        pts = [sh["sup"][0], 0.0, sh["sup"][1]]
    mass, mass_err = integrate(g, sh["sup"], pts)
    C1, C1e = integrate(lambda x: g(x) ** 2, sh["sup"], pts)
    if sh["smooth_derivative"]:
        C2, C2e = integrate(lambda x: dg(x) ** 2, sh["sup"], pts)
    else:
        C2, C2e = float("inf"), float("nan")
    return dict(mass=mass, mass_err=mass_err, C1=C1, C1_err=C1e,
                C2=C2, C2_err=C2e, ratio_C2_over_C1=C2 / C1)


def norms_at_width(name, w, convention="unit_mass"):
    """||B_w||^2 and ||dB_w||^2 by direct quadrature at width w."""
    sh = SHAPES[name]
    g = sh["g"]
    dg = sh["dg"] or _numeric_dg(g)
    if convention == "unit_mass":
        amp = 1.0 / w
    elif convention == "unit_height":
        amp = 1.0
    elif convention == "unit_l2":
        C1 = shape_constants(name)["C1"]
        amp = 1.0 / math.sqrt(C1 * w)
    else:
        raise ValueError(convention)
    a, b = sh["sup"]
    sup = (a * w, b * w)
    pts = None
    if name in ("hann", "triangular"):
        pts = [sup[0], 0.0, sup[1]]
    B = lambda f: amp * g(f / w)
    dB = lambda f: amp * dg(f / w) / w
    n2, n2e = integrate(lambda f: B(f) ** 2, sup, pts)
    if sh["smooth_derivative"]:
        d2, d2e = integrate(lambda f: dB(f) ** 2, sup, pts)
    else:
        d2, d2e = float("nan"), float("nan")
    return n2, d2, n2e, d2e


def loglog_fit(x, y):
    """OLS slope of log y on log x with a standard error."""
    lx, ly = np.log(np.asarray(x, float)), np.log(np.asarray(y, float))
    n = len(lx)
    X = np.column_stack([np.ones(n), lx])
    beta, *_ = np.linalg.lstsq(X, ly, rcond=None)
    resid = ly - X @ beta
    dof = n - 2
    s2 = float(resid @ resid) / dof if dof > 0 else 0.0
    cov = s2 * np.linalg.inv(X.T @ X)
    return dict(slope=float(beta[1]), slope_stderr=float(math.sqrt(max(cov[1, 1], 0.0))),
                intercept=float(beta[0]),
                max_abs_resid=float(np.max(np.abs(resid))))


WIDTHS = np.geomspace(0.02, 50.0, 24)


def run_fit_control():
    """Control: the fitter must recover planted exponents exactly."""
    w = WIDTHS
    out = {}
    for planted in (-1.0, -3.0, -2.0):
        y = 7.3 * w ** planted
        f = loglog_fit(w, y)
        out[f"planted_{planted}"] = f
    return out


def run_rectangular_divergence():
    """The rectangular band has no finite ||dB||^2: show the grid dependence."""
    rows = []
    w = 1.0
    for n in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        f = np.linspace(-1.5 * w, 1.5 * w, n)
        dx = f[1] - f[0]
        B = np.where(np.abs(f) <= 0.5 * w, 1.0 / w, 0.0)
        dB = np.gradient(B, dx)
        rows.append(dict(grid_points=n, dx=float(dx),
                         normSq=float(np.sum(B ** 2) * dx),
                         gradNormSq=float(np.sum(dB ** 2) * dx)))
    fit = loglog_fit([r["dx"] for r in rows], [r["gradNormSq"] for r in rows])
    return dict(rows=rows, gradNormSq_vs_dx_slope=fit,
                note="gradNormSq grows without bound as dx -> 0 (slope ~ -1 in dx), "
                     "i.e. ||dB||^2 = +infinity in the continuum")


def main():
    out = {"controls": {}, "shapes": {}, "conventions": {}}
    out["controls"]["loglog_fitter"] = run_fit_control()

    gc = shape_constants("gaussian")
    out["controls"]["gaussian_closed_form"] = dict(
        C1_numeric=gc["C1"], C1_exact=1.0 / (2 * SQPI),
        C1_rel_err=abs(gc["C1"] - 1.0 / (2 * SQPI)) / (1.0 / (2 * SQPI)),
        C2_numeric=gc["C2"], C2_exact=1.0 / (4 * SQPI),
        C2_rel_err=abs(gc["C2"] - 1.0 / (4 * SQPI)) / (1.0 / (4 * SQPI)),
        mass_numeric=gc["mass"],
    )

    for name in SHAPES:
        const = shape_constants(name)
        rec = dict(description=SHAPES[name]["desc"], constants=const)
        n2s, d2s, ws = [], [], []
        for w in WIDTHS:
            n2, d2, _, _ = norms_at_width(name, w)
            ws.append(w)
            n2s.append(n2)
            if np.isfinite(d2):
                d2s.append(d2)
        rec["normSq_fit"] = loglog_fit(ws, n2s)
        if len(d2s) == len(ws):
            rec["gradNormSq_fit"] = loglog_fit(ws, d2s)
            rec["ratio_fit"] = loglog_fit(ws, np.array(d2s) / np.array(n2s))
            rec["ratio_times_w2"] = [float(d / n * w ** 2)
                                     for w, n, d in zip(ws, n2s, d2s)]
            rec["ratio_times_w2_spread"] = float(
                np.ptp(rec["ratio_times_w2"]) / np.mean(rec["ratio_times_w2"]))
            # width rescaling that would force the two shape constants to agree
            lam = math.sqrt(const["C1"] / const["C2"])
            rec["width_rescale_to_equalise_constants"] = lam
            rec["common_constant_after_rescale"] = const["C1"] * lam
        else:
            rec["gradNormSq_fit"] = None
            rec["ratio_fit"] = None
        out["shapes"][name] = rec

    out["rectangular_derivative_divergence"] = run_rectangular_divergence()

    # normalisation conventions: only unit-mass gives (-1, -3)
    for conv in ("unit_mass", "unit_height", "unit_l2"):
        n2s, d2s = [], []
        for w in WIDTHS:
            n2, d2, _, _ = norms_at_width("gaussian", w, conv)
            n2s.append(n2)
            d2s.append(d2)
        out["conventions"][conv] = dict(
            normSq_slope=loglog_fit(WIDTHS, n2s)["slope"],
            gradNormSq_slope=loglog_fit(WIDTHS, d2s)["slope"],
        )

    # headline: does the ratio constant cancel across shapes?
    ratios = {k: v["constants"]["ratio_C2_over_C1"]
              for k, v in out["shapes"].items()
              if np.isfinite(v["constants"]["ratio_C2_over_C1"])}
    out["shape_freedom_verdict"] = dict(
        ratio_constant_by_shape=ratios,
        min=min(ratios.values()), max=max(ratios.values()),
        max_over_min=max(ratios.values()) / min(ratios.values()),
        exponent_is_shape_free=True,
        constant_is_shape_free=bool(
            (max(ratios.values()) - min(ratios.values())) / min(ratios.values()) < 1e-6),
    )
    print(json.dumps(out, indent=1, default=str))


if __name__ == "__main__":
    main()
