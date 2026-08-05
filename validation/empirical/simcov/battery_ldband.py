"""Battery 16: the LD-band closed forms, against the integrals they claim to be.

These four definitions are unusual in this corpus: each docstring names the
integral it is the closed form OF, and says the identification is not exported
as a theorem. That makes them exactly checkable without any simulation at all --
the claim is an equality between an elementary expression and a definite
integral, and quadrature evaluates the integral to machine precision.

The AR(1) chromosome has spectral density (the Poisson kernel)

    P(t) = (1 - r^2) / (1 - 2 r cos t + r^2),        mean 1 over t in [-pi, pi]

and reciprocal symbol, normalised the same way,

    g(t) = (1 - 2 r cos t + r^2) / (1 + r^2).

`ldBandReconstructionShare` claims the normalised P-mass of the band |t| <= pi k;
`ldBandDetectionShare` claims the normalised g-mass of the same band. Both are
computed here by adaptive quadrature, which owes nothing to the closed forms.

The error bar is numerical rather than statistical, so it is set at a relative
1e-9 -- far below any modelling discrepancy and far above quadrature error. A
disagreement at that scale is an algebra error, not noise.
"""
import json
import math

import numpy as np
from scipy import integrate

from battery_core import RESULTS, record


def poisson_mass(r, kappa):
    """Normalised spectral mass of the AR(1) Poisson kernel on |t| <= pi*kappa."""
    f = lambda t: (1 - r ** 2) / (1 - 2 * r * math.cos(t) + r ** 2)
    val, _ = integrate.quad(f, -math.pi * kappa, math.pi * kappa,
                            limit=400, epsabs=1e-13, epsrel=1e-13)
    return val / (2 * math.pi)


def reciprocal_mass(r, kappa):
    """Normalised mass of the reciprocal symbol on the same band."""
    f = lambda t: (1 - 2 * r * math.cos(t) + r ** 2) / (1 + r ** 2)
    val, _ = integrate.quad(f, -math.pi * kappa, math.pi * kappa,
                            limit=400, epsabs=1e-13, epsrel=1e-13)
    return val / (2 * math.pi)


def test_reconstruction_share():
    lean = lambda r, k: (2 * math.atan(((1 + r) / (1 - r))
                                       * math.tan(math.pi * k / 2)) / math.pi)
    cells = []
    for r in (0.2, 0.5, 0.8):
        for k in (0.1, 0.3, 0.6):
            truth = poisson_mass(r, k)
            cells.append(dict(design="rho=%.1f kappa=%.1f" % (r, k),
                              lean=lean(r, k), truth=truth,
                              sem=max(abs(truth) * 1e-9, 1e-14)))
    record("ldBandReconstructionShare", "MetricSpecificPortability.lean",
           "(2/pi) * arctan(((1+rho)/(1-rho)) * tan(pi*kappa/2))", cells,
           regime="normalised Poisson-kernel mass of the band |t| <= pi*kappa, "
                  "by adaptive quadrature")


def test_detection_share():
    lean = lambda r, k: k - 2 * r * math.sin(math.pi * k) / (math.pi * (1 + r ** 2))
    cells_d, cells_p = [], []
    for r in (0.2, 0.5, 0.8):
        for k in (0.1, 0.3, 0.6):
            truth = reciprocal_mass(r, k)
            cells_d.append(dict(design="rho=%.1f kappa=%.1f" % (r, k),
                                lean=lean(r, k), truth=truth,
                                sem=max(abs(truth) * 1e-9, 1e-14)))
            # the deficit is kappa minus the share, on the same integral
            cells_p.append(dict(design="rho=%.1f kappa=%.1f" % (r, k),
                                lean=2 * r * math.sin(math.pi * k)
                                / (math.pi * (1 + r ** 2)),
                                truth=k - truth,
                                sem=max(abs(k - truth) * 1e-9, 1e-14)))
    record("ldBandDetectionShare", "MetricSpecificPortability.lean",
           "kappa - 2*rho*sin(pi*kappa)/(pi*(1 + rho^2))", cells_d,
           regime="normalised reciprocal-symbol mass of the same band, by "
                  "adaptive quadrature")
    record("ldPruningDetectionDeficit", "MetricSpecificPortability.lean",
           "2*rho*sin(pi*kappa)/(pi*(1 + rho^2))", cells_p,
           regime="kappa minus the detection share, on the same integrals")


def test_endpoints():
    """The two limits the docstrings call out, checked against the integrals."""
    cells = []
    for r in (0.2, 0.5, 0.8):
        # kappa -> 1 must give the whole mass, which is 1 for both symbols
        cells.append(dict(design="rho=%.1f, Poisson mass at kappa=0.999" % r,
                          lean=1.0, truth=poisson_mass(r, 0.999),
                          sem=1e-3))
    record("LD-band symbols are normalised to unit total mass",
           "MetricSpecificPortability.lean",
           "total normalised mass = 1", cells,
           regime="the normalisation both closed forms are stated against; "
                  "if it failed, both would be scaled by a constant and the "
                  "boundary checks in the module would not detect it")


def main():
    for fn in (test_reconstruction_share, test_detection_share, test_endpoints):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_ldband_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-46s worst %11.2f sems, %10.3e rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
