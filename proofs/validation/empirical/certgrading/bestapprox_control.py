#!/usr/bin/env python3
"""Control for the graded-modulus LP: best uniform polynomial approximation to |u|.

LP duality for the moment problem says that with no statistical-distance constraint,

    sup { E_mu|theta| - E_nu|theta| : mu, nu prob. on [-A,A], moments 1..K matched }
      = 2 A E_K(|u|),   E_K(|u|) = min_{deg p <= K} max_{|u|<=1} | |u| - p(u) |.

E_K is computed here from the *approximation* side (a minimax LP over a grid graded near
the kink) with no code shared with the measure-side LP, so agreement is a genuine check.

Exact anchors, derived by hand and used to validate this script itself:
    E_0 = E_1 = 1/2      (best constant is 1/2)
    E_2 = E_3 = 1/8      (best quadratic is u^2 + 1/8)
Bernstein: E_n(|u|) -> beta/n with beta = 0.2801694990...
"""

import json
import sys

import numpy as np
from scipy.optimize import linprog

BERNSTEIN = 0.2801694990238691


def grid():
    """Chebyshev points plus a geometric refinement near the kink at u = 0."""
    cheb = np.cos(np.linspace(0, np.pi, 4001))
    geo = np.concatenate([np.logspace(-12, 0, 2000), -np.logspace(-12, 0, 2000), [0.0]])
    u = np.unique(np.concatenate([cheb, geo]))
    return u[np.abs(u) <= 1.0]


def best_approx_error(K):
    u = grid()
    n = u.size
    V = np.vander(u, K + 1, increasing=True)      # monomial basis is fine at K <= 8
    # minimise e s.t.  -e <= |u| - V a <= e
    c = np.zeros(K + 2)
    c[-1] = 1.0
    A_ub = np.vstack([
        np.hstack([-V, -np.ones((n, 1))]),
        np.hstack([V, -np.ones((n, 1))]),
    ])
    b_ub = np.concatenate([-np.abs(u), np.abs(u)])
    bounds = [(None, None)] * (K + 1) + [(0, None)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs",
                  options=dict(primal_feasibility_tolerance=1e-10,
                               dual_feasibility_tolerance=1e-10))
    assert res.success, res.message
    a = res.x[:K + 1]
    # verify off-grid on a much finer grid
    uf = np.unique(np.concatenate([np.cos(np.linspace(0, np.pi, 200001)),
                                   np.logspace(-14, 0, 40000),
                                   -np.logspace(-14, 0, 40000), [0.0]]))
    uf = uf[np.abs(uf) <= 1.0]
    err_fine = float(np.max(np.abs(np.abs(uf) - np.vander(uf, K + 1, increasing=True) @ a)))
    return dict(K=K, E_lp=float(res.x[-1]), E_verified=err_fine,
                coeffs=[float(v) for v in a],
                bernstein_ratio=err_fine * (K if K else np.nan) / BERNSTEIN)


def main():
    out = sys.argv[1]
    rows = [best_approx_error(K) for K in range(0, 13)]
    anchors = {"E0_exact": 0.5, "E1_exact": 0.5, "E2_exact": 0.125, "E3_exact": 0.125}
    with open(out, "w") as fh:
        json.dump({"anchors": anchors, "rows": rows, "bernstein": BERNSTEIN}, fh, indent=1)
    for r in rows:
        print(r["K"], r["E_verified"], r["bernstein_ratio"])


if __name__ == "__main__":
    main()
