#!/usr/bin/env python3
"""Measure the graded modulus Delta_K(h) of a nonsmooth functional by linear programming.

Model.  Gaussian location mixture on a bounded interval.  A prior pi on [-A,A] induces the
mixture density f_pi(x) = int phi(x - theta) dpi(theta), phi = standard normal density.
The functional is the canonical nonsmooth one, F(pi) = E_pi |theta|.

Graded modulus.  For grade K (number of matched moments; K = 0 is the ungraded calculus)
and scale h (a total-variation budget on the mixtures),

    Delta_K(h) = sup { F(mu) - F(nu) :  mu, nu probability measures on [-A,A],
                                        int theta^k dmu = int theta^k dnu, k = 1..K,
                                        TV(f_mu, f_nu) <= h }.

Everything in that program is linear in the pair of weight vectors once the support is
discretised, so it is an LP:

    variables  p_i >= 0, q_i >= 0  (weights of mu, nu on the theta grid)
               t_j >= 0            (epigraph variables for |f_mu - f_nu| on the x grid)
    maximise   sum_i |theta_i| (p_i - q_i)
    s.t.       sum_i p_i = 1,  sum_i q_i = 1
               sum_i T_k(theta_i/A) (p_i - q_i) = 0     for k = 1..K
               +/- sum_i (p_i - q_i) phi(x_j - theta_i) - t_j <= 0
               (dx/2) sum_j t_j <= h

Chebyshev polynomials T_1..T_K span the same space as the monomials theta^1..theta^K given
that the masses already match, and are vastly better conditioned on a fine grid.

Controls.
  * With the TV constraint slack, LP duality gives Delta_K = 2 A E_K(|u|) where E_K is the
    best degree-K uniform polynomial approximation error to |u| on [-1,1].  E_K is computed
    independently in bestapprox_control.py, from the approximation side, and validated there
    against the exact anchors E_0 = E_1 = 1/2, E_2 = E_3 = 1/8 and against the Bernstein
    constant.  No code is shared between the two sides.
  * Every reported optimum is re-verified off the LP: the TV of the returned pair is
    recomputed on a 4x finer x grid, and the moment residuals are recomputed in exact
    rational arithmetic from the returned weights.
"""

import json
import os
import sys
import time
from fractions import Fraction

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

SQRT2PI = np.sqrt(2.0 * np.pi)


def normal_pdf(z):
    return np.exp(-0.5 * z * z) / SQRT2PI


def build_design(A, m, dx, pad):
    """Theta grid on [-A,A], x grid on [-A-pad, A+pad], and the mixture matrix."""
    theta = np.linspace(-A, A, m)
    xhi = A + pad
    nx = int(round(2 * xhi / dx)) + 1
    x = np.linspace(-xhi, xhi, nx)
    # Phi[j, i] = phi(x_j - theta_i)
    Phi = normal_pdf(x[:, None] - theta[None, :])
    return theta, x, Phi


def cheb_rows(theta, A, K):
    """Rows T_1..T_K evaluated on the theta grid (scaled to [-1,1])."""
    if K == 0:
        return np.zeros((0, theta.size))
    u = theta / A
    rows = np.empty((K, theta.size))
    Tm1 = np.ones_like(u)
    T = u.copy()
    for k in range(1, K + 1):
        rows[k - 1] = T
        Tm1, T = T, 2 * u * T - Tm1
    return rows


def solve_modulus(A, m, K, h, dx=0.02, pad=8.0, tol=1e-10):
    theta, x, Phi = build_design(A, m, dx, pad)
    nx, _ = Phi.shape
    nv = 2 * m + nx  # p, q, t

    c = np.concatenate([-np.abs(theta), np.abs(theta), np.zeros(nx)])  # minimise -objective

    # equality rows: mass(p)=1, mass(q)=1, Chebyshev moment matching
    Cr = cheb_rows(theta, A, K)
    A_eq = sparse.vstack([
        sparse.hstack([sparse.csr_matrix(np.ones((1, m))), sparse.csr_matrix((1, m)), sparse.csr_matrix((1, nx))]),
        sparse.hstack([sparse.csr_matrix((1, m)), sparse.csr_matrix(np.ones((1, m))), sparse.csr_matrix((1, nx))]),
        sparse.hstack([sparse.csr_matrix(Cr), sparse.csr_matrix(-Cr), sparse.csr_matrix((K, nx))]),
    ], format="csr")
    b_eq = np.concatenate([[1.0, 1.0], np.zeros(K)])

    Inx = sparse.identity(nx, format="csr")
    Psp = sparse.csr_matrix(Phi)
    A_ub = sparse.vstack([
        sparse.hstack([Psp, -Psp, -Inx]),
        sparse.hstack([-Psp, Psp, -Inx]),
        sparse.hstack([sparse.csr_matrix((1, m)), sparse.csr_matrix((1, m)),
                       sparse.csr_matrix(np.full((1, nx), 0.5 * dx))]),
    ], format="csr")
    b_ub = np.concatenate([np.zeros(2 * nx), [h]])

    t0 = time.time()
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=(0, None), method="highs",
                  options=dict(primal_feasibility_tolerance=tol,
                               dual_feasibility_tolerance=tol))
    wall = time.time() - t0
    if not res.success:
        return dict(A=A, m=m, K=K, h=h, ok=False, msg=res.message)

    p = res.x[:m]
    q = res.x[m:2 * m]
    delta = -res.fun

    # ---- independent verification, not reusing the LP's own discretisation ----
    dxf = dx / 4.0
    xf = np.arange(-(A + pad), A + pad + 0.5 * dxf, dxf)
    diff = normal_pdf(xf[:, None] - theta[None, :]) @ (p - q)
    tv_fine = 0.5 * np.trapezoid(np.abs(diff), xf)

    # exact rational moment residuals from the returned weights
    thq = [Fraction(int(round(v * 2 ** 30)), 2 ** 30) for v in theta]
    dq = [Fraction(int(round(v * 2 ** 40)), 2 ** 40) for v in (p - q)]
    mom_exact = []
    for k in range(1, max(K, 4) + 1):
        s = sum(t ** k * d for t, d in zip(thq, dq))
        mom_exact.append(float(s))

    return dict(A=A, m=m, K=K, h=h, ok=True, delta=float(delta),
                tv_lp=float(0.5 * dx * res.x[2 * m:].sum()),
                tv_fine=float(tv_fine),
                mom_exact=mom_exact,
                mass_p=float(p.sum()), mass_q=float(q.sum()),
                support_p=[float(theta[p > 1e-9].min()), float(theta[p > 1e-9].max())] if (p > 1e-9).any() else None,
                natoms_p=int((p > 1e-9).sum()), natoms_q=int((q > 1e-9).sum()),
                wall=wall)


def main():
    which = sys.argv[1]
    out = sys.argv[2]
    results = []
    if which == "noTV":
        # control: TV budget slack, Delta_K should equal 2 A E_K(|u|)
        for A in (1.0, 3.0):
            for m in (201, 401):
                for K in range(0, 9):
                    results.append(solve_modulus(A, m, K, h=10.0))
    elif which == "main":
        hs = [1e-1, 3e-2, 1e-2, 3e-3, 1e-3, 3e-4, 1e-4, 3e-5, 1e-5, 3e-6, 1e-6]
        for A in (1.0, 3.0):
            for K in range(0, 9):
                for h in hs:
                    results.append(solve_modulus(A, 201, K, h))
    elif which == "growA":
        # The module header says the K-free envelope is obtained "by an explicit
        # deconvolution construction at scale sqrt(log(1/h))".  Take it at its word: let the
        # support half-width grow as A(h) = c sqrt(log(1/h)) instead of staying fixed.
        hs = [1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-9]
        for c in (0.7, 1.0, 1.5):
            for h in hs:
                A = c * np.sqrt(np.log(1.0 / h))
                for K in range(0, 9):
                    r = solve_modulus(A, 241, K, h)
                    r["c"] = c
                    results.append(r)
    elif which == "refine":
        hs = [1e-2, 1e-4, 1e-6]
        for m in (101, 201, 401, 801):
            for K in (0, 1, 2, 4, 8):
                for h in hs:
                    results.append(solve_modulus(3.0, m, K, h))
    else:
        raise SystemExit("unknown mode")
    with open(out, "w") as fh:
        json.dump(results, fh, indent=1)
    print("wrote", out, len(results))


if __name__ == "__main__":
    main()
