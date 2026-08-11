"""ld2d_iter.py -- the 2-D lattice test, scored MECHANICALLY against ld2d_prereg.md.

WHY THIS FILE EXISTS RATHER THAN ld2d.py FINISHING.  ld2d.py used a sparse DIRECT
solve (scipy spsolve / SuperLU).  It completed 3x3 (9639 states) in minutes and then
spent 58 minutes on 4x4 (82432 states) at 5.2 GB of resident memory and still
climbing, which is fill-in: the two-locus state space is a four-fold product of the
lattice, so its graph has large separators and a direct factorisation densifies.
5x5 (454375 states) is out of reach that way, and 5x5 is required -- the
pre-registration's inconclusive branch is decided by comparing L fitted on 4x4
against L fitted on 5x5.  So the direct solve cannot deliver the test at all, and the
solver is replaced by an iterative one (BiCGSTAB, Jacobi-preconditioned), which needs
no factorisation and therefore no fill-in.

THIS IS NOT A CHANGE TO THE PRE-REGISTRATION, and the distinction matters.  Solver
choice is not one of the pre-registered degrees of freedom: the criteria fix a SHAPE
tolerance and an L-match tolerance, both stated in the file at md5
ae7c6da9739b718ba348a5a60c7dc5e2, and neither mentions how the linear system is
solved.  The prereg does say spsolve is accurate to ~1e-10 so that residuals above
1e-8 are model error; the iterative solve is held to a TIGHTER standard than that --
every solve below asserts a relative residual under 1e-12 -- and, as the equivalence
proof, reproduces the already-published 3x3 numbers that are in ld2d.log.  Those 3x3
numbers were read and declared uninformative long ago, so checking against them
breaks no blind.

SCORING IS PERFORMED BY THIS SCRIPT, not by me reading numbers and deciding.  The two
criteria and the inconclusive branch are coded below exactly as filed, and the script
prints the branch it lands in.

ONE READING OF THE FILED TEXT I HAD TO FIX, and I fix it in the least discretionary
direction.  The prereg lists the 1-D target L at each rho as TWO numbers, the n=3 and
n=4 chain values, without selecting between them -- and it justifies the 15% tolerance
by the spread between them.  The least discretionary reading is therefore that the
target is the INTERVAL they span, and the fitted L passes if it lies within 15% of
that interval (i.e. within 15% of the nearer endpoint, or inside it).  Both endpoints
are printed so anyone can re-score under a stricter reading.
"""

import sys
import time

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import bicgstab, LinearOperator
from scipy.special import kn
from scipy.optimize import curve_fit

sys.path.insert(0, "/projects/standard/hsiehph/sauer354/theory-out")
import argcore as ac

T0 = time.time()
def tick(m):
    print("[%7.1fs] %s" % (time.time() - T0, m), flush=True)

M_GRID = 3.6                       # grid2d's per-edge 4Nm; the only M in scope
RHOS = [1.0, 5.0, 20.0]            # the rho values the prereg carries targets for
# prereg targets: L implied by the 1-D chains, (n=3, n=4), at M = 3.6
L1D = {1.0: (2.3292, 2.2779), 5.0: (1.0592, 1.0528), 20.0: (0.5571, 0.5574)}
SHAPE_TOL = 0.06                   # criterion (a)
L_TOL = 0.15                       # criterion (b), and the inconclusive test
# already published in ld2d.log, used only as the solver-equivalence check
LOGGED_3x3 = {1.0: [0.593569, 0.477509], 5.0: [0.304652, 0.173644],
              20.0: [0.131780, 0.039922]}


def lattice(side):
    nd = side * side
    rc = [(r, c) for r in range(side) for c in range(side)]
    nbr = [[] for _ in range(nd)]
    for i, (r, c) in enumerate(rc):
        for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            r2, c2 = r + dr, c + dc
            if 0 <= r2 < side and 0 <= c2 < side:
                nbr[i].append(r2 * side + c2)
    return nd, rc, nbr


def isolve(Q, b, tag):
    """BiCGSTAB with Jacobi preconditioning; asserts a relative residual < 1e-12."""
    d = Q.diagonal().copy()
    d[d == 0] = 1.0
    Minv = LinearOperator(Q.shape, matvec=lambda x: x / d)
    x, info = bicgstab(Q, b, M=Minv, rtol=1e-14, atol=0.0, maxiter=20000)
    res = np.linalg.norm(Q @ x - b, np.inf) / max(np.linalg.norm(b, np.inf), 1e-300)
    if res > 1e-12:
        x, info = bicgstab(Q, b, x0=x, M=Minv, rtol=1e-15, atol=0.0, maxiter=60000)
        res = np.linalg.norm(Q @ x - b, np.inf) / max(np.linalg.norm(b, np.inf), 1e-300)
    assert res <= 1e-12, "%s: residual %.3e exceeds 1e-12 (info=%s)" % (tag, res, info)
    return x, res


def solve_rD(side, Mv, rv):
    nd, rc, nbr = lattice(side)
    mu = Mv / 2.0
    r_, c_, v_ = [], [], []
    for u in range(nd):
        for w in range(nd):
            i = u * nd + w
            for x in nbr[u]:
                r_ += [i, i]; c_ += [x * nd + w, i]; v_ += [mu, -mu]
            for x in nbr[w]:
                r_ += [i, i]; c_ += [u * nd + x, i]; v_ += [mu, -mu]
            if u == w:
                r_ += [i]; c_ += [i]; v_ += [-1.0]
    Q2 = sparse.coo_matrix((v_, (r_, c_)), shape=(nd * nd, nd * nd)).tocsr()
    T2, r2 = isolve(Q2, -np.ones(nd * nd), "pair(%d)" % side)

    ts = ac.TwoLocus(nd)
    NS = ts.ns
    r_, c_, v_ = [], [], []
    for i, (si, dm) in enumerate(ts.keys):
        sh, nb = ac.SHAPES[si], ac.NBLK[si]
        dmu = [dm[sh[u]] for u in range(4)]
        for blk in range(nb):
            for w in nbr[dm[blk]]:
                nd_ = [w if sh[u] == blk else dmu[u] for u in range(4)]
                r_ += [i, i]; c_ += [ts.mk(list(sh), nd_), i]; v_ += [mu, -mu]
        for b1 in range(nb):
            for b2 in range(b1 + 1, nb):
                if dm[b1] != dm[b2]:
                    continue
                j = ts.mk([b1 if sh[u] == b2 else sh[u] for u in range(4)], dmu)
                if j is not None:
                    r_ += [i]; c_ += [j]; v_ += [1.0]
                r_ += [i]; c_ += [i]; v_ += [-1.0]
        for blk in range(nb):
            units = [u for u in range(4) if sh[u] == blk]
            if not (any(u in ac.AU for u in units) and any(u in ac.BU for u in units)):
                continue
            pr, new = list(sh), max(sh) + 1
            for u in units:
                if u in ac.BU:
                    pr[u] = new
            r_ += [i, i]; c_ += [ts.mk(pr, dmu), i]; v_ += [rv / 2.0, -rv / 2.0]
    Q = sparse.coo_matrix((v_, (r_, c_)), shape=(NS, NS)).tocsr()
    P, res = isolve(Q, -(T2[ts.srcA] + T2[ts.srcB]), "twolocus(%d)" % side)

    S = lambda a, b: (ts.state([((0, 2), a), ((1, 3), b)]),
                      ts.state([((0, 2), a), ((1,), b), ((3,), b)]),
                      ts.state([((0,), a), ((2,), a), ((1, 3), b)]),
                      ts.state([((0,), a), ((2,), a), ((1,), b), ((3,), b)]))
    Nab = lambda a, b: (lambda q: P[q[0]] - P[q[1]] - P[q[2]] + P[q[3]])(S(a, b))
    ctr = (side // 2) * side + (side // 2)
    by_d = {}
    for j in range(nd):
        d = abs(rc[j][0] - rc[ctr][0]) + abs(rc[j][1] - rc[ctr][1])
        if d:
            by_d.setdefault(d, []).append(
                Nab(ctr, j) / (Nab(ctr, ctr) * Nab(j, j)) ** 0.5)
    ds = sorted(by_d)
    return ds, np.array([np.mean(by_d[d]) for d in ds]), NS, max(res, r2)


def fit_k0(ds, obs):
    p, _ = curve_fit(lambda d, A, L: A * kn(0, np.asarray(d, float) / L),
                     np.array(ds, float), obs, p0=[1.0, 1.0], maxfev=40000)
    pred = p[0] * kn(0, np.array(ds, float) / p[1])
    return p[0], p[1], float(np.max(np.abs(pred / obs - 1)))


print(__doc__)
print("=" * 78)
print("SOLVER EQUIVALENCE CHECK against the 3x3 numbers already in ld2d.log")
for rv in RHOS:
    ds, obs, NS, res = solve_rD(3, M_GRID, rv)
    dev = max(abs(obs[k] / LOGGED_3x3[rv][k] - 1) for k in range(2))
    print("  rho=%-5g logged %s  iterative %s  max rel dev %.2e  (residual %.1e)"
          % (rv, LOGGED_3x3[rv], ["%.6f" % v for v in obs[:2]], dev, res), flush=True)
    assert dev < 1e-5, "iterative solver does not reproduce the published 3x3 values"
tick("solver equivalence established")

results = {}
for side in (4, 5, 6):
    for rv in RHOS:
        ds, obs, NS, res = solve_rD(side, M_GRID, rv)
        A, L, err = fit_k0(ds, obs)
        results[(side, rv)] = (ds, obs, A, L, err)
        tick("%dx%d (%d states) rho=%g: d=%s rD=%s | K0 fit A=%.4f L=%.4f maxerr %.2f%%"
             % (side, side, NS, rv, ds, ["%.5f" % v for v in obs], A, L, 100 * err))

print("\n" + "=" * 78)
print("MECHANICAL SCORING against ld2d_prereg.md (md5 ae7c6da9739b718ba348a5a60c7dc5e2)")
print("  criterion (a) SHAPE : max |K0 fit residual| <= %.0f%%" % (100 * SHAPE_TOL))
print("  criterion (b) L     : fitted L within %.0f%% of the 1-D target interval"
      % (100 * L_TOL))
print("  inconclusive branch : |L(4x4)/L(5x5) - 1| > %.0f%%" % (100 * L_TOL))
print()
verdicts = []
for rv in RHOS:
    L4 = results[(4, rv)][3]
    L5 = results[(5, rv)][3]
    incons = abs(L4 / L5 - 1) > L_TOL
    lo, hi = min(L1D[rv]), max(L1D[rv])
    for side in (4, 5, 6):
        ds, obs, A, L, err = results[(side, rv)]
        if L < lo:
            gap = lo / L - 1
        elif L > hi:
            gap = L / hi - 1
        else:
            gap = 0.0
        a_ok, b_ok = err <= SHAPE_TOL, gap <= L_TOL
        print("  rho=%-5g %dx%d : shape err %6.2f%% %-4s | L=%7.4f vs target [%.4f,%.4f]"
              " gap %6.2f%% %-4s" % (rv, side, side, 100 * err, "PASS" if a_ok else "FAIL",
                                     L, lo, hi, 100 * gap, "PASS" if b_ok else "FAIL"))
    print("      L(4x4)=%.4f  L(5x5)=%.4f  differ by %.2f%%  -> %s"
          % (L4, L5, 100 * abs(L4 / L5 - 1),
             "INCONCLUSIVE (lattices too small)" if incons else "internally consistent"))
    if incons:
        verdicts.append("INCONCLUSIVE")
    else:
        a_ok = results[(5, rv)][4] <= SHAPE_TOL
        L = results[(5, rv)][3]
        gap = (lo / L - 1) if L < lo else ((L / hi - 1) if L > hi else 0.0)
        verdicts.append("PASS" if (a_ok and gap <= L_TOL) else
                        ("RULED OUT" if a_ok else "FAIL"))
    print("      BRANCH at rho=%g : %s\n" % (rv, verdicts[-1]))
print("BRANCHES BY RHO: %s" % dict(zip(RHOS, verdicts)))
