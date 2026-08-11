"""ld2d.py -- IS THE LD-CORRELATION DECAY GEOMETRIC IN 2-D, OR MALECOT-BESSEL?

THE CANDIDATE LAW, from the literature and from the 1-D exact solutions.
The exact chain solutions gave rD(0,d) = rD(0,1)^d to within 6% -- geometric in lattice
steps, i.e. EXPONENTIAL in distance. That is the signature of a Green's function of a
SCREENED (killed) random walk: in one dimension the Green's function of the discrete
Laplacian minus a killing rate is exactly geometric, G(d) proportional to lambda^d.
The classical one-locus isolation-by-distance theory (Malecot; Sawyer 1977, Adv. Appl.
Prob. 9:268-282) says the SAME operator in two dimensions has Green's function
K_0(r/L), the modified Bessel function of the second kind -- log-divergent at short
range and e^{-r/L}/sqrt(r) at long range, NOT lambda^r. If the two-locus correlation
inherits that structure, then the 2-D analogue of the geometric law is

    rD(r) proportional to K_0(r / L),   with the SAME decay length L that the 1-D
    nearest-neighbour value pins, and the dimension entering ONLY through the Green's
    function -- an algebraic prefactor, not a different rate.

That is a falsifiable structural claim and this file tests it. THE SOLVES HERE ARE
NUMERIC AND VALIDATE ONLY; what is being tested is the SHAPE of an analytic law.

Conventions as everywhere else: deme diploid size N, time in units of 2N generations,
rho = 4Nc (joint block splits at rho/2), M = 4Nm per EDGE (a block hops to EACH
neighbour at M/2), same-deme coalescence rate 1.
"""
import sys
import time

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import spsolve
from scipy.special import kn
from scipy.optimize import curve_fit

sys.path.insert(0, "/projects/standard/hsiehph/sauer354/theory-out")
import argcore as ac

T0 = time.time()
def tick(m):
    print("[%6.1fs] %s" % (time.time() - T0, m), flush=True)


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


def solve_rD(side, Mv, rv):
    nd, rc, nbr = lattice(side)
    mu = Mv / 2.0
    # ---- pair coalescent (n^2 states), exact linear solve
    r_, c_, v_ = [], [], []
    for u in range(nd):
        for w in range(nd):
            i = u * nd + w
            for x in nbr[u]:
                r_.append(i); c_.append(x * nd + w); v_.append(mu)
                r_.append(i); c_.append(i); v_.append(-mu)
            for x in nbr[w]:
                r_.append(i); c_.append(u * nd + x); v_.append(mu)
                r_.append(i); c_.append(i); v_.append(-mu)
            if u == w:
                r_.append(i); c_.append(i); v_.append(-1.0)
    Q2 = sparse.coo_matrix((v_, (r_, c_)), shape=(nd * nd, nd * nd)).tocsc()
    T2 = spsolve(Q2, -np.ones(nd * nd))
    # ---- two-locus generator
    ts = ac.TwoLocus(nd)
    NS = ts.ns
    r_, c_, v_ = [], [], []
    for i, (si, dm) in enumerate(ts.keys):
        sh = ac.SHAPES[si]; nb = ac.NBLK[si]
        dmu = [dm[sh[u]] for u in range(4)]
        for blk in range(nb):
            for w in nbr[dm[blk]]:
                nd_ = list(dmu)
                for u in range(4):
                    if sh[u] == blk:
                        nd_[u] = w
                r_.append(i); c_.append(ts.mk(list(sh), nd_)); v_.append(mu)
                r_.append(i); c_.append(i); v_.append(-mu)
        for b1 in range(nb):
            for b2 in range(b1 + 1, nb):
                if dm[b1] != dm[b2]:
                    continue
                j = ts.mk([b1 if sh[u] == b2 else sh[u] for u in range(4)], dmu)
                if j is not None:
                    r_.append(i); c_.append(j); v_.append(1.0)
                r_.append(i); c_.append(i); v_.append(-1.0)
        for blk in range(nb):
            units = [u for u in range(4) if sh[u] == blk]
            if not (any(u in ac.AU for u in units) and any(u in ac.BU for u in units)):
                continue
            pr = list(sh); new = max(pr) + 1
            for u in units:
                if u in ac.BU:
                    pr[u] = new
            r_.append(i); c_.append(ts.mk(pr, dmu)); v_.append(rv / 2.0)
            r_.append(i); c_.append(i); v_.append(-rv / 2.0)
    Q = sparse.coo_matrix((v_, (r_, c_)), shape=(NS, NS)).tocsc()
    src = T2[ts.srcA] + T2[ts.srcB]
    P = spsolve(Q, -src)
    S = lambda a, b: (ts.state([((0, 2), a), ((1, 3), b)]),
                      ts.state([((0, 2), a), ((1,), b), ((3,), b)]),
                      ts.state([((0,), a), ((2,), a), ((1, 3), b)]),
                      ts.state([((0,), a), ((2,), a), ((1,), b), ((3,), b)]))
    Nab = lambda a, b: (lambda q: P[q[0]] - P[q[1]] - P[q[2]] + P[q[3]])(S(a, b))
    R = np.zeros((nd, nd))
    for i in range(nd):
        for j in range(nd):
            R[i, j] = Nab(i, j) / np.sqrt(Nab(i, i) * Nab(j, j))
    return R, rc, NS


print(__doc__)
M_GRID = 3.6      # grid2d's 4Nm, per edge
for side in (3, 4, 5):
    print("\n" + "=" * 78)
    for rv in (1.0, 5.0, 20.0):
        R, rc, NS = solve_rD(side, M_GRID, rv)
        tick("%dx%d lattice (%d demes, %d two-locus states), rho=%g solved"
             % (side, side, side * side, NS, rv))
        # centre deme, to keep boundary effects symmetric
        ctr = (side // 2) * side + (side // 2)
        by_d = {}
        for j in range(side * side):
            d = abs(rc[j][0] - rc[ctr][0]) + abs(rc[j][1] - rc[ctr][1])
            if d > 0:
                by_d.setdefault(d, []).append(R[ctr, j])
        ds = sorted(by_d)
        obs = np.array([np.mean(by_d[d]) for d in ds])
        r1 = obs[0]
        geo = np.array([r1 ** d for d in ds])
        # Malecot/Sawyer shape: A*K_0(d/L), two parameters, but L is pinned by the
        # SAME nearest-neighbour value the geometric law uses, so compare like with like:
        # fit L to d=1 only, then predict d>=2 with no further freedom.
        def k0shape(L):
            return np.array([kn(0, d / L) for d in ds])
        Ls = np.logspace(-2, 1.5, 40000)
        # choose L so that K0(2/L)/K0(1/L) is not used -- pin by matching the RATIO at d=1
        # is impossible with one point, so pin L by matching rD(2)/rD(1) is fitting.
        # Honest comparison: one free scale A and one free L, fitted to ALL d, versus the
        # geometric law with its ONE parameter r1 fitted to d=1 only.
        try:
            popt, _ = curve_fit(lambda d, A, L: A * kn(0, np.asarray(d) / L),
                                np.array(ds, float), obs, p0=[1.0, 1.0], maxfev=20000)
            bes = popt[0] * kn(0, np.array(ds, float) / popt[1])
            bfit = "A=%.4f L=%.4f" % (popt[0], popt[1])
        except Exception as e:
            bes = np.full(len(ds), np.nan); bfit = "fit failed: %s" % e
        print("  rho=%-5g  centre deme, rD by Manhattan distance" % rv)
        print("    %3s %11s %11s %9s | %11s %9s" %
              ("d", "exact rD", "geometric", "geo err", "Bessel K0", "K0 err"))
        for k, d in enumerate(ds):
            print("    %3d %11.6f %11.6f %+8.2f%% | %11.6f %+8.2f%%" %
                  (d, obs[k], geo[k], 100 * (geo[k] / obs[k] - 1),
                   bes[k], 100 * (bes[k] / obs[k] - 1)))
        print("    geometric max |err| over d>=2 = %+.2f%%   Bessel (%s) max |err| = %.2f%%"
              % (100 * np.max(np.abs(geo[1:] / obs[1:] - 1)), bfit,
                 100 * np.nanmax(np.abs(bes[1:] / obs[1:] - 1))))
