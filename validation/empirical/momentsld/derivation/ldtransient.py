"""ldtransient.py -- THE NON-EQUILIBRIUM (post-split) two-deme LD law.

The equilibrium form in ld2evidence.py does not describe either gnomon demography,
because both are SPLITS OF FINITE AGE: grid2d's demes all split 12000 generations ago,
and serial1d's adjacent pairs split at 201 + (8 - min(i,j))*400 generations and have
exchanged migrants ever since.  This file closes that gap for the two-deme case, and
it closes it in CLOSED FORM rather than by integration, because a split supplies an
exact initial condition.

THE ARGUMENT.  On the post-split interval the generator Q(rho, M) is constant, so the
moment vector obeys the linear inhomogeneous system  dP/ds = -(src + Q P)  (present-ward
s).  Its exact solution with the terminal condition supplied at the split is

    P(present) = P_eq + exp(Q * T) * (P_anc - P_eq),      P_eq = -Q^{-1} src

where T is the split age in units of 2N and P_anc is the ANCESTRAL panmictic solution
mapped through the shape map -- at the split the two demes are one population, so P
depends only on the partition shape and not on the deme labels.  Everything on the right
is exact: P_eq is the rational function already derived, exp(Q T) is the matrix
exponential of the 9x9 LUMPED generator (an eigen-expansion, i.e. a finite sum of
exponentials with algebraic coefficients), and P_anc is the 3-state panmictic solve at
the ancestral size.  No integration and no closure.

THE ANCESTRAL PHASE, and why its size does not complicate the rates: time is in units of
2N with N the DEME size, so the recombination rate per joint block is rho/2 whatever the
population size, while the pairwise coalescence rate in the ancestor is 2N/(2*Nanc) =
N/Nanc, and the ancestral t2 is Nanc/N.  Both are exact rationals for the gnomon values.

RIGOROUS CONSEQUENCE EVEN BEFORE THE NUMBERS: at T = 0 the demes are identical so
rD = 1, and as T -> oo rD -> the equilibrium value.  The transient therefore brackets the
LD slot from BOTH ends, and the width of that bracket is set by the slowest relaxation
mode of Q -- which this file reports as the spectral gap.
"""
import sys
import time

import numpy as np
import sympy as sp
from sympy import QQ
from sympy.polys.matrices import DomainMatrix
from scipy.linalg import expm

sys.path.insert(0, "/projects/standard/hsiehph/sauer354")
sys.path.insert(0, "/projects/standard/hsiehph/sauer354/theory-out")
import argcore as ac

rho = sp.Symbol("rho", positive=True)
ts = ac.TwoLocus(2)
NS = ts.ns

# ---------------------------------------------------------------- orbits (as before)
def apply_perm(i, uperm, swap):
    si, dm = ts.keys[i]
    sh = ac.SHAPES[si]
    dmu = [dm[sh[u]] for u in range(4)]
    inv = [0] * 4
    for u in range(4):
        inv[uperm[u]] = u
    return ts.mk([sh[inv[u]] for u in range(4)],
                 [(1 - dmu[inv[u]]) if swap else dmu[inv[u]] for u in range(4)])

GENS = [((1, 0, 2, 3), False), ((0, 1, 3, 2), False),
        ((2, 3, 0, 1), False), ((0, 1, 2, 3), True)]
orbit_of = [-1] * NS
orbits = []
for i in range(NS):
    if orbit_of[i] >= 0:
        continue
    o = len(orbits); stack, mem = [i], set()
    while stack:
        x = stack.pop()
        if x in mem:
            continue
        mem.add(x); orbit_of[x] = o
        for g in GENS:
            stack.append(apply_perm(x, *g))
    orbits.append(sorted(mem))
NO = len(orbits)
reps = [m[0] for m in orbits]


def build(Mv, rv):
    """lumped generator, source and equilibrium at numeric (M, rho); rates in 2N units."""
    mu = Mv / 2.0
    Q = np.zeros((NS, NS))
    for i, (si, dm) in enumerate(ts.keys):
        sh = ac.SHAPES[si]; nb = ac.NBLK[si]
        dmu = [dm[sh[u]] for u in range(4)]
        for blk in range(nb):
            nd = list(dmu)
            for u in range(4):
                if sh[u] == blk:
                    nd[u] = 1 - dm[blk]
            Q[i, ts.mk(list(sh), nd)] += mu; Q[i, i] -= mu
        for b1 in range(nb):
            for b2 in range(b1 + 1, nb):
                if dm[b1] != dm[b2]:
                    continue
                j = ts.mk([b1 if sh[u] == b2 else sh[u] for u in range(4)], dmu)
                if j is not None:
                    Q[i, j] += 1.0
                Q[i, i] -= 1.0
        for blk in range(nb):
            units = [u for u in range(4) if sh[u] == blk]
            if not (any(u in ac.AU for u in units) and any(u in ac.BU for u in units)):
                continue
            pr = list(sh); new = max(pr) + 1
            for u in units:
                if u in ac.BU:
                    pr[u] = new
            Q[i, ts.mk(pr, dmu)] += rv / 2.0; Q[i, i] -= rv / 2.0
    t2s, t2d = 2.0, (2 * Mv + 1) / Mv
    src = np.array([(t2s if ts.udeme[i, 0] == ts.udeme[i, 1] else t2d)
                    + (t2s if ts.udeme[i, 2] == ts.udeme[i, 3] else t2d) for i in range(NS)])
    Qr = np.array([[Q[ia, orbits[b]].sum() for b in range(NO)] for ia in reps])
    return Q, src, Qr, np.array([src[ia] for ia in reps])


def panmictic_anc(rv, lam, t2anc):
    """3-state panmictic solve in the ANCESTOR: pair coalescence rate lam per 2N unit,
    recombination rho/2, source 2*t2anc.  Returns P by SHAPE (7 shapes)."""
    ts1 = ac.TwoLocus(1)
    Q = np.zeros((7, 7))
    for i, (si, _) in enumerate(ts1.keys):
        sh = ac.SHAPES[si]; nb = ac.NBLK[si]
        for b1 in range(nb):
            for b2 in range(b1 + 1, nb):
                j = ts1.mk([b1 if sh[u] == b2 else sh[u] for u in range(4)], [0] * 4)
                if j is not None:
                    Q[i, j] += lam
                Q[i, i] -= lam
        for blk in range(nb):
            units = [u for u in range(4) if sh[u] == blk]
            if not (any(u in ac.AU for u in units) and any(u in ac.BU for u in units)):
                continue
            pr = list(sh); new = max(pr) + 1
            for u in units:
                if u in ac.BU:
                    pr[u] = new
            Q[i, ts1.mk(pr, [0] * 4)] += rv / 2.0; Q[i, i] -= rv / 2.0
    return np.linalg.solve(Q, -np.full(7, 2.0 * t2anc))


def rD_of(P):
    S = lambda a, b: (ts.state([((0, 2), a), ((1, 3), b)]),
                      ts.state([((0, 2), a), ((1,), b), ((3,), b)]),
                      ts.state([((0,), a), ((2,), a), ((1, 3), b)]),
                      ts.state([((0,), a), ((2,), a), ((1,), b), ((3,), b)]))
    n = lambda a, b: (lambda q: P[q[0]] - P[q[1]] - P[q[2]] + P[q[3]])(S(a, b))
    return n(0, 1) / n(0, 0)


def transient(Mv, rv, T, NoverNanc):
    """rD at split age T (units of 2N), exact closed form, plus the equilibrium value."""
    Q, src, Qr, srcr = build(Mv, rv)
    Peq_r = np.linalg.solve(Qr, -srcr)
    Peq = Peq_r[np.array(orbit_of)]
    Panc_shape = panmictic_anc(rv, NoverNanc, 1.0 / NoverNanc)
    Panc = Panc_shape[ts.shape_of]
    # lumped: P(0) = Peq + expm(Qr*T) (Panc_r - Peq_r)
    Panc_r = np.array([Panc[ia] for ia in reps])
    P0_r = Peq_r + expm(Qr * T) @ (Panc_r - Peq_r)
    return rD_of(P0_r[np.array(orbit_of)]), rD_of(Peq), np.sort(np.linalg.eigvals(Qr).real)[-1]


print(__doc__)
N = 3000.0
UNIT = 2 * N                      # 6000 generations per scaled unit
NoverNanc = N / 10000.0           # ancestral pair-coalescence rate in 2N units = 0.3
RHOS = [0.5, 1.0, 2.0, 5.0, 10.0, 20.0]

print("=" * 78)
print("SANITY GATES ON THE TRANSIENT")
Mv, rv = 12.0, 5.0
r0, req, gap = transient(Mv, rv, 1e-9, NoverNanc)
print("  T -> 0   rD = %.8f   (must be 1: the demes ARE the same population)" % r0)
assert abs(r0 - 1.0) < 1e-6, "T->0 gate failed"
rinf, req2, _ = transient(Mv, rv, 60.0, NoverNanc)
print("  T -> oo  rD = %.8f   equilibrium closed form = %.8f   diff %.2e"
      % (rinf, req2, abs(rinf - req2)))
assert abs(rinf - req2) < 1e-8, "T->oo gate failed"
print("  slowest relaxation eigenvalue of the lumped generator = %.5f per 2N units"
      " (=> %.0f generations)" % (gap, -UNIT / gap))
print("  BOTH GATES PASS: the transient interpolates rD = 1 at the split to the")
print("  equilibrium rational function at infinite age, so it brackets the LD slot.")

print("\n" + "=" * 78)
print("grid2d: ALL demes split at 4N = 12000 generations = %.4f units of 2N; 4Nm = 3.6"
      % (12000.0 / UNIT))
print("  %6s | %10s %12s %10s | %s" % ("rho", "rD(T=2.0)", "rD(equilib)", "ratio",
                                       "how far from equilibrium"))
for rv in RHOS:
    rt, re_, _ = transient(3.6, rv, 12000.0 / UNIT, NoverNanc)
    print("  %6.2f | %10.5f %12.5f %10.3f | transient is %.1f%% ABOVE equilibrium"
          % (rv, rt, re_, rt / re_, 100 * (rt / re_ - 1)))

print("\n" + "=" * 78)
print("serial1d: adjacent pair (k-1,k) split at 201 + (8-(k-1))*400 generations; 4Nm = 12.")
print("Split ages run 201 (the d8-d9 edge) to 3401 (the d0-d1 edge) -- a factor of 17,")
print("which is why the standing Jensen warning bites hardest here.")
print("  %5s %8s %8s |" % ("edge", "T(gen)", "T(2N)") + "".join(" rD@rho=%-5g" % r for r in RHOS))
for k in range(1, 10):
    Tg = 201 + (8 - (k - 1)) * 400
    row = "  %d-%d %8d %8.4f |" % (k - 1, k, Tg, Tg / UNIT)
    for rv in RHOS:
        rt, _, _ = transient(12.0, rv, Tg / UNIT, NoverNanc)
        row += " %10.5f" % rt
    print(row)
print("  equilibrium (T=oo) for comparison:")
row = "  %20s|" % ""
for rv in RHOS:
    _, re_, _ = transient(12.0, rv, 1.0, NoverNanc)
    row += " %10.5f" % re_
print(row)

print("\n" + "=" * 78)
print("THE JENSEN EXPOSURE, MADE QUANTITATIVE.  Averaging rD over the split ages in a")
print("distance bin is NOT the same as rD at the mean split age.  serial1d d=1 bin:")
for rv in [1.0, 5.0, 20.0]:
    ages = [201 + (8 - (k - 1)) * 400 for k in range(1, 10)]
    vals = [transient(12.0, rv, a / UNIT, NoverNanc)[0] for a in ages]
    at_mean = transient(12.0, rv, float(np.mean(ages)) / UNIT, NoverNanc)[0]
    print("  rho=%5g : mean of rD over the 9 edges = %.5f   rD at the mean age = %.5f"
          "   Jensen error %+.2f%%" % (rv, np.mean(vals), at_mean,
                                       100 * (at_mean / np.mean(vals) - 1)))
