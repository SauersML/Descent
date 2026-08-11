"""ldchain.py -- SYMBOLIC equilibrium two-locus second moments for an n-deme LINEAR
stepping stone (nearest-neighbour migration), extending ld2deme2.py from n=2.

Usage: ldchain.py <n>

Same conventions: deme diploid size N, time in units of 2N generations,
rho := 4Nc (joint block splits at rho/2), M := 4Nm (a block hops to an ADJACENT
deme at M/2 in each available direction), two blocks in one deme coalesce at rate 1.

Reports, for every ordered pair (i,j):
    N_ij  = unnormalised E[D_i D_j]
    rD_ij = N_ij / sqrt(N_ii N_jj)     (the cross-deme LD correlation)
as EXACT rational functions of (rho, M).
"""
import sys
import time
import itertools

import sympy as sp
from sympy import QQ
from sympy.polys.matrices import DomainMatrix

sys.path.insert(0, "/projects/standard/hsiehph/sauer354/theory-out")
import argcore as ac

n = int(sys.argv[1])
# Optional second argument: M as an EXACT RATIONAL (e.g. "18/5" for grid2d's 4Nm=3.6,
# "12" for serial1d's). Specialising M keeps the answer an exact rational function of rho
# -- a closed form at the demography's exact migration rate, not a numerical fill -- and
# avoids the bivariate expression swell that stalls the n>=3 two-symbol solve.
MVAL = sp.Rational(sys.argv[2]) if len(sys.argv) > 2 else None
TAG = "" if MVAL is None else "_M%s" % str(MVAL).replace("/", "over")

T0 = time.time()
def tick(msg):
    print("[%7.1fs] n=%d M=%s %s" % (time.time() - T0, n, MVAL, msg), flush=True)

rho, M = sp.symbols("rho M", positive=True)
if MVAL is None:
    K = QQ.frac_field(rho, M)
    mu = M / 2
else:
    K = QQ.frac_field(rho)
    M = MVAL
    mu = M / 2

# ---------------------------------------------------------------- pair coalescent
# t2[i][j], symbolic, from the structured 2-lineage chain (leaks on coalescence)
pv = [[sp.Symbol("t_%d_%d" % (min(i, j), max(i, j))) for j in range(n)] for i in range(n)]
unk = sorted({pv[i][j] for i in range(n) for j in range(n)}, key=str)
eqs = []
for i in range(n):
    for j in range(i, n):
        acc = sp.Integer(1)
        rate = sp.Integer(0)
        for (a, b) in [(i, j), (j, i)]:
            for w in (a - 1, a + 1):
                if 0 <= w < n:
                    acc += mu * pv[min(w, b)][max(w, b)]
                    rate += mu
        if i == j:
            rate += 1
        eqs.append(sp.Eq(acc - rate * pv[i][j], 0))
psol = sp.solve(eqs, unk, dict=True)[0]
T2 = [[sp.cancel(psol[pv[i][j]]) for j in range(n)] for i in range(n)]
tick("pair coalescent solved; t2[0][0]=%s  t2[0][%d]=%s" % (T2[0][0], n - 1, T2[0][n - 1]))

# ---------------------------------------------------------------- generator
ts = ac.TwoLocus(n)
NS = ts.ns
tick("state space: %d states" % NS)

Q = [dict() for _ in range(NS)]
def add(i, j, v):
    Q[i][j] = Q[i].get(j, sp.Integer(0)) + v

for i, (si, dm) in enumerate(ts.keys):
    sh = ac.SHAPES[si]
    nb = ac.NBLK[si]
    dmu = [dm[sh[u]] for u in range(4)]
    for blk in range(nb):
        for w in (dm[blk] - 1, dm[blk] + 1):
            if not (0 <= w < n):
                continue
            nd = list(dmu)
            for u in range(4):
                if sh[u] == blk:
                    nd[u] = w
            add(i, ts.mk(list(sh), nd), mu)
            add(i, i, -mu)
    for b1 in range(nb):
        for b2 in range(b1 + 1, nb):
            if dm[b1] != dm[b2]:
                continue
            pr = [b1 if sh[u] == b2 else sh[u] for u in range(4)]
            j = ts.mk(pr, dmu)
            if j is not None:
                add(i, j, sp.Integer(1))
            add(i, i, sp.Integer(-1))
    for blk in range(nb):
        units = [u for u in range(4) if sh[u] == blk]
        if not (any(u in ac.AU for u in units) and any(u in ac.BU for u in units)):
            continue
        pr = list(sh)
        new = max(pr) + 1
        for u in units:
            if u in ac.BU:
                pr[u] = new
        add(i, ts.mk(pr, dmu), rho / 2)
        add(i, i, -rho / 2)
for i in range(NS):
    Q[i] = {j: sp.expand(v) for j, v in Q[i].items() if sp.expand(v) != 0}

SRC = [sp.cancel(T2[ts.udeme[i, 0]][ts.udeme[i, 1]] + T2[ts.udeme[i, 2]][ts.udeme[i, 3]])
       for i in range(NS)]
tick("generator built (%d nonzeros)" % sum(len(r) for r in Q))

# ---------------------------------------------------------------- orbits
def apply_perm(i, uperm, reflect):
    si, dm = ts.keys[i]
    sh = ac.SHAPES[si]
    dmu = [dm[sh[u]] for u in range(4)]
    inv = [0] * 4
    for u in range(4):
        inv[uperm[u]] = u
    pr = [sh[inv[u]] for u in range(4)]
    nd = [dmu[inv[u]] for u in range(4)]
    if reflect:
        nd = [n - 1 - d for d in nd]
    return ts.mk(pr, nd)

GENS = [((1, 0, 2, 3), False), ((0, 1, 3, 2), False),
        ((2, 3, 0, 1), False), ((0, 1, 2, 3), True)]
orbit_of = [-1] * NS
orbits = []
for i in range(NS):
    if orbit_of[i] >= 0:
        continue
    o = len(orbits)
    stack, members = [i], set()
    while stack:
        x = stack.pop()
        if x in members:
            continue
        members.add(x)
        orbit_of[x] = o
        for g in GENS:
            stack.append(apply_perm(x, *g))
    orbits.append(sorted(members))
NO = len(orbits)
tick("orbits: %d" % NO)

for o, mem in enumerate(orbits):
    assert len({sp.cancel(SRC[j]) for j in mem}) == 1, ("src not orbit-constant", o)
reps = [mem[0] for mem in orbits]
Qr = [[sp.expand(sum(Q[ia].get(j, 0) for j in orbits[b])) for b in range(NO)] for ia in reps]
Sr = [SRC[ia] for ia in reps]
for a, mem in enumerate(orbits):
    for ia in mem:
        for b in range(NO):
            assert sp.expand(sum(Q[ia].get(j, 0) for j in orbits[b]) - Qr[a][b]) == 0, \
                ("not lumpable", a, ia, b)
tick("lumpability verified exactly on all %d states" % NS)

A = DomainMatrix([[K.from_sympy(Qr[i][j]) for j in range(NO)] for i in range(NO)], (NO, NO), K)
b = DomainMatrix([[K.from_sympy(-Sr[i])] for i in range(NO)], (NO, 1), K)
X = A.lu_solve(b).to_Matrix()
Pr = [sp.cancel(X[i]) for i in range(NO)]
tick("reduced %dx%d system solved over QQ(rho,M)" % (NO, NO))
Pfull = [Pr[orbit_of[i]] for i in range(NS)]

bad = 0
for i in range(NS):
    r = sp.cancel(sum(v * Pfull[j] for j, v in Q[i].items()) + SRC[i])
    if r != 0:
        bad += 1
        print("  RESIDUAL NONZERO at state %d" % i, flush=True)
assert bad == 0
tick("FULL %d-equation residual exactly zero" % NS)

# ---------------------------------------------------------------- LD moments
def N_ab(a, bb):
    s_pp = ts.state([((0, 2), a), ((1, 3), bb)])
    s_pm = ts.state([((0, 2), a), ((1,), bb), ((3,), bb)])
    s_mp = ts.state([((0,), a), ((2,), a), ((1, 3), bb)])
    s_mm = ts.state([((0,), a), ((2,), a), ((1,), bb), ((3,), bb)])
    return sp.cancel(Pfull[s_pp] - Pfull[s_pm] - Pfull[s_mp] + Pfull[s_mm])

NN = {(i, j): N_ab(i, j) for i in range(n) for j in range(i, n)}
tick("LD moments assembled")

out = open("/projects/standard/hsiehph/sauer354/theory-out/ldchain%d%s_forms.txt" % (n, TAG), "w")
print("\n" + "=" * 78, flush=True)
print("EXACT rD_ij = E[D_i D_j]/sqrt(E[D_i^2] E[D_j^2]) for the %d-deme chain" % n, flush=True)
print("numerical evaluation at representative (rho, M):", flush=True)
cells = [(0.5, None), (1.0, None), (2.0, None), (5.0, None), (10.0, None), (20.0, None)]
if MVAL is None:
    cells = [(0.5, 1.0), (1.0, 1.0), (5.0, 1.0), (1.0, 5.0), (5.0, 5.0), (20.0, 3.6)]
hdr = "  %6s %6s |" % ("rho", "M") + "".join(" rD_0%d  " % j for j in range(1, n))
print(hdr, flush=True)
for (rv, mv) in cells:
    row = "  %6.2f %6s |" % (rv, str(MVAL) if mv is None else mv)
    for j in range(1, n):
        v = NN[(0, j)] / sp.sqrt(NN[(0, 0)] * NN[(j, j)])
        sub = {rho: rv} if mv is None else {rho: rv, M: mv}
        row += " %7.5f" % float(v.subs(sub))
    print(row, flush=True)
for i in range(n):
    for j in range(i, n):
        out.write("N_%d_%d = %s\n" % (i, j, sp.srepr(NN[(i, j)])))
        out.write("N_%d_%d_pretty = %s\n\n" % (i, j, NN[(i, j)]))
out.close()
tick("forms written to theory-out/ldchain%d%s_forms.txt" % (n, TAG))

# free check: interior-pair rD at n>=3 must lie strictly between the n=2 value and 0
print("\nDEGREE SUMMARY (rho, M) of each N_ij numerator/denominator:", flush=True)
for i in range(n):
    for j in range(i, n):
        num, den = sp.fraction(sp.cancel(sp.together(NN[(i, j)])))
        print("  N_%d_%d: num deg (rho,M) = (%d,%d)  den deg = (%d,%d)"
              % (i, j, sp.degree(num, rho), sp.degree(num, M) if MVAL is None else 0,
                 sp.degree(den, rho), sp.degree(den, M)), flush=True)
