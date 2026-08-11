"""ld2deme2.py -- SYMBOLIC equilibrium two-locus second moments for TWO demes.

Same derivation as ld2deme.py but with fraction-field (DomainMatrix over QQ(rho,M))
linear algebra, `cancel` instead of `simplify`, and progress timings.

CONVENTIONS: deme diploid size N, 2 demes, time in units of 2N generations,
rho := 4Nc (block carrying both loci splits at rho/2), M := 4Nm (block migrates at
M/2), two blocks in the same deme coalesce at rate 1.
"""
import sys
import time

import sympy as sp
from sympy import QQ
from sympy.polys.matrices import DomainMatrix

sys.path.insert(0, "/projects/standard/hsiehph/sauer354/theory-out")
import argcore as ac

T0 = time.time()
def tick(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)

rho, M = sp.symbols("rho M", positive=True)
K = QQ.frac_field(rho, M)

# ------------------------------------------------------------------ pair coalescent
mu = M / 2
ts_, td_ = sp.symbols("t_s t_d")
sol = sp.solve([sp.Eq(1 - (1 + 2 * mu) * ts_ + 2 * mu * td_, 0),
                sp.Eq(1 - 2 * mu * td_ + 2 * mu * ts_, 0)], [ts_, td_], dict=True)[0]
T2S, T2D = sp.cancel(sol[ts_]), sp.cancel(sol[td_])
tick("pair coalescent: t2(same)=%s  t2(diff)=%s" % (T2S, T2D))
assert T2S == 2

def t2(da, db):
    return T2S if da == db else T2D

# ------------------------------------------------------------------ full generator
ts = ac.TwoLocus(2)
NS = ts.ns
tick("state space: %d states, %d shapes" % (NS, len(ac.SHAPES)))

Q = [[sp.Integer(0)] * NS for _ in range(NS)]
for i, (si, dm) in enumerate(ts.keys):
    sh = ac.SHAPES[si]
    nb = ac.NBLK[si]
    dmu = [dm[sh[u]] for u in range(4)]
    for blk in range(nb):
        nd = list(dmu)
        for u in range(4):
            if sh[u] == blk:
                nd[u] = 1 - dm[blk]
        j = ts.mk(list(sh), nd)
        Q[i][j] += mu
        Q[i][i] -= mu
    for b1 in range(nb):
        for b2 in range(b1 + 1, nb):
            if dm[b1] != dm[b2]:
                continue
            pr = [b1 if sh[u] == b2 else sh[u] for u in range(4)]
            j = ts.mk(pr, dmu)
            if j is not None:
                Q[i][j] += 1
            Q[i][i] -= 1
    for blk in range(nb):
        units = [u for u in range(4) if sh[u] == blk]
        if not (any(u in ac.AU for u in units) and any(u in ac.BU for u in units)):
            continue
        pr = list(sh)
        new = max(pr) + 1
        for u in units:
            if u in ac.BU:
                pr[u] = new
        j = ts.mk(pr, dmu)
        Q[i][j] += rho / 2
        Q[i][i] -= rho / 2

SRC = [sp.cancel(t2(ts.udeme[i, 0], ts.udeme[i, 1]) + t2(ts.udeme[i, 2], ts.udeme[i, 3]))
       for i in range(NS)]
tick("generator + source built")

# ------------------------------------------------------------------ symmetry orbits
def apply_perm(i, uperm, swap_demes):
    si, dm = ts.keys[i]
    sh = ac.SHAPES[si]
    dmu = [dm[sh[u]] for u in range(4)]
    inv = [0] * 4
    for u in range(4):
        inv[uperm[u]] = u
    pr = [sh[inv[u]] for u in range(4)]
    nd = [dmu[inv[u]] for u in range(4)]
    if swap_demes:
        nd = [1 - d for d in nd]
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
tick("orbits: %d (sizes %s)" % (NO, [len(o) for o in orbits]))

for o, mem in enumerate(orbits):
    vals = {sp.cancel(SRC[j]) for j in mem}
    assert len(vals) == 1, ("src not orbit-constant", o, vals)

reps = [mem[0] for mem in orbits]
Qr = [[sp.expand(sum(Q[ia][j] for j in orbits[b])) for b in range(NO)] for ia in reps]
Sr = [SRC[ia] for ia in reps]

for a, mem in enumerate(orbits):
    for ia in mem:
        for b in range(NO):
            assert sp.expand(sum(Q[ia][j] for j in orbits[b]) - Qr[a][b]) == 0, \
                ("not lumpable", a, ia, b)
tick("lumpability verified exactly on all %d states" % NS)

# ------------------------------------------------------------------ symbolic solve
A = DomainMatrix([[K.from_sympy(Qr[i][j]) for j in range(NO)] for i in range(NO)], (NO, NO), K)
b = DomainMatrix([[K.from_sympy(-Sr[i])] for i in range(NO)], (NO, 1), K)
X = A.lu_solve(b).to_Matrix()
Pr = [sp.cancel(X[i]) for i in range(NO)]
tick("reduced %dx%d system solved over QQ(rho,M)" % (NO, NO))
Pfull = [Pr[orbit_of[i]] for i in range(NS)]

bad = 0
for i in range(NS):
    r = sp.cancel(sum(Q[i][j] * Pfull[j] for j in range(NS) if Q[i][j] != 0) + SRC[i])
    if r != 0:
        bad += 1
        print("  RESIDUAL NONZERO at state %d: %s" % (i, r), flush=True)
assert bad == 0
tick("FULL %d-equation residual is exactly zero" % NS)

# ------------------------------------------------------------------ the LD moments
def N_ab(a, bb):
    s_pp = ts.state([((0, 2), a), ((1, 3), bb)])
    s_pm = ts.state([((0, 2), a), ((1,), bb), ((3,), bb)])
    s_mp = ts.state([((0,), a), ((2,), a), ((1, 3), bb)])
    s_mm = ts.state([((0,), a), ((2,), a), ((1,), bb), ((3,), bb)])
    return sp.cancel(Pfull[s_pp] - Pfull[s_pm] - Pfull[s_mp] + Pfull[s_mm])

def denom(a, bb):
    return sp.cancel(Pfull[ts.state([((0,), a), ((2,), a), ((1,), bb), ((3,), bb)])])

N00, N01 = N_ab(0, 0), N_ab(0, 1)
D00, D01 = denom(0, 0), denom(0, 1)
sd2_within = sp.cancel(N00 / D00)
sd2_cross = sp.cancel(N01 / D01)
corrD = sp.cancel(N01 / N00)
tick("LD moments assembled")

print("\n" + "=" * 78, flush=True)
for nm, ex in [("E[D_0 D_0]  (unnormalised, units (2N)^2)", N00),
               ("E[D_0 D_1]  (unnormalised, units (2N)^2)", N01),
               ("E[p0(1-p0) q0(1-q0)]  (= E[T^A_13 T^B_24], a=b=0)", D00),
               ("E[p0(1-p0) q1(1-q1)]", D01),
               ("sigma_d^2 WITHIN  = E[D_0^2] / E[p0(1-p0)q0(1-q0)]", sd2_within),
               ("sigma_d^2 CROSS   = E[D_0 D_1] / E[p0(1-p0)q1(1-q1)]", sd2_cross),
               ("LD CORRELATION rD = E[D_0 D_1] / E[D_0^2]", corrD)]:
    n_, d_ = sp.fraction(sp.cancel(sp.together(ex)))
    print("\n%s\n   numerator   = %s\n   denominator = %s"
          % (nm, sp.factor(sp.expand(n_)), sp.factor(sp.expand(d_))), flush=True)

# ------------------------------------------------------------------ MANDATORY GATE
print("\n" + "=" * 78, flush=True)
print("MANDATORY FREE VALIDATION: M -> oo reproduces Ohta-Kimura", flush=True)
rhoT = sp.symbols("rho_T", positive=True)
OK = (10 + rhoT) / ((2 + rhoT) * (11 + rhoT))
tgt = sp.cancel(OK.subs(rhoT, 2 * rho))   # rho_T = 4*(2N)*c = 2*rho
print("  Ohta-Kimura at rho_T = 2*rho (total size 2N):  %s" % sp.factor(tgt), flush=True)
for nm, ex in [("sigma_d^2 within", sd2_within), ("sigma_d^2 cross", sd2_cross)]:
    lim = sp.cancel(sp.limit(ex, M, sp.oo))
    print("  lim_{M->oo} %-18s = %s   DIFF = %s"
          % (nm, sp.factor(lim), sp.cancel(lim - tgt)), flush=True)
    assert sp.cancel(lim - tgt) == 0, "M->oo GATE FAILED: " + nm
lim_corr = sp.cancel(sp.limit(corrD, M, sp.oo))
print("  lim_{M->oo} rD = %s  (must be 1)" % lim_corr, flush=True)
assert lim_corr == 1

print("\n  M->0 (isolation):", flush=True)
for nm, ex in [("sigma_d^2 within", sd2_within), ("sigma_d^2 cross", sd2_cross),
               ("rD", corrD), ("E[D_0 D_1]", N01), ("E[D_0^2]", N00)]:
    print("     lim_{M->0} %-18s = %s" % (nm, sp.factor(sp.limit(ex, M, 0))), flush=True)
print("\n  rho->0 (complete linkage):", flush=True)
for nm, ex in [("sigma_d^2 within", sd2_within), ("rD", corrD)]:
    print("     lim_{rho->0} %-16s = %s" % (nm, sp.factor(sp.limit(ex, rho, 0))), flush=True)
print("\n  rho->oo (free recombination), leading order:", flush=True)
for nm, ex in [("rD", corrD)]:
    ser = sp.limit(rho * ex, rho, sp.oo)
    print("     rD ~ (%s)/rho" % sp.factor(ser), flush=True)

print("\n  SVED (2009) island-model comparison: his LIBD steady state gives, for k demes,",
      flush=True)
print("     r_i r_j / r^2 = rho_S := m/(m+(k-1)c)  -> for k=2:  M/(M+rho) in scaled units",
      flush=True)
sved = M / (M + rho)
print("     Sved k=2 prediction  = %s" % sved, flush=True)
print("     EXACT rD             = %s" % sp.factor(corrD), flush=True)
print("     EXACT - Sved         = %s" % sp.factor(sp.cancel(corrD - sved)), flush=True)
for (rv, mv) in [(1, 1), (1, 10), (10, 1), (0.1, 1), (100, 100)]:
    print("       rho=%-6g M=%-6g  exact rD=%.6f   Sved=%.6f"
          % (rv, mv, float(corrD.subs({rho: rv, M: mv})), float(sved.subs({rho: rv, M: mv}))),
          flush=True)

print("\nGATE: PASS", flush=True)

with open("/projects/standard/hsiehph/sauer354/theory-out/ld2deme_forms.txt", "w") as f:
    for k, v in [("N00", N00), ("N01", N01), ("D00", D00), ("D01", D01),
                 ("sd2_within", sd2_within), ("sd2_cross", sd2_cross), ("rD", corrD)]:
        f.write("%s = %s\n" % (k, sp.srepr(sp.cancel(v))))
        f.write("%s_pretty = %s\n\n" % (k, sp.cancel(v)))
tick("forms written to theory-out/ld2deme_forms.txt")
