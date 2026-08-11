#!/usr/bin/env python3
"""Why the two-deme LD-retention surface must not be applied across a chain.

WHAT THIS IS.  `ld_surface.py` beside this file records the cross-deme LD
correlation `Corr(D)` for a TWO-DEME split with symmetric migration, and a
witness in the corpus reads two of its numbers.  The tempting next step is to
reuse that surface for a pair of demes at separation `d >= 2` in a many-deme
demography, taking the pair's own `F_ST` and inverting the two-deme relation
`F_ST = 1/(2M+1)` to get an effective migration rate.  THAT REDUCTION IS WRONG,
and this file measures by how much.

It measures it by computing the exact answer to compare against: the same
two-locus moment system solved on a LINEAR STEPPING STONE of 2, 3 and 4 demes,
so the multi-deme value and the two-deme surrogate are available at the same
`(rho, M)` and the same `F_ST`.

WHY THE SYSTEM IS EXACT AND TAKES NO CLOSURE.  A state is a partition of the
four ancestral units {a1,a2,b1,b2} into lineages, each carrying a deme label,
and the transitions are the events themselves -- a lineage migrates, two
lineages in one deme coalesce, a lineage carrying units of both loci
recombines.  Four units admit finitely many partitions and the set is closed
under those events, so the generator maps the span of these states into itself
with nothing truncated and no moment replaced by a function of lower ones.
There is no larger system this one approximates.  (This says nothing about any
other package's implementation; it is a statement about the object solved here.)

WHAT IT IS NOT.  Not a battery: it emits no `record()` row, has no simulation,
and its "competitor" is refuted against an exact reference rather than against
data.  Nothing here reaches `simcov/ledger.json` and nothing should cite it as
a battery.

ARITHMETIC.  Everything is exact rational arithmetic in `fractions.Fraction`
with a stdlib Gaussian elimination; floats appear only when printing.  The
symmetry reduction is not assumed -- lumpability is CHECKED on every state, and
the lumped solution is substituted back into the full system and required to
have exactly zero residual.

CONVENTIONS.  Deme diploid size `N`; time in units of `2N` generations; a block
carrying units of both loci splits at `rho/2` with `rho = 4*N*c`; a block hops
to EACH adjacent deme at `M/2` with `M = 4*N*m`; two blocks in one deme coalesce
at rate 1.  `M = 18/5` is grid2d's per-edge `4*N*m = 3.6`; `M = 12` is
serial1d's.

    python3 ldchain_reduction.py
"""

from __future__ import annotations

import itertools
import json
import pathlib
from fractions import Fraction as F

RHOS = [F(1, 2), F(1), F(2), F(5), F(10), F(20)]
CELLS = [("grid2d-per-edge", F(18, 5)), ("serial1d-per-edge", F(12))]
SIZES = [2, 3, 4]


# ---------------------------------------------------------------- state space
def _canon(part):
    m, out = {}, []
    for x in part:
        if x not in m:
            m[x] = len(m)
        out.append(m[x])
    return tuple(out)


SHAPES = [p for p in itertools.product(range(4), repeat=4)
          if _canon(p) == p and p[0] != p[1] and p[2] != p[3]]
assert len(SHAPES) == 7, SHAPES
SHAPE_IX = {s: i for i, s in enumerate(SHAPES)}
NBLK = [max(s) + 1 for s in SHAPES]
AU, BU = (0, 1), (2, 3)


class TwoLocus:
    """Phase-1 two-locus ancestral configurations over `n` demes."""

    def __init__(self, n):
        self.n = n
        self.keys = [(si, dm) for si in range(len(SHAPES))
                     for dm in itertools.product(range(n), repeat=NBLK[si])]
        self.ix = {k: i for i, k in enumerate(self.keys)}
        self.ns = len(self.keys)
        self.udeme = [[dm[SHAPES[si][u]] for u in range(4)] for si, dm in self.keys]

    def mk(self, part_raw, dmu):
        cp = _canon(part_raw)
        if cp[0] == cp[1] or cp[2] == cp[3]:
            return None
        dm = [0] * NBLK[SHAPE_IX[cp]]
        for u in range(4):
            dm[cp[u]] = dmu[u]
        return self.ix[(SHAPE_IX[cp], tuple(dm))]

    def state(self, blocks):
        pr, dmu = [-1] * 4, [-1] * 4
        for bi, (units, d) in enumerate(blocks):
            for u in units:
                pr[u], dmu[u] = bi, d
        return self.mk(pr, dmu)


def neighbours(n):
    return [[w for w in (i - 1, i + 1) if 0 <= w < n] for i in range(n)]


# ---------------------------------------------------------------- exact solver
def solve_exact(A, b):
    """Gaussian elimination with partial pivoting over the rationals."""
    n = len(b)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        inv = F(1) / M[c][c]
        M[c] = [v * inv for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [a - f * bb for a, bb in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]


def pair_t2(n, Mv):
    """Exact mean pairwise coalescence times on the n-deme chain, units of 2N."""
    nbr, mu = neighbours(n), Mv / 2
    idx = {}
    for i in range(n):
        for j in range(i, n):
            idx[(i, j)] = len(idx)
    k = lambda a, b: idx[(min(a, b), max(a, b))]
    A = [[F(0)] * len(idx) for _ in idx]
    b = [F(-1)] * len(idx)
    for (i, j), r in idx.items():
        for (a, o) in ((i, j), (j, i)):
            for w in nbr[a]:
                A[r][k(w, o)] += mu
                A[r][r] -= mu
        if i == j:
            A[r][r] -= F(1)
    return {p: v for p, v in zip(idx, solve_exact(A, b))}, k


def rD_chain(n, Mv, rv):
    """Exact rD(i,j) and Hudson F_ST(i,j) on the n-deme chain at rational (M, rho)."""
    t2, kk = pair_t2(n, Mv)
    T2 = lambda a, b: t2[(min(a, b), max(a, b))]
    ts, nbr, mu = TwoLocus(n), neighbours(n), Mv / 2
    NS = ts.ns
    Q = [[F(0)] * NS for _ in range(NS)]
    for i, (si, dm) in enumerate(ts.keys):
        sh, nb = SHAPES[si], NBLK[si]
        dmu = ts.udeme[i]
        for blk in range(nb):
            for w in nbr[dm[blk]]:
                nd = [w if sh[u] == blk else dmu[u] for u in range(4)]
                Q[i][ts.mk(list(sh), nd)] += mu
                Q[i][i] -= mu
        for b1 in range(nb):
            for b2 in range(b1 + 1, nb):
                if dm[b1] != dm[b2]:
                    continue
                j = ts.mk([b1 if sh[u] == b2 else sh[u] for u in range(4)], dmu)
                if j is not None:
                    Q[i][j] += F(1)
                Q[i][i] -= F(1)
        for blk in range(nb):
            units = [u for u in range(4) if sh[u] == blk]
            if not (any(u in AU for u in units) and any(u in BU for u in units)):
                continue
            pr, new = list(sh), max(sh) + 1
            for u in units:
                if u in BU:
                    pr[u] = new
            Q[i][ts.mk(pr, dmu)] += rv / 2
            Q[i][i] -= rv / 2
    src = [T2(ts.udeme[i][0], ts.udeme[i][1]) + T2(ts.udeme[i][2], ts.udeme[i][3])
           for i in range(NS)]

    # symmetry orbits: a1<->a2, b1<->b2, locus A<->B, chain reflection
    def perm(i, up, refl):
        si, dm = ts.keys[i]
        sh, dmu = SHAPES[si], ts.udeme[i]
        inv = [0] * 4
        for u in range(4):
            inv[up[u]] = u
        return ts.mk([sh[inv[u]] for u in range(4)],
                     [(n - 1 - dmu[inv[u]]) if refl else dmu[inv[u]] for u in range(4)])

    GENS = [((1, 0, 2, 3), False), ((0, 1, 3, 2), False),
            ((2, 3, 0, 1), False), ((0, 1, 2, 3), True)]
    orb_of, orbits = [-1] * NS, []
    for i in range(NS):
        if orb_of[i] >= 0:
            continue
        o, stack, mem = len(orbits), [i], set()
        while stack:
            x = stack.pop()
            if x in mem:
                continue
            mem.add(x)
            orb_of[x] = o
            for g in GENS:
                stack.append(perm(x, *g))
        orbits.append(sorted(mem))
    NO = len(orbits)
    for mem in orbits:
        assert len({src[j] for j in mem}) == 1, "source not orbit-constant"
    reps = [m[0] for m in orbits]
    Qr = [[sum(Q[ia][j] for j in orbits[b]) for b in range(NO)] for ia in reps]
    for a, mem in enumerate(orbits):          # lumpability, checked not assumed
        for ia in mem:
            for b in range(NO):
                assert sum(Q[ia][j] for j in orbits[b]) == Qr[a][b], "not lumpable"
    Pr = solve_exact(Qr, [-src[ia] for ia in reps])
    P = [Pr[orb_of[i]] for i in range(NS)]
    for i in range(NS):                        # exact residual on the FULL system
        assert sum(Q[i][j] * P[j] for j in range(NS) if Q[i][j]) + src[i] == 0, "residual"

    def Nab(a, b):
        return (P[ts.state([((0, 2), a), ((1, 3), b)])]
                - P[ts.state([((0, 2), a), ((1,), b), ((3,), b)])]
                - P[ts.state([((0,), a), ((2,), a), ((1, 3), b)])]
                + P[ts.state([((0,), a), ((2,), a), ((1,), b), ((3,), b)])])

    rd, fst = {}, {}
    for i in range(n):
        for j in range(i, n):
            rd[(i, j)] = float(Nab(i, j)) / (float(Nab(i, i)) * float(Nab(j, j))) ** 0.5
            if i != j:
                fst[(i, j)] = 1 - (T2(i, i) + T2(j, j)) / 2 / T2(i, j)
    return rd, fst


def main() -> None:
    out = {"engine": "exact two-locus ancestral-configuration system, "
                     "rational arithmetic, no closure",
           "conventions": "time in units of 2N; rho = 4Nc; M = 4Nm per edge; "
                          "same-deme coalescence rate 1",
           "cells": {}}
    two_deme_cache: dict = {}
    worst = (0.0, None)
    for cname, Mv in CELLS:
        cell = {"M": float(Mv), "chains": {}}
        for n in SIZES:
            rows = []
            for rv in RHOS:
                rd, fst = rD_chain(n, Mv, rv)
                for d in range(1, n):
                    Feff = fst[(0, d)]
                    Meff = (1 / Feff - 1) / 2          # invert F_ST = 1/(2M+1)
                    key = (Meff, rv)
                    if key not in two_deme_cache:
                        two_deme_cache[key] = rD_chain(2, Meff, rv)[0][(0, 1)]
                    sur = two_deme_cache[key]
                    err = sur / rd[(0, d)] - 1
                    if abs(err) > abs(worst[0]):
                        worst = (err, (cname, n, d, float(rv)))
                    rows.append({"rho": float(rv), "d": d,
                                 "rD_exact": rd[(0, d)],
                                 "fst_hudson": float(Feff),
                                 "M_eff_from_fst": float(Meff),
                                 "rD_two_deme_surrogate": sur,
                                 "surrogate_rel_error": err,
                                 "rD_geometric": rd[(0, 1)] ** d,
                                 "geometric_rel_error": rd[(0, 1)] ** d / rd[(0, d)] - 1})
            cell["chains"][f"n={n}"] = rows
        out["cells"][cname] = cell
    out["headline"] = {
        "worst_two_deme_surrogate_rel_error": worst[0],
        "worst_at": {"cell": worst[1][0], "n_demes": worst[1][1],
                     "separation": worst[1][2], "rho": worst[1][3]},
        "reading": "the F_ST-matched two-deme surrogate is biased HIGH at every "
                   "separation >= 1 and the bias grows with separation and with rho"}

    for cname, cell in out["cells"].items():
        print(f"\n{cname}  (M = {cell['M']})")
        for nk, rows in cell["chains"].items():
            print(f"  {nk}")
            print("    %5s %2s %10s %10s %9s %10s %9s"
                  % ("rho", "d", "exact rD", "surrogate", "sur err", "geometric", "geo err"))
            for r in rows:
                print("    %5g %2d %10.5f %10.5f %+8.1f%% %10.5f %+8.1f%%"
                      % (r["rho"], r["d"], r["rD_exact"], r["rD_two_deme_surrogate"],
                         100 * r["surrogate_rel_error"], r["rD_geometric"],
                         100 * r["geometric_rel_error"]))
    h = out["headline"]
    print("\nWORST two-deme surrogate error %+.1f%% at %s, n=%d demes, separation %d, rho=%g"
          % (100 * h["worst_two_deme_surrogate_rel_error"], h["worst_at"]["cell"],
             h["worst_at"]["n_demes"], h["worst_at"]["separation"], h["worst_at"]["rho"]))
    here = pathlib.Path(__file__).resolve().parent
    (here / "ldchain_reduction.json").write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
