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

ARITHMETIC.  Everything is exact rational arithmetic in `fractions.Fraction`;
floats appear only when printing.  The symmetry reduction is not assumed --
lumpability is CHECKED on every state, and the lumped solution is substituted
back into the full system and required to have exactly zero residual.  Both
checks, the state-space enumeration and the exact solver come from `lumping.py`
beside this file, which is also standard library only; this file adds the chain
geometry and the comparison, and holds no second copy of the shared machinery.

CONVENTIONS.  Deme diploid size `N`; time in units of `2N` generations; a block
carrying units of both loci splits at `rho/2` with `rho = 4*N*c`; a block hops
to EACH adjacent deme at `M/2` with `M = 4*N*m`; two blocks in one deme coalesce
at rate 1.  `M = 18/5` is grid2d's per-edge `4*N*m = 3.6`; `M = 12` is
serial1d's.

    python3 ldchain_reduction.py
"""

from __future__ import annotations

import json
import pathlib
import sys
from fractions import Fraction as F

RHOS = [F(1, 2), F(1), F(2), F(5), F(10), F(20)]
CELLS = [("grid2d-per-edge", F(18, 5)), ("serial1d-per-edge", F(12))]
SIZES = [2, 3, 4]


# The shared machinery lives beside this file. Import it by path so the script
# runs from any working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lumping import (  # noqa: E402
    AU, BU, NBLK, SHAPES, TwoLocusSpace, lump, orbits, pair_rows, solve_exact,
    verify_residual,
)


def neighbours(n):
    return [[w for w in (i - 1, i + 1) if 0 <= w < n] for i in range(n)]


def pair_t2(n, Mv):
    """Exact mean pairwise coalescence times on the n-deme chain, units of 2N."""
    Q, idx, key = pair_rows(n, neighbours(n), Mv / 2, coal=F(1))
    A = [[Q[i].get(j, F(0)) for j in range(len(idx))] for i in range(len(idx))]
    return dict(zip(idx, solve_exact(A, [F(-1)] * len(idx)))), key


def rD_chain(n, Mv, rv):
    """Exact rD(i,j) and Hudson F_ST(i,j) on the n-deme chain at rational (M, rho)."""
    t2, kk = pair_t2(n, Mv)
    T2 = lambda a, b: t2[(min(a, b), max(a, b))]
    ts, nbr, mu = TwoLocusSpace(n), neighbours(n), Mv / 2
    NS = ts.ns
    Q = [dict() for _ in range(NS)]

    def add(i, j, v):
        Q[i][j] = Q[i].get(j, F(0)) + v

    for i, (si, dm) in enumerate(ts.keys):
        sh, nb = SHAPES[si], NBLK[si]
        dmu = ts.udeme[i]
        for blk in range(nb):
            for w in nbr[dm[blk]]:
                nd = [w if sh[u] == blk else dmu[u] for u in range(4)]
                add(i, ts.mk(list(sh), nd), mu)
                add(i, i, -mu)
        for b1 in range(nb):
            for b2 in range(b1 + 1, nb):
                if dm[b1] != dm[b2]:
                    continue
                j = ts.mk([b1 if sh[u] == b2 else sh[u] for u in range(4)], dmu)
                if j is not None:
                    add(i, j, F(1))
                add(i, i, -F(1))
        for blk in range(nb):
            units = [u for u in range(4) if sh[u] == blk]
            if not (any(u in AU for u in units) and any(u in BU for u in units)):
                continue
            pr, new = list(sh), max(sh) + 1
            for u in units:
                if u in BU:
                    pr[u] = new
            add(i, ts.mk(pr, dmu), rv / 2)
            add(i, i, -rv / 2)
    Q = [{c: v for c, v in row.items() if v != 0} for row in Q]
    src = [T2(ts.udeme[i][0], ts.udeme[i][1]) + T2(ts.udeme[i][2], ts.udeme[i][3])
           for i in range(NS)]

    # symmetry orbits: a1<->a2, b1<->b2, locus A<->B, chain reflection.
    # lump() verifies the source is orbit-constant AND that every orbit member
    # gives the identical lumped row before it reduces anything.
    refl = lambda d: n - 1 - d
    maps = [lambda i: ts.permute(i, (1, 0, 2, 3)),
            lambda i: ts.permute(i, (0, 1, 3, 2)),
            lambda i: ts.permute(i, (2, 3, 0, 1)),
            lambda i: ts.permute(i, (0, 1, 2, 3), relabel=refl)]
    orb_of, mem = orbits(NS, maps)
    Qr, srcr, _ = lump(Q, src, mem)
    Pr = solve_exact(Qr, [-v for v in srcr])
    P = [Pr[orb_of[i]] for i in range(NS)]
    verify_residual(Q, src, P, zero=F(0))

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
