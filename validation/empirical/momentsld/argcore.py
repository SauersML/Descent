"""argcore.py -- exact two-locus ARG moment machinery (McVean-2002 route).

IDENTITY (derived, not quoted; see task11_final.md for the derivation).
Under the neutral infinite-sites low-mutation limit, with 1,2 iid draws from deme
`a` and 3,4 iid draws from deme `b`, the unnormalised cross-deme LD second moment is

    N_ab  =  E[T^A_13 T^B_13] - E[T^A_13 T^B_14] - E[T^A_13 T^B_23] + E[T^A_13 T^B_24]

(the population-root terms cancel by exchangeability of 1<->2 and 3<->4), and the
LD correlation is  Corr(D_a,D_b) = N_ab / sqrt(N_aa N_bb).  Setting a=b and dividing
by E[T^A_12 T^B_34] gives sigma_d^2.

MACHINERY.  To get E[T^A_ij T^B_kl] we need only the ancestry of FOUR units of
ancestral material: a1,a2 (locus A) and b1,b2 (locus B).  A state is a partition of
{a1,a2,b1,b2} into blocks (= ancestral lineages) with a1 !~ a2 and b1 !~ b2 ("phase
1": neither locus has coalesced yet), each block carrying a deme label.  There are
exactly 7 such partitions.  Transitions: migration (a block moves), coalescence
(two blocks in the same deme merge, rate 1/(2Ne)), recombination (a block carrying
both an a-unit and a b-unit splits, rate c).

With tau_A = T^A - t, tau_B = T^B - t and P(S,t) = E[tau_A tau_B | S at t], any
coalescence that merges a1,a2 or b1,b2 sends the product to zero, so those
transitions LEAK, and

    -dP/dt = A(S,t) + B(S,t) + Q1(t) P ,

where A(S,t) = E[tau_A] and B(S,t) = E[tau_B].  Crucially the marginal process of
the two blocks carrying a1 and a2 is exactly the structured PAIR coalescent (rates
do not depend on block content), so A(S,t) = T2(deme(a1), deme(a2); t) -- the same
121-state object ld5.py already validates.  Same for B.
"""
import itertools

import numpy as np
from scipy import sparse

# unit indices: 0 = a1, 1 = a2, 2 = b1, 3 = b2
AU = (0, 1)
BU = (2, 3)


def _canon(part):
    m = {}
    out = []
    for x in part:
        if x not in m:
            m[x] = len(m)
        out.append(m[x])
    return tuple(out)


SHAPES = []
for _p in itertools.product(range(4), repeat=4):
    if _canon(_p) != _p:
        continue
    if _p[0] == _p[1] or _p[2] == _p[3]:
        continue
    SHAPES.append(_p)
SHAPE_IX = {s: i for i, s in enumerate(SHAPES)}
NBLK = [max(s) + 1 for s in SHAPES]
assert len(SHAPES) == 7, SHAPES
# the three sampling configurations that the sigma_d^2 identity needs
IX_4CHR = SHAPE_IX[(0, 1, 2, 3)]                       # E[T^A_12 T^B_34]
IX_3CHR = [i for i, s in enumerate(SHAPES) if NBLK[i] == 3]   # E[T^A_12 T^B_13]
IX_2CHR = [i for i, s in enumerate(SHAPES) if NBLK[i] == 2]   # E[T^A_12 T^B_12]


class TwoLocus:
    """Phase-1 two-locus lineage-configuration state space over `n` demes."""

    def __init__(self, n):
        self.n = n
        keys = []
        for si in range(len(SHAPES)):
            for dm in itertools.product(range(n), repeat=NBLK[si]):
                keys.append((si, dm))
        self.keys = keys
        self.ix = {k: i for i, k in enumerate(keys)}
        self.ns = len(keys)
        ud = np.empty((self.ns, 4), dtype=np.int64)
        for i, (si, dm) in enumerate(keys):
            sh = SHAPES[si]
            for u in range(4):
                ud[i, u] = dm[sh[u]]
        self.udeme = ud
        self.srcA = ud[:, 0] * n + ud[:, 1]     # gather index into flat T2
        self.srcB = ud[:, 2] * n + ud[:, 3]
        self.shape_of = np.array([si for si, _ in keys], dtype=np.int64)

    def mk(self, part_raw, dmu):
        """State index for raw partition labels + per-unit demes; None if it leaks."""
        cp = _canon(part_raw)
        if cp[0] == cp[1] or cp[2] == cp[3]:
            return None
        si = SHAPE_IX[cp]
        dm = [0] * NBLK[si]
        for u in range(4):
            dm[cp[u]] = dmu[u]
        return self.ix[(si, tuple(dm))]

    def state(self, blocks):
        """blocks: list of (tuple-of-units, deme). Returns the state index."""
        pr = [-1] * 4
        dmu = [-1] * 4
        for bi, (units, d) in enumerate(blocks):
            for u in units:
                pr[u] = bi
                dmu[u] = d
        assert min(pr) >= 0, blocks
        return self.mk(pr, dmu)

    def rec_matrix(self):
        """Generator contribution of recombination, per unit rate c."""
        r, c, v = [], [], []
        for i, (si, dm) in enumerate(self.keys):
            sh = SHAPES[si]
            dmu = [dm[sh[u]] for u in range(4)]
            for blk in range(NBLK[si]):
                units = [u for u in range(4) if sh[u] == blk]
                if not (any(u in AU for u in units) and any(u in BU for u in units)):
                    continue
                pr = list(sh)
                new = max(pr) + 1
                for u in units:
                    if u in BU:
                        pr[u] = new
                j = self.mk(pr, dmu)
                r.append(i); c.append(j); v.append(1.0)
                r.append(i); c.append(i); v.append(-1.0)
        return sparse.coo_matrix((v, (r, c)), shape=(self.ns, self.ns)).tocsr()

    def mc_matrix(self, M, Nsz):
        """Generator contribution of migration + coalescence (leaks on A/B coalescence)."""
        nbr = [[(v, M[u, v]) for v in range(self.n) if v != u and M[u, v] > 0]
               for u in range(self.n)]
        r, c, v = [], [], []
        for i, (si, dm) in enumerate(self.keys):
            sh = SHAPES[si]
            nb = NBLK[si]
            dmu = [dm[sh[u]] for u in range(4)]
            for blk in range(nb):
                for (w, rate) in nbr[dm[blk]]:
                    nd = list(dmu)
                    for u in range(4):
                        if sh[u] == blk:
                            nd[u] = w
                    j = self.mk(list(sh), nd)
                    r.append(i); c.append(j); v.append(rate)
                    r.append(i); c.append(i); v.append(-rate)
            for b1 in range(nb):
                for b2 in range(b1 + 1, nb):
                    if dm[b1] != dm[b2]:
                        continue
                    rate = 1.0 / (2.0 * Nsz[dm[b1]])
                    pr = [b1 if sh[u] == b2 else sh[u] for u in range(4)]
                    j = self.mk(pr, dmu)
                    if j is not None:
                        r.append(i); c.append(j); v.append(rate)
                    r.append(i); c.append(i); v.append(-rate)
        return sparse.coo_matrix((v, (r, c)), shape=(self.ns, self.ns)).tocsr()

    def relabel_index(self, perm):
        """P_new[i] = P_old[idx[i]] across an instantaneous deme relabelling."""
        idx = np.empty(self.ns, dtype=np.int64)
        for i, (si, dm) in enumerate(self.keys):
            sh = SHAPES[si]
            dmu = [perm[dm[sh[u]]] for u in range(4)]
            idx[i] = self.mk(list(sh), dmu)
        return idx


def pair_matrix(M, Nsz, n):
    """Generator for the 2-lineage structured coalescent on n^2 states (leaks)."""
    r, c, v = [], [], []
    for u in range(n):
        for w in range(n):
            i = u * n + w
            for x in range(n):
                if x != u and M[u, x] > 0:
                    r.append(i); c.append(x * n + w); v.append(M[u, x])
                    r.append(i); c.append(i); v.append(-M[u, x])
                if x != w and M[w, x] > 0:
                    r.append(i); c.append(u * n + x); v.append(M[w, x])
                    r.append(i); c.append(i); v.append(-M[w, x])
            if u == w:
                rate = 1.0 / (2.0 * Nsz[u])
                r.append(i); c.append(i); v.append(-rate)
    return sparse.coo_matrix((v, (r, c)), shape=(n * n, n * n)).tocsr()


def panmictic_P(N, cvals):
    """Stationary P on the 7 single-deme states: solves 0 = 4N + (Qmc + c Qrec) P."""
    ts1 = TwoLocus(1)
    Qmc = ts1.mc_matrix(np.zeros((1, 1)), np.array([float(N)]))
    Qrec = ts1.rec_matrix()
    src = np.full(ts1.ns, 2.0 * (2.0 * N))          # A + B, each = E[T2] = 2N
    out = np.empty((len(cvals), ts1.ns))
    for k, cc in enumerate(cvals):
        Q = (Qmc + cc * Qrec).toarray()
        out[k] = np.linalg.solve(Q, -src)
    return out, ts1


def sigma_d2_panmictic(N, cvals):
    """sigma_d^2 from the general machinery at one panmictic deme (THE GATE)."""
    P, ts1 = panmictic_P(N, cvals)
    p4 = P[:, IX_4CHR]
    p3 = P[:, IX_3CHR]
    p2 = P[:, IX_2CHR]
    # symmetry check: all 3-chromosome states equal, both 2-chromosome states equal
    spread = max(float(np.abs(p3 / p3[:, :1] - 1.0).max()),
                 float(np.abs(p2 / p2[:, :1] - 1.0).max()))
    num = p2[:, 0] - 2.0 * p3[:, 0] + p4
    return num / p4, spread


# --------------------------------------------------------------------------
# demography parsing -- taken verbatim from ld5.py (validated to 1.8e-10 on T2)
# --------------------------------------------------------------------------
def parse(demo):
    pops = [p.name for p in demo.populations]
    n = len(pops)
    ix = {nm: i for i, nm in enumerate(pops)}
    Nsz = np.array([float(p.initial_size) for p in demo.populations])
    M = np.array(demo.migration_matrix, dtype=float).copy()
    segments = []
    relabels = {}
    t_prev = 0.0
    t_root = None
    for e in sorted(demo.events, key=lambda e: e.time):
        t = float(e.time)
        cls = type(e).__name__
        if t > t_prev:
            segments.append((t_prev, t, M.copy()))
            t_prev = t
        if cls == "MigrationRateChange":
            src, dst = e.source, e.dest
            if src == -1 or dst == -1:
                M[:, :] = float(e.rate)
                np.fill_diagonal(M, 0.0)
            else:
                M[ix[src] if isinstance(src, str) else src,
                  ix[dst] if isinstance(dst, str) else dst] = float(e.rate)
        elif cls == "MassMigration":
            relabels.setdefault(t, {})[ix[e.source]] = ix[e.dest]
        elif cls == "PopulationSplit":
            for dn in e.derived:
                relabels.setdefault(t, {})[ix[dn]] = ix[e.ancestral]
            t_root = t
        else:
            raise RuntimeError(cls)
    if t_prev < t_root:
        segments.append((t_prev, t_root, M.copy()))
    return pops, n, ix, Nsz, segments, relabels, t_root


def solve_ARG(demo, cvals, anc_name="ANC", h=1.0, progress=None):
    """Integrate T2 and P present-ward through the real schedule.

    Returns (P at t=0, shape (len(cvals), ns), TwoLocus space, T2 at t=0 (n,n)).
    Heun (2nd-order) with a 1-generation step; the ancestral phase is solved exactly.
    """
    pops, n, ix, Nsz, segments, relabels, t_root = parse(demo)
    anc = ix[anc_name]
    ts = TwoLocus(n)
    Qrec = ts.rec_matrix()
    nc = len(cvals)
    cv = np.asarray(cvals, dtype=float)[None, :]        # (1, nc)

    # ---- terminal condition at t_root: everything is in ANC, stationary there
    Panc, _ = panmictic_P(Nsz[anc], cvals)              # (nc, 7)
    P = Panc[:, ts.shape_of].T.copy()                   # (ns, nc)
    T2 = np.full(n * n, 2.0 * Nsz[anc])

    times = sorted(relabels.keys(), reverse=True)
    rel_cache = {}
    mat_cache = {}
    for (t0, t1, Mseg) in reversed(segments):
        for tau in times:
            if t0 < tau <= t1:
                perm = np.arange(n)
                for s, d in relabels[tau].items():
                    perm[s] = d
                key = tuple(perm)
                if key not in rel_cache:
                    rel_cache[key] = (ts.relabel_index(perm),
                                      (perm[:, None] * n + perm[None, :]).ravel())
                ip, i2 = rel_cache[key]
                P = P[ip, :]
                T2 = T2[i2]
        mkey = Mseg.tobytes()
        if mkey not in mat_cache:
            mat_cache[mkey] = (ts.mc_matrix(Mseg, Nsz), pair_matrix(Mseg, Nsz, n))
        Qmc, Q2 = mat_cache[mkey]
        nsteps = int(round((t1 - t0) / h))
        for _ in range(nsteps):
            src0 = T2[ts.srcA] + T2[ts.srcB]
            k1T = 1.0 + Q2 @ T2
            k2T = 1.0 + Q2 @ (T2 + h * k1T)
            T2 = T2 + 0.5 * h * (k1T + k2T)
            src1 = T2[ts.srcA] + T2[ts.srcB]
            k1 = src0[:, None] + (Qmc @ P) + cv * (Qrec @ P)
            Pt = P + h * k1
            k2 = src1[:, None] + (Qmc @ Pt) + cv * (Qrec @ Pt)
            P = P + 0.5 * h * (k1 + k2)
        if progress:
            progress(t0, t1)
    for tau in times:
        if tau == 0:
            perm = np.arange(n)
            for s, d in relabels[tau].items():
                perm[s] = d
            P = P[ts.relabel_index(perm), :]
            T2 = T2[(perm[:, None] * n + perm[None, :]).ravel()]
    return P, ts, T2.reshape(n, n)


def ld_moments(P, ts, a, b):
    """Unnormalised E[D_a D_b] per recombination value; P has shape (ns, nc)."""
    s_pp = ts.state([((0, 2), a), ((1, 3), b)])          # chr1={a1,b1}@a chr3={a2,b2}@b
    s_pm = ts.state([((0, 2), a), ((1,), b), ((3,), b)])  # T^A_13 T^B_14
    s_mp = ts.state([((0,), a), ((2,), a), ((1, 3), b)])  # T^A_13 T^B_23
    s_mm = ts.state([((0,), a), ((2,), a), ((1,), b), ((3,), b)])
    return P[s_pp, :] - P[s_pm, :] - P[s_mp, :] + P[s_mm, :]


def pqpq_moment(P, ts, a, b):
    """Unnormalised E[p(1-p)q(1-q)] = E[T^A_13 T^B_24], the sigma_d^2 denominator."""
    return P[ts.state([((0,), a), ((2,), a), ((1,), b), ((3,), b)]), :]


# ---------------------------------------------------------------- interpolation
def cheb_nodes(nn, xmax):
    """Chebyshev-Gauss-Lobatto nodes on [0, xmax], ascending."""
    k = np.arange(nn)
    return 0.5 * xmax * (1.0 - np.cos(np.pi * k / (nn - 1)))


def cheb_bary(xn, fv, xq):
    """Barycentric interpolation of a 1-D f from CGL nodes `xn` (ascending) onto `xq`.

    An affine change of variable leaves the barycentric weights unchanged up to a
    common factor that cancels, so the CGL weights (-1)^k (halved at the ends) apply
    directly to the mapped nodes.
    """
    nn = len(xn)
    w = (-1.0) ** np.arange(nn)
    w[0] *= 0.5
    w[-1] *= 0.5
    dx = xq[:, None] - xn[None, :]
    hit = np.isclose(dx, 0.0)
    dx = np.where(hit, 1.0, dx)
    q = np.where(hit, 0.0, w[None, :] / dx)
    out = (q @ fv) / q.sum(axis=1)
    rows, cols = np.nonzero(hit)
    out[rows] = fv[cols]
    return out
