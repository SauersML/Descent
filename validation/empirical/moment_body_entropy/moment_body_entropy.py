#!/usr/bin/env python3
"""Test the two RATES named (not proved) in the MomentBodyEntropy section of
Descent/PopGen/PolygenicArchitecture.lean.

Class C(M, alpha): positive measures mu on [0,1] with boundary tail
    mu([1-t, 1]) <= M t^alpha   for all t in (0,1].
Moment body: { (m_1, m_2, ...) : m_k = int x^k dmu, mu in C }, metric = l2.

Claimed:
    log N(eps, moment body) = Theta( (M/eps)^(1/alpha) )
    log N(eps, enclosing hyperrectangle) = eps^(-2/(2 alpha - 1))

Instrument 1 (BOX).  The enclosing hyperrectangle is |m_k| <= b_k with
    b_k = sup_{mu in C} m_k = M Gamma(1+a) Gamma(k+1)/Gamma(k+1+a)  ~  M G(1+a) k^-a
(attained by the extremal measure whose right tail saturates M t^alpha).  Its
l2 covering number is computed by exact water-filling over a truncation
dimension d and a per-coordinate resolution: this is the standard sharp
construction, and the exponent it returns is the box rate.
    CONTROLS, run first: (i) a finite-dimensional box, where log N must have
    slope exactly d in log(1/eps); (ii) a geometrically decaying box
    b_k = e^{-gamma k}, whose known rate is (log 1/eps)^2/(2 gamma) -- a
    NON-power rate, included so a machine that returns a power law for
    everything is caught.

Instrument 2 (MOMENT BODY, lower bound).  A Varshamov-Gilbert packing built
from disjoint signed atom pairs in boundary shells, with the tail budget
respected exactly and the near-orthogonality VERIFIED by the smallest
eigenvalue of the actual Gram matrix of moment vectors (not assumed).  This
gives a rigorous-in-form numerical LOWER bound on the moment body's entropy
exponent.  If it exceeds 1/alpha, the claimed rate is refuted.
    CONTROL: the identical VG machinery, fed the box's orthogonal coordinate
    directions, must return the box exponent 2/(2 alpha - 1).

Instrument 3 (ORDERING).  A greedy net over sampled points, applied identically
to moment-body samples and box samples, to check the moment body really is the
smaller set at matched eps.  Biased downward (finite sample); used only for the
ordering, not for an exponent.
"""

import json
import math

import numpy as np
from scipy.special import gammaln

LOG2 = math.log(2.0)


def loglog_fit(x, y):
    lx, ly = np.log(np.asarray(x, float)), np.log(np.asarray(y, float))
    n = len(lx)
    X = np.column_stack([np.ones(n), lx])
    beta, *_ = np.linalg.lstsq(X, ly, rcond=None)
    resid = ly - X @ beta
    dof = max(n - 2, 1)
    s2 = float(resid @ resid) / dof
    cov = s2 * np.linalg.inv(X.T @ X)
    return dict(slope=float(beta[1]), stderr=float(math.sqrt(max(cov[1, 1], 0.0))),
                intercept=float(beta[0]), n=n,
                max_abs_resid=float(np.max(np.abs(resid))))


# ---------------------------------------------------------------------------
# Instrument 1: covering number of a coordinate box in l2, by water-filling
# ---------------------------------------------------------------------------

def box_log_covering(b, eps):
    """log N(eps) for K = {|x_k| <= b_k} in l2, minimised over truncation d.

    Budget split: half the squared radius to the discarded tail, half to the
    retained coordinates.  Within the retained block the optimal allocation of
    a fixed squared budget minimising sum log(b_k/delta_k) is delta_k =
    min(b_k, mu) (water-filling); mu is found by bisection.
    """
    b = np.asarray(b, float)
    n = b.size
    tail = np.concatenate([np.cumsum((b ** 2)[::-1])[::-1][1:], [0.0]])  # tail[d-1]=sum_{k>d}
    ok = np.nonzero(tail <= eps ** 2 / 2.0)[0]
    if ok.size == 0:
        return None
    best = None
    # candidate truncations: the smallest admissible d and a few above it
    cands = sorted(set([int(ok[0])] + [min(n - 1, int(ok[0] * f)) for f in (1.5, 2, 4)]))
    for di in cands:
        d = di + 1
        bb = b[:d]
        budget = eps ** 2 / 2.0
        lo, hi = 0.0, float(bb.max())
        for _ in range(200):
            mu = 0.5 * (lo + hi)
            s = float(np.sum(np.minimum(bb, mu) ** 2))
            if s > budget:
                hi = mu
            else:
                lo = mu
        mu = 0.5 * (lo + hi)
        if mu <= 0:
            continue
        act = bb[bb > mu]
        cost = float(np.sum(np.log(act / mu)))
        if best is None or cost < best[0]:
            best = (cost, d, mu)
    if best is None:
        return None
    return dict(logN=best[0], d=best[1], mu=best[2])


def box_exponent(b, epss):
    xs, ys, ds = [], [], []
    for e in epss:
        r = box_log_covering(b, e)
        if r is None or r["logN"] <= 0:
            continue
        xs.append(1.0 / e)
        ys.append(r["logN"])
        ds.append(r["d"])
    if len(xs) < 3:
        return None
    f = loglog_fit(xs, ys)
    f["truncation_dims"] = ds
    f["eps"] = [1.0 / x for x in xs]
    f["logN"] = ys
    return f


def moment_box_axes(M, alpha, K):
    k = np.arange(1, K + 1, dtype=float)
    return M * np.exp(gammaln(1 + alpha) + gammaln(k + 1) - gammaln(k + 1 + alpha))


def run_box():
    out = {"controls": {}}

    # CONTROL (i): finite-dimensional box.  Known answer log N = d log(1/eps) + O(1):
    # LINEAR in log(1/eps) with slope exactly d, and therefore a power-law exponent
    # of 0.  Both readings are checked.
    for d in (2, 5, 10):
        b = np.ones(d)
        epss = np.geomspace(1e-1, 1e-5, 12)
        ys, xs = [], []
        for e in epss:
            r = box_log_covering(b, e)
            xs.append(math.log(1.0 / e))
            ys.append(r["logN"])
        A = np.column_stack([np.ones(len(xs)), xs])
        beta, *_ = np.linalg.lstsq(A, np.array(ys), rcond=None)
        f = box_exponent(b, epss)
        out["controls"][f"finite_box_d{d}"] = dict(
            slope_of_logN_vs_log_inv_eps=float(beta[1]), expected_that_slope=float(d),
            residual=float(np.max(np.abs(np.array(ys) - A @ beta))),
            power_law_exponent_if_forced=f["slope"], expected_power_exponent=0.0)

    # CONTROL (ii): geometric axes -> known NON-power rate (log 1/eps)^2/(2 gamma)
    gamma = 0.5
    b = np.exp(-gamma * np.arange(1, 4001))
    epss = np.geomspace(1e-2, 1e-12, 14)
    xs, ys = [], []
    for e in epss:
        r = box_log_covering(b, e)
        if r:
            xs.append(e)
            ys.append(r["logN"])
    L = np.log(1.0 / np.array(xs))
    coef = float(np.linalg.lstsq(L[:, None] ** 2, np.array(ys), rcond=None)[0][0])
    out["controls"]["geometric_axes"] = dict(
        gamma=gamma, fitted_coef_of_log2=coef, expected_coef=1.0 / (2 * gamma),
        power_law_slope_if_forced=loglog_fit(1.0 / np.array(xs), ys)["slope"],
        note="known rate is (log 1/eps)^2/(2 gamma); a power-law fit here is a bad fit "
             "by construction, which is what makes this a discriminating control")

    # THE TEST: the true enclosing hyperrectangle of the moment class
    out["hyperrectangle"] = {}
    M = 1.0
    for alpha, emin, K in ((1.0, 3e-3, 1500000), (1.5, 1e-5, 1500000),
                           (2.0, 1e-7, 400000), (3.0, 1e-9, 200000)):
        b = moment_box_axes(M, alpha, K)
        epss = np.geomspace(emin * 300, emin, 10)
        f = box_exponent(b, epss)
        out["hyperrectangle"][f"alpha_{alpha}"] = dict(
            fitted_slope=f["slope"], stderr=f["stderr"],
            claimed_2_over_2a_minus_1=2.0 / (2 * alpha - 1),
            alternative_1_over_alpha=1.0 / alpha,
            max_abs_log_resid=f["max_abs_resid"],
            truncation_dims=f["truncation_dims"],
            eps=f["eps"], logN=f["logN"],
        )
    return out


# ---------------------------------------------------------------------------
# Instrument 2: Varshamov-Gilbert packing of the moment body
# ---------------------------------------------------------------------------

def _f_geom(x):
    """sum_{n>=1} x^n = x/(1-x), used to get the moment-space Gram in closed form."""
    return x / (1 - x)


def exact_gram(atoms, masses):
    """Gram matrix of the moment vectors of signed atom pairs, computed EXACTLY.

    Direction j is masses[j] * (delta_{a_j} - delta_{b_j}); its moment vector is
    v_j[n] = m_j (a_j^n - b_j^n) for n = 1, 2, ... (the FULL, untruncated moment
    sequence -- no truncation error enters).  Then

        <v_j, v_k> = m_j m_k [ f(a_j a_k) - f(a_j b_k) - f(b_j a_k) + f(b_j b_k) ]

    with f(x) = x/(1-x).  Evaluated at mpmath precision so that the small
    eigenvalues -- which is exactly where a float64 Gram collapses to zero --
    are resolved.
    """
    import mpmath as mp
    K = len(atoms)
    G = mp.matrix(K, K)
    a = [mp.mpf(x[0]) for x in atoms]
    b = [mp.mpf(x[1]) for x in atoms]
    m = [mp.mpf(x) for x in masses]
    for j in range(K):
        for k in range(j, K):
            val = m[j] * m[k] * (_f_geom(a[j] * a[k]) - _f_geom(a[j] * b[k])
                                 - _f_geom(b[j] * a[k]) + _f_geom(b[j] * b[k]))
            G[j, k] = val
            G[k, j] = val
    return G


def pivoted_cholesky_logdets(G, rmax):
    """Greedy pivoted Cholesky.  Returns the running list of (r, log det of the
    best r x r principal minor found greedily), which is 2 log vol_r of the
    parallelepiped spanned by the chosen r directions."""
    import mpmath as mp
    K = G.rows
    A = mp.matrix(G)
    idx = list(range(K))
    logdet = mp.mpf(0)
    out = []
    for r in range(min(rmax, K)):
        # pick the remaining index with the largest Schur diagonal
        best, bestv = -1, mp.mpf(0)
        for i in range(r, K):
            if A[i, i] > bestv:
                bestv, best = A[i, i], i
        if best < 0 or bestv <= 0:
            break
        if best != r:
            for c in range(K):
                A[r, c], A[best, c] = A[best, c], A[r, c]
            for rr in range(K):
                A[rr, r], A[rr, best] = A[rr, best], A[rr, r]
            idx[r], idx[best] = idx[best], idx[r]
        piv = A[r, r]
        logdet += mp.log(piv)
        for i in range(r + 1, K):
            fac = A[i, r] / piv
            for jj in range(r + 1, K):
                A[i, jj] -= fac * A[r, jj]
        out.append((r + 1, float(logdet)))
    return out


def volumetric_bound(logdets, epss):
    """log N(eps) >= (1/2) log det G_r + r log(1/eps) - log vol(unit r-ball),
    maximised over r.  This is the standard volume lower bound for the covering
    number of the zonotope {sum_j c_j v_j : c in [0,1]^K}, which is contained in
    the moment body by construction."""
    rows = []
    for e in epss:
        best, bestr = None, None
        for r, ld in logdets:
            logvolball = (r / 2.0) * math.log(math.pi) - gammaln(r / 2.0 + 1.0)
            val = 0.5 * ld + r * math.log(1.0 / e) - logvolball
            if best is None or val > best:
                best, bestr = val, r
        rows.append(dict(eps=float(e), logN_lower=float(best), r=bestr))
    return rows


def vg_from_directions(V):
    """Given K perturbation directions (rows of V, all admissible as a +/- set),
    return (eps, log packing) from the Gilbert-Varshamov bound.

    With G = V V^T, any +/-1 combination on a subset S has squared norm at least
    lambda_min(G) |S|.  VG supplies 2^(K/8) subsets pairwise Hamming >= K/4, so
    the packing separation is at least sqrt(lambda_min * K/4) and the log packing
    is at least (K/8) log 2.
    """
    G = V @ V.T
    lam = float(np.linalg.eigvalsh(G)[0])
    if lam <= 0:
        return None
    sep = math.sqrt(lam * V.shape[0] / 4.0)
    return dict(eps=sep / 2.0, logN=V.shape[0] * LOG2 / 8.0, lam_min=lam,
                lam_min_over_mean_diag=lam / float(np.mean(np.diag(G))))


def shell_directions(t, K, M, alpha, D):
    """K disjoint signed atom pairs inside the boundary shell at distance ~t.

    Shell j occupies [1 - t - (j+1)*h, 1 - t - j*h] scaled so all K pairs lie in
    [1-2t, 1-t]; each carries mass m = (M/2) t^alpha / K, so the total mass added
    inside [1-s,1] is at most (M/2) s^alpha for every s (checked below), leaving
    the base measure with the other half of the budget.
    """
    h = t / K
    m = 0.5 * M * (t ** alpha) / K
    k = np.arange(1, D + 1, dtype=float)
    V = np.empty((K, D))
    for j in range(K):
        left = max(1.0 - t - (j + 1) * h, 1e-12)   # farther from 1
        right = max(1.0 - t - j * h, 2e-12)        # closer to 1
        V[j] = m * (np.exp(k * math.log(right)) - np.exp(k * math.log(left)))
    # exact tail check: total perturbation mass inside [1-s,1] vs (M/2) s^alpha
    worst = 0.0
    for j in range(K):
        s = t + (j + 1) * h
        added = (j + 1) * m
        worst = max(worst, added / (0.5 * M * s ** alpha))
    return V, dict(mass_per_atom=m, shell_width=h, tail_budget_usage=worst)


def build_shell_family(M, alpha, scales, per_scale):
    """Signed atom pairs in boundary shells, with the tail budget enforced EXACTLY.

    Returns (atoms, masses, budget_usage).  Direction j puts +m at 1 - u_j and
    -m at 1 - v_j with u_j < v_j.  The measure formed by any subset of the
    positive parts must satisfy mu([1-s,1]) <= (M/2) s^alpha for every s (the
    other half of the budget is held by a base measure), so the masses are scaled
    down by the exact worst-case ratio over all s.
    """
    atoms, raw = [], []
    for t in scales:
        h = t / per_scale
        for j in range(per_scale):
            u = t + j * h
            v = t + (j + 1) * h
            atoms.append((1.0 - u, 1.0 - v))
            raw.append((u, t ** alpha / per_scale))
    order = np.argsort([r[0] for r in raw])
    m = np.array([r[1] for r in raw], float)
    cum = np.cumsum(m[order])
    s = np.array([raw[i][0] for i in order])
    ratio = float(np.max(cum / (0.5 * M * s ** alpha)))
    m = m / ratio
    masses = np.empty_like(m)
    masses[:] = m
    return atoms, masses, ratio


def run_zonotope(M=1.0, K_per_scale=12, n_scales=25, dps=400):
    """Instrument 2: numerical LOWER bound on the moment body's entropy exponent."""
    import mpmath as mp
    mp.mp.dps = dps
    out = {"controls": {}, "moment_body": {}}

    # CONTROL: identical bound-optimiser fed the box's orthogonal axes must
    # return the box exponent 2/(2 alpha - 1).
    for alpha, emax, emin in ((1.0, 1e-1, 1e-3), (1.5, 1e-2, 1e-6), (2.0, 1e-3, 1e-8)):
        b = moment_box_axes(M, alpha, 2000000)
        ld = 2.0 * np.cumsum(np.log(b))
        logdets = [(r + 1, float(ld[r])) for r in range(0, len(b), 11)]
        epss = np.geomspace(emax, emin, 10)
        rows = volumetric_bound(logdets, epss)
        rows = [r for r in rows if r["logN_lower"] > 0]
        f = loglog_fit([1.0 / r["eps"] for r in rows], [r["logN_lower"] for r in rows])
        out["controls"][f"volumetric_on_box_alpha_{alpha}"] = dict(
            fitted_slope=f["slope"], stderr=f["stderr"],
            expected=2.0 / (2 * alpha - 1), r_used=[r["r"] for r in rows])

    scales = [0.4 * 0.5 ** i for i in range(n_scales)]
    for alpha in (1.0, 1.5, 2.0, 3.0):
        atoms, masses, ratio = build_shell_family(M, alpha, scales, K_per_scale)
        G = exact_gram(atoms, masses)
        logdets = pivoted_cholesky_logdets(G, rmax=len(atoms))
        epss = np.geomspace(1e-2, 1e-12, 14)
        rows = volumetric_bound(logdets, epss)
        rows = [r for r in rows if r["logN_lower"] > 0]
        f = loglog_fit([1.0 / r["eps"] for r in rows],
                       [r["logN_lower"] for r in rows]) if len(rows) >= 3 else None
        out["moment_body"][f"alpha_{alpha}"] = dict(
            n_directions=len(atoms), mass_scaledown=ratio,
            max_r_certified=logdets[-1][0] if logdets else 0,
            r_selected=[r["r"] for r in rows],
            fitted_lower_bound_slope=f["slope"] if f else None,
            stderr=f["stderr"] if f else None,
            claimed_1_over_alpha=1.0 / alpha,
            box_2_over_2a_minus_1=2.0 / (2 * alpha - 1),
            rows=rows,
            note="a LOWER bound on log N; the fitted slope is a lower bound on the "
                 "entropy exponent only insofar as r is not capped by the family size",
        )
    return out


def run_vg(M=1.0):
    out = {"controls": {}, "moment_body": {}}

    # CONTROL: same VG machinery on the box's orthogonal axes must return
    # the box exponent 2/(2 alpha - 1).
    for alpha in (1.0, 1.5, 2.0):
        b = moment_box_axes(M, alpha, 200000)
        pts = []
        for d in (32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768):
            V = np.zeros((16, 0))
            lam = b[d - 1] ** 2           # orthogonal axes: Gram = diag(b_k^2)
            sep = math.sqrt(lam * d / 4.0)
            pts.append((sep / 2.0, d * LOG2 / 8.0))
        f = loglog_fit([1.0 / p[0] for p in pts], [p[1] for p in pts])
        out["controls"][f"vg_on_box_alpha_{alpha}"] = dict(
            fitted_slope=f["slope"], stderr=f["stderr"],
            expected=2.0 / (2 * alpha - 1))

    # THE TEST
    for alpha in (1.0, 1.5, 2.0, 3.0):
        pts = []
        detail = []
        for t in (0.4, 0.3, 0.2, 0.1, 0.05, 0.02, 0.01):
            D = min(30000, max(400, int(25.0 / t)))
            for K in (4, 8, 16, 32, 64, 128, 256):
                V, info = shell_directions(t, K, M, alpha, D)
                if info["tail_budget_usage"] > 1.0:
                    continue
                r = vg_from_directions(V)
                if r is None or r["eps"] <= 0:
                    continue
                pts.append((r["eps"], r["logN"]))
                detail.append(dict(t=t, K=K, D=D, eps=r["eps"], logN=r["logN"],
                                   lam_ratio=r["lam_min_over_mean_diag"],
                                   tail_usage=info["tail_budget_usage"]))
        # upper envelope: for each eps, the best logN achievable at eps or finer
        pts.sort()
        env = []
        best = -1.0
        for e, ln in reversed(pts):        # from coarse eps down to fine
            if ln > best:
                best = ln
                env.append((e, ln))
        env = list(reversed(env))
        f = loglog_fit([1.0 / e for e, _ in env], [ln for _, ln in env]) if len(env) >= 3 else None
        out["moment_body"][f"alpha_{alpha}"] = dict(
            envelope_points=len(env),
            fitted_lower_bound_slope=f["slope"] if f else None,
            stderr=f["stderr"] if f else None,
            claimed_1_over_alpha=1.0 / alpha,
            box_2_over_2a_minus_1=2.0 / (2 * alpha - 1),
            envelope=[dict(eps=e, logN=ln) for e, ln in env],
            detail=detail[:60],
        )
    return out


# ---------------------------------------------------------------------------
# Instrument 3: greedy net, moment body vs box, identical estimator
# ---------------------------------------------------------------------------

def greedy_net(X, eps):
    """Greedy (sequential) eps-net size over the sample rows of X."""
    centers = []
    for i in range(X.shape[0]):
        x = X[i]
        if centers:
            C = X[centers]
            if np.min(np.linalg.norm(C - x, axis=1)) <= eps:
                continue
        centers.append(i)
    return len(centers)


def sample_moment_body(n, M, alpha, D, rng, n_atoms=40):
    k = np.arange(1, D + 1, dtype=float)
    out = np.empty((n, D))
    for i in range(n):
        # atoms at 1 - t_j with t_j random; masses drawn then rescaled down until
        # the tail constraint mu([1-t,1]) <= M t^alpha holds at every atom.
        t = np.sort(rng.uniform(0, 1, n_atoms))
        w = rng.exponential(1.0, n_atoms)
        w = w / w.sum() * M
        cum = np.cumsum(w)                    # mass within [1-t_j, 1]
        scale = np.min(M * t ** alpha / np.maximum(cum, 1e-300))
        w = w * min(scale, 1.0)
        x = 1.0 - t
        out[i] = (w[None, :] * np.exp(np.outer(k, np.log(np.maximum(x, 1e-300))))).sum(axis=1)
    return out


def run_greedy(M=1.0, alpha=1.5, D=64, n=3000, seed=0):
    rng = np.random.default_rng(seed)
    b = moment_box_axes(M, alpha, D)
    Xbox = rng.uniform(0, 1, size=(n, D)) * b[None, :]
    Xmom = sample_moment_body(n, M, alpha, D, rng)
    # estimator control: uniform samples in a d-cube, slope must be ~ d
    ctrl = {}
    for d in (2, 3):
        Xc = rng.uniform(0, 1, size=(n, d))
        es = np.geomspace(0.5, 0.05, 6)
        ns = [greedy_net(Xc, e) for e in es]
        keep = [(e, c) for e, c in zip(es, ns) if 3 <= c <= n / 5]
        ctrl[f"cube_d{d}"] = dict(
            fitted_slope=loglog_fit([1 / e for e, _ in keep], [c for _, c in keep])["slope"]
            if len(keep) >= 3 else None, expected=float(d),
            counts=list(map(int, ns)), eps=list(map(float, es)))
    es = np.geomspace(0.3, 0.002, 10)
    rows = []
    for e in es:
        rows.append(dict(eps=float(e), net_box=greedy_net(Xbox, e),
                         net_moment=greedy_net(Xmom, e)))
    return dict(alpha=alpha, D=D, n_samples=n, controls=ctrl, rows=rows,
                note="greedy net over a finite sample lower-bounds the covering number "
                     "and saturates at the sample size; used for the ORDERING only")


if __name__ == "__main__":
    res = {}
    res["instrument1_box"] = run_box()
    res["instrument2_zonotope_moment_body"] = run_zonotope()
    res["instrument2b_vg_moment_body"] = run_vg()
    res["instrument3_greedy_ordering"] = run_greedy()
    print(json.dumps(res, indent=1, default=str))
