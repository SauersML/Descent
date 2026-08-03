#!/usr/bin/env /usr/bin/python3.12
"""
Refinements to tau_c_sim.py:

 (1) MEASURED alpha-sweep: realized value of a shrinkage design with an arbitrary
     (i.e. mis-estimated) shrinkage factor alpha, to test "damping never hurts"
     empirically rather than by algebra.  Predicted premium alpha(2rho-alpha)V.

 (2) Wright-Fisher with the SECOND (quadratic) mode as the value signal, using
     g = (p-1/2)^2 centred by its pooled stationary mean.  The first run centred
     heterozygosity h = 1/2 - 2q^2 by E[h] ~ 0.476, subtracting 0.227 from 0.228 --
     catastrophic cancellation.  Using q^2 directly removes it.
     Exact discrete relaxation factor of the quadratic mode:
         E[q_{t+1}^2 | q_t] = 1/(8N) + (1-2u)^2 (1 - 1/(2N)) q_t^2
     so lam_2 = -log[ (1-2u)^2 (1 - 1/(2N)) ]  ~  4u + 1/(2N):
     the SAME environment process, but the value signal's rate mixes mutation AND drift.

 (3) Higher-precision rerun of the marginal WF config (N=500, u=0.005).
"""

import json
import math
import os
import random
import sys
from multiprocessing import Pool

NPROC = int(os.environ.get("TAUC_NPROC", "16"))
OUT = "refine_results.json"


def bisect(f, lo, hi, tol=1e-12, itmax=300):
    flo, fhi = f(lo), f(hi)
    if flo * fhi > 0:
        return None
    for _ in range(itmax):
        mid = 0.5 * (lo + hi)
        fm = f(mid)
        if fm == 0.0 or (hi - lo) < tol:
            return mid
        if flo * fm < 0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return 0.5 * (lo + hi)


# ---------------- (1) measured alpha sweep on the exact-transition OU ----------------

def _alpha_block(args):
    seed, M, lam, taus, mults = args
    rng = random.Random(seed)
    acc = [[[0.0, 0.0] for _ in mults] for _ in taus]
    for _ in range(M):
        xs = rng.gauss(0.0, 1.0)
        for ti, t in enumerate(taus):
            rho = math.exp(-lam * t)
            xt = rho * xs + math.sqrt(max(0.0, 1 - rho * rho)) * rng.gauss(0.0, 1.0)
            for mi, mu in enumerate(mults):
                c = mu * rho * xs
                j = 2.0 * c * xt - c * c
                acc[ti][mi][0] += j
                acc[ti][mi][1] += j * j
    return acc, M


def run_alpha(lam, taus, mults, M_total, seed0):
    per = M_total // NPROC
    with Pool(NPROC) as p:
        blocks = p.map(_alpha_block, [(seed0 + i, per, lam, taus, mults)
                                      for i in range(NPROC)])
    Mtot = sum(b[1] for b in blocks)
    rows = []
    for ti, t in enumerate(taus):
        rho = math.exp(-lam * t)
        for mi, mu in enumerate(mults):
            s = sum(b[0][ti][mi][0] for b in blocks)
            s2 = sum(b[0][ti][mi][1] for b in blocks)
            m = s / Mtot
            se = math.sqrt(max(0.0, s2 / Mtot - m * m) / Mtot)
            pred = (mu * rho) * (2 * rho - mu * rho) * 1.0
            rows.append(dict(tau=t, rho=rho, alpha_over_rho=mu, alpha=mu * rho,
                             measured=m, se=se, pred=pred,
                             z=(m - pred) / max(se, 1e-15),
                             beats_blind=m > 0))
    return rows, Mtot


# ---------------- (2,3) Wright-Fisher, linear and quadratic value signals ----------------

def _wf2_block(args):
    seed, R, N, u, burn, T, taus, GROUP = args
    rng = random.Random(seed)
    twoN = 2 * N
    ntau = len(taus)
    groups = []
    g = None
    for r in range(R):
        if r % GROUP == 0:
            g = [0.0] * (ntau * 7)
            groups.append(g)
        p = rng.random()
        for _ in range(burn):
            p = rng.binomialvariate(twoN, p * (1 - 2 * u) + u) / twoN
        traj = []
        for _ in range(T):
            p = rng.binomialvariate(twoN, p * (1 - 2 * u) + u) / twoN
            traj.append(p - 0.5)
        for ti, tau in enumerate(taus):
            if tau >= T:
                continue
            o = ti * 7
            for t0 in range(0, T - tau):
                a = traj[t0]
                b = traj[t0 + tau]
                a2 = a * a
                b2 = b * b
                g[o] += a * b        # linear cov
                g[o + 1] += a2       # linear var (source window)
                g[o + 2] += b2       # linear var (target window)
                g[o + 3] += a2 * b2  # quadratic raw cross
                g[o + 4] += a2 * a2  # quadratic raw second moment
                g[o + 5] += a2       # quadratic raw mean (= linear var)
                g[o + 6] += 1.0
    return groups


def run_wf2(N, u, taus, R, burn, T, seed0, nboot=400, GROUP=10):
    per = max(GROUP, (R // NPROC // GROUP) * GROUP)
    with Pool(NPROC) as p:
        res = p.map(_wf2_block, [(seed0 + 6203 * i, per, N, u, burn, T, taus, GROUP)
                                 for i in range(NPROC)])
    groups = [g for b in res for g in b]
    ntau = len(taus)

    def agg(idxs):
        s = [0.0] * (ntau * 7)
        for i in idxs:
            g = groups[i]
            for k in range(ntau * 7):
                s[k] += g[k]
        out = []
        for ti in range(ntau):
            o = ti * 7
            c = s[o + 6]
            if c == 0:
                out.append(None)
                continue
            out.append([s[o + k] / c for k in range(6)])
        return out

    def prem_lin(a):
        cov, v1, v2 = a[0], a[1], a[2]
        rho = cov / v1
        return dict(V=v1, rho_hat=rho, blind=0.0, stale=2 * cov - v1,
                    damped=2 * rho * cov - rho * rho * v1, oracle=v2,
                    myopia=(2 * rho * cov - rho * rho * v1) - (2 * cov - v1))

    def prem_quad(a, m2):
        # signal g = q^2 - m2 ; cov = E[a2 b2] - m2^2 ; V = E[a2^2] - m2^2
        cov = a[3] - m2 * m2
        V = a[4] - m2 * m2
        rho = cov / V
        return dict(V=V, rho_hat=rho, blind=0.0, stale=2 * cov - V,
                    damped=2 * rho * cov - rho * rho * V,
                    myopia=(2 * rho * cov - rho * rho * V) - (2 * cov - V))

    def crossing(vals):
        for i in range(len(vals) - 1):
            t0, v0 = vals[i]
            t1, v1 = vals[i + 1]
            if v0 > 0 >= v1:
                return t0 + (t1 - t0) * v0 / (v0 - v1)
        return None

    allidx = list(range(len(groups)))

    def full(idxs):
        a = agg(idxs)
        # pooled stationary mean of q^2 across all taus (all are stationary windows)
        num = sum(x[5] for x in a if x)
        m2 = num / len([x for x in a if x])
        L = [prem_lin(x) if x else None for x in a]
        Q = [prem_quad(x, m2) if x else None for x in a]
        return m2, L, Q

    m2, L, Q = full(allidx)
    ptL = crossing([(taus[i], L[i]["stale"]) for i in range(ntau) if L[i]])
    ptQ = crossing([(taus[i], Q[i]["stale"]) for i in range(ntau) if Q[i]])

    rng = random.Random(seed0 + 8)
    bL, bQ = [], []
    for _ in range(nboot):
        idxs = [rng.randrange(len(groups)) for _ in range(len(groups))]
        _, l, q = full(idxs)
        cl = crossing([(taus[i], l[i]["stale"]) for i in range(ntau) if l[i]])
        cq = crossing([(taus[i], q[i]["stale"]) for i in range(ntau) if q[i]])
        if cl is not None:
            bL.append(cl)
        if cq is not None:
            bQ.append(cq)

    def ci(b):
        if len(b) < 20:
            return None
        b = sorted(b)
        return [b[int(0.025 * len(b))], b[int(0.5 * len(b))], b[int(0.975 * len(b))]]

    lam1 = -math.log(1 - 2 * u)
    lam2 = -math.log((1 - 2 * u) ** 2 * (1 - 1.0 / (2 * N)))
    return dict(
        N=N, u=u, theta_4Nu=4 * N * u, ngroups=len(groups), group_size=GROUP,
        nchains=len(groups) * GROUP, T=T, burn=burn, taus=taus, m2_pooled=m2,
        lam1_exact=lam1, tau_c1_exact=math.log(2) / lam1,
        lam2_exact=lam2, tau_c2_exact=math.log(2) / lam2,
        lam2_approx_4u_plus_1_over_2N=4 * u + 1.0 / (2 * N),
        lam_naive_drift=1.0 / (2 * N),
        crossing_linear=ptL, crossing_linear_ci=ci(bL),
        crossing_quadratic=ptQ, crossing_quadratic_ci=ci(bQ),
        rows=[dict(tau=taus[i], linear=L[i], quadratic=Q[i])
              for i in range(ntau) if L[i]],
    )


def main():
    R = {"meta": dict(python=sys.version.split()[0], nproc=NPROC)}
    rows, M = run_alpha(1.0, [0.5, 1.0, 2.0, 4.0],
                        [0.25, 0.5, 1.0, 1.5, 1.9, 2.0, 2.1, 3.0],
                        4_000_000, 909)
    R["alpha_sweep_measured"] = dict(M=M, lam=1.0, V=1.0, rows=rows)

    R["wf_two_signals"] = {}
    for tag, N, u, Tmul in [("N500_u0.005_theta10", 500, 0.005, 15.0),
                            ("N200_u0.00075_theta0.6", 200, 0.00075, 10.0)]:
        lam1 = -math.log(1 - 2 * u)
        tc1 = math.log(2) / lam1
        taus = sorted(set(int(round(f * tc1)) for f in
                          [0.0, 0.1, 0.2, 0.3, 0.35, 0.4, 0.45, 0.5, 0.6, 0.7, 0.8,
                           0.9, 0.95, 1.0, 1.05, 1.15, 1.3, 1.6, 2.0, 2.8]))
        T = int(Tmul / lam1)
        R["wf_two_signals"][tag] = run_wf2(N, u, taus, R=6000, burn=int(8 / lam1),
                                           T=T, seed0=4400 + N, nboot=400, GROUP=10)
    with open(OUT, "w") as f:
        json.dump(R, f, indent=1)
    print("WROTE", OUT)


if __name__ == "__main__":
    main()
