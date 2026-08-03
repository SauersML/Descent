#!/usr/bin/env /usr/bin/python3.12
"""
Adversarial identification test: is `tau` the split DEPTH or the total PATH LENGTH?

The theorem assumes source and target are related by a single application of a
reversible semigroup, P_tau.  Real transfer settings are usually a SPLIT: an ancestral
population at stationarity bifurcates and the two descendants evolve INDEPENDENTLY for
d generations.  The source design is built in population 1 and deployed in population 2.

If reversibility holds, conditional independence given the ancestor gives
    Cov(x_1(d), x_2(d)) = Cov(x_0, x_{2d})   =  e^{-2 lam d} Var(x)
so the theorem applies with tau = 2d, i.e. the crossover in SPLIT-DEPTH units is
    d_c = log2 / (2 lam)  =  tau_c / 2.
A practitioner who reads "tau" off the divergence time of the two populations, rather
than the total path length between them, is off by exactly a factor of two.

This script MEASURES d_c from a forward Wright-Fisher split simulation and compares it
against both log2/(2 lam) and log2/lam.  Pure stdlib.
"""

import json
import math
import os
import random
import sys
from multiprocessing import Pool

NPROC = int(os.environ.get("TAUC_NPROC", "16"))
OUT = os.environ.get("TAUC_OUT", "split_results.json")


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


def _step(rng, p, u, twoN):
    return rng.binomialvariate(twoN, p * (1 - 2 * u) + u) / twoN


def _split_block(args):
    seed, R, N, u, burn, depths = args
    rng = random.Random(seed)
    twoN = 2 * N
    maxd = max(depths)
    dset = {d: i for i, d in enumerate(depths)}
    # per-replicate accumulators, kept per replicate for the bootstrap
    reps = []
    for _ in range(R):
        p = rng.random()
        for _ in range(burn):
            p = _step(rng, p, u, twoN)
        p0 = p
        p1, p2 = p0, p0
        rec = [0.0] * (4 * len(depths))
        if 0 in dset:
            i = dset[0]
            a = p1 - 0.5
            b = p2 - 0.5
            rec[4 * i] = a * b
            rec[4 * i + 1] = a * a
            rec[4 * i + 2] = b * b
            rec[4 * i + 3] = 1.0
        for g in range(1, maxd + 1):
            p1 = _step(rng, p1, u, twoN)
            p2 = _step(rng, p2, u, twoN)
            if g in dset:
                i = dset[g]
                a = p1 - 0.5
                b = p2 - 0.5
                rec[4 * i] = a * b
                rec[4 * i + 1] = a * a
                rec[4 * i + 2] = b * b
                rec[4 * i + 3] = 1.0
        reps.append(rec)
    return reps


def run_split(N, u, depths, R, burn, seed0, nboot=400):
    per = max(1, R // NPROC)
    args = [(seed0 + 6151 * i, per, N, u, burn, depths) for i in range(NPROC)]
    with Pool(NPROC) as p:
        blocks = p.map(_split_block, args)
    reps = [r for b in blocks for r in b]
    nd = len(depths)
    M = len(reps)

    def agg(idxs):
        s = [0.0] * (4 * nd)
        for i in idxs:
            r = reps[i]
            for k in range(4 * nd):
                s[k] += r[k]
        out = []
        for i in range(nd):
            c = s[4 * i + 3]
            out.append((s[4 * i] / c, s[4 * i + 1] / c, s[4 * i + 2] / c))
        return out

    def premiums(a):
        cov, v1, v2 = a
        stale = 2.0 * cov - v1
        rho = cov / v1
        damped = 2.0 * rho * cov - rho * rho * v1
        return dict(cov=cov, var_src=v1, var_tgt=v2, rho_hat=rho,
                    blind=0.0, stale=stale, damped=damped, oracle=v2,
                    myopia=damped - stale)

    def crossing(vals):
        for i in range(len(vals) - 1):
            t0, v0 = vals[i]
            t1, v1 = vals[i + 1]
            if v0 > 0 >= v1:
                return t0 + (t1 - t0) * v0 / (v0 - v1)
        return None

    allidx = list(range(M))
    base = [premiums(a) for a in agg(allidx)]
    pt = crossing([(depths[i], base[i]["stale"]) for i in range(nd)])

    rng = random.Random(seed0 + 99)
    boots = []
    for _ in range(nboot):
        idxs = [rng.randrange(M) for _ in range(M)]
        a = agg(idxs)
        c = crossing([(depths[i], premiums(a[i])["stale"]) for i in range(nd)])
        if c is not None:
            boots.append(c)
    boots.sort()
    ci = [boots[int(0.025 * len(boots))], boots[int(0.975 * len(boots))]] if len(boots) > 20 else None
    rows = [dict(depth=depths[i], **base[i]) for i in range(nd)]
    return dict(N=N, u=u, theta_4Nu=4 * N * u, R=M, burn=burn, rows=rows,
                depth_crossing=pt, depth_crossing_ci95=ci, nboot=len(boots))


def main():
    res = {"meta": dict(python=sys.version.split()[0], nproc=NPROC)}
    for tag, N, u in [("N500_u0.005_theta10", 500, 0.005),
                      ("N1000_u0.002_theta8", 1000, 0.002)]:
        lam = -math.log(1 - 2 * u)
        tau_c = math.log(2) / lam
        d_pred = tau_c / 2.0
        depths = sorted(set(int(round(f * d_pred)) for f in
                            [0.0, 0.2, 0.4, 0.55, 0.7, 0.8, 0.9, 0.95, 1.0, 1.05,
                             1.15, 1.3, 1.5, 1.9, 2.5, 3.5]))
        r = run_split(N, u, depths, R=24000, burn=int(6 / lam), seed0=515 + N)
        r["lam_per_gen"] = lam
        r["pred_depth_crossing_pathlength_tau_2d"] = d_pred
        r["pred_depth_crossing_if_tau_equals_depth"] = tau_c
        res[tag] = r
    with open(OUT, "w") as f:
        json.dump(res, f, indent=1)
    print("WROTE", OUT)


if __name__ == "__main__":
    main()
