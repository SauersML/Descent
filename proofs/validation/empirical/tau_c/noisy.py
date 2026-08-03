#!/usr/bin/env /usr/bin/python3.12
"""
The claims assume the stale design is the source signal EXACTLY (c = x_S).  A real
adjustment is FITTED in the source environment from n samples, so c = x_S + eps with
eps ~ N(0, s2) independent of the environment.  Then

    premium(alpha) = 2 alpha rho V - alpha^2 (V + s2)

so the crossover for the full-strength design (alpha=1) moves from rho = 1/2 to
rho = (1 + s2/V)/2, i.e.

    tau_c(noisy) = log( 2 / (1 + s2/V) ) / lam   <   log2/lam,

and vanishes entirely once s2 >= V (a design noisier than its own signal never beats
blind at any horizon).  Estimation noise makes the crossover EARLIER, never later.
Conversely a design already shrunk by alpha < 1 crosses at rho = alpha/2, i.e. LATER.
Both are measured here against the exact-transition OU harness.
"""

import json
import math
import os
import random
import sys
from multiprocessing import Pool

NPROC = int(os.environ.get("TAUC_NPROC", "16"))
OUT = "noisy_results.json"


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


def _blk(args):
    seed, M, lam, s2s, alphas, NB = args
    rng = random.Random(seed)
    ns = len(s2s)
    na = len(alphas)
    # sufficient stats per (s2, alpha) sub-block: for c = alpha*(xs + eps),
    #   premium(tau) = 2 alpha (rho A + sqrt(1-rho^2) B + rho C + ...)  -- expand directly:
    # x_T = rho xs + sqrt(1-rho^2) z ; c = alpha (xs + e)
    # J = 2 c x_T - c^2 = 2 alpha (xs+e)(rho xs + sqrt(1-rho^2) z) - alpha^2 (xs+e)^2
    # stats needed: P = sum (xs+e) xs , Q = sum (xs+e) z , R = sum (xs+e)^2
    sub = [[[0.0, 0.0, 0.0] for _ in range(ns)] for _ in range(NB)]
    per = M // NB
    for b in range(NB):
        for _ in range(per):
            xs = rng.gauss(0.0, 1.0)
            z = rng.gauss(0.0, 1.0)
            for si, s2 in enumerate(s2s):
                e = rng.gauss(0.0, math.sqrt(s2)) if s2 > 0 else 0.0
                w = xs + e
                sub[b][si][0] += w * xs
                sub[b][si][1] += w * z
                sub[b][si][2] += w * w
    return sub, per


def run(lam, s2s, alphas, M_total, seed0, nboot=1500):
    NB = 150
    per_proc = M_total // NPROC
    with Pool(NPROC) as p:
        res = p.map(_blk, [(seed0 + 313 * i, per_proc, lam, s2s, alphas, NB)
                           for i in range(NPROC)])
    subs = []
    per_sub = res[0][1]
    for sub, ps in res:
        subs.extend(sub)
    NBt = len(subs)
    ns = len(s2s)

    def totals(idxs):
        T = [[0.0, 0.0, 0.0] for _ in range(ns)]
        for i in idxs:
            s = subs[i]
            for si in range(ns):
                T[si][0] += s[si][0]
                T[si][1] += s[si][1]
                T[si][2] += s[si][2]
        return T, len(idxs) * per_sub

    def prem(T, c, si, alpha, tau):
        rho = math.exp(-lam * tau)
        sq = math.sqrt(max(0.0, 1 - rho * rho))
        P, Q, Rr = T[si]
        return (2 * alpha * (rho * P + sq * Q) - alpha * alpha * Rr) / c

    allidx = list(range(NBt))
    T0, c0 = totals(allidx)
    rng = random.Random(seed0 + 77)
    boot_T = []
    for _ in range(nboot):
        idxs = [rng.randrange(NBt) for _ in range(NBt)]
        boot_T.append(totals(idxs))

    out = []
    for si, s2 in enumerate(s2s):
        for alpha in alphas:
            pred_rho = alpha * (1 + s2) / 2.0
            pred_tau = math.log(1.0 / pred_rho) / lam if 0 < pred_rho < 1 else None
            pt = bisect(lambda t: prem(T0, c0, si, alpha, t), 1e-9, 60.0 / lam)
            bs = []
            for T, c in boot_T:
                r = bisect(lambda t: prem(T, c, si, alpha, t), 1e-9, 60.0 / lam)
                if r is not None:
                    bs.append(r)
            bs.sort()
            ci = [bs[int(0.025 * len(bs))], bs[int(0.975 * len(bs))]] if len(bs) > 20 else None
            out.append(dict(s2_over_V=s2, alpha=alpha,
                            measured_tau_c=pt, ci95=ci, n_boot_crossed=len(bs),
                            predicted_tau_c=pred_tau,
                            baseline_log2_over_lam=math.log(2) / lam))
    return out, c0


def main():
    rows, M = run(1.0, [0.0, 0.1, 0.25, 0.5, 1.0], [1.0, 0.5],
                  6_000_000, 2718)
    json.dump({"meta": dict(python=sys.version.split()[0], nproc=NPROC, M=M, lam=1.0,
                            V=1.0,
                            note="tau_c where premium of c=alpha*(x_S+eps) over blind "
                                 "crosses zero; predicted log(1/(alpha(1+s2/V)/2))/lam"),
               "rows": rows}, open(OUT, "w"), indent=1)
    print("WROTE", OUT)


if __name__ == "__main__":
    main()
