#!/usr/bin/env /usr/bin/python3.12
"""
Measure the staleness crossover tau_c = log2/lambda and the shrinkage-rule premiums.

Claims under test (proofs/Calibrator/DirichletTransfer.lean, StalenessCrossover/ShrinkageRule):
  damped premium over blind  =  exp(-2 lam tau) * V      (positive at every horizon)
  stale  premium over blind  =  (2 exp(-lam tau) - 1) * V (negative past tau_c = log2/lam)
  price of myopia            =  (1 - exp(-lam tau))^2 * V

Model.  The environment is a reversible Markov process X_t with stationary law pi.
A "design" is a vector c in the value space.  Realized payoff of deploying c against the
target environment state x_T is the linear-quadratic functional

    J(c; x_T) = 2 * sum_n w_n c_n x_{T,n}  -  sum_n w_n c_n^2

which is the standard quadratic objective whose maximiser over c is the target signal
itself and whose optimum-over-conditional-expectation is P_tau x_S.  Designs:

    blind  : c = 0                       (no adaptation)
    stale  : c = x_S                     (full-strength adaptation to the SOURCE state)
    damped : c = diag(e^{-lam_n tau}) x_S (the shrinkage rule)
    oracle : c = x_T                     (adaptation to the TRUE target state)

Nothing about the premium formulas is fed to the payoff computation: the payoffs are
evaluated on simulated states and compared to the formulas afterwards.

Pure stdlib.  No numpy, no sympy.
"""

import json
import math
import os
import random
import sys
from multiprocessing import Pool

NPROC = int(os.environ.get("TAUC_NPROC", "16"))
OUT = os.environ.get("TAUC_OUT", "tau_c_results.json")

# ----------------------------------------------------------------------------
# generic helpers
# ----------------------------------------------------------------------------

def mean_se(xs):
    n = len(xs)
    m = sum(xs) / n
    if n < 2:
        return m, 0.0
    v = sum((x - m) ** 2 for x in xs) / (n - 1)
    return m, math.sqrt(v / n)


def bisect(f, lo, hi, tol=1e-12, itmax=200):
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


def theory_crossing(ws, lams, hi=1e6):
    """Solve sum_n w_n (2 e^{-lam_n tau} - 1) = 0."""
    f = lambda t: sum(w * (2.0 * math.exp(-l * t) - 1.0) for w, l in zip(ws, lams))
    return bisect(f, 1e-12, hi)


# ----------------------------------------------------------------------------
# HARNESS A: multi-mode OU / Gaussian reversible environment, exact transitions
# ----------------------------------------------------------------------------
# dX_n = -lam_n X_n dt + sqrt(2 lam_n) dW_n  =>  stationary N(0,1) per mode, and
# X_T,n | X_S,n  ~  N(rho_n X_S,n, 1 - rho_n^2),  rho_n = exp(-lam_n tau).
# The transition is sampled EXACTLY (no time discretisation), so any deviation from
# the formulas is a defect in the formulas, not in an integrator.

def _ou_block(args):
    seed, M, ws, lams, taus = args
    rng = random.Random(seed)
    n = len(ws)
    # accumulators: per tau, per design, sum and sum-of-squares of the payoff
    acc = [[[0.0, 0.0] for _ in range(4)] for _ in taus]
    rhos = [[math.exp(-l * t) for l in lams] for t in taus]
    for _ in range(M):
        xs = [rng.gauss(0.0, 1.0) for _ in range(n)]
        for ti, t in enumerate(taus):
            rh = rhos[ti]
            xt = [rh[k] * xs[k] + math.sqrt(max(0.0, 1.0 - rh[k] ** 2)) * rng.gauss(0.0, 1.0)
                  for k in range(n)]
            # blind
            j_blind = 0.0
            # stale  c = xs
            j_stale = sum(ws[k] * (2.0 * xs[k] * xt[k] - xs[k] * xs[k]) for k in range(n))
            # damped c = rho*xs
            j_damp = sum(ws[k] * (2.0 * (rh[k] * xs[k]) * xt[k] - (rh[k] * xs[k]) ** 2)
                         for k in range(n))
            # oracle c = xt
            j_orac = sum(ws[k] * (2.0 * xt[k] * xt[k] - xt[k] * xt[k]) for k in range(n))
            for di, jv in enumerate((j_blind, j_stale, j_damp, j_orac)):
                acc[ti][di][0] += jv
                acc[ti][di][1] += jv * jv
    return acc, M


def run_ou(ws, lams, taus, M_total, seed0):
    per = M_total // NPROC
    args = [(seed0 + i, per, ws, lams, taus) for i in range(NPROC)]
    with Pool(NPROC) as p:
        blocks = p.map(_ou_block, args)
    Mtot = sum(b[1] for b in blocks)
    out = []
    for ti in range(len(taus)):
        row = {}
        for di, name in enumerate(("blind", "stale", "damped", "oracle")):
            s = sum(b[0][ti][di][0] for b in blocks)
            s2 = sum(b[0][ti][di][1] for b in blocks)
            m = s / Mtot
            var = max(0.0, s2 / Mtot - m * m)
            row[name] = m
            row[name + "_se"] = math.sqrt(var / Mtot)
        row["tau"] = taus[ti]
        out.append(row)
    return out, Mtot


# ----------------------------------------------------------------------------
# HARNESS A': common-random-numbers crossing estimate with bootstrap CI
# ----------------------------------------------------------------------------
# Using ONE sample of (x_S, z) shared across tau, the stale-premium estimator is a
# smooth deterministic function of tau, so its zero can be root-found on the sample
# and its sampling uncertainty obtained by bootstrapping over independent replicates.
#   x_T,n(tau) = rho_n x_S,n + sqrt(1-rho_n^2) z_n
#   premium_stale(tau) = (1/M) sum_r sum_n w_n [ 2 x_S x_T - x_S^2 ]
# Per-replicate sufficient statistics per mode: a_n = x_S,n^2 , b_n = x_S,n z_n .

def _crn_block(args):
    seed, M, n = args
    rng = random.Random(seed)
    A = [0.0] * n
    B = [0.0] * n
    # also keep per-chunk sums for bootstrap: split M into 200 sub-blocks
    NB = 200
    sub = [[0.0] * (2 * n) for _ in range(NB)]
    per = M // NB
    for b in range(NB):
        for _ in range(per):
            for k in range(n):
                xs = rng.gauss(0.0, 1.0)
                z = rng.gauss(0.0, 1.0)
                sub[b][2 * k] += xs * xs
                sub[b][2 * k + 1] += xs * z
    for b in range(NB):
        for k in range(n):
            A[k] += sub[b][2 * k]
            B[k] += sub[b][2 * k + 1]
    return sub, per


def crn_crossing(ws, lams, M_total, seed0, nboot=2000):
    n = len(ws)
    per = M_total // NPROC
    args = [(seed0 + 977 * i, per, n) for i in range(NPROC)]
    with Pool(NPROC) as p:
        res = p.map(_crn_block, args)
    subs = []
    per_sub = res[0][1]
    for sub, ps in res:
        subs.extend(sub)
    NB = len(subs)

    def totals(idxs):
        A = [0.0] * n
        B = [0.0] * n
        for i in idxs:
            s = subs[i]
            for k in range(n):
                A[k] += s[2 * k]
                B[k] += s[2 * k + 1]
        c = len(idxs) * per_sub
        return A, B, c

    def make_premium(A, B, c):
        def f(tau):
            tot = 0.0
            for k in range(n):
                rho = math.exp(-lams[k] * tau)
                sq = math.sqrt(max(0.0, 1.0 - rho * rho))
                tot += ws[k] * (2.0 * (rho * A[k] + sq * B[k]) - A[k])
            return tot / c
        return f

    allidx = list(range(NB))
    hi = 50.0 / min(lams)
    A0, B0, c0 = totals(allidx)
    point = bisect(make_premium(A0, B0, c0), 1e-9, hi)
    rng = random.Random(seed0 + 31337)
    boots = []
    for _ in range(nboot):
        idxs = [rng.randrange(NB) for _ in range(NB)]
        A, B, c = totals(idxs)
        r = bisect(make_premium(A, B, c), 1e-9, hi)
        if r is not None:
            boots.append(r)
    boots.sort()
    lo = boots[int(0.025 * len(boots))]
    up = boots[int(0.975 * len(boots))]
    return point, lo, up, len(boots), NB * per_sub


# ----------------------------------------------------------------------------
# HARNESS C: Wright-Fisher environment (bounded, non-Gaussian, discrete population)
# ----------------------------------------------------------------------------
# Diploid population size N, biallelic locus, symmetric mutation rate u per allele
# per generation:   p' = p(1-2u) + u ;  p_{t+1} = Binomial(2N, p') / (2N).
# The CENTRED FREQUENCY x = p - 1/2 is an EXACT eigenfunction of the transition
# operator:  E[x_{t+1} | x_t] = (1-2u) x_t.  So lambda_1 = -log(1-2u) per generation,
# set by MUTATION, not by the drift/coalescent rate 1/(2N).  Heterozygosity is a
# genuinely multi-mode signal and is measured separately.

def _wf_block(args):
    seed, R, N, u, burn, T, taus = args
    rng = random.Random(seed)
    twoN = 2 * N
    # per-chain trajectory statistics, accumulated per tau
    ntau = len(taus)
    # accumulate over chains: for each tau, sums of x_S x_T, x_S^2, x_T^2, and het versions
    sums = [[0.0] * 6 for _ in range(ntau)]
    counts = [0] * ntau
    chain_stats = []  # per-chain per-tau sums, for the chain bootstrap
    for r in range(R):
        p = rng.random()
        for _ in range(burn):
            pp = p * (1 - 2 * u) + u
            p = rng.binomialvariate(twoN, pp) / twoN
        traj = []
        for _ in range(T):
            pp = p * (1 - 2 * u) + u
            p = rng.binomialvariate(twoN, pp) / twoN
            traj.append(p)
        cs = [[0.0] * 6 for _ in range(ntau)]
        cc = [0] * ntau
        for ti, tau in enumerate(taus):
            tau = int(tau)
            if tau >= T:
                continue
            for t0 in range(0, T - tau):
                a = traj[t0] - 0.5
                b = traj[t0 + tau] - 0.5
                ha = 2.0 * traj[t0] * (1.0 - traj[t0])
                hb = 2.0 * traj[t0 + tau] * (1.0 - traj[t0 + tau])
                cs[ti][0] += a * b
                cs[ti][1] += a * a
                cs[ti][2] += b * b
                cs[ti][3] += ha * hb
                cs[ti][4] += ha * ha
                cs[ti][5] += ha
                cc[ti] += 1
        chain_stats.append((cs, cc))
        for ti in range(ntau):
            for k in range(6):
                sums[ti][k] += cs[ti][k]
            counts[ti] += cc[ti]
    return chain_stats


def run_wf(N, u, taus, R, burn, T, seed0, nboot=1000):
    per = max(1, R // NPROC)
    args = [(seed0 + 7919 * i, per, N, u, burn, T, taus) for i in range(NPROC)]
    with Pool(NPROC) as p:
        res = p.map(_wf_block, args)
    chains = []
    for c in res:
        chains.extend(c)
    ntau = len(taus)

    def agg(idxs):
        out = []
        for ti in range(ntau):
            s = [0.0] * 6
            c = 0
            for i in idxs:
                cs, cc = chains[i]
                for k in range(6):
                    s[k] += cs[ti][k]
                c += cc[ti]
            if c == 0:
                out.append(None)
                continue
            xsxt = s[0] / c
            xs2 = s[1] / c
            xt2 = s[2] / c
            hh = s[3] / c
            h2 = s[4] / c
            hm = s[5] / c
            out.append((xsxt, xs2, xt2, hh, h2, hm))
        return out

    allidx = list(range(len(chains)))
    base = agg(allidx)

    # premiums for the linear (single-mode) signal, from measured moments only
    def linear_premiums(a):
        xsxt, xs2, xt2 = a[0], a[1], a[2]
        V = xs2
        stale = 2.0 * xsxt - xs2
        rho_hat = xsxt / xs2                     # measured, not assumed
        damped = 2.0 * rho_hat * xsxt - rho_hat ** 2 * xs2
        oracle = xt2
        return dict(V=V, blind=0.0, stale=stale, damped=damped, oracle=oracle,
                    rho_hat=rho_hat)

    def het_premiums(a):
        hh, h2, hm = a[3], a[4], a[5]
        # centre heterozygosity by its stationary mean
        cV = h2 - hm * hm
        c_xsxt = hh - hm * hm
        stale = 2.0 * c_xsxt - cV
        rho_hat = c_xsxt / cV
        damped = 2.0 * rho_hat * c_xsxt - rho_hat ** 2 * cV
        return dict(V=cV, stale=stale, damped=damped, rho_hat=rho_hat)

    rows = []
    for ti, tau in enumerate(taus):
        if base[ti] is None:
            continue
        lp = linear_premiums(base[ti])
        hp = het_premiums(base[ti])
        rows.append(dict(tau=tau, linear=lp, het=hp))

    # crossing by chain bootstrap on the interpolated zero of the stale premium
    def crossing_from(vals):
        # vals: list of (tau, stale_premium); linear interpolation of the zero
        for i in range(len(vals) - 1):
            t0, v0 = vals[i]
            t1, v1 = vals[i + 1]
            if v0 > 0 >= v1:
                return t0 + (t1 - t0) * v0 / (v0 - v1)
        return None

    rng = random.Random(seed0 + 4242)
    boot_lin, boot_het = [], []
    for _ in range(nboot):
        idxs = [rng.randrange(len(chains)) for _ in range(len(chains))]
        a = agg(idxs)
        vl = [(taus[ti], linear_premiums(a[ti])["stale"]) for ti in range(ntau) if a[ti]]
        vh = [(taus[ti], het_premiums(a[ti])["stale"]) for ti in range(ntau) if a[ti]]
        cl, ch = crossing_from(vl), crossing_from(vh)
        if cl is not None:
            boot_lin.append(cl)
        if ch is not None:
            boot_het.append(ch)

    def ci(b):
        if len(b) < 20:
            return None
        b = sorted(b)
        return [b[int(0.025 * len(b))], sum(b) / len(b), b[int(0.975 * len(b))]]

    pt_lin = crossing_from([(r["tau"], r["linear"]["stale"]) for r in rows])
    pt_het = crossing_from([(r["tau"], r["het"]["stale"]) for r in rows])
    return dict(rows=rows, nchains=len(chains),
                crossing_linear=pt_lin, crossing_linear_ci=ci(boot_lin),
                crossing_het=pt_het, crossing_het_ci=ci(boot_het))


# ----------------------------------------------------------------------------
# HARNESS D: lambda estimated from finite data -> propagated error in tau_c
# ----------------------------------------------------------------------------
# A practitioner does not know lambda.  Estimate it by AR(1) regression on a finite
# observed series of the environment, then report the spread of tau_c_hat = log2/lam_hat
# and, more importantly, the realised value of a damped design built on lam_hat.

def _est_block(args):
    seed, reps, lam, Tobs, dt, ws = args
    rng = random.Random(seed)
    rho1 = math.exp(-lam * dt)
    sd = math.sqrt(1.0 - rho1 * rho1)
    out = []
    for _ in range(reps):
        x = rng.gauss(0.0, 1.0)
        num = 0.0
        den = 0.0
        for _ in range(Tobs):
            xn = rho1 * x + sd * rng.gauss(0.0, 1.0)
            num += x * xn
            den += x * x
            x = xn
        r = num / den
        if r <= 0.0:
            out.append(None)
        else:
            out.append(-math.log(r) / dt)
    return out


def run_lambda_estimation(lam, Tobs_list, dt, reps, seed0):
    res = {}
    for Tobs in Tobs_list:
        per = max(1, reps // NPROC)
        args = [(seed0 + 131 * i + Tobs, per, lam, Tobs, dt, None) for i in range(NPROC)]
        with Pool(NPROC) as p:
            blocks = p.map(_est_block, args)
        lams = [v for b in blocks for v in b if v is not None]
        m, se = mean_se(lams)
        lams_s = sorted(lams)
        tc = [math.log(2) / l for l in lams_s]
        tc.sort()
        res[str(Tobs)] = dict(
            n=len(lams), lam_true=lam, lam_mean=m, lam_se=se,
            lam_q025=lams_s[int(0.025 * len(lams_s))],
            lam_q975=lams_s[int(0.975 * len(lams_s))],
            tau_c_true=math.log(2) / lam,
            tau_c_median=tc[len(tc) // 2],
            tau_c_q025=tc[int(0.025 * len(tc))],
            tau_c_q975=tc[int(0.975 * len(tc))],
        )
    return res


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------

def main():
    R = {}
    R["meta"] = dict(python=sys.version.split()[0], nproc=NPROC,
                     model="LQ design J(c;x_T)=2<c,x_T>_w - ||c||^2_w on a reversible "
                           "environment; blind c=0, stale c=x_S, damped c=P_tau x_S, "
                           "oracle c=x_T")

    # ---------------- POSITIVE CONTROLS (run first) ----------------
    lam = 1.0
    ws, lams = [1.0], [lam]
    V = sum(ws)
    ctrl_taus = [0.0, 20.0 / lam]
    ctrl, Mc = run_ou(ws, lams, ctrl_taus, 2_000_000, 1001)
    R["positive_controls"] = dict(
        M=Mc, V=V, taus=ctrl_taus, rows=ctrl,
        expect_tau0="stale = damped = oracle = V = %.3f ; blind = 0" % V,
        expect_tauinf="damped -> 0 (blind); stale -> -V; oracle -> +V "
                      "(the team-lead-stated control 'all three -> blind' is WRONG "
                      "for stale and oracle and contradicts the claim under test)",
    )

    # ---------------- (a,b,c) SINGLE RATE ----------------
    taus = [0.0, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.65, 0.693147, 0.75, 0.8, 0.9,
            1.0, 1.25, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0, 7.0]
    rows, M1 = run_ou(ws, lams, taus, 4_000_000, 2002)
    fit = []
    for r in rows:
        t = r["tau"]
        rho = math.exp(-lam * t)
        fit.append(dict(
            tau=t,
            blind=r["blind"], blind_se=r["blind_se"],
            stale=r["stale"], stale_se=r["stale_se"],
            damped=r["damped"], damped_se=r["damped_se"],
            oracle=r["oracle"], oracle_se=r["oracle_se"],
            pred_stale=(2 * rho - 1) * V,
            pred_damped=rho * rho * V,
            pred_oracle=V,
            pred_myopia=(1 - rho) ** 2 * V,
            meas_myopia=r["damped"] - r["stale"],
            z_stale=(r["stale"] - (2 * rho - 1) * V) / max(r["stale_se"], 1e-15),
            z_damped=(r["damped"] - rho * rho * V) / max(r["damped_se"], 1e-15),
            z_myopia=((r["damped"] - r["stale"]) - (1 - rho) ** 2 * V) /
                     max(math.hypot(r["damped_se"], r["stale_se"]), 1e-15),
        ))
    R["single_rate"] = dict(lam=lam, V=V, M=M1, rows=fit,
                            tau_c_theory=math.log(2) / lam)
    pt, lo, up, nb, Mx = crn_crossing(ws, lams, 8_000_000, 3003)
    R["single_rate"]["crossing_measured"] = dict(
        point=pt, ci95=[lo, up], nboot=nb, M=Mx, theory=math.log(2) / lam)

    # ---------------- (d) MULTI RATE ----------------
    for tag, ws_m, lams_m in [
        ("two_rate_1_and_10", [1.0, 1.0], [1.0, 10.0]),
        ("two_rate_heavy_slow", [3.0, 1.0], [0.5, 20.0]),
        ("three_rate", [1.0, 1.0, 1.0], [0.3, 2.0, 15.0]),
    ]:
        Vm = sum(ws_m)
        tct = theory_crossing(ws_m, lams_m)
        pt, lo, up, nb, Mx = crn_crossing(ws_m, lams_m, 6_000_000, 4004 + len(tag))
        naive = math.log(2) / min(lams_m)
        gtaus = [0.0, 0.1, 0.2, 0.3, 0.5, 0.7, 1.0, 1.4, 2.0, 3.0, 5.0]
        gr, Mg = run_ou(ws_m, lams_m, gtaus, 2_000_000, 5005 + len(tag))
        grows = []
        for r in gr:
            t = r["tau"]
            pd = sum(w * math.exp(-2 * l * t) for w, l in zip(ws_m, lams_m))
            ps = sum(w * (2 * math.exp(-l * t) - 1) for w, l in zip(ws_m, lams_m))
            grows.append(dict(tau=t, stale=r["stale"], stale_se=r["stale_se"],
                              damped=r["damped"], damped_se=r["damped_se"],
                              oracle=r["oracle"], oracle_se=r["oracle_se"],
                              pred_stale=ps, pred_damped=pd, pred_oracle=Vm))
        R.setdefault("multi_rate", {})[tag] = dict(
            w=ws_m, lam=lams_m, V=Vm,
            crossing_measured=pt, ci95=[lo, up], nboot=nb, M=Mx,
            crossing_mixture_theory=tct,
            crossing_single_rate_naive_slowest=naive,
            crossing_single_rate_naive_mean_lam=math.log(2) / (sum(
                w * l for w, l in zip(ws_m, lams_m)) / Vm),
            naive_slowest_relative_error=(naive - tct) / tct if tct else None,
            grid=grows, grid_M=Mg,
        )

    # ---------------- (b) damping robustness: alpha sweep ----------------
    # damped design with an arbitrary shrinkage alpha (i.e. a MIS-ESTIMATED lambda):
    # premium = alpha (2 rho - alpha) V, so the safe region is 0 < alpha < 2 rho.
    alpha_rows = []
    for t in [0.5, 1.0, 2.0, 4.0]:
        rho = math.exp(-lam * t)
        for mult in [0.25, 0.5, 1.0, 1.5, 1.9, 2.0, 2.1, 3.0]:
            alpha = mult * rho
            alpha_rows.append(dict(tau=t, rho=rho, alpha=alpha, alpha_over_rho=mult,
                                   pred_premium=alpha * (2 * rho - alpha) * V))
    R["shrinkage_robustness"] = dict(
        note="premium of shrinkage alpha over blind = alpha(2rho-alpha)V; safe iff "
             "0 < alpha < 2rho, i.e. lam_hat > lam - log2/tau. Over-estimating lambda "
             "is ALWAYS safe; under-estimating is safe only within log2/tau.",
        rows=alpha_rows)

    # ---------------- lambda identification from finite data ----------------
    R["lambda_estimation"] = run_lambda_estimation(
        lam=1.0, Tobs_list=[50, 200, 1000, 5000], dt=0.1, reps=4000, seed0=6006)

    # ---------------- Wright-Fisher ----------------
    R["wright_fisher"] = {}
    for tag, N, u in [("N500_u0.005_theta10", 500, 0.005),
                      ("N200_u0.00075_theta0.6", 200, 0.00075)]:
        lam_mut = -math.log(1 - 2 * u)
        tc = math.log(2) / lam_mut
        # tau grid scaled to the true crossover; horizon several correlation times
        wf_taus = [int(round(f * tc)) for f in
                   [0.0, 0.15, 0.3, 0.45, 0.6, 0.75, 0.85, 0.95, 1.0, 1.05, 1.15,
                    1.3, 1.6, 2.0, 2.6, 3.5]]
        T = int(5.0 / lam_mut)
        burn = int(6.0 / lam_mut)
        res = run_wf(N, u, wf_taus, R=1600, burn=burn, T=T, seed0=7007 + N, nboot=300)
        res["T_gens"] = T
        res["burn_gens"] = burn
        res["tau_grid"] = wf_taus
        res["N"] = N
        res["u"] = u
        res["theta_4Nu"] = 4 * N * u
        res["lam_true_per_gen"] = lam_mut
        res["tau_c_true"] = math.log(2) / lam_mut
        res["lam_naive_drift_1_over_2N"] = 1.0 / (2 * N)
        res["tau_c_naive_drift"] = math.log(2) * 2 * N
        R["wright_fisher"][tag] = res

    with open(OUT, "w") as f:
        json.dump(R, f, indent=1)
    print("WROTE", OUT)


if __name__ == "__main__":
    main()
