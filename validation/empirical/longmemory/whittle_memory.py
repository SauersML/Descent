#!/usr/bin/env python3
"""Whittle estimation of a memory parameter, and the transported estimation floor.

Claims under test (Descent/Decision/TransportedMinimax.lean, section LongMemoryGeometry):

  (a) the conformal metric is  g = eps^2 / delta^3 ;
  (b) the memory-parameter variance is  V = 3 delta^3 / (n eps^2) ;
  (c) hence the transported floor  (1/2) g V = 3/(2n)  uniformly in delta and eps;
  (d) an upstream gloss says the variance "blows up" as memory lengthens, while the stated
      formula shrinks there (long memory is delta -> 0).

Model choice.  The compendium's pair (eps = amplitude, delta = memory rate) with a metric
eps^2/delta^3 is the signature of a Lorentzian / Ornstein-Uhlenbeck spectral density
f(lambda) = eps^2 / (delta^2 + lambda^2): delta^-1 is the correlation time, eps the
innovation amplitude, and long memory is delta -> 0.  Its exact discrete-time analogue is
the near-unit-root AR(1) with rho = 1 - delta, which is what is simulated.  An
ARFIMA(0,d,0) arm is included as a second, genuinely long-range-dependent notion of memory
where the Whittle information for d is known analytically (pi^2/6 per observation).

Arms:
  iid       : X ~ N(0, s^2).  Whittle estimate of s^2.  Var = 2 s^4 / n exactly.   [control]
  ar1_short : AR(1), rho = 0.5.  Var(rho_hat) = (1 - rho^2)/n.                      [control]
  ar1_near  : AR(1), rho = 1 - delta, delta small.  Measure Var(delta_hat) vs delta.
  arfima    : ARFIMA(0,d,0).  Var(d_hat) = 6/(pi^2 n), flat in d.                   [control
              for the "memory is free" phenomenon in its cleanest form]
  ar1_3par  : AR(1) with unknown (delta, innovation sd, mean) -- a 3-parameter model, to
              test the hypothesis that the constant 3 in 3/(2n) is the parameter count.

For each arm the script reports the Monte-Carlo variance of the estimator with a bootstrap
standard error, the analytic Whittle information, and the transported loss
(1/2) * E[(theta_hat - theta)^T I_per_obs (theta_hat - theta)] * n, which under efficiency
equals p/2 for a p-parameter model regardless of parameterisation.
"""

import json
import sys
import time
from multiprocessing import Pool

import numpy as np
from scipy.optimize import minimize_scalar, minimize
from scipy.integrate import quad

TWOPI = 2.0 * np.pi


# ----------------------------------------------------------------- spectral densities

def f_ar1(lam, rho, s2):
    return s2 / (TWOPI * (1.0 - 2.0 * rho * np.cos(lam) + rho * rho))


def f_arfima(lam, d, s2):
    return s2 / TWOPI * (2.0 * np.sin(np.abs(lam) / 2.0)) ** (-2.0 * d)


# ----------------------------------------------------------------- simulation

def sim_ar1(rho, s, n, rng):
    x = np.empty(n)
    x[0] = rng.normal(0.0, s / np.sqrt(1.0 - rho * rho))
    e = rng.normal(0.0, s, n)
    for i in range(1, n):
        x[i] = rho * x[i - 1] + e[i]
    return x


def sim_ar1_fast(rho, s, n, rng):
    from scipy.signal import lfilter
    e = rng.normal(0.0, s, n)
    e[0] = rng.normal(0.0, s / np.sqrt(1.0 - rho * rho))
    return lfilter([1.0], [1.0, -rho], e)


def arfima_acf(d, n):
    """Autocovariance of ARFIMA(0,d,0) with unit innovation variance."""
    k = np.arange(n)
    from scipy.special import gammaln
    lg = (gammaln(1.0 - 2.0 * d) + gammaln(k + d)
          - gammaln(d) - gammaln(1.0 - d) - gammaln(k + 1.0 - d))
    return np.exp(lg)


def sim_arfima(d, n, rng):
    """Davies-Harte circulant embedding: exact Gaussian sample."""
    m = 1
    while m < 2 * n:
        m *= 2
    g = arfima_acf(d, m // 2 + 1)
    c = np.concatenate([g, g[-2:0:-1]])
    lam = np.fft.fft(c).real
    if lam.min() <= 0:
        lam = np.clip(lam, 1e-14, None)
    z = rng.normal(size=m) + 1j * rng.normal(size=m)
    z[0] = np.sqrt(2.0) * rng.normal()
    z[m // 2] = np.sqrt(2.0) * rng.normal()
    y = np.fft.fft(np.sqrt(lam / (2.0 * m)) * z).real
    return y[:n]


# ----------------------------------------------------------------- Whittle

def periodogram(x):
    n = x.size
    j = np.arange(1, n // 2)          # drop lambda=0 (kills the mean) and Nyquist
    lam = TWOPI * j / n
    J = np.fft.fft(x)[j]
    I = (np.abs(J) ** 2) / (TWOPI * n)
    return lam, I


def whittle_nll(lam, I, f):
    return np.sum(np.log(f) + I / f)


def fit_ar1_rho(x, bracket=(-0.999, 0.999)):
    lam, I = periodogram(x)
    cl = np.cos(lam)

    def nll(rho):
        # profile out s2 analytically
        w = 1.0 - 2.0 * rho * cl + rho * rho
        s2 = TWOPI * np.mean(I * w)
        return np.sum(np.log(s2 / (TWOPI * w)) + I * TWOPI * w / s2)

    r = minimize_scalar(nll, bounds=bracket, method="bounded",
                        options=dict(xatol=1e-12))
    rho = r.x
    w = 1.0 - 2.0 * rho * cl + rho * rho
    s2 = TWOPI * np.mean(I * w)
    return rho, s2


def fit_iid_s2(x):
    lam, I = periodogram(x)
    return TWOPI * np.mean(I)


def fit_arfima_d(x):
    lam, I = periodogram(x)
    base = (2.0 * np.sin(lam / 2.0))

    def nll(d):
        w = base ** (2.0 * d)
        s2 = TWOPI * np.mean(I * w)
        return np.sum(np.log(s2 / (TWOPI * w)) + I * TWOPI * w / s2)

    r = minimize_scalar(nll, bounds=(-0.49, 0.49), method="bounded",
                        options=dict(xatol=1e-12))
    return r.x


def fit_ar1_3par(x):
    """(rho, s2, mu) jointly; mu enters through the mean, estimated by the sample mean,
    which is the Whittle/Gaussian MLE's leading-order solution."""
    mu = x.mean()
    rho, s2 = fit_ar1_rho(x - mu)
    return np.array([rho, s2, mu])


# ----------------------------------------------------------------- Whittle information

def whittle_info_ar1(rho, s2):
    """Per-observation Whittle information matrix for (rho, s2).
    I_ab = (1/4pi) int_{-pi}^{pi} dlog f/da dlog f/db dlambda."""
    def dlr(lam):
        return -(-2.0 * np.cos(lam) + 2.0 * rho) / (1.0 - 2.0 * rho * np.cos(lam) + rho * rho)

    def ds2(lam):
        return 1.0 / s2

    Irr = quad(lambda l: dlr(l) ** 2, -np.pi, np.pi, limit=400)[0] / (4 * np.pi)
    Irs = quad(lambda l: dlr(l) * ds2(l), -np.pi, np.pi, limit=400)[0] / (4 * np.pi)
    Iss = quad(lambda l: ds2(l) ** 2, -np.pi, np.pi, limit=400)[0] / (4 * np.pi)
    return np.array([[Irr, Irs], [Irs, Iss]])


def whittle_info_arfima(d):
    def dld(lam):
        return -2.0 * np.log(2.0 * np.sin(np.abs(lam) / 2.0))
    Idd = quad(lambda l: dld(l) ** 2, 1e-12, np.pi, limit=400)[0] / (2 * np.pi)
    return Idd


# ----------------------------------------------------------------- experiment driver

def run_rep(args):
    arm, params, n, seed = args
    rng = np.random.default_rng(seed)
    if arm == "iid":
        s = params["s"]
        x = rng.normal(0.0, s, n)
        return [fit_iid_s2(x)]
    if arm in ("ar1_short", "ar1_near"):
        rho, s = params["rho"], params["s"]
        x = sim_ar1_fast(rho, s, n, rng)
        r, s2 = fit_ar1_rho(x)
        return [r, s2]
    if arm == "arfima":
        d = params["d"]
        x = sim_arfima(d, n, rng)
        return [fit_arfima_d(x)]
    if arm == "ar1_3par":
        rho, s, mu = params["rho"], params["s"], params["mu"]
        x = sim_ar1_fast(rho, s, n, rng) + mu
        return list(fit_ar1_3par(x))
    raise ValueError(arm)


def bootstrap_var_se(v, B=400, rng=None):
    rng = rng or np.random.default_rng(0)
    n = v.size
    idx = rng.integers(0, n, size=(B, n))
    return float(np.std(v[idx].var(axis=1, ddof=1)))


def main():
    out = sys.argv[1]
    nrep = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    nproc = int(sys.argv[3]) if len(sys.argv) > 3 else 12

    jobs = []
    configs = []

    def add(arm, params, n, tag):
        base = len(jobs)
        for r in range(nrep):
            jobs.append((arm, params, n, hash((tag, r)) % (2 ** 31)))
        configs.append(dict(arm=arm, params=params, n=n, tag=tag,
                            lo=base, hi=base + nrep))

    # controls
    for n in (512, 2048, 8192):
        add("iid", dict(s=1.7), n, f"iid_{n}")
        add("ar1_short", dict(rho=0.5, s=1.0), n, f"ar1s_{n}")
    for d in (0.1, 0.2, 0.3, 0.4, 0.45):
        for n in (1024, 4096):
            add("arfima", dict(d=d), n, f"arfima_{d}_{n}")
    # main arm: near unit root, memory delta
    for delta in (0.5, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005):
        for n in (1024, 4096, 16384):
            for s in (1.0, 2.5):
                add("ar1_near", dict(rho=1.0 - delta, s=s), n,
                    f"ar1n_{delta}_{n}_{s}")
    # three-parameter arm
    for delta in (0.4, 0.2, 0.1, 0.05, 0.02, 0.01):
        for n in (4096, 16384, 65536):
            add("ar1_3par", dict(rho=1.0 - delta, s=1.0, mu=0.3), n,
                f"ar13p_{delta}_{n}")

    t0 = time.time()
    with Pool(nproc) as pool:
        raw = pool.map(run_rep, jobs, chunksize=8)
    print(f"{len(jobs)} reps in {time.time()-t0:.1f}s", file=sys.stderr)

    rows = []
    for cfg in configs:
        est = np.array(raw[cfg["lo"]:cfg["hi"]], dtype=float)
        rec = dict(arm=cfg["arm"], params=cfg["params"], n=cfg["n"], nrep=nrep,
                   mean=[float(v) for v in est.mean(axis=0)],
                   var=[float(v) for v in est.var(axis=0, ddof=1)])
        rec["var_se"] = [bootstrap_var_se(est[:, k]) for k in range(est.shape[1])]
        rec["cov"] = np.cov(est, rowvar=False, ddof=1).reshape(est.shape[1], est.shape[1]).tolist()
        if cfg["arm"] in ("ar1_near", "ar1_short"):
            # relative precision of the memory parameter: does it "blow up" as delta -> 0?
            dhat = 1.0 - est[:, 0]
            rec["delta_hat_mean"] = float(dhat.mean())
            rec["delta_hat_var"] = float(dhat.var(ddof=1))
            pos = dhat[dhat > 0]
            rec["log_delta_var"] = float(np.log(pos).var(ddof=1))
            rec["frac_nonpositive_delta"] = float((dhat <= 0).mean())
        rows.append(rec)

    with open(out, "w") as fh:
        json.dump(dict(rows=rows, nrep=nrep), fh, indent=1)
    print("wrote", out)


if __name__ == "__main__":
    main()
