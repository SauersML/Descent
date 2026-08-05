#!/usr/bin/env python3.12
"""Simulation of the blind-frequency prediction (MATH_LEDGER row 9 / gap #4).

Claim under test (Descent/PopGen/StandardizedGenotypeMoments.lean:563, `gaussianKurtosisMaf`):

    "the prediction that an interaction statistic relying on fourth-cumulant
     separation loses power near this frequency has not been checked in simulation.
     It is the most directly falsifiable number this development produces."

with the blind frequency q* = (3 - sqrt 3)/6 = 0.2113248654..., where the standardized
HWE genotype has E[x^4] = 1/V = 3 exactly (V = 2q(1-q) = 1/3), i.e. fourth cumulant zero.

Three statistics are measured on a MAF grid straddling q*.  All three are calibrated
EMPIRICALLY at each MAF from its own null replicates (two-sided, alpha = 0.05), so the
size is 0.05 by construction everywhere and power is comparable across MAF.

  S1  HUB / FOURTH-CUMULANT CHANNEL (latent locus).
      y = b*x + sqrt(1-b^2)*e,  x not observed.  Statistic = sample excess kurtosis of y.
      Population value: kappa4(y) = b^4 * kappa4(x) = b^4 * (1/V - 3).
      -> predicted to vanish EXACTLY at q*.  This is the channel the corpus describes.

  S2  FOURTH-ORDER CUMULANT INTERACTION TEST with a MEASURED locus.
      null  y = b*x + s*e                 (purely additive)
      alt   y = b*x + g*x*u + s*e         (x interacts with a hidden Gaussian modifier u)
      Statistic = cum(y,y,x,x) = E[y^2 x^2] - E[y^2]E[x^2] - 2 E[yx]^2.
      Population value: null  b^2 (1/V - 3)      <- zero exactly at q*
                        alt   (b^2+g^2)(1/V - 1) - 2 b^2
      So at q* the statistic is UNBIASED under the additive null; the separation
      alt-null = g^2 (1/V - 1) is nonzero everywhere.  Tests whether "blind" means
      loss of power or merely loss of null bias.

  S3  POSITIVE CONTROL: ordinary OLS interaction t-test, y ~ 1 + x1 + x2 + x1*x2,
      both loci measured, true gamma != 0.  Must have high power at every MAF,
      including q*.  A null result in S1/S2 is only interpretable against this.

Also recorded: the mean of each statistic under its own null, to compare against the
closed-form population value (an internal consistency check on the estimator), and the
size of S2 when calibrated against the GAUSSIAN SURROGATE instead of the true null.

stdlib only.
"""

import json
import math
import os
import random
import sys
from multiprocessing import Pool

Q_STAR = (3.0 - math.sqrt(3.0)) / 6.0

N = 8000          # individuals per replicate
REPS = 2500       # replicates per (MAF, model)
B2 = 0.30         # additive variance of the focal locus
G2 = 0.05         # interaction variance with the hidden modifier (S2 alternative)
GAMMA_EP = 0.05   # two-locus interaction coefficient (S3 alternative)
A_EP = 0.30       # per-locus additive coefficient in the S3 model

GRID = ([0.02, 0.05, 0.08, 0.11, 0.14]
        + [round(0.155 + 0.005 * i, 4) for i in range(25)]   # 0.155 .. 0.275
        + [0.29, 0.32, 0.35, 0.40, 0.45, 0.50])


# --------------------------------------------------------------------------

def geno_sampler(q, rng):
    """One uniform per genotype; returns standardized genotype value."""
    p0 = (1.0 - q) ** 2
    p1 = 2.0 * q * (1.0 - q)
    v = math.sqrt(2.0 * q * (1.0 - q))
    c0 = (0.0 - 2.0 * q) / v
    c1 = (1.0 - 2.0 * q) / v
    c2 = (2.0 - 2.0 * q) / v
    t0 = p0
    t1 = p0 + p1
    r = rng.random
    def draw(n):
        out = [0.0] * n
        for i in range(n):
            uu = r()
            out[i] = c0 if uu < t0 else (c1 if uu < t1 else c2)
        return out
    return draw


def excess_kurtosis(y):
    n = len(y)
    m = sum(y) / n
    s2 = 0.0
    s4 = 0.0
    for v in y:
        d = v - m
        d2 = d * d
        s2 += d2
        s4 += d2 * d2
    return n * s4 / (s2 * s2) - 3.0


def cum22(y, x):
    """cum(y,y,x,x) with y centered and x centered+scaled to unit sample variance."""
    n = len(x)
    mx = sum(x) / n
    vx = sum((v - mx) ** 2 for v in x) / n
    sx = math.sqrt(vx)
    my = sum(y) / n
    eyyxx = 0.0
    eyy = 0.0
    eyx = 0.0
    for i in range(n):
        xc = (x[i] - mx) / sx
        yc = y[i] - my
        yy = yc * yc
        eyyxx += yy * xc * xc
        eyy += yy
        eyx += yc * xc
    eyyxx /= n
    eyy /= n
    eyx /= n
    return eyyxx - eyy - 2.0 * eyx * eyx


def ols_interaction_t(y, x1, x2):
    """t statistic for the coefficient on x1*x2 in y ~ 1 + x1 + x2 + x1x2."""
    n = len(y)
    p = 4
    XtX = [[0.0] * p for _ in range(p)]
    Xty = [0.0] * p
    for i in range(n):
        row = (1.0, x1[i], x2[i], x1[i] * x2[i])
        yi = y[i]
        for a in range(p):
            ra = row[a]
            Xty[a] += ra * yi
            for bq in range(a, p):
                XtX[a][bq] += ra * row[bq]
    for a in range(p):
        for bq in range(a):
            XtX[a][bq] = XtX[bq][a]
    # solve and invert via Gauss-Jordan on [XtX | I | Xty]
    M = [XtX[i][:] + [1.0 if i == j else 0.0 for j in range(p)] + [Xty[i]] for i in range(p)]
    for c in range(p):
        piv = max(range(c, p), key=lambda r: abs(M[r][c]))
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [v / pv for v in M[c]]
        for r in range(p):
            if r != c and M[r][c] != 0.0:
                f = M[r][c]
                M[r] = [vr - f * vc for vr, vc in zip(M[r], M[c])]
    beta = [M[i][2 * p] for i in range(p)]
    inv33 = M[3][p + 3]
    rss = 0.0
    for i in range(n):
        pred = beta[0] + beta[1] * x1[i] + beta[2] * x2[i] + beta[3] * x1[i] * x2[i]
        d = y[i] - pred
        rss += d * d
    s2 = rss / (n - p)
    se = math.sqrt(s2 * inv33)
    return beta[3] / se


def quantiles(vals, lo=0.025, hi=0.975):
    s = sorted(vals)
    m = len(s)
    return s[int(lo * m)], s[min(m - 1, int(hi * m))]


def run_maf(args):
    q, seed = args
    rng = random.Random(seed)
    gauss = rng.gauss
    draw = geno_sampler(q, rng)

    b = math.sqrt(B2)
    g = math.sqrt(G2)
    s_add = math.sqrt(1.0 - B2)
    s_int = math.sqrt(1.0 - B2 - G2)

    s1_null, s1_alt = [], []
    s2_null, s2_alt = [], []
    s3_null, s3_alt = [], []

    for _ in range(REPS):
        x1 = draw(N)
        x2 = draw(N)
        u = [gauss(0.0, 1.0) for _ in range(N)]
        e = [gauss(0.0, 1.0) for _ in range(N)]

        # ---- S1: hub channel, latent locus
        y_g = e                                                  # null: pure Gaussian
        y_a = [b * x1[i] + s_add * e[i] for i in range(N)]       # alt: additive locus
        s1_null.append(excess_kurtosis(y_g))
        s1_alt.append(excess_kurtosis(y_a))

        # ---- S2: fourth-order cumulant with a measured locus
        y_i = [b * x1[i] + g * x1[i] * u[i] + s_int * e[i] for i in range(N)]
        s2_null.append(cum22(y_a, x1))       # additive null
        s2_alt.append(cum22(y_i, x1))

        # ---- S3: positive control, OLS interaction t
        base = [A_EP * (x1[i] + x2[i]) + e[i] for i in range(N)]
        y_e0 = base
        y_e1 = [base[i] + GAMMA_EP * x1[i] * x2[i] for i in range(N)]
        s3_null.append(ols_interaction_t(y_e0, x1, x2))
        s3_alt.append(ols_interaction_t(y_e1, x1, x2))

    V = 2.0 * q * (1.0 - q)
    out = {"maf": q, "V": V, "n": N, "reps": REPS}

    for name, nulls, alts, pred_null, pred_alt in (
        ("S1_kurtosis", s1_null, s1_alt, 0.0, B2 * B2 * (1.0 / V - 3.0)),
        ("S2_cum22", s2_null, s2_alt,
         B2 * (1.0 / V - 3.0), (B2 + G2) * (1.0 / V - 1.0) - 2.0 * B2),
        ("S3_ols_control", s3_null, s3_alt, 0.0, None),
    ):
        lo, hi = quantiles(nulls)
        power = sum(1 for v in alts if v < lo or v > hi) / len(alts)
        size = sum(1 for v in nulls if v < lo or v > hi) / len(nulls)
        mn = sum(nulls) / len(nulls)
        ma = sum(alts) / len(alts)
        sdn = math.sqrt(sum((v - mn) ** 2 for v in nulls) / (len(nulls) - 1))
        out[name] = {
            "power": power,
            "power_se": math.sqrt(max(power * (1 - power), 1e-12) / len(alts)),
            "size_selfcal": size,
            "mean_null": mn, "sd_null": sdn, "mean_alt": ma,
            "predicted_mean_null": pred_null,
            "predicted_mean_alt": pred_alt,
            "null_crit": [lo, hi],
        }

    # S2 calibrated against the Gaussian surrogate (null centred at 0, same spread):
    lo, hi = quantiles(s2_null)
    half = 0.5 * (hi - lo)
    out["S2_cum22"]["size_gaussian_surrogate"] = (
        sum(1 for v in s2_null if abs(v) > half) / len(s2_null))
    return out


def main():
    nproc = int(os.environ.get("NPROC", "16"))
    tasks = [(q, 900000 + i * 7919) for i, q in enumerate(GRID)]
    with Pool(nproc) as pool:
        rows = pool.map(run_maf, tasks)
    res = {
        "q_star": Q_STAR,
        "params": {"N": N, "REPS": REPS, "B2": B2, "G2": G2,
                   "GAMMA_EP": GAMMA_EP, "A_EP": A_EP, "alpha": 0.05},
        "rows": rows,
    }
    json.dump(res, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
