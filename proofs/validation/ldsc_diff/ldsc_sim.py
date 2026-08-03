#!/usr/bin/env python3.12
"""Differential test of Calibrator/StatisticalGeneticsMethodology.lean:281
geneticCorrelationLDSC against genuine bivariate LD score regression.

Pure stdlib (cluster python3.12 has no numpy/sympy).

Model: standardized genotypes as block-AR(1) Gaussians (the exact setting in
which LDSC's E[z1 z2] = sqrt(N1 N2) rho_G l_j / M + N_o rho_pheno / sqrt(N1 N2)
is derived).  Individual-level simulation, streamed row by row.

Estimators compared
  lean_true  : cosine similarity of the TRUE effect vectors (the Lean body fed
               the quantity its docstring describes)
  lean_hat   : cosine similarity of the ESTIMATED marginal effects (the Lean
               body fed what a user actually has)
  ldsc       : genuine bivariate LD score regression with free intercept
  ldsc_ci    : same with the intercept constrained to the no-overlap value 0
"""
import json
import math
import random
import sys
from multiprocessing import Pool


# ---------------------------------------------------------------- utilities
def ols2(xs, ys):
    """OLS of ys on [1, xs]; returns (intercept, slope)."""
    n = len(xs)
    mx = sum(xs) / n
    my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    slope = sxy / sxx
    return my - slope * mx, slope


def ols_noint(xs, ys):
    """OLS of ys on xs through the origin; returns slope."""
    return sum(x * y for x, y in zip(xs, ys)) / sum(x * x for x in xs)


def cosine(a, b):
    num = sum(x * y for x, y in zip(a, b))
    den = math.sqrt(sum(x * x for x in a) * sum(y * y for y in b))
    return num / den


def blocks(M, B):
    """Block boundaries.  B > 0 gives uniform blocks; B = 0 gives geometrically
    varying block sizes so the LD scores span a wide range (real LDSC gets its
    leverage from l_j varying over orders of magnitude, not from a narrow band).
    Returns a list of (lo, hi) per SNP."""
    sizes = []
    if B > 0:
        while sum(sizes) < M:
            sizes.append(B)
    else:
        cyc = [1, 2, 3, 5, 8, 13, 21, 34, 55]
        i = 0
        while sum(sizes) < M:
            sizes.append(cyc[i % len(cyc)])
            i += 1
    spans = []
    lo = 0
    for s in sizes:
        hi = min(lo + s, M)
        for _ in range(lo, hi):
            spans.append((lo, hi))
        lo = hi
        if lo >= M:
            break
    return spans


def ld_scores(M, B, r):
    """Exact LD scores for block-AR(1) correlation R_jk = r^|j-k| in-block."""
    sp = blocks(M, B)
    return [sum(r ** (2 * abs(j - k)) for k in range(sp[j][0], sp[j][1]))
            for j in range(M)]


def bivnorm(rng, rho, sd1, sd2):
    z1 = rng.gauss(0, 1)
    z2 = rho * z1 + math.sqrt(1 - rho * rho) * rng.gauss(0, 1)
    return z1 * sd1, z2 * sd2


# ---------------------------------------------------------------- one replicate
def one_rep(cfg, seed):
    M, B, r = cfg["M"], cfg["B"], cfg["ld_r"]
    N1, N2, Nover = cfg["N1"], cfg["N2"], cfg["Nover"]
    h1, h2 = cfg["h2_1"], cfg["h2_2"]
    rg, re = cfg["rho_g"], cfg["rho_e"]
    rng = random.Random(seed)

    # true effects on the standardized-genotype scale
    sd1, sd2 = math.sqrt(h1 / M), math.sqrt(h2 / M)
    b1, b2 = [], []
    for _ in range(M):
        u, v = bivnorm(rng, rg, sd1, sd2)
        b1.append(u)
        b2.append(v)

    Np = N1 + N2 - Nover           # pool
    lo2 = N1 - Nover               # study 2 = individuals [lo2, Np)
    sq = math.sqrt(1 - r * r)
    starts = cfg["_starts"]        # True where a new LD block begins
    e_sd1, e_sd2 = math.sqrt(1 - h1), math.sqrt(1 - h2)

    Sx1 = [0.0] * M; Sxx1 = [0.0] * M; Sxy1 = [0.0] * M
    Sx2 = [0.0] * M; Sxx2 = [0.0] * M; Sxy2 = [0.0] * M
    Sy1 = Syy1 = Sy2 = Syy2 = 0.0

    for i in range(Np):
        x = [0.0] * M
        prev = 0.0
        for j in range(M):
            if starts[j]:
                prev = rng.gauss(0, 1)
            else:
                prev = r * prev + sq * rng.gauss(0, 1)
            x[j] = prev
        in1 = i < N1
        in2 = i >= lo2
        if in1 and in2:
            e1, e2 = bivnorm(rng, re, e_sd1, e_sd2)
        else:
            e1 = rng.gauss(0, e_sd1)
            e2 = rng.gauss(0, e_sd2)
        if in1:
            y = sum(xx * bb for xx, bb in zip(x, b1)) + e1
            Sy1 += y; Syy1 += y * y
            for j in range(M):
                xj = x[j]
                Sx1[j] += xj; Sxx1[j] += xj * xj; Sxy1[j] += xj * y
        if in2:
            y = sum(xx * bb for xx, bb in zip(x, b2)) + e2
            Sy2 += y; Syy2 += y * y
            for j in range(M):
                xj = x[j]
                Sx2[j] += xj; Sxx2[j] += xj * xj; Sxy2[j] += xj * y

    def marginals(Sx, Sxx, Sxy, Sy, Syy, N):
        vy = Syy / N - (Sy / N) ** 2
        out = []
        for j in range(M):
            vx = Sxx[j] / N - (Sx[j] / N) ** 2
            cxy = Sxy[j] / N - (Sx[j] / N) * (Sy / N)
            out.append(cxy / math.sqrt(vx * vy))   # marginal corr = std. effect
        return out

    bh1 = marginals(Sx1, Sxx1, Sxy1, Sy1, Syy1, N1)
    bh2 = marginals(Sx2, Sxx2, Sxy2, Sy2, Syy2, N2)
    z1 = [v * math.sqrt(N1) for v in bh1]
    z2 = [v * math.sqrt(N2) for v in bh2]

    L = cfg["_L"]
    # univariate LDSC:  E[z^2] = N h2 l / M + 1
    _, s1 = ols2(L, [v * v for v in z1])
    _, s2 = ols2(L, [v * v for v in z2])
    h2a, h2b = s1 * M / N1, s2 * M / N2
    # bivariate LDSC:  E[z1 z2] = sqrt(N1 N2) rho_G l / M + N_o rho_p/sqrt(N1N2)
    icpt, sxy = ols2(L, [a * b for a, b in zip(z1, z2)])
    gcov = sxy * M / math.sqrt(N1 * N2)
    sxy_c = ols_noint(L, [a * b for a, b in zip(z1, z2)])
    gcov_c = sxy_c * M / math.sqrt(N1 * N2)

    def rat(g, x, y):
        d = x * y
        return g / math.sqrt(d) if d > 0 else float("nan")

    return {
        "lean_true": cosine(b1, b2),
        "lean_hat": cosine(bh1, bh2),
        "ldsc": rat(gcov, h2a, h2b),
        "ldsc_ci": rat(gcov_c, h2a, h2b),
        "ldsc_intercept": icpt,
        "h2_1_ldsc": h2a,
        "h2_2_ldsc": h2b,
        "gcov_ldsc": gcov,
        "gcov_true": sum(a * b for a, b in zip(b1, b2)),
    }


def run_cfg(cfg):
    cfg = dict(cfg)
    cfg["_L"] = ld_scores(cfg["M"], cfg["B"], cfg["ld_r"])
    sp = blocks(cfg["M"], cfg["B"])
    cfg["_starts"] = [j == sp[j][0] for j in range(cfg["M"])]
    reps = [one_rep(cfg, cfg["seed"] * 1000 + k) for k in range(cfg["reps"])]
    keys = reps[0].keys()
    out = {"cfg": {k: v for k, v in cfg.items() if not k.startswith("_")}}
    for k in keys:
        vals = [rp[k] for rp in reps]
        n = len(vals)
        m = sum(vals) / n
        sd = math.sqrt(sum((v - m) ** 2 for v in vals) / (n - 1)) if n > 1 else 0.0
        out[k] = {"mean": m, "se": sd / math.sqrt(n)}
    # analytic predictions
    c = out["cfg"]
    M, N1, N2 = c["M"], c["N1"], c["N2"]
    h1, h2, rg = c["h2_1"], c["h2_2"], c["rho_g"]
    Lbar = sum(cfg["_L"]) / M          # signal in marginal effects is amplified
    s1, s2 = h1 * Lbar, h2 * Lbar      # by the mean LD score; noise is not
    att = math.sqrt(s1 / (s1 + M / N1)) * math.sqrt(s2 / (s2 + M / N2))
    rho_p = rg * math.sqrt(h1 * h2) + c["rho_e"] * math.sqrt((1 - h1) * (1 - h2))
    bias = (M * c["Nover"] * rho_p / (N1 * N2)) / math.sqrt(
        (s1 + M / N1) * (s2 + M / N2))
    out["mean_ld_score"] = Lbar
    out["pred_lean_hat"] = rg * att + bias
    out["pred_attenuation_factor"] = att
    out["pred_overlap_bias"] = bias
    out["pred_ldsc_intercept"] = c["Nover"] * rho_p / math.sqrt(N1 * N2)
    # pooled ratio: ratio of the mean linear estimates, far better behaved than
    # the mean of per-replicate ratios when h2 estimates can go negative
    d = out["h2_1_ldsc"]["mean"] * out["h2_2_ldsc"]["mean"]
    out["ldsc_pooled"] = (out["gcov_ldsc"]["mean"] / math.sqrt(d)
                          if d > 0 else float("nan"))
    out["lean_true_pooled"] = out["lean_true"]["mean"]
    return out


BASE = dict(M=800, B=0, ld_r=0.7, N1=1600, N2=1600, Nover=0,
            h2_1=0.5, h2_2=0.5, rho_g=0.6, rho_e=0.0, reps=16, seed=1)


def cfgs():
    out = []
    s = 0
    def add(name, **kw):
        nonlocal s
        s += 1
        c = dict(BASE); c.update(kw); c["name"] = name; c["seed"] = 100 + s
        out.append(c)

    # --- POSITIVE CONTROL 1 (no-false-alarm): negligible noise, no LD, no
    #     overlap.  Both estimators must return rho_g; if lean_hat missed here
    #     the harness itself would be broken.
    add("PC1_lowNoise_noLD_noOverlap", ld_r=0.0, M=200, N1=20000, N2=20000,
        h2_1=0.8, h2_2=0.8, reps=8)
    # --- POSITIVE CONTROL 2 (defect present by construction): no LD, M/N = 1,
    #     h2 = 0.5 => analytic attenuation factor exactly 1/2.  The harness must
    #     report lean_hat ~ rho_g/2 while LDSC still recovers rho_g.
    add("PC2_knownAttenuation_half", M=800, N1=800, N2=800, ld_r=0.0, reps=16)

    # --- attenuation ladder, no overlap, with LD
    for ratio in (0.2, 0.5, 1.0, 4.0):
        N = int(800 / ratio)
        add(f"ATT_LD_MoverN_{ratio:g}", N1=N, N2=N, reps=16)
    # --- attenuation without LD (isolates estimation noise from LD)
    for ratio in (0.2, 1.0):
        N = int(800 / ratio)
        add(f"ATT_noLD_MoverN_{ratio:g}", ld_r=0.0, N1=N, N2=N, reps=16)

    # --- sample overlap at TRUE rho_g = 0 (pure false-signal test)
    for f in (0.0, 0.5, 1.0):
        add(f"OVL_rg0_frac{f:g}", rho_g=0.0, rho_e=0.5, Nover=int(1600 * f))
    # --- sample overlap with a real signal, and with NEGATIVE env correlation
    add("OVL_rg0.6_frac1_re+0.5", rho_g=0.6, rho_e=0.5, Nover=1600)
    add("OVL_rg0.6_frac1_re-0.5", rho_g=0.6, rho_e=-0.5, Nover=1600)
    return out


if __name__ == "__main__":
    nproc = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    with Pool(nproc) as p:
        res = p.map(run_cfg, cfgs())
    print(json.dumps(res, indent=1))
