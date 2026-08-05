#!/usr/bin/env python3
"""Empirical test of the BLOCK-COUNT reduction asserted in
Descent/Portability/ScoreDistribution.lean, section `BlockCount`.

THE CLAIM UNDER TEST (the Lean file carries it as an unproved analytic input):

    a polygenic score over m markers with LD correlation length L behaves,
    for normal-approximation purposes, like a sum over m/L effectively
    independent BLOCKS.

Consequences the Lean file then proves algebraically and which we also measure:

    deviation(m markers, corr length L)  ==  deviation(m/L independent markers)
    deviation(m markers, corr length L)  ==  sqrt(L) * deviation(m independent markers)

WHAT IS MEASURED

For a standardized score Z we measure three deviation-from-normal functionals:

  * skew(Z)      -- the Berry-Esseen-relevant one.  For an iid sum of n summands
                    skew = gamma/sqrt(n), so skew IS the sqrt(effective count)
                    probe, and it is estimable to ~1e-3 with a few 1e5 draws.
  * exkurt(Z)    -- scales as 1/n, an independent probe of the same count.
  * KS(Z, N(0,1))-- the actual distributional distance a practitioner cares about.

REFERENCE VALUES.  For an INDEPENDENT panel the three functionals are available in
closed form given the weight vector, so the reference arms carry no Monte-Carlo
noise at all:

    score = sum_j w_j g_j ,  g_j iid,  mean mu1, var v1, 3rd central mu3,
                                       4th cumulant k4_1
    skew   = mu3 * S3 / (v1 * S2)^{3/2}
    exkurt = k4_1 * S4 / (v1 * S2)^2          where Sk = sum_j w_j^k

(KS has no closed form and its independent reference is simulated.)

ARMS

  indep       L=1, genotypes drawn marker-by-marker through a DIFFERENT code path
              from every other arm.  Positive control on the machinery.
  blockconst  block-constant haplotypes, deterministic block length L.
  copy        Li-Stephens-style copying chain: at each marker, redraw with prob
              1/L else copy the previous marker.  Block lengths ~ Geometric(1/L),
              mean L.  This is the genuine renewal process, and its lag-d
              correlation is exactly (1-1/L)^d -- the same expression the Lean
              file calls `residualDiscreteness`.
  latent      NEGATIVE CONTROL.  Equicorrelated liability: a single global factor
              with loading `a` couples every marker to every other.  There is no
              excursion decomposition and no renewal.  `a` is calibrated so the
              score's VARIANCE INFLATION matches the copy arm at the same L, i.e.
              a practitioner reading correlation length off variance inflation
              assigns it the same L.  The block reduction has no right to hold.
  copy_global NEGATIVE CONTROL (subtle).  copy(L) local renewal PLUS a weak global
              factor contributing only a few percent of the variance.  Tests
              whether a small non-renewal component destroys the law.

CONTROLS DEMANDED BY THE REPO STANDARD
  * L=1 in blockconst and copy must reproduce indep exactly.
  * latent / copy_global must BREAK the prediction; if they do not, the test has
    no discriminating power and the confirmation is worthless.
"""

import json
import math
import os
import sys
import time
from multiprocessing import Pool

import numpy as np

P_ALLELE = 0.2          # haplotype allele frequency; genotype = h1 + h2
N_PER_REP = 200_000
N_REPS = 8
CHUNK_CELLS = 4_000_000       # individuals x columns held at once


def chunk_for(cols):
    return max(1000, min(25_000, CHUNK_CELLS // max(cols, 1)))
KS_SUBSET_L = (1, 4, 16)

# ---------------------------------------------------------------- normal CDF


def _phi(x):
    """Abramowitz & Stegun 7.1.26 erf, |err| < 1.5e-7.  Ample for KS at 1e-3."""
    z = np.asarray(x, dtype=np.float64) / math.sqrt(2.0)
    s = np.sign(z)
    az = np.abs(z)
    t = 1.0 / (1.0 + 0.3275911 * az)
    y = 1.0 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t
                - 0.284496736) * t + 0.254829592) * t * np.exp(-az * az)
    return 0.5 * (1.0 + s * y)


def _phi_inv(q):
    lo, hi = -12.0, 12.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if _phi(mid) < q:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


THRESH = _phi_inv(1.0 - P_ALLELE)   # liability threshold giving allele freq p

# ------------------------------------------------------- single-marker moments

_V1 = 2.0 * P_ALLELE * (1.0 - P_ALLELE)
_MU3 = 2.0 * P_ALLELE * (1.0 - P_ALLELE) * (1.0 - 2.0 * P_ALLELE)
_MU4 = 2.0 * P_ALLELE * (1.0 - P_ALLELE)          # Binom(2,p) 4th central, n=2
_K4 = _MU4 - 3.0 * _V1 * _V1


def indep_moments(w):
    """Exact skew / excess kurtosis / variance of an INDEPENDENT panel score."""
    s2 = float(np.sum(w ** 2))
    s3 = float(np.sum(w ** 3))
    s4 = float(np.sum(w ** 4))
    var = _V1 * s2
    return {
        "var": var,
        "skew": _MU3 * s3 / var ** 1.5,
        "exkurt": _K4 * s4 / var ** 2,
    }


# ------------------------------------------------------------------- weights


def draw_weights(rng, m, mode):
    if mode == "unit":
        return np.ones(m)
    if mode == "cont":                 # positive, heterogeneous effect sizes
        return np.abs(rng.standard_normal(m))
    if mode == "signed":               # sign-random: LD cross terms cancel
        return rng.standard_normal(m)
    raise ValueError(mode)


# ------------------------------------------------------------- allele drawing


def _block_alleles(rng, shape, a):
    """Bernoulli(p) block alleles.  a>0 couples every block of an individual to a
    single global liability factor -> non-renewal long-range dependence."""
    if a <= 0.0:
        return rng.random(shape) < P_ALLELE
    u = rng.standard_normal((shape[0], 1))
    liab = math.sqrt(a) * u + math.sqrt(1.0 - a) * rng.standard_normal(shape)
    return liab > THRESH


# ----------------------------------------------------------------- generators
# Each returns scores for `n` individuals.  Genotype = haplotype1 + haplotype2,
# the two haplotypes drawn independently (independent global factors too).


def gen_indep(rng, w, n, a=0.0):
    """Marker-by-marker genotype matrix.  Deliberately a separate code path."""
    m = w.size
    out = np.empty(n)
    ck = chunk_for(m)
    for s in range(0, n, ck):
        c = min(ck, n - s)
        g = _block_alleles(rng, (c, m), a).astype(np.float64)
        g += _block_alleles(rng, (c, m), a)
        out[s:s + c] = g @ w
    return out


def gen_blockconst(rng, w, n, L, a=0.0):
    m = w.size
    B = m // L
    W = np.concatenate([[0.0], np.cumsum(w)])
    bw = W[L * np.arange(1, B + 1)] - W[L * np.arange(B)]
    out = np.empty(n)
    ck = chunk_for(B)
    for s in range(0, n, ck):
        c = min(ck, n - s)
        g = _block_alleles(rng, (c, B), a).astype(np.float64)
        g += _block_alleles(rng, (c, B), a)
        out[s:s + c] = g @ bw
    return out


def gen_copy(rng, w, n, L, a=0.0):
    """Renewal copying chain: block lengths iid Geometric(1/L) on {1,2,...}."""
    m = w.size
    W = np.concatenate([[0.0], np.cumsum(w)])
    if L == 1:
        Bmax = m
    else:
        mean_blocks = m / L
        Bmax = int(mean_blocks + 8.0 * math.sqrt(mean_blocks) + 24)
    out = np.zeros(n)
    ck = chunk_for(Bmax)
    for s in range(0, n, ck):
        c = min(ck, n - s)
        acc = np.zeros(c)
        for _hap in range(2):
            if L == 1:
                ends = np.broadcast_to(np.arange(1, m + 1), (c, m))
                starts = np.broadcast_to(np.arange(m), (c, m))
            else:
                lens = rng.geometric(1.0 / L, size=(c, Bmax))
                ends = np.cumsum(lens, axis=1)
                if ends[:, -1].min() < m:
                    raise RuntimeError("Bmax too small: block budget exhausted")
                np.clip(ends, 0, m, out=ends)
                starts = np.concatenate(
                    [np.zeros((c, 1), dtype=ends.dtype), ends[:, :-1]], axis=1)
            bw = W[ends] - W[starts]
            al = _block_alleles(rng, bw.shape, a)
            acc += np.einsum("ij,ij->i", bw, al.astype(np.float64))
        out[s:s + c] = acc
    return out


# --------------------------------------------------------------- calibration


def calibrate_latent(B, L, seed=99, n=40_000, steps=16):
    """Find the global-factor loading `a` for which the equicorrelated LATENT
    panel of m = B*L markers shows the SAME score variance inflation as the
    genuine renewal `copy` panel at correlation length L.

    That is the point of the negative control: the two arms are indistinguishable
    to the standard practitioner estimate of correlation length (variance
    inflation of the score), so if the block reduction is a property of
    correlation length it must hold for both."""
    m = B * L
    w = np.ones(m)
    base = indep_moments(w)["var"]
    target = float(np.var(gen_copy(np.random.default_rng(seed), w, n, L))) / base

    def infl(a):
        sc = gen_blockconst(np.random.default_rng(seed + 7), w, n, 1, a=a)
        return float(np.var(sc)) / base

    lo, hi = 0.0, 0.995
    if infl(hi) < target:
        return hi, infl(hi), target
    for _ in range(steps):
        mid = 0.5 * (lo + hi)
        if infl(mid) < target:
            lo = mid
        else:
            hi = mid
    a = 0.5 * (lo + hi)
    return a, infl(a), target


# ---------------------------------------------------------------- statistics


def stats(x):
    z = (x - x.mean()) / x.std()
    m3 = float(np.mean(z ** 3))
    m4 = float(np.mean(z ** 4)) - 3.0
    zs = np.sort(z)
    n = zs.size
    cdf = _phi(zs)
    i = np.arange(1, n + 1)
    d = max(float(np.max(i / n - cdf)), float(np.max(cdf - (i - 1) / n)))
    return {"skew": m3, "exkurt": m4, "ks": d, "var": float(x.var())}


def agg(rows):
    out = {}
    for k in rows[0]:
        v = np.array([r[k] for r in rows])
        out[k] = float(v.mean())
        out[k + "_se"] = float(v.std(ddof=1) / math.sqrt(v.size))
    return out


# --------------------------------------------------------------------- driver


def run_config(cfg):
    arm, B, L, wmode, a = cfg["arm"], cfg["B"], cfg["L"], cfg["wmode"], cfg["a"]
    m = B * L
    t0 = time.time()
    meas, ref_block, ref_marker = [], [], []
    ks_ref_block = []
    want_ks_ref = cfg["ks_ref"]
    for r in range(N_REPS):
        rng = np.random.default_rng(cfg["seed"] + 1000 * r)
        w = draw_weights(rng, m, wmode)
        if arm == "indep":
            sc = gen_indep(rng, w, N_PER_REP)
        elif arm == "blockconst":
            sc = gen_blockconst(rng, w, N_PER_REP, L)
        elif arm == "copy":
            sc = gen_copy(rng, w, N_PER_REP, L)
        elif arm == "latent":
            sc = gen_blockconst(rng, w, N_PER_REP, 1, a=a)
        elif arm == "copy_global":
            sc = gen_copy(rng, w, N_PER_REP, L, a=a)
        else:
            raise ValueError(arm)
        meas.append(stats(sc))
        # exact independent references (no MC noise)
        ref_marker.append(indep_moments(w))            # m independent markers
        # m/L independent markers.  At L=1 the reference must be the SAME weight
        # vector, so that the L=1 positive control is an exact identity check.
        wb = w if L == 1 else draw_weights(rng, B, wmode)
        ref_block.append(indep_moments(wb))
        if want_ks_ref:
            ks_ref_block.append(stats(gen_indep(rng, wb, N_PER_REP)))

    res = {"arm": arm, "B": B, "L": L, "m": m, "wmode": wmode, "a": a,
           "meas": agg(meas), "ref_block": agg(ref_block),
           "ref_marker": agg(ref_marker),
           "secs": round(time.time() - t0, 1)}
    if want_ks_ref:
        res["ks_ref_block"] = agg(ks_ref_block)
    res["var_inflation"] = res["meas"]["var"] / res["ref_marker"]["var"]

    def ratio(num, num_se, den, den_se):
        if abs(den) < 1e-9:
            return None, None
        return num / den, abs(num / den) * math.sqrt(
            (num_se / num) ** 2 + (den_se / den) ** 2) if abs(num) > 1e-12 else None

    for stat in ("skew", "exkurt"):
        v, vse = res["meas"][stat], res["meas"][stat + "_se"]
        rb, rbse = res["ref_block"][stat], res["ref_block"][stat + "_se"]
        rm, rmse = res["ref_marker"][stat], res["ref_marker"][stat + "_se"]
        res[f"R_pred_{stat}"], res[f"R_pred_{stat}_se"] = ratio(v, vse, rb, rbse)
        res[f"R_infl_{stat}"], res[f"R_infl_{stat}_se"] = ratio(v, vse, rm, rmse)
    if want_ks_ref:
        v, vse = res["meas"]["ks"], res["meas"]["ks_se"]
        rb, rbse = res["ks_ref_block"]["ks"], res["ks_ref_block"]["ks_se"]
        res["R_pred_ks"], res["R_pred_ks_se"] = ratio(v, vse, rb, rbse)
    return res


def main():
    ncore = int(os.environ.get("NCORE", "14"))
    Bs = (16, 64, 256)
    Ls = (1, 2, 4, 8, 16, 32)
    wmodes = ("unit", "cont", "signed")

    cfgs = []
    seed = 12345
    for wmode in wmodes:
        for B in Bs:
            for L in Ls:
                for arm in ("blockconst", "copy"):
                    if L == 1 and arm == "copy":
                        pass  # keep: L=1 positive control through the copy path
                    cfgs.append({"arm": arm, "B": B, "L": L, "wmode": wmode,
                                 "a": 0.0, "seed": seed,
                                 "ks_ref": L in KS_SUBSET_L})
                    seed += 17
            # indep positive control at the block counts
            for L in (1,):
                cfgs.append({"arm": "indep", "B": B, "L": L, "wmode": wmode,
                             "a": 0.0, "seed": seed, "ks_ref": True})
                seed += 17

    # ---- negative controls: calibrate the global-factor loading per (B, L)
    calib = {}
    neg = []
    a_weak = 0.02          # weak non-renewal contamination of a renewal chain
    for L in (4, 16):
        for B in Bs:
            a_lat, got, tgt = calibrate_latent(B, L)
            calib[f"latent_B{B}_L{L}"] = {"target_inflation": tgt, "a": a_lat,
                                          "achieved_inflation": got}
            for wmode in wmodes:
                neg.append({"arm": "latent", "B": B, "L": L, "wmode": wmode,
                            "a": a_lat, "seed": seed,
                            "ks_ref": L in KS_SUBSET_L})
                seed += 17
                neg.append({"arm": "copy_global", "B": B, "L": L,
                            "wmode": wmode, "a": a_weak, "seed": seed,
                            "ks_ref": L in KS_SUBSET_L})
                seed += 17
    calib["copy_global_a"] = a_weak
    cfgs.extend(neg)

    print(f"{len(cfgs)} configs on {ncore} workers", flush=True)
    with Pool(ncore) as pool:
        results = pool.map(run_config, cfgs, chunksize=1)

    out = {
        "meta": {
            "p_allele": P_ALLELE, "n_per_rep": N_PER_REP, "n_reps": N_REPS,
            "total_draws_per_config": N_PER_REP * N_REPS,
            "Bs": list(Bs), "Ls": list(Ls), "wmodes": list(wmodes),
            "numpy": np.__version__, "python": sys.version.split()[0],
        },
        "calibration": calib,
        "results": results,
    }
    path = os.environ.get("OUT", "block_count_results.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print("wrote", path, flush=True)


if __name__ == "__main__":
    main()
