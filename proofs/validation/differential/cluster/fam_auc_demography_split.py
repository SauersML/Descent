#!/usr/bin/env python3
"""Why the AUC formula's best-fit prevalence splits by DEMOGRAPHY. numpy only.

THE LEAD, ESTABLISHED AND NOT YET EXPLAINED

fam_serial_founder.py measured the Wray AUC formula against the study's 400 runs
with the TRUE prevalence K = 0.15, which is fixed by construction (one intercept
solve pins mean(p_true) over all individuals, and every deme is split 50/50 so
the test set carries the same composition). Pooled RMSE 0.0126 at the true K
against 0.0116 for a prevalence fitted per cell, so fitting buys 8% and the
formula needs no free parameter.

But the best-fit K splits by DEMOGRAPHY and not by trait:

    serial1d   0.139 - 0.166   (straddles the true 0.150)
    grid2d     0.180 - 0.216   (all above it)

and dAUC/dK < 0 throughout the range, so a best-fit K above 0.15 means the
formula at the true K OVER-predicts AUC, i.e. grid2d's liability_r2 is larger
than the AUC it achieves can support.

THREE CANDIDATES, AND THIS FILE'S JOB IS TO EXCLUDE, NOT TO CONFIRM

  (a) liability_r2 mis-estimated on grid2d specifically;
  (b) residual population structure inflating the apparent R^2 without improving
      ranking -- a linear correlation is not a rank statistic, so a score with
      ancestry-correlated MEANS can carry correlation that buys no ordering;
  (c) the equal-variance assumption inside the LIABILITY model breaking
      differently under 2-D structure -- per-deme score VARIANCE heterogeneity
      rather than mean heterogeneity.

THE ONE STRUCTURAL DIFFERENCE THAT IS NOT A GUESS. The two demographies differ
in how much of the test set is out of training ancestry:

    serial1d  test = 2500 train-deme + 9*125  = 3625, so 31% out of ancestry
    grid2d    test = 2500 train-deme + 35*125 = 6875, so 64% out of ancestry

grid2d's test set is twice as ancestrally heterogeneous. If heterogeneity alone
drives the effect, the same structure magnitude evaluated at f = 0.31 and
f = 0.64 must reproduce BOTH observed bands. That is the quantitative test, and
it can fail.

PREDICTIONS, STATED BEFORE THE RUN

  P0 CONTROL, must fire: with NO structure at all -- no deme mean shift, no
     baseline variation, no variance heterogeneity -- the best-fit K must come
     back at 0.150 at EVERY heterogeneity fraction, because the model is then
     exactly the liability threshold model the formula assumes. If the control
     does not return 0.150 the instrument is broken and nothing else in the file
     means anything.
  P1 If (b) is the cause, arm A1 (score mean shift only) drives best-fit K
     UPWARD and the effect grows with the out-of-ancestry fraction.
  P2 If (c) is the cause, arm A3 (per-deme score variance only, equal means)
     drives it and A1 does not.
  P3 Arm A2 (liability baseline variation only) is the phenoA/phenoR effect and
     is separated from both, because the study shows the elevation on phenoB and
     phenoC too, where baseline variation is absent or removed by construction.

  A candidate is EXCLUDED if its arm cannot move best-fit K into the observed
  band at the observed heterogeneity. If more than one arm can, the candidates
  are NOT separated and this file says so rather than picking one.

Written for Python 3.6.8 with numpy only.
"""

import json
import math
import sys

import numpy as np

SEED = 20260806
PREV = 0.15

# observed, from fam_serial_founder_results.json
OBS = {"serial1d": (0.139, 0.166, 0.31), "grid2d": (0.180, 0.216, 0.64)}


def _phi(x):
    return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


def _Phi(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def _probit(q):
    lo, hi = -12.0, 12.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if _Phi(mid) < q:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def auc_from_r2(R2, K):
    """Wray et al. 2010. Zero free parameters given (R2, K)."""
    if not (0.0 < R2 < 1.0) or not (0.0 < K < 1.0):
        return float("nan")
    T = _probit(1.0 - K)
    i = _phi(T) / K
    v = -i * K / (1.0 - K)
    var_case = 1.0 - R2 * i * (i - T)
    var_ctrl = 1.0 - R2 * v * (v - T)
    if var_case <= 0.0 or var_ctrl <= 0.0:
        return float("nan")
    return _Phi((i - v) * math.sqrt(R2) / math.sqrt(var_case + var_ctrl))


def empirical_auc(score, y):
    order = np.argsort(score, kind="mergesort")
    s = score[order]
    yy = y[order]
    ranks = np.empty(len(s))
    i = 0
    while i < len(s):
        j = i
        while j + 1 < len(s) and s[j + 1] == s[i]:
            j += 1
        ranks[i:j + 1] = 0.5 * (i + j) + 1.0
        i = j + 1
    n1 = float(yy.sum())
    n0 = float(len(yy) - n1)
    if n1 == 0 or n0 == 0:
        return float("nan")
    return float((ranks[yy == 1].sum() - n1 * (n1 + 1) / 2.0) / (n0 * n1))


def lee_liability_r2(p, y):
    """EXACTLY the study's _lee_liability_r2 in fit_binary.py."""
    K = float(y.mean())
    if K <= 0 or K >= 1:
        return float("nan")
    r2_obs = float(np.corrcoef(p, y)[0, 1] ** 2)
    z = _phi(_probit(1.0 - K))
    return float(r2_obs * K * (1 - K) / (z * z)) if z > 0 else float("nan")


def simulate(rng, f_out, sd_score_shift, sd_baseline, sd_logvar, n=200000,
             n_demes=36, rho=0.45):
    """One synthetic study cell.

    f_out          fraction of the test set out of training ancestry
    sd_score_shift per-deme MEAN shift in the score            -> candidate (b)
    sd_baseline    per-deme baseline on the liability          -> the pheno A/R effect
    sd_logvar      per-deme log-SD of the score (equal means)  -> candidate (c)

    Everything else is the liability threshold model the AUC formula assumes, so
    with all three set to zero the formula must be exact.
    """
    n_out = int(round(n * f_out))
    n_in = n - n_out
    deme = np.zeros(n, dtype=int)
    if n_out > 0:
        deme[n_in:] = rng.integers(1, n_demes, n_out)
    shift = rng.normal(0.0, sd_score_shift, n_demes) if sd_score_shift > 0 \
        else np.zeros(n_demes)
    base = rng.normal(0.0, sd_baseline, n_demes) if sd_baseline > 0 \
        else np.zeros(n_demes)
    lv = rng.normal(0.0, sd_logvar, n_demes) if sd_logvar > 0 \
        else np.zeros(n_demes)
    shift -= shift.mean()
    base -= base.mean()
    lv -= lv.mean()

    g = rng.standard_normal(n)                       # genetic liability
    # score: correlation rho with g, plus per-deme mean and variance structure
    s = rho * g + math.sqrt(1.0 - rho * rho) * rng.standard_normal(n)
    s = s * np.exp(lv[deme]) + shift[deme]
    # liability and outcome; threshold set so the GLOBAL prevalence is PREV
    L = g + base[deme] + rng.standard_normal(n)
    thr = float(np.quantile(L, 1.0 - PREV))
    y = (L > thr).astype(float)
    # the study's best case: a well-calibrated probability from the score
    order = np.argsort(s)
    p = np.empty(n)
    nb = 200
    edges = np.linspace(0, n, nb + 1).astype(int)
    for b in range(nb):
        sl = order[edges[b]:edges[b + 1]]
        p[sl] = y[sl].mean()
    p = np.clip(p, 1e-6, 1 - 1e-6)

    auc = empirical_auc(s, y)
    lr2 = lee_liability_r2(p, y)
    best, bestd = None, 1e9
    for K in np.linspace(0.05, 0.45, 801):
        d = abs(auc_from_r2(lr2, float(K)) - auc)
        if d < bestd:
            best, bestd = float(K), d
    return {"auc": auc, "liability_r2": lr2, "best_fit_K": best,
            "auc_at_true_K": auc_from_r2(lr2, PREV),
            "residual_at_true_K": auc_from_r2(lr2, PREV) - auc}


def main():
    rng = np.random.default_rng(SEED)
    out = {"observed": OBS}
    print("=" * 78)
    print("WHY THE BEST-FIT PREVALENCE SPLITS BY DEMOGRAPHY")
    print("=" * 78)
    print("  observed: serial1d %.3f-%.3f at %.0f%% out of ancestry"
          % (OBS["serial1d"][0], OBS["serial1d"][1], 100 * OBS["serial1d"][2]))
    print("            grid2d   %.3f-%.3f at %.0f%% out of ancestry"
          % (OBS["grid2d"][0], OBS["grid2d"][1], 100 * OBS["grid2d"][2]))
    print("  true K = %.3f. dAUC/dK < 0, so K above it means the formula" % PREV)
    print("  OVER-predicts AUC at the true K.")

    arms = [
        ("P0 CONTROL no structure", 0.0, 0.0, 0.0),
        ("A1 score mean shift", 0.45, 0.0, 0.0),
        ("A2 liability baseline", 0.0, 0.45, 0.0),
        ("A3 score variance het", 0.0, 0.0, 0.35),
    ]
    fracs = [0.0, 0.31, 0.64, 0.90]
    print("")
    print("  best-fit K by arm and out-of-ancestry fraction (n = 200000 each):")
    print("  %-26s %-9s %-9s %-9s %-9s"
          % ("arm", "f=0.00", "f=0.31", "f=0.64", "f=0.90"))
    rows = []
    table = {}
    for (name, ss, sb, sv) in arms:
        vals = []
        for f in fracs:
            r = simulate(rng, f, ss, sb, sv)
            vals.append(r["best_fit_K"])
            rows.append({"arm": name, "f_out": f, "sd_score_shift": ss,
                         "sd_baseline": sb, "sd_logvar": sv, **r})
        table[name] = vals
        print("  %-26s %-9.4f %-9.4f %-9.4f %-9.4f"
              % (name, vals[0], vals[1], vals[2], vals[3]))

    # ---- P0 must fire -----------------------------------------------------
    ctl = table["P0 CONTROL no structure"]
    p0 = all(abs(v - PREV) < 0.012 for v in ctl)
    print("")
    print("  P0 CONTROL: no structure returns K = %s against the true %.3f"
          % (", ".join("%.4f" % v for v in ctl), PREV))
    print("     -> %s. Without this the rest of the file means nothing."
          % ("FIRED (instrument sound)" if p0 else "BROKEN"))

    # ---- which arms can reach the observed bands --------------------------
    print("")
    print("  Can each arm reproduce BOTH observed bands at the observed")
    print("  heterogeneities (serial1d f=0.31 -> %.3f-%.3f, grid2d f=0.64 ->"
          % (OBS["serial1d"][0], OBS["serial1d"][1]))
    print("  %.3f-%.3f)? An arm must land in BOTH to survive."
          % (OBS["grid2d"][0], OBS["grid2d"][1]))
    print("  %-26s %-14s %-14s %-10s"
          % ("arm", "K at f=0.31", "K at f=0.64", "verdict"))
    survivors = []
    for (name, _ss, _sb, _sv) in arms:
        k31, k64 = table[name][1], table[name][2]
        in31 = OBS["serial1d"][0] <= k31 <= OBS["serial1d"][1]
        in64 = OBS["grid2d"][0] <= k64 <= OBS["grid2d"][1]
        verdict = ("REPRODUCES BOTH" if (in31 and in64)
                   else "grid2d only" if in64
                   else "serial1d only" if in31 else "neither")
        if in31 and in64:
            survivors.append(name)
        print("  %-26s %-14.4f %-14.4f %-10s" % (name, k31, k64, verdict))

    print("")
    print("  DOES HETEROGENEITY ALONE DRIVE IT? For each structured arm, the")
    print("  monotone rise of best-fit K with f is the signature the")
    print("  heterogeneity explanation requires:")
    for (name, _ss, _sb, _sv) in arms:
        v = table[name]
        mono = all(v[i] >= v[i - 1] - 0.004 for i in range(1, len(v)))
        print("    %-26s rises with f: %-6s  (%.4f -> %.4f over f = 0 -> 0.90)"
              % (name, mono, v[0], v[-1]))

    print("")
    print("=" * 78)
    print("VERDICT")
    print("=" * 78)
    if not p0:
        print("  INSTRUMENT BROKEN -- the no-structure control did not return")
        print("  the true prevalence, so no candidate can be excluded here.")
    elif len(survivors) == 1:
        print("  ONE candidate reproduces both observed bands: %s."
              % survivors[0])
        print("  The others are EXCLUDED at the observed heterogeneities. That")
        print("  is an exclusion, not a mechanism: it says which of the three")
        print("  can produce the split, not that it is what the study does.")
    elif len(survivors) == 0:
        print("  NO candidate reproduces both bands at these magnitudes. The")
        print("  split is therefore NOT explained by any of the three at the")
        print("  structure sizes tried, and the lead stays open. Reporting this")
        print("  is the point: a magnitude sweep would be needed before any of")
        print("  them could be excluded rather than merely unsupported.")
    else:
        print("  %d candidates reproduce both bands: %s."
              % (len(survivors), ", ".join(survivors)))
        print("  THE CANDIDATES ARE NOT SEPARATED by this experiment. Picking")
        print("  one would be a preference, not a result.")
    print("")
    print("  What IS established, and does not depend on the above: the sign")
    print("  (best-fit K above the truth means liability_r2 too large for the")
    print("  AUC achieved), the split (demography, not trait), and that the")
    print("  formula needs no free parameter at the true K.")

    out["arms"] = rows
    out["table"] = dict((k, v) for k, v in table.items())
    out["P0_control_fired"] = bool(p0)
    out["survivors"] = survivors
    fh = open("fam_auc_demography_split_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("")
    print("-> fam_auc_demography_split_results.json")
    return 0 if p0 else 1


if __name__ == "__main__":
    sys.exit(main())
