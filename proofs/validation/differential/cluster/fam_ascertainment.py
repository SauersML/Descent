#!/usr/bin/env python3
"""Family simulator: ASCERTAINMENT (GWAS discovery thresholds, vectorized).

Run with the popgen venv:
    /projects/standard/hsiehph/sauer354/popgenv/bin/python fam_ascertainment.py

WHY THIS FAMILY MATTERS MORE THAN ITS SIZE
    Several published claims this corpus examines get their force from an
    ascertainment step: an effect is reported, the variants carrying it were
    chosen because they were significant, and the reported magnitude is
    therefore conditional on selection. Whether such an effect is biology or
    selection bias is a question a simulator can settle and algebra alone
    cannot, because the conditional expectation under a two-sided threshold has
    no elementary closed form the corpus is currently willing to write.

WHERE THE MEMBERS WENT
    families.py lists discoveryNCP, truncationBias, winnersCurseInflation,
    approxPower, tagGenotypeVariance. THREE OF THOSE FIVE NO LONGER EXIST:
    truncationBias, winnersCurseInflation and approxPower were removed from
    PowerAnalysis.lean, and tagGenotypeVariance is not in defs.json either. A
    simulator aimed at the list would have checked a corpus that is gone. The
    live members were found by grepping defs.json rather than trusting the
    list, and they are:

      discoveryNCP        n β² ld² · 2·maf_causal·(1-maf_causal)
      noncentralityParam  n β² · 2p(1-p)
      ncp                 n_eff β²
      effectiveSampleSize n · 2p(1-p) · r2_ld
      standardErrorSq     1 / (n · 2p(1-p) · r2_ld)
      powerAtThreshold    Φ(√ncp - z_α)
      multiTraitEffectiveSampleSize / multiTraitDiscoveryNCP
      ascertainment_loss  (1 - coverage) · v_causal

    The removals are themselves checked here, because a removal rests on stated
    numbers ("5.6 to 5.9 standard errors at genome-wide significance",
    "-73% to +23%") that had never been simulated.

THE DIFFERENCE THE DEFINITIONS CANNOT SEE: WHICH VARIANT'S FREQUENCY.
    discoveryNCP's docstring states the convention -- `maf_causal` is the
    CAUSAL variant's frequency -- and quantifies the cost of misreading it as
    the tag's at "-24% to +33%". Every other member takes a single `p` and
    cannot distinguish the two at all. The simulator therefore holds r² fixed
    and varies the tag/causal frequency MISMATCH, which is the axis on which a
    matched-frequency test cannot fail.

CONTROL DISCIPLINE -- split, each isolating one factor
    C1 SAMPLING VARIANCE ALONE, NO THRESHOLD, NO LD.
       Regress y on the causal genotype directly. The measured Var(β̂) must be
       standardErrorSq at r2_ld = 1. Isolates the n·2p(1-p) factor from
       everything downstream. If C1 failed, no NCP number below would mean
       anything.
    C2 LD ATTENUATION ALONE, NO THRESHOLD.
       Regress y on a TAG in LD r² with the causal variant, at MATCHED
       frequencies. The measured NCP must be r² times the C1 NCP. Isolates the
       ld² factor. C1 and C2 are split because a simulator that got the
       genotype variance wrong by 1/r² and the LD term wrong by r² would pass
       a combined "does discoveryNCP predict the NCP" check and fail both.
    C3 THRESHOLD ALONE, NO LD, NO EFFECT.
       Under β = 0 the rejection rate at z_α must equal the nominal 2Φ(-z_α),
       and E[β̂ | selected] must be ZERO by symmetry. Isolates the selection
       machinery from the signal. This is the control that shows the two-sided
       convention is implemented, which is precisely where the removed
       one-sided truncationBias went wrong.
    C4 POWER. Simulated rejection rate vs powerAtThreshold. Isolates the Φ
       step given a correct NCP from C1-C2.
    C5 POSITIVE CONTROL. The frequency-mismatch comparison is re-run with the
       prediction deliberately fed the WRONG frequency; the checker must flag
       it at mismatched frequencies AND must NOT flag it at matched ones. A
       check that flags both is not measuring the mismatch.

CAN-FAIL CLAUSE ON THE GRID
    maf_causal and maf_tag are swept independently from 0.05 to 0.45 at fixed
    r², so the grid contains cells where the two frequencies are equal (the
    two readings COINCIDE and must agree) and cells where they differ 9-fold
    (the two readings must diverge). A grid at matched frequencies only would
    validate both readings and settle nothing, which is the failure mode the
    discoveryNCP docstring names.

SPEED
    VECTORIZED OVER REPLICATES. Each block draws a (C, n, 2) haplotype array in
    one call and computes C least-squares slopes with a single set of column
    reductions -- no Python loop over replicates, no loop over individuals. The
    replicate axis is cut into blocks only to bound peak RAM (see `gwas`); the
    arithmetic is identical to doing all R at once.

    The winner's-curse conditional mean is EXACT rather than simulated over the
    whole grid, because at genome-wide significance and a weak true effect the
    selection probability is 10^-8 and no affordable replicate count reaches
    it. The exact formula is then checked against a simulated GWAS at the
    lambda where selection IS common -- so the cheap method is validated by the
    expensive one rather than substituted for it.
"""

import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.normpath(os.path.join(HERE, "..", "..", "extract"))
if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

import api  # noqa: E402


def call(name, *pos):
    """Evaluate a corpus definition POSITIONALLY, in Lean binder order."""
    fn, args = api.callable_for(name)
    if len(pos) != len(args):
        raise RuntimeError("%s takes %d args %r, got %d"
                           % (name, len(args), args, len(pos)))
    return float(fn(*pos))


RNG = np.random.default_rng(20260802)

Z_GW = 5.4513104  # two-sided p < 5e-8


def norm_cdf(x):
    return 0.5 * (1.0 + np.vectorize(math.erf)(np.asarray(x, dtype=float)
                                               / math.sqrt(2.0)))


# ===========================================================================
# One vectorized GWAS: R replicates, n individuals, one causal + one tag.
# ===========================================================================

CELLS_PER_CHUNK = 4_000_000     # replicates x individuals held in RAM at once


def gwas(R, n, beta, maf_causal, maf_tag, r2, sigma_e=1.0, seed=None):
    """Simulate R independent GWAS and return slopes and SEs at BOTH variants.

    The causal and tag genotypes are built from a haplotype model so that the
    allelic correlation between the two is sqrt(r2) while their allele
    frequencies are set independently. That separation is the whole point: r2
    and the frequency mismatch must be movable one at a time or the two factors
    cannot be isolated.

    CHUNKED OVER REPLICATES, NOT LOOPED OVER THEM. An (R, n, 2) haplotype array
    at R = 5x10^5 and n = 3000 is three terabytes, so the replicate axis is cut
    into blocks of CELLS_PER_CHUNK/n replicates and each block is done in one
    vectorized pass. The arithmetic per block is identical to the unchunked
    version; only the peak footprint changes.
    """
    rng = np.random.default_rng(seed)
    r = math.sqrt(r2)
    pc, pt = maf_causal, maf_tag
    D = r * math.sqrt(pc * (1 - pc) * pt * (1 - pt))
    probs = np.array([(1 - pc) * (1 - pt) + D,      # 00
                      (1 - pc) * pt - D,            # 01 tag only
                      pc * (1 - pt) - D,            # 10 causal only
                      pc * pt + D])                 # 11
    if probs.min() < -1e-12:
        return None                      # requested (p, p', r) is infeasible
    probs = np.clip(probs, 0.0, None)
    probs = probs / probs.sum()
    cdf = np.cumsum(probs)

    bc = np.empty(R); sec = np.empty(R)
    bt = np.empty(R); set_ = np.empty(R)
    r_real = []
    step = max(1, CELLS_PER_CHUNK // n)
    done = 0
    while done < R:
        C = min(step, R - done)
        u = rng.random((C, n, 2))
        hap = np.searchsorted(cdf, u)              # 0..3
        g_c = ((hap >> 1) & 1).sum(axis=2).astype(np.float64)
        g_t = (hap & 1).sum(axis=2).astype(np.float64)
        y = beta * g_c + rng.normal(0.0, sigma_e, size=(C, n))
        yc = y - y.mean(axis=1, keepdims=True)

        def ols(x):
            xc = x - x.mean(axis=1, keepdims=True)
            sxx = (xc * xc).sum(axis=1)
            b = (xc * yc).sum(axis=1) / sxx
            resid = yc - b[:, None] * xc
            s2 = (resid * resid).sum(axis=1) / (n - 2)
            return b, np.sqrt(s2 / sxx)

        bc[done:done + C], sec[done:done + C] = ols(g_c)
        bt[done:done + C], set_[done:done + C] = ols(g_t)
        if not r_real:
            r_real = [float(np.corrcoef(g_c[i], g_t[i])[0, 1])
                      for i in range(min(C, 200))]
        done += C
    return {"beta_causal": bc, "se_causal": sec,
            "beta_tag": bt, "se_tag": set_,
            "r_realized": float(np.mean(r_real))}


# ===========================================================================
# CONTROL 1 -- sampling variance alone. No threshold, no LD.
# ===========================================================================

def control_sampling_variance():
    rows = []
    R, n = 20000, 4000
    for p in (0.05, 0.2, 0.45):
        for beta in (0.0, 0.03):
            out = gwas(R, n, beta, p, p, 1.0, seed=11)
            var_meas = float(out["beta_causal"].var())
            pred = call("standardErrorSq", n, p, 1.0)
            n_eff = call("effectiveSampleSize", n, p, 1.0)
            rows.append({"p": p, "beta": beta, "n": n,
                         "measured_var_beta_hat": var_meas,
                         "corpus_standardErrorSq": pred,
                         "corpus_effectiveSampleSize": n_eff,
                         "rel_err": (pred - var_meas) / var_meas})
            print("  p=%.2f beta=%.2f  Var(beta_hat)=%.6g  "
                  "standardErrorSq=%.6g  rel %+.2f%%"
                  % (p, beta, var_meas, pred,
                     100 * (pred - var_meas) / var_meas))
    ok = all(abs(r["rel_err"]) < 0.05 for r in rows)
    print("  CONTROL 1 (sampling variance, r2=1, no threshold): %s"
          % ("PASS" if ok else "FAIL"))
    return ok, rows


# ===========================================================================
# CONTROL 2 -- LD attenuation alone, at MATCHED frequencies.
# ===========================================================================

def control_ld_attenuation():
    rows = []
    R, n, beta, p = 20000, 4000, 0.05, 0.25
    base = gwas(R, n, beta, p, p, 1.0, seed=21)
    ncp_causal = float(np.mean((base["beta_causal"] / base["se_causal"]) ** 2))
    for r2 in (1.0, 0.6, 0.3):
        out = gwas(R, n, beta, p, p, r2, seed=22)
        ncp_tag = float(np.mean((out["beta_tag"] / out["se_tag"]) ** 2))
        pred = call("discoveryNCP", float(n), beta, p, math.sqrt(r2))
        rows.append({"r2": r2, "p": p, "beta": beta, "n": n,
                     "measured_ncp_at_tag": ncp_tag,
                     "measured_ncp_at_causal": ncp_causal,
                     "ratio_tag_over_causal": ncp_tag / ncp_causal,
                     "corpus_discoveryNCP": pred,
                     "rel_err": (pred - (ncp_tag - 1.0)) / (ncp_tag - 1.0)})
        print("  r2=%.2f  E[chi2] at tag %.4f  at causal %.4f  ratio %.4f "
              "(r2 says %.2f)  discoveryNCP %.4f"
              % (r2, ncp_tag, ncp_causal, ncp_tag / ncp_causal, r2, pred))
    # The chi-square has mean ncp + 1 under the alternative; the ratio of
    # NONCENTRALITIES is what r2 predicts, so subtract the central 1.
    ok = all(abs(((r["measured_ncp_at_tag"] - 1.0)
                  / (r["measured_ncp_at_causal"] - 1.0)) - r["r2"]) < 0.06
             for r in rows)
    print("  CONTROL 2 (LD attenuation is exactly r2, matched frequencies): %s"
          % ("PASS" if ok else "FAIL"))
    return ok, rows


# ===========================================================================
# CONTROL 3 -- threshold alone, under the null. Two-sided by construction.
# ===========================================================================

def control_threshold_null():
    R, n = 200000, 1500
    p = 0.25
    out = gwas(R, n, 0.0, p, p, 1.0, seed=31)
    z = out["beta_causal"] / out["se_causal"]
    for z_alpha in (1.96, 3.0):
        sel = np.abs(z) > z_alpha
        rate = float(sel.mean())
        nominal = 2.0 * float(norm_cdf(-z_alpha))
        cond_mean = float(out["beta_causal"][sel].mean()) if sel.any() else 0.0
        cond_sem = (float(out["beta_causal"][sel].std()) / math.sqrt(sel.sum())
                    if sel.any() else 0.0)
        print("  z_alpha=%.2f  rejection rate %.5f vs nominal %.5f  |  "
              "E[beta_hat | selected] = %+.6f +- %.6f  (must be 0 by symmetry)"
              % (z_alpha, rate, nominal, cond_mean, cond_sem))
        if z_alpha == 1.96:
            ok_rate = abs(rate - nominal) < 4 * math.sqrt(
                nominal * (1 - nominal) / R)
            ok_sym = abs(cond_mean) < 4 * cond_sem
    ok = bool(ok_rate and ok_sym)
    print("  CONTROL 3 (threshold two-sided, null unbiased): %s"
          % ("PASS" if ok else "FAIL"))
    return ok, {"rejection_rate_ok": bool(ok_rate),
                "conditional_mean_zero_ok": bool(ok_sym)}


# ===========================================================================
# CONTROL 4 -- power. Simulated rejection rate vs powerAtThreshold.
# ===========================================================================

def control_power():
    rows = []
    R, n, p = 100000, 2000, 0.25
    for beta in (0.02, 0.04, 0.06, 0.08):
        out = gwas(R, n, beta, p, p, 1.0, seed=41)
        z = out["beta_causal"] / out["se_causal"]
        for z_alpha in (1.96, 4.0):
            rate = float((np.abs(z) > z_alpha).mean())
            ncp = call("noncentralityParam", n, beta, p)
            pred = call("powerAtThreshold", ncp, z_alpha)
            # the corpus form is the ONE-SIDED upper tail; the two-sided
            # rejection rate adds Phi(-z_alpha - sqrt(ncp)), which is what the
            # simulator measures. Both are reported.
            twosided = pred + float(norm_cdf(-z_alpha - math.sqrt(ncp)))
            rows.append({"beta": beta, "n": n, "p": p, "z_alpha": z_alpha,
                         "measured_rejection_rate": rate,
                         "corpus_noncentralityParam": ncp,
                         "corpus_powerAtThreshold": pred,
                         "one_sided_plus_lower_tail": twosided,
                         "rel_err_corpus": (pred - rate) / rate if rate else None})
            print("  beta=%.2f z_a=%.2f  rate %.5f  ncp %.4f  "
                  "powerAtThreshold %.5f (%+.2f%%)  two-sided %.5f"
                  % (beta, z_alpha, rate, ncp, pred,
                     100 * (pred - rate) / rate if rate else float("nan"),
                     twosided))
    ok = all(abs(r["rel_err_corpus"]) < 0.05 for r in rows
             if r["measured_rejection_rate"] > 0.02)
    print("  CONTROL 4 (powerAtThreshold given a correct NCP): %s"
          % ("PASS" if ok else "FAIL"))
    return ok, rows


# ===========================================================================
# REGIME 1 -- THE AXIS: tag/causal frequency MISMATCH at fixed r2.
# discoveryNCP's docstring pins the convention and quantifies misreading it.
# This measures both readings against the simulated NCP at the tag.
# ===========================================================================

def regime_frequency_mismatch():
    out = []
    R, n, beta, r2 = 20000, 4000, 0.05, 0.5
    for pc in (0.05, 0.15, 0.45):
        for pt in (0.05, 0.15, 0.45):
            res = gwas(R, n, beta, pc, pt, r2, seed=51)
            if res is None:
                print("  maf_causal=%.2f maf_tag=%.2f r2=%.2f INFEASIBLE "
                      "haplotype frequencies -- skipped" % (pc, pt, r2))
                continue
            chi2 = float(np.mean((res["beta_tag"] / res["se_tag"]) ** 2))
            ncp_meas = chi2 - 1.0
            as_causal = call("discoveryNCP", float(n), beta, pc,
                             math.sqrt(r2))
            as_tag = call("discoveryNCP", float(n), beta, pt, math.sqrt(r2))
            out.append({"maf_causal": pc, "maf_tag": pt, "r2": r2,
                        "beta": beta, "n": n,
                        "realized_allelic_corr": res["r_realized"],
                        "measured_ncp_at_tag": ncp_meas,
                        "corpus_read_as_causal_maf": as_causal,
                        "corpus_read_as_tag_maf": as_tag,
                        "rel_err_causal_reading":
                            (as_causal - ncp_meas) / ncp_meas,
                        "rel_err_tag_reading":
                            (as_tag - ncp_meas) / ncp_meas})
            print("  maf_c=%.2f maf_t=%.2f  measured NCP %.4f | as CAUSAL "
                  "%.4f (%+7.1f%%) | as TAG %.4f (%+7.1f%%)"
                  % (pc, pt, ncp_meas, as_causal,
                     100 * (as_causal - ncp_meas) / ncp_meas, as_tag,
                     100 * (as_tag - ncp_meas) / ncp_meas))
    return out


# ===========================================================================
# REGIME 2 -- WINNER'S CURSE. The corpus REMOVED winnersCurseInflation
# (beta + sigma/sqrt(n), one standard error) and truncationBias (a one-sided
# inverse-Mills numerator) with stated numbers. Nobody had simulated them.
# ===========================================================================

def wc_exact(lam, z):
    """E[beta_hat | |z| > z_alpha] / SE for a true effect of lam standard errors.

    u = beta_hat/SE ~ N(lam, 1); selection is |u| > z, which is the TWO-SIDED
    event GWASObservationModel.isSelected states. Then
        P    = Phi(-z-lam) + Phi(lam-z)
        E[u|sel] = lam + (phi(z-lam) - phi(z+lam)) / P
    Exact, not asymptotic, and defined at lam = 0 where it equals 0 by
    symmetry -- the point at which the removed `beta + sigma/sqrt(n)` claimed
    one full standard error of inflation.
    """
    phi = lambda x: math.exp(-0.5 * x * x) / math.sqrt(2 * math.pi)
    P = float(norm_cdf(-z - lam)) + float(norm_cdf(lam - z))
    if P <= 0:
        return float("nan"), P
    return lam + (phi(z - lam) - phi(z + lam)) / P, P


def regime_winners_curse():
    """Two parts, deliberately separated.

    PART A -- EXACT. The two-sided conditional mean over the whole lam grid,
    including lam = 0 and the rare-selection regime a direct simulation cannot
    reach at any replicate count that fits on a shared node. This is algebra,
    so it carries no Monte Carlo error.
    PART B -- SIMULATION CONTROL ON PART A. A genotype-level GWAS at the one
    place where selection is common enough to measure directly (lam = 4 and 6
    at genome-wide significance, and lam = 0 and 1 at z = 1.96). If the exact
    formula did not reproduce the simulated GWAS there, Part A would be a
    formula about a model rather than about a GWAS, and nothing in Part A
    could be quoted.
    """
    out_exact = []
    for z_name, z in (("genome-wide 5e-8", Z_GW), ("nominal 0.05", 1.96)):
        for lam in (0.0, 0.5, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 8.0):
            e, P = wc_exact(lam, z)
            removed = lam + 1.0          # winnersCurseInflation, in SE units
            out_exact.append({"z_alpha_name": z_name, "z_alpha": z,
                              "beta_over_se": lam,
                              "selection_probability": P,
                              "E_beta_hat_given_selected_in_SE": e,
                              "bias_in_SE": e - lam,
                              "removed_winnersCurseInflation_in_SE": removed,
                              "rel_err_of_removed_form":
                                  (removed - e) / e if e else None})
            print("  %-16s lam=%4.1f  P(sel)=%9.3e  E[b|sel]=%8.4f SE  "
                  "bias=%7.4f SE  |  removed 'beta+SE' = %5.1f SE (rel %+8.1f%%)"
                  % (z_name, lam, P, e, e - lam, removed,
                     100 * (removed - e) / e if e else float("nan")))
    print("  The corpus removal note states the true conditional mean sits "
          "'near 5.6 to 5.9 standard errors at genome-wide significance' and "
          "that beta+SE is wrong by '-73%% to +23%%'; both are read off above.")

    out_sim = []
    n, p = 3000, 0.25
    probe = gwas(2000, n, 0.0, p, p, 1.0, seed=61)
    se_nom = float(probe["se_causal"].mean())
    for (lam, z, R) in ((4.0, Z_GW, 300000), (6.0, Z_GW, 60000),
                        (0.0, 1.96, 200000), (1.0, 1.96, 200000)):
        res = gwas(R, n, lam * se_nom, p, p, 1.0, seed=62)
        zz = res["beta_causal"] / res["se_causal"]
        sel = np.abs(zz) > z
        k = int(sel.sum())
        if k < 100:
            out_sim.append({"beta_over_se": lam, "z_alpha": z,
                            "selected": k, "replicates": R,
                            "note": "fewer than 100 selected; not estimated"})
            print("  SIM lam=%.1f z=%.2f: only %d/%d selected -- not estimated"
                  % (lam, z, k, R))
            continue
        cond = float(res["beta_causal"][sel].mean()) / se_nom
        sem = float(res["beta_causal"][sel].std()) / se_nom / math.sqrt(k)
        exact, P = wc_exact(lam, z)
        out_sim.append({"beta_over_se": lam, "z_alpha": z, "replicates": R,
                        "selected": k, "selection_rate": k / R,
                        "exact_selection_probability": P,
                        "simulated_E_in_SE": cond, "sem": sem,
                        "exact_E_in_SE": exact,
                        "deviation_in_sems": (exact - cond) / sem if sem else None})
        print("  SIM lam=%4.1f z=%5.2f  selected %6d (%.3e vs exact %.3e)  "
              "E[b|sel]=%8.4f +- %.4f SE   exact %8.4f  (%.2f sems)"
              % (lam, z, k, k / R, P, cond, sem, exact,
                 (exact - cond) / sem if sem else float("nan")))
    ok = all(abs(r.get("deviation_in_sems") or 0.0) < 4.0 for r in out_sim
             if "deviation_in_sems" in r)
    print("  CONTROL 6 (exact conditional mean reproduces a simulated GWAS): "
          "%s" % ("PASS" if ok else "FAIL"))
    return ok, {"exact": out_exact, "simulation_control": out_sim}


# ===========================================================================
# REGIME 3 -- ascertainment_loss = (1 - coverage) * v_causal.
# Measured: R2 of a score built from an array covering a fraction of causal
# variants, against the R2 of a complete score.
# ===========================================================================

def regime_ascertainment_loss():
    out = []
    R, n, L = 40, 4000, 400
    for coverage in (1.0, 0.8, 0.5, 0.2):
        losses = []
        for r in range(R):
            rng = np.random.default_rng(7000 + r)
            p = rng.uniform(0.05, 0.5, size=L)
            b = rng.normal(0.0, 1.0, size=L)
            G = rng.binomial(2, p, size=(n, L)).astype(np.float64)
            v_per = 2.0 * p * (1 - p) * b ** 2
            v_causal = v_per.sum()
            g = G @ b
            y = g + rng.normal(0.0, math.sqrt(v_causal), size=n)
            covered = rng.random(L) < coverage
            g_cov = G[:, covered] @ b[covered]
            r2_full = np.corrcoef(g, y)[0, 1] ** 2
            r2_cov = np.corrcoef(g_cov, y)[0, 1] ** 2 if covered.any() else 0.0
            losses.append((v_causal, r2_full, r2_cov,
                           v_per[~covered].sum()))
        arr = np.array(losses)
        v_causal_bar = float(arr[:, 0].mean())
        missed_variance = float(arr[:, 3].mean())
        pred = call("ascertainment_loss", coverage, v_causal_bar)
        out.append({"coverage": coverage, "n": n, "L": L,
                    "v_causal": v_causal_bar,
                    "measured_uncovered_causal_variance": missed_variance,
                    "corpus_ascertainment_loss": pred,
                    "rel_err": (pred - missed_variance) / missed_variance
                        if missed_variance else None,
                    "mean_r2_full": float(arr[:, 1].mean()),
                    "mean_r2_covered": float(arr[:, 2].mean()),
                    "measured_r2_loss": float(arr[:, 1].mean()
                                              - arr[:, 2].mean())})
        print("  coverage=%.2f  uncovered causal variance %.4f  corpus "
              "(1-cov)*v_causal %.4f (%+.2f%%)  |  R2 %.4f -> %.4f"
              % (coverage, missed_variance, pred,
                 100 * (pred - missed_variance) / missed_variance
                 if missed_variance else float("nan"),
                 float(arr[:, 1].mean()), float(arr[:, 2].mean())))
    return out


# ===========================================================================
# CONTROL 5 -- POSITIVE CONTROL on the frequency-mismatch comparison.
# ===========================================================================

def control_positive(rows):
    matched = [r for r in rows if r["maf_causal"] == r["maf_tag"]]
    mismatched = [r for r in rows if r["maf_causal"] != r["maf_tag"]]
    TOL = 0.10
    matched_agree = all(abs(r["rel_err_tag_reading"]) < TOL for r in matched)
    mismatched_caught = sum(1 for r in mismatched
                            if abs(r["rel_err_tag_reading"]) >= TOL)
    ok = bool(matched and mismatched and matched_agree
              and mismatched_caught == len(mismatched))
    print("  C5 at MATCHED frequencies the two readings coincide and the "
          "checker is silent: %s (%d cells)"
          % ("yes" if matched_agree else "NO", len(matched)))
    print("  C5 at MISMATCHED frequencies the wrong reading is caught: "
          "%d/%d cells" % (mismatched_caught, len(mismatched)))
    print("  CONTROL 5 (the mismatch axis is what is being measured): %s"
          % ("PASS" if ok else "FAIL"))
    return ok, {"matched_cells": len(matched),
                "matched_agree": bool(matched_agree),
                "mismatched_cells": len(mismatched),
                "mismatched_caught": mismatched_caught,
                "tolerance": TOL}


def main():
    res = {"family": "ascertainment",
           "stale_membership_list_in_families_py":
               ["truncationBias -- REMOVED from PowerAnalysis.lean",
                "winnersCurseInflation -- REMOVED from PowerAnalysis.lean",
                "approxPower -- REMOVED",
                "tagGenotypeVariance -- not present in defs.json"],
           "covers": ["discoveryNCP", "noncentralityParam",
                      "effectiveSampleSize", "standardErrorSq",
                      "powerAtThreshold", "ascertainment_loss"]}
    print("CONTROL 1 -- SAMPLING VARIANCE ALONE")
    c1, res["control_sampling_variance"] = control_sampling_variance()
    print("")
    print("CONTROL 2 -- LD ATTENUATION ALONE (matched frequencies)")
    c2, res["control_ld_attenuation"] = control_ld_attenuation()
    print("")
    print("CONTROL 3 -- THRESHOLD ALONE, UNDER THE NULL")
    c3, res["control_threshold_null"] = control_threshold_null()
    print("")
    print("CONTROL 4 -- POWER")
    c4, res["control_power"] = control_power()
    print("")
    print("REGIME 1 -- TAG/CAUSAL FREQUENCY MISMATCH AT FIXED r2")
    res["frequency_mismatch"] = regime_frequency_mismatch()
    print("")
    print("CONTROL 5 -- POSITIVE CONTROL ON THE MISMATCH AXIS")
    c5, res["control_positive"] = control_positive(res["frequency_mismatch"])
    print("")
    print("REGIME 2 -- WINNER'S CURSE AT GENOME-WIDE SIGNIFICANCE")
    c6, res["winners_curse"] = regime_winners_curse()
    print("")
    print("REGIME 3 -- ASCERTAINMENT LOSS")
    res["ascertainment_loss"] = regime_ascertainment_loss()

    res["controls"] = {"sampling_variance": bool(c1),
                       "ld_attenuation": bool(c2),
                       "threshold_null_two_sided": bool(c3),
                       "power": bool(c4),
                       "positive_control_mismatch_axis": bool(c5),
                       "winners_curse_exact_matches_simulated_gwas": bool(c6)}
    res["READ_THE_TEST"] = bool(c1 and c2 and c3 and c4 and c5 and c6)
    fh = open(os.path.join(HERE, "fam_ascertainment_results.json"), "w")
    json.dump(res, fh, indent=1)
    fh.close()
    print("")
    print("READ_THE_TEST: %s   -> fam_ascertainment_results.json"
          % res["READ_THE_TEST"])
    return 0 if res["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
