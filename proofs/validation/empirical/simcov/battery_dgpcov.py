"""battery_dgpcov: empirical verdicts for four uncovered definitions.

FRESHNESS GUARD: DGPCOV-2026-08-04-A

Groups
  A  GeneticArchitectureDiscovery.gwasDiscovered              (threshold semantics)
  B  MetricSpecificPortability.requiredEffectiveSampleSizeForTraceMSE
  C  GeneticArchitectureDiscovery.multiTraitDiscoveryNCP
  D  MetricSpecificPortability.ldBlockDetectionShare / ldBlockPruningDeficit

Every group carries (i) a competing formula on the SAME cells, (ii) realized
inputs re-measured from the draws, (iii) a declared argument_source, and
(iv) a positive control that could fail.
"""
import json
import sys

import numpy as np
from scipy import stats
from scipy.linalg import toeplitz

GUARD = "DGPCOV-2026-08-04-A"
OUT = {}


def sems(obs, pred, se):
    return abs(obs - pred) / se if se > 0 else float("inf")


# ---------------------------------------------------------------- group D ----
def group_d():
    """ldBlockDetectionShare decay panel = ldBandDetectionShare decay (retained/total).

    The band law's `kappa` is the fraction of DIRECTIONS (a contiguous
    low-frequency band of the AR(1) symbol).  `LDPanelRetention` is a count of
    MARKERS.  This measures both operations exactly, by linear algebra, on the
    same kernel.

    argument_source: the two comparison values are computed from the AR(1)
    covariance matrix itself (eigen-truncation and submatrix inversion) and
    owe nothing to the closed form under test.
    """
    res = []
    n = 1024
    rng = np.random.default_rng(20260804)
    for rho in (0.2, 0.5, 0.8):
        sig = toeplitz(rho ** np.arange(n))
        inv = np.linalg.inv(sig)
        w_full = np.trace(inv)
        kappa = 0.5
        body = kappa - 2 * rho * np.sin(np.pi * kappa) / (np.pi * (1 + rho ** 2))

        # POSITIVE CONTROL: the band operation the closed form is FOR.
        # Keep the lowest-frequency half of the circulant/Fourier directions of
        # the same AR(1) symbol and integrate the reciprocal symbol over it.
        t = np.linspace(-np.pi, np.pi, 2_000_001)
        recip = (1 - 2 * rho * np.cos(t) + rho ** 2) / (1 + rho ** 2)
        band = np.abs(t) <= np.pi * kappa
        band_share = np.trapezoid(recip * band, t) / np.trapezoid(recip, t)

        # Reading (i): markers thinned uniformly, whitened weight of the
        # retained panel = trace of the inverse of the retained submatrix.
        idx = np.arange(0, n, 2)
        thin = np.trace(np.linalg.inv(sig[np.ix_(idx, idx)])) / w_full
        # Reading (ii): submatrix of the inverse (weight "carried by" retained
        # markers in the full kernel).
        subinv = np.trace(inv[np.ix_(idx, idx)]) / w_full
        # Reading (iii): a random half-panel, and (iv) a contiguous half.
        ridx = np.sort(rng.choice(n, n // 2, replace=False))
        rand = np.trace(np.linalg.inv(sig[np.ix_(ridx, ridx)])) / w_full
        cidx = np.arange(n // 2)
        cont = np.trace(np.linalg.inv(sig[np.ix_(cidx, cidx)])) / w_full
        # closed form for uniform thinning: retained panel is AR(1) at rho^2
        thin_cf = 0.5 * (1 + rho ** 4) / (1 + rho ** 2) ** 2

        res.append(dict(rho=rho, kappa=kappa, body=body,
                        band_control=band_share, thin=thin, thin_closed=thin_cf,
                        submatrix_of_inverse=subinv, random_panel=rand,
                        contiguous_panel=cont,
                        deficit_body=2 * rho * np.sin(np.pi * kappa) / (np.pi * (1 + rho ** 2)),
                        deficit_thin=kappa - thin))
    return res


# ---------------------------------------------------------------- group B ----
def group_b():
    """requiredEffectiveSampleSizeForTraceMSE d I tau = (d/I)/tau.

    argument_source: n_req comes from the formula; the trace MSE at that n is
    measured from independent replicate estimates, and the target tau is a
    number chosen before the run.  Two exponential families with different
    Fisher information so `I` is not a relabelled variance.
    """
    rng = np.random.default_rng(7)
    res = []
    for fam, d, tau in (("gaussian", 5, 0.10), ("gaussian", 20, 0.02),
                        ("bernoulli", 5, 0.10), ("bernoulli", 12, 0.05)):
        if fam == "gaussian":
            sigma2 = 4.0
            info = 1.0 / sigma2
        else:
            p = 0.3
            info = 1.0 / (p * (1 - p))
        cands = {"body": (d / info) / tau,
                 "tau_squared": (d / info) / tau ** 2,
                 "info_multiplied": (d * info) / tau,
                 "d_squared": (d ** 2 / info) / tau}
        cell = dict(family=fam, d=d, tau=tau, info=info)
        for label, nreq in cands.items():
            n = int(round(nreq))
            if n < 1 or n > 400_000:
                cell[label] = dict(n=n, trace_mse=None, note="out of range")
                continue
            reps = 4000
            if fam == "gaussian":
                est = rng.normal(0.0, np.sqrt(sigma2 / n), size=(reps, d))
            else:
                est = (rng.binomial(n, p, size=(reps, d)) / n) - p
            tmse = float((est ** 2).sum(axis=1).mean())
            se = float((est ** 2).sum(axis=1).std(ddof=1) / np.sqrt(reps))
            cell[label] = dict(n=n, trace_mse=tmse, se=se,
                               sems_from_tau=sems(tmse, tau, se))
        res.append(cell)
    return res


# ---------------------------------------------------------------- group A ----
def group_a():
    """gwasDiscovered n b maf ld z  <->  z^2 <= discoveryNCP n b maf ld.

    Two questions: (1) is n*b^2*ld^2*2p(1-p) the realized noncentrality of the
    Wald statistic, with maf the CAUSAL frequency and ld the tag-causal
    correlation, and (2) what discovery probability does the deterministic
    predicate's boundary actually mark?

    argument_source: the noncentrality is measured as mean(chi2)-1 over
    independent replicate GWASes; maf, ld and beta are REMEASURED from the
    realized genotype draws of each replicate set.
    """
    rng = np.random.default_rng(4242)
    res = []
    for (n, beta, p_causal, p_tag, dprime) in ((2000, 0.05, 0.30, 0.30, 1.0),
                                               (4000, 0.04, 0.15, 0.35, 0.8),
                                               (1500, 0.07, 0.40, 0.20, 0.6)):
        reps = 3000
        chi2 = np.empty(reps)
        lds = np.empty(reps)
        mafs = np.empty(reps)
        for r in range(reps):
            # Two-locus haplotype frequencies with D = dprime * Dmax.
            pa, pb = p_causal, p_tag
            dmax = min(pa * (1 - pb), pb * (1 - pa))
            D = dprime * dmax
            hap = np.array([pa * pb + D, pa * (1 - pb) - D,
                            (1 - pa) * pb - D, (1 - pa) * (1 - pb) + D])
            hap = np.clip(hap, 0, None)
            hap /= hap.sum()
            h = rng.choice(4, size=(n, 2), p=hap)
            gc = (h < 2).sum(axis=1).astype(float)          # causal dosage
            gt = ((h == 0) | (h == 2)).sum(axis=1).astype(float)  # tag dosage
            y = beta * gc + rng.normal(0, 1.0, n)
            xt = gt - gt.mean()
            vt = (xt ** 2).sum()
            bhat = float(xt @ (y - y.mean()) / vt)
            resid = (y - y.mean()) - bhat * xt
            s2 = float(resid @ resid / (n - 2))
            chi2[r] = bhat ** 2 * vt / s2
            mafs[r] = gc.mean() / 2
            sc, st = gc.std(), gt.std()
            lds[r] = float(np.corrcoef(gc, gt)[0, 1]) if sc > 0 and st > 0 else 0.0
        maf_r = float(mafs.mean())
        ld_r = float(np.sqrt((lds ** 2).mean()))   # r^2 is what enters
        ncp_obs = float(chi2.mean() - 1.0)
        se = float(chi2.std(ddof=1) / np.sqrt(reps))
        body = n * beta ** 2 * ld_r ** 2 * 2 * maf_r * (1 - maf_r)
        comp_half = n * beta ** 2 * ld_r ** 2 * maf_r * (1 - maf_r)
        comp_ld1 = n * beta ** 2 * ld_r * 2 * maf_r * (1 - maf_r)
        # Threshold semantics: what power does z^2 = ncp mark?
        lam = body
        power_at_boundary = float((chi2 > lam).mean())
        power_theory = float(stats.ncx2.sf(lam, 1, lam))
        res.append(dict(n=n, beta=beta, p_causal=p_causal, p_tag=p_tag,
                        dprime=dprime, maf_realized=maf_r, ld_realized=ld_r,
                        ncp_measured=ncp_obs, se=se, body=body,
                        sems_body=sems(ncp_obs, body, se),
                        competitor_ploidy_half=comp_half,
                        sems_ploidy_half=sems(ncp_obs, comp_half, se),
                        competitor_ld_first_power=comp_ld1,
                        sems_ld_first_power=sems(ncp_obs, comp_ld1, se),
                        power_at_predicate_boundary=power_at_boundary,
                        power_theory_ncx2=power_theory,
                        power_se=float(np.sqrt(0.25 / reps))))
    return res


# ---------------------------------------------------------------- group C ----
def group_c():
    """multiTraitDiscoveryNCP n1 n2 rg tau2 beta maf ld
         = discoveryNCP (multiTraitEffectiveSampleSize n1 n2 rg tau2) beta maf ld.

    The composition claim: cross-trait borrowing enters discovery power ONLY
    through an effective sample size, at the same ncp arithmetic.

    argument_source: the noncentrality is the realized mean chi-square of the
    Wald test built on the borrowed estimator, over independent replicates;
    rg and the effect scale are REMEASURED from the drawn effect pairs.  The
    predicted value is computed from the formula alone.
    """
    rng = np.random.default_rng(99)
    res = []
    for (n1, n2, rg, tau2) in ((4000, 8000, 0.6, 1e-4),
                               (4000, 8000, 0.9, 1e-4),
                               (6000, 3000, 0.5, 5e-5)):
        reps = 20000
        p = 0.3
        vg = 2 * p * (1 - p)
        b = rng.multivariate_normal([0, 0], tau2 * np.array([[1, rg], [rg, 1]]),
                                    size=reps)
        rg_real = float(np.corrcoef(b[:, 0], b[:, 1])[0, 1])
        tau2_real = float(b[:, 0].var())
        # per-SNP GWAS estimates: var = 1/(n*vg) for residual variance 1
        v1, v2 = 1.0 / (n1 * vg), 1.0 / (n2 * vg)
        bh1 = b[:, 0] + rng.normal(0, np.sqrt(v1), reps)
        bh2 = b[:, 1] + rng.normal(0, np.sqrt(v2), reps)
        # Posterior mean of beta1 under the bivariate prior (the borrowing rule).
        prior = tau2_real * np.array([[1, rg_real], [rg_real, 1]])
        noise = np.diag([v1, v2])
        post = prior @ np.linalg.inv(prior + noise)
        bt = post[0, 0] * bh1 + post[0, 1] * bh2
        # Wald statistic of the borrowed estimator, normalised by its own
        # sampling sd at fixed effects (the frequentist noncentrality).
        sd_bt = np.sqrt(post[0, 0] ** 2 * v1 + post[0, 1] ** 2 * v2)
        chi2 = (bt / sd_bt) ** 2
        ncp_obs = float(chi2.mean() - 1.0)
        se = float(chi2.std(ddof=1) / np.sqrt(reps))
        neff = n1 + rg_real ** 2 / ((1 - rg_real ** 2) * tau2_real + 1.0 / n2)
        body = neff * tau2_real * 1.0 ** 2 * vg
        comp_n1 = n1 * tau2_real * vg
        comp_small = (n1 + rg_real ** 2 * n2) * tau2_real * vg
        comp_sum = (n1 + n2) * tau2_real * vg
        res.append(dict(n1=n1, n2=n2, rg_nominal=rg, rg_realized=rg_real,
                        tau2_nominal=tau2, tau2_realized=tau2_real,
                        neff=neff, ncp_measured=ncp_obs, se=se, body=body,
                        sems_body=sems(ncp_obs, body, se),
                        competitor_n1_alone=comp_n1,
                        sems_n1_alone=sems(ncp_obs, comp_n1, se),
                        competitor_small_prior_limit=comp_small,
                        sems_small_prior=sems(ncp_obs, comp_small, se),
                        competitor_n1_plus_n2=comp_sum,
                        sems_n1_plus_n2=sems(ncp_obs, comp_sum, se)))
    return res


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "abcd"
    print("FRESHNESS=%s" % GUARD, flush=True)
    if "d" in which:
        OUT["group_d_ldBlockDetectionShare"] = group_d()
        print("D done", flush=True)
    if "b" in which:
        OUT["group_b_requiredEffectiveSampleSizeForTraceMSE"] = group_b()
        print("B done", flush=True)
    if "a" in which:
        OUT["group_a_gwasDiscovered"] = group_a()
        print("A done", flush=True)
    if "c" in which:
        OUT["group_c_multiTraitDiscoveryNCP"] = group_c()
        print("C done", flush=True)
    OUT["_guard"] = GUARD
    json.dump(OUT, open("battery_dgpcov_results.json", "w"), indent=1,
              default=float)
    print(json.dumps(OUT, indent=1, default=float))
