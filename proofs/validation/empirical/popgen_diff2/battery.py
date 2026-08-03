#!/usr/bin/env python3.12
"""Differential tests of Calibrator population-genetics definitions.

Every test transcribes the Lean body literally (file:line quoted), states the
standard formula with a reference, and compares BOTH against a direct Monte
Carlo simulation of the underlying process wherever a process exists.

stdlib only (cluster python3.12 has no numpy/sympy).
"""

import json
import math
import random
from fractions import Fraction

R = random.Random(20260803)

# ---------------------------------------------------------------- utilities

def phi(x):
    return math.exp(-0.5 * x * x) / math.sqrt(2 * math.pi)

def Phi(x):
    return 0.5 * math.erfc(-x / math.sqrt(2))

def Phi_inv(p):
    # bisection; exact enough (1e-14) and dependency-free
    lo, hi = -40.0, 40.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if Phi(mid) < p:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)

def gauss_legendre(n=400, a=-9.0, b=9.0):
    """Composite Simpson on [a,b] -- plenty for smooth Gaussian integrands."""
    if n % 2:
        n += 1
    h = (b - a) / n
    xs = [a + i * h for i in range(n + 1)]
    w = [h / 3 * (1 if i in (0, n) else (4 if i % 2 else 2)) for i in range(n + 1)]
    return list(zip(xs, w))

QUAD = gauss_legendre(4000)

def mean_sd(xs):
    n = len(xs)
    m = sum(xs) / n
    v = sum((x - m) ** 2 for x in xs) / (n - 1)
    return m, math.sqrt(v), math.sqrt(v / n)

RESULTS = []

def record(**kw):
    RESULTS.append(kw)
    print(json.dumps(kw, sort_keys=True))


# =========================================================================
# T1  VarianceComponents.lean:435  liabilityScaleH2
#     Lean:  h2_liab = h2_obs * K * (1-K) / z^2
#     Standard (Dempster & Lerner 1950; Falconer 1965; Lee et al. 2011 AJHG
#     eq. 3 with P=K, i.e. no case-control ascertainment):
#            h2_obs = h2_liab * z^2 / (K(1-K))   <=>  same formula.
#     So the two AGREE algebraically.  The question a simulation can answer and
#     a formula-vs-formula check cannot: is the underlying relation exact, or
#     only first-order in h2?  Ground truth = the liability-threshold model
#     itself, evaluated by quadrature and cross-checked by Monte Carlo.
# =========================================================================

def lean_liabilityScaleH2(h2_observed, prevalence, z_height):
    return h2_observed * prevalence * (1 - prevalence) / z_height ** 2

def exact_h2_observed(h2_liab, K):
    """Var(E[D|G]) / Var(D) in the liability-threshold model, exactly.

    L = G + E, G ~ N(0,h2), E ~ N(0,1-h2), D = 1[L > T], T = Phi^{-1}(1-K).
    E[D|G] = Phi((G - T)/sqrt(1-h2)).
    """
    T = Phi_inv(1 - K)
    sg = math.sqrt(h2_liab)
    se = math.sqrt(1 - h2_liab)
    m1 = m2 = 0.0
    for x, w in QUAD:
        dens = phi(x) * w
        p = Phi((sg * x - T) / se)
        m1 += dens * p
        m2 += dens * p * p
    var_pred = m2 - m1 * m1
    return var_pred / (m1 * (1 - m1)), m1

def mc_h2_observed(h2_liab, K, n=400000):
    T = Phi_inv(1 - K)
    sg = math.sqrt(h2_liab)
    se = math.sqrt(1 - h2_liab)
    gs = []
    ds = []
    for _ in range(n):
        g = R.gauss(0, 1) * sg
        l = g + R.gauss(0, 1) * se
        gs.append(g)
        ds.append(1.0 if l > T else 0.0)
    mg = sum(gs) / n
    md = sum(ds) / n
    cov = sum((a - mg) * (b - md) for a, b in zip(gs, ds)) / n
    vg = sum((a - mg) ** 2 for a in gs) / n
    vd = md * (1 - md)
    # variance explained on the observed scale by the BEST LINEAR predictor
    # of D from G; equals Var(E[D|G])/Var(D) only up to the nonlinearity.
    return cov * cov / (vg * vd), md

def t1():
    for K in (0.5, 0.2, 0.05, 0.01, 0.001):
        T = Phi_inv(1 - K)
        z = phi(T)
        for h2 in (0.02, 0.1, 0.3, 0.5, 0.8):
            h2obs, Kcheck = exact_h2_observed(h2, K)
            lean = lean_liabilityScaleH2(h2obs, K, z)
            rel = (lean - h2) / h2
            row = dict(test="T1-liabilityScaleH2", K=K, h2_liab_true=h2,
                       z=z, h2_obs_exact=h2obs, lean_recovers=lean,
                       rel_err=rel, quad_prevalence_check=Kcheck)
            if h2 in (0.1, 0.5) and K in (0.5, 0.01):
                mc, mdK = mc_h2_observed(h2, K, 200000)
                row["h2_obs_mc_linear"] = mc
                row["mc_prevalence"] = mdK
            record(**row)


# =========================================================================
# T2  HaplotypeTheory.lean:522  haplotypeEffectEstimationVariance
#     Lean:  sigma2 / (n * freq)
#     Standard OLS: Var(beta_hat) = sigma^2 / (n * Var(X)) and for a binary
#     haplotype indicator X ~ Bernoulli(f), Var(X) = f(1-f).
#     Ground truth = Monte Carlo over simulated regressions.
# =========================================================================

def lean_hapvar(s2, n, f):
    return s2 / (n * f)

def mc_hapvar(n, f, s2, reps):
    betas = []
    sd = math.sqrt(s2)
    for _ in range(reps):
        sx = sxx = sy = sxy = 0.0
        for _ in range(n):
            x = 1.0 if R.random() < f else 0.0
            y = R.gauss(0, sd)          # true beta = 0
            sx += x; sxx += x * x; sy += y; sxy += x * y
        den = n * sxx - sx * sx
        if den == 0:
            continue
        betas.append((n * sxy - sx * sy) / den)
    m, s, _ = mean_sd(betas)
    return s * s

def t2():
    n, s2, reps = 1000, 1.0, 3000
    for f in (0.02, 0.05, 0.1, 0.3, 0.5):
        mc = mc_hapvar(n, f, s2, reps)
        lean = lean_hapvar(s2, n, f)
        std = s2 / (n * f * (1 - f))
        record(test="T2-haplotypeEffectEstimationVariance", f=f, n=n,
               mc_var=mc, lean=lean, standard=std,
               lean_rel_err=(lean - mc) / mc, std_rel_err=(std - mc) / mc,
               mc_se_frac=math.sqrt(2.0 / reps))


# =========================================================================
# T3  StatisticalGeneticsMethodology.lean:152  effectiveSampleSizeSE
#     Lean:  n_eff = 1 / se^2
#     Standard (e.g. Prive et al. 2022 Am J Hum Genet; GenomicSEM):
#            n_eff = 1 / (se^2 * 2 p (1-p))   for a standardized trait,
#     because se^2 = sigma_y^2 / (n * Var(g)) and Var(g) = 2p(1-p).
#     Ground truth = Monte Carlo GWAS regressions of a standardized trait on
#     HWE dosages.
# =========================================================================

def lean_neff(se):
    return 1.0 / se ** 2

def mc_gwas_se(n, p, reps):
    ses = []
    for _ in range(reps):
        sx = sxx = sy = sxy = syy = 0.0
        for _ in range(n):
            g = (1.0 if R.random() < p else 0.0) + (1.0 if R.random() < p else 0.0)
            y = R.gauss(0, 1)
            sx += g; sxx += g * g; sy += y; sxy += g * y; syy += y * y
        mx = sx / n; my = sy / n
        sxx_c = sxx - n * mx * mx
        sxy_c = sxy - n * mx * my
        syy_c = syy - n * my * my
        b = sxy_c / sxx_c
        rss = syy_c - b * sxy_c
        s2 = rss / (n - 2)
        ses.append(math.sqrt(s2 / sxx_c))
    return sum(ses) / len(ses)

def t3():
    n, reps = 2000, 400
    for p in (0.5, 0.3, 0.1, 0.05, 0.01):
        se = mc_gwas_se(n, p, reps)
        lean = lean_neff(se)
        std = 1.0 / (se ** 2 * 2 * p * (1 - p))
        record(test="T3-effectiveSampleSizeSE", p=p, n_true=n, mean_se=se,
               lean_neff=lean, standard_neff=std,
               lean_rel_err=(lean - n) / n, std_rel_err=(std - n) / n)


# =========================================================================
# T4  HaplotypeTheory.lean:680  expectedSegmentLength
#     Lean:  1 / (g * r_total)
#     Standard (Pool & Nielsen 2009; Liang & Nielsen 2014; hybrid-isolation,
#     single pulse of admixture proportion alpha, g generations ago):
#     ancestry-1 tract lengths are ~ Exp with mean 1/(g(1-alpha)) MORGANS.
#     Ground truth = forward pedigree simulation with explicit crossovers.
# =========================================================================

def lean_seglen(g, r_total):
    return 1.0 / (g * r_total)

def sim_tracts(alpha, g, morgans, pop=400, chrom_reps=400):
    """Forward WF admixture with explicit recombination.

    A chromosome is a list of (end_position, ancestry) blocks over [0,morgans].
    Generation 0: each individual gets two chromosomes, each entirely of
    ancestry 1 with prob alpha else ancestry 2 (single pulse).
    Each later generation: pick two random parents, recombine each parent's
    two chromosomes with Poisson(morgans) crossovers, transmit one gamete.
    """
    def solid(a):
        return [(morgans, a)]

    pops = []
    for _ in range(pop):
        a1 = 1 if R.random() < alpha else 2
        a2 = 1 if R.random() < alpha else 2
        pops.append((solid(a1), solid(a2)))

    def gamete(ind):
        c1, c2 = ind
        k = 0
        # Poisson(morgans) crossovers
        L = math.exp(-morgans)
        pk = R.random()
        s = L
        while pk > s:
            k += 1
            L *= morgans / k
            s += L
            if k > 50:
                break
        xs = sorted(R.random() * morgans for _ in range(k))
        cur, other = (c1, c2) if R.random() < 0.5 else (c2, c1)
        out = []
        prev = 0.0
        for x in xs:
            out.extend(clip(cur, prev, x))
            prev = x
            cur, other = other, cur
        out.extend(clip(cur, prev, morgans))
        return merge(out)

    def clip(chrom, lo, hi):
        seg = []
        start = 0.0
        for end, a in chrom:
            s, e = max(start, lo), min(end, hi)
            if e > s:
                seg.append((e, a))
            start = end
        return seg

    def merge(chrom):
        out = []
        for end, a in chrom:
            if out and out[-1][1] == a:
                out[-1] = (end, a)
            else:
                out.append((end, a))
        return [tuple(x) for x in out]

    for _ in range(g):
        nxt = []
        for _ in range(pop):
            i = pops[R.randrange(pop)]
            j = pops[R.randrange(pop)]
            nxt.append((gamete(i), gamete(j)))
        pops = nxt

    # measure ancestry-1 tract lengths, excluding chromosome-edge tracts
    lengths = []
    for ind in pops[:chrom_reps]:
        for chrom in ind:
            prev = 0.0
            for idx, (end, a) in enumerate(chrom):
                if a == 1 and idx > 0 and idx < len(chrom) - 1:
                    lengths.append(end - prev)
                prev = end
    return lengths

def t4():
    morgans = 4.0
    for alpha in (0.2, 0.5, 0.8):
        for g in (5, 10, 20):
            L = sim_tracts(alpha, g, morgans)
            if not L:
                record(test="T4-expectedSegmentLength", alpha=alpha, g=g,
                       note="no interior tracts")
                continue
            m, sd, se = mean_sd(L)
            std = 1.0 / (g * (1 - alpha))
            lean = lean_seglen(g, morgans)
            record(test="T4-expectedSegmentLength", alpha=alpha, g=g,
                   morgans=morgans, n_tracts=len(L), mc_mean_morgans=m,
                   mc_se=se, standard_1_over_g_1minus_alpha=std,
                   lean_1_over_g_rtotal=lean,
                   lean_rel_err=(lean - m) / m, std_rel_err=(std - m) / m)


# =========================================================================
# T5  HaplotypeTheory.lean:566  phaseAttenuation   [POSITIVE CONTROL]
#     Lean: (1 - 2s)^2.  Standard binary-misclassification attenuation: the
#     correlation between true and called phase is (1-2s), so the effect
#     attenuates by (1-2s) and the VARIANCE EXPLAINED by (1-2s)^2.
#     Ground truth = Monte Carlo regression on misclassified phase.
# =========================================================================

def lean_phaseAttenuation(s):
    return (1 - 2 * s) ** 2

def t5():
    n, reps = 4000, 60
    for s in (0.0, 0.01, 0.05, 0.1, 0.25):
        r2s, bs = [], []
        for _ in range(reps):
            sx = sxx = sy = sxy = syy = 0.0
            for _ in range(n):
                x = 1.0 if R.random() < 0.5 else -1.0
                y = 1.0 * x + R.gauss(0, 1.0)
                xhat = -x if R.random() < s else x
                sx += xhat; sxx += xhat * xhat; sy += y
                sxy += xhat * y; syy += y * y
            mx, my = sx / n, sy / n
            sxxc = sxx - n * mx * mx
            sxyc = sxy - n * mx * my
            syyc = syy - n * my * my
            b = sxyc / sxxc
            bs.append(b)
            r2s.append(b * sxyc / syyc)
        mb, _, seb = mean_sd(bs)
        mr, _, ser = mean_sd(r2s)
        r2_0 = 1.0 / (1.0 + 1.0)  # true var explained at s=0: 1/(1+1)
        record(test="T5-phaseAttenuation", s=s, mc_beta=mb, beta_se=seb,
               mc_r2=mr, r2_se=ser, r2_ratio=mr / r2_0,
               lean=lean_phaseAttenuation(s),
               one_minus_2s=1 - 2 * s,
               r2ratio_rel_err=(lean_phaseAttenuation(s) - mr / r2_0) /
                               (mr / r2_0))


# =========================================================================
# T6  StatisticalGeneticsMethodology.lean:177,180  fixed_se_sq/random_se_sq
#     [POSITIVE CONTROL]  DerSimonian & Laird 1986: Var(theta_RE) =
#     1/sum(1/(v_i+tau^2)) when tau^2 is known.  MC over simulated studies.
# =========================================================================

def t6():
    variances = [0.01, 0.02, 0.005, 0.04, 0.015]
    for tau2 in (0.0, 0.005, 0.02):
        w = [1.0 / (v + tau2) for v in variances]
        wf = [1.0 / v for v in variances]
        pred_re = 1.0 / sum(w)
        pred_fe = 1.0 / sum(wf)
        ests_re, ests_fe = [], []
        for _ in range(200000):
            th = [R.gauss(0, math.sqrt(tau2)) if tau2 > 0 else 0.0
                  for _ in variances]
            obs = [t + R.gauss(0, math.sqrt(v)) for t, v in zip(th, variances)]
            ests_re.append(sum(o * ww for o, ww in zip(obs, w)) / sum(w))
            ests_fe.append(sum(o * ww for o, ww in zip(obs, wf)) / sum(wf))
        _, sre, _ = mean_sd(ests_re)
        _, sfe, _ = mean_sd(ests_fe)
        record(test="T6-meta-se", tau2=tau2, lean_random_se_sq=pred_re,
               mc_var_random=sre ** 2,
               rel_err_random=(pred_re - sre ** 2) / sre ** 2,
               lean_fixed_se_sq=pred_fe, mc_var_fixed=sfe ** 2,
               rel_err_fixed=(pred_fe - sfe ** 2) / sfe ** 2)


# =========================================================================
# T7  HaplotypeTheory.lean:39  expectedDistinctHaplotypes
#     Lean: 2^k * (1 - (1 - 2^-k)^n)   -- the uniform-occupancy expectation,
#     i.e. n balls thrown independently and uniformly into 2^k boxes.
#     Standard population genetics: haplotypes in a sample are drawn from a
#     genealogy, not uniformly.  Ground truth = Kingman coalescent with
#     infinite-sites mutation, conditioned on k segregating sites.
# =========================================================================

def lean_distinct(k, n):
    m = 2.0 ** k
    return m * (1 - (1 - 1 / m) ** n)

def coalescent_haplotypes(n, theta):
    """Kingman coalescent, infinite sites. Returns (#segregating, #distinct)."""
    # build tree by coalescing lineage-sets
    blocks = [frozenset([i]) for i in range(n)]
    muts = {i: set() for i in range(n)}
    site = 0
    k = n
    while k > 1:
        t = R.expovariate(k * (k - 1) / 2.0)
        # mutations on each branch during this interval
        for b in blocks:
            nm = poisson(theta / 2.0 * t)
            for _ in range(nm):
                for leaf in b:
                    muts[leaf].add(site)
                site += 1
        i, j = R.sample(range(len(blocks)), 2)
        newb = blocks[i] | blocks[j]
        blocks = [b for idx, b in enumerate(blocks) if idx not in (i, j)]
        blocks.append(newb)
        k -= 1
    haps = {frozenset(muts[i]) for i in range(n)}
    return site, len(haps)

def poisson(lam):
    if lam <= 0:
        return 0
    L = math.exp(-lam)
    k = 0
    p = 1.0
    while True:
        p *= R.random()
        if p <= L:
            return k
        k += 1
        if k > 10000:
            return k

def t7():
    n = 50
    for theta in (1.0, 5.0, 20.0):
        seg, dis = [], []
        for _ in range(400):
            s, d = coalescent_haplotypes(n, theta)
            seg.append(s)
            dis.append(d)
        ms, _, ses = mean_sd(seg)
        md, _, sed = mean_sd(dis)
        lean = lean_distinct(int(round(ms)), n)
        record(test="T7-expectedDistinctHaplotypes", n=n, theta=theta,
               mc_mean_segsites=ms, mc_mean_distinct=md, mc_se_distinct=sed,
               lean_at_k_equal_segsites=lean,
               lean_rel_err=(lean - md) / md)


# =========================================================================
# T8  HumanDemography.lean:66  neutralDriftR2Ratio
#     Lean: presentDayR2 V_A V_E fst / presentDayR2 V_A V_E 0
#         = (1-f)(V_A+V_E) / ((1-f)V_A + V_E)
#     Standard: under Balding-Nichols drift with FIXED per-allele effects,
#     E[2 p_T (1-p_T)] = (1-f) 2 p_0 (1-p_0), so target additive variance is
#     (1-f) V_A and R2_T = (1-f)V_A/((1-f)V_A+V_E).
#     Ground truth = explicit BN drift + genotype + phenotype simulation, with
#     R2 measured as squared correlation between the source-trained score and
#     the target phenotype.
# =========================================================================

def lean_neutralDriftR2Ratio(V_A, V_E, fst):
    def r2(va, ve, f):
        return (1 - f) * va / ((1 - f) * va + ve)
    return r2(V_A, V_E, fst) / r2(V_A, V_E, 0.0)

def beta_sample(a, b):
    # Beta via two Gammas (Marsaglia-Tsang)
    def gam(shape):
        if shape < 1:
            u = R.random()
            return gam(shape + 1) * u ** (1.0 / shape)
        d = shape - 1.0 / 3
        c = 1.0 / math.sqrt(9 * d)
        while True:
            x = R.gauss(0, 1)
            v = (1 + c * x) ** 3
            if v <= 0:
                continue
            u = R.random()
            if math.log(u) < 0.5 * x * x + d - d * v + d * math.log(v):
                return d * v
    ga, gb = gam(a), gam(b)
    return ga / (ga + gb)

def t8():
    M = 400          # loci
    n_ind = 4000
    V_A, V_E = 0.4, 0.6
    for fst in (0.02, 0.05, 0.1, 0.2):
        p0 = [R.uniform(0.05, 0.95) for _ in range(M)]
        # per-allele effects standardized so source V_A matches
        raw = [R.gauss(0, 1) for _ in range(M)]
        vs = sum(r * r * 2 * p * (1 - p) for r, p in zip(raw, p0))
        scale = math.sqrt(V_A / vs)
        beta = [r * scale for r in raw]
        a = (1 - fst) / fst
        pT = [beta_sample(a * p, a * (1 - p)) for p in p0]
        ratios = []
        for pop, label in ((p0, "src"), (pT, "tgt")):
            gs, ys = [], []
            for _ in range(n_ind):
                g = 0.0
                for b, p in zip(beta, pop):
                    d = (1 if R.random() < p else 0) + (1 if R.random() < p else 0)
                    g += b * d
                gs.append(g)
                ys.append(g + R.gauss(0, math.sqrt(V_E)))
            mg = sum(gs) / n_ind; my = sum(ys) / n_ind
            sxy = sum((x - mg) * (y - my) for x, y in zip(gs, ys)) / n_ind
            sxx = sum((x - mg) ** 2 for x in gs) / n_ind
            syy = sum((y - my) ** 2 for y in ys) / n_ind
            ratios.append(sxy * sxy / (sxx * syy))
        r2_src, r2_tgt = ratios
        mc_ratio = r2_tgt / r2_src
        record(test="T8-neutralDriftR2Ratio", fst=fst, mc_r2_src=r2_src,
               mc_r2_tgt=r2_tgt, mc_ratio=mc_ratio,
               lean=lean_neutralDriftR2Ratio(V_A, V_E, fst),
               floor_1_minus_fst=1 - fst,
               lean_rel_err=(lean_neutralDriftR2Ratio(V_A, V_E, fst)
                             - mc_ratio) / mc_ratio)


# =========================================================================
# T9  exact-rational cross-check: Conventions.neiGst vs hudsonFst, and the
#     AncestrySpecificArchitecture argument-order pair.  No floats.
# =========================================================================

def t9():
    def nei(p1, p2):
        pbar = (p1 + p2) / 2
        HT = 2 * pbar * (1 - pbar)
        HS = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2
        return (HT - HS) / HT

    for p1s, p2s in (("1/5", "3/5"), ("1/10", "9/10"), ("2/5", "1/2")):
        p1, p2 = Fraction(p1s), Fraction(p2s)
        g = nei(p1, p2)
        h = (p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1))
        record(test="T9-nei-vs-hudson-exact", p1=str(p1), p2=str(p2),
               nei_gst=str(g), hudson_fst=str(h), ratio=str(h / g),
               exact=True)

    # argument-order sanity: driftVariance(p0,fst) vs expectedFreqDiffSq(fst,p0)
    for p0s, fs in (("1/4", "1/20"), ("1/2", "1/10")):
        p0, f = Fraction(p0s), Fraction(fs)
        dv = p0 * (1 - p0) * f
        efd = 2 * f * p0 * (1 - p0)
        swapped = 2 * p0 * f * (1 - f)   # what an arg-order slip would give
        record(test="T9-argorder", p0=str(p0), fst=str(f),
               two_driftVariance=str(2 * dv), expectedFreqDiffSq=str(efd),
               agree=(2 * dv == efd), if_swapped=str(swapped), exact=True)


if __name__ == "__main__":
    import sys
    which = sys.argv[1:] if len(sys.argv) > 1 else list("123456789")
    fns = {"1": t1, "2": t2, "3": t3, "4": t4, "5": t5,
           "6": t6, "7": t7, "8": t8, "9": t9}
    for w in which:
        fns[w]()
    import os
    outdir = os.environ.get("PGD2_OUT", ".")
    with open(os.path.join(outdir, f"res_{'_'.join(which)}.json"), "w") as fh:
        json.dump(RESULTS, fh, indent=1)
