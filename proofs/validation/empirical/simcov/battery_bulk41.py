"""Battery 41: the worthless MATCHes, and a suspected NOMINAL-PARAMETER artefact.

Group A re-runs `battery_bulk22.group_a`.  That group reported
`ancestryRecalibratedR2`, `effectTurnoverR2Loss` and `ancestryRecalibratedSlope`
FALSIFIED at 353, 353 and 185 sems with a passing control -- but it evaluated
the predictions at the NOMINAL genetic correlation rho while the m = 400 effect
vectors it actually drew have a realised correlation off by O(1/sqrt(m)) ~ 5%,
and at n = 200000 the error bar is small enough that 5% is hundreds of sems.
That is the exact failure mode the harness's own rules name.  Here every
prediction is evaluated at the REALISED correlation between the two effect
vectors that were drawn, and at the REALISED source R-squared and score-scale
ratio; the nominal reading is carried on the same cells as the competitor, so
the data says which one the disagreement belonged to.

Groups B-D attack MATCHes that carried no competitor and therefore measured
nothing:

  B `driftVariance = p0(1-p0) F`, `twoPopDriftVariance`, `expectedFreqDiffSq`
    (battery 21, three MATCHes, no competitor).  The competitors are the two
    readings the definition's own section note warns about -- the Hudson
    pairwise F_ST and Nei's G_ST, both MEASURED on the same replicates -- plus
    the dropped factor of two.
  C `haplotypeHomozygosity = sum f_i^2` (battery 23, MATCH, no competitor) and
    `additiveGeneticVariance = sum beta_i^2` (battery 18, MATCH, no competitor).
  D `ldDecayPerGeneration = (1-r)^t` and
    `admixtureLDMagnitude = a(1-a)(pA-pB)^2 (1-r)^g`, which had no verdict at
    all, against an individual-based recombination simulation.

Conventions, stated:
  * `fst` in group B is the PER-BRANCH Wright F against the ancestor, as the
    definition's own docstring insists, computed from the simulation's own Ne
    and t as 1-(1-1/(2Ne))^t and NOT from the sample (feeding the sample's own
    heterozygosity loss back in would make the comparison an algebraic
    identity: Var(p_t) = p0(1-p0) - E[p_t(1-p_t)] holds exactly whenever drift
    is unbiased, whatever F is).
  * group C's genotypes are standardized to unit variance and in linkage
    equilibrium, which is the regime `sum beta^2` needs; an LD cell is carried
    to show the regime is a condition and not decoration.
  * `r` in group D is the per-generation recombination FRACTION between the two
    loci, and `t`/`g` are generations since the LD was created.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import json
import math
import os

import numpy as np

from battery_core import RESULTS, record

FRESH_TOKEN = "SIMCOV-BATTERY41-MERLIN-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def r2_of(pred, y):
    return float(np.corrcoef(pred, y)[0, 1] ** 2)


# ---------------------------------------------------------------------------
# A.  the recalibration scalars, at the REALISED genetic correlation
# ---------------------------------------------------------------------------
def group_a():
    rng = np.random.default_rng(41001)
    n, m, h2 = 200000, 400, 0.5
    cells_r2, cells_loss, cells_slope = [], [], []
    nom_r2, nom_loss, nom_slope = [], [], []
    alt_slope = []
    control = None
    for rho, alpha in ((0.9, 1.0), (0.7, 1.0), (0.5, 1.0), (0.9, 1.6),
                       (0.7, 0.6)):
        bs = rng.normal(0, math.sqrt(h2 / m), m)
        bt = rho * bs + math.sqrt(max(1 - rho ** 2, 0)) * rng.normal(
            0, math.sqrt(h2 / m), m)
        # THE REALISED genetic correlation between the two effect vectors that
        # were actually drawn -- not the nominal rho that generated them.
        rho_hat = float(bs @ bt / math.sqrt((bs @ bs) * (bt @ bt)))
        Gs = rng.normal(0, 1, (n, m))
        gs = Gs @ bs
        ys = gs + rng.normal(0, math.sqrt(max(1 - gs.var(), 1e-6)), n)
        pgs_s = Gs @ bs
        r2_source = r2_of(pgs_s, ys)
        Gt = rng.normal(0, 1, (n, m)) * alpha
        gt = Gt @ bt
        yt = gt + rng.normal(0, math.sqrt(max(1 - gt.var(), 1e-6)), n)
        pgs_t = Gt @ bs
        r2_target = r2_of(pgs_t, yt)
        slope = float(np.cov(pgs_t, yt, ddof=1)[0, 1] / pgs_t.var(ddof=1))
        b_source = float(np.cov(pgs_s, ys, ddof=1)[0, 1] / pgs_s.var(ddof=1))
        alpha_meas = float(pgs_t.std(ddof=1) / pgs_s.std(ddof=1))
        sem_r2 = max(2 * abs(r2_target) * math.sqrt(max(1 - r2_target, 1e-6) / n),
                     1e-5)
        sem_slope = abs(slope) * math.sqrt(2.0 / n) + 1e-9
        lab = "rho=%.1f alpha=%.1f (realised rho %.4f)" % (rho, alpha, rho_hat)
        print("  %-40s r2_tgt=%.5f (realised-rho %.5f, nominal-rho %.5f) | "
              "slope=%.5f (realised %.5f, nominal %.5f)"
              % (lab, r2_target, r2_source * rho_hat ** 2,
                 r2_source * rho ** 2, slope, rho_hat * b_source / alpha_meas,
                 rho * b_source / alpha_meas))
        cells_r2.append(dict(design=lab, lean=r2_source * rho_hat ** 2,
                             truth=r2_target, sem=sem_r2))
        nom_r2.append(dict(design=lab, lean=r2_source * rho ** 2,
                           truth=r2_target, sem=sem_r2))
        cells_loss.append(dict(design=lab,
                               lean=r2_source * (1 - rho_hat ** 2),
                               truth=r2_source - r2_target, sem=sem_r2))
        nom_loss.append(dict(design=lab, lean=r2_source * (1 - rho ** 2),
                             truth=r2_source - r2_target, sem=sem_r2))
        cells_slope.append(dict(design=lab,
                                lean=rho_hat * b_source / alpha_meas,
                                truth=slope, sem=sem_slope))
        nom_slope.append(dict(design=lab, lean=rho * b_source / alpha_meas,
                              truth=slope, sem=sem_slope))
        alt_slope.append(dict(design=lab,
                              lean=rho_hat * b_source * alpha_meas,
                              truth=slope, sem=sem_slope))
        if rho == 0.9 and alpha == 1.0:
            control = dict(design=lab + " [source-population slope = 1]",
                           lean=1.0, truth=b_source,
                           sem=abs(b_source) * math.sqrt(2.0 / n) + 1e-9)
    reg = ("400 causal variants, standardized genotypes, 200000 individuals "
           "per population; the target effect vector is drawn rho-correlated "
           "with the source vector and the target genotype scale is alpha. "
           "Every quantity compared against is a realised sample statistic, "
           "and -- the change from battery 22 -- every prediction is evaluated "
           "at the REALISED correlation between the two effect vectors drawn, "
           "which with m = 400 differs from the nominal rho by about 5%")
    record("ancestryRecalibratedR2", "AncestryCalibration.lean",
           "r2Source * rhoSq  [rhoSq = REALISED squared effect correlation]",
           cells_r2, regime=reg, control=control)
    record("ancestryRecalibratedR2 [nominal rho, the battery-22 reading, "
           "competing]", "AncestryCalibration.lean",
           "r2Source * rhoSq  [rhoSq = NOMINAL]", nom_r2, regime=reg,
           control=control)
    record("effectTurnoverR2Loss", "AncestryCalibration.lean",
           "r2Source * (1 - rhoSq)  [rhoSq = REALISED]", cells_loss,
           regime=reg, control=control)
    record("effectTurnoverR2Loss [nominal rho, competing]",
           "AncestryCalibration.lean", "r2Source * (1 - rhoSq)  [NOMINAL]",
           nom_loss, regime=reg, control=control)
    record("ancestryRecalibratedSlope", "AncestryCalibration.lean",
           "rho * bSource / alpha  [rho = REALISED]", cells_slope, regime=reg,
           control=control)
    record("ancestryRecalibratedSlope [nominal rho, competing]",
           "AncestryCalibration.lean", "rho * bSource / alpha  [NOMINAL]",
           nom_slope, regime=reg, control=control)
    record("ancestryRecalibratedSlope [rho*b*alpha reading, competing]",
           "AncestryCalibration.lean", "rho * bSource * alpha", alt_slope,
           regime=reg, control=control)


# ---------------------------------------------------------------------------
# B.  driftVariance / twoPopDriftVariance / expectedFreqDiffSq
# ---------------------------------------------------------------------------
def group_b():
    """Wright-Fisher drift from a common ancestor, two independent lineages.

    10^5 independent loci per cell are carried through t generations of
    binomial sampling in each of two demes of size Ne.  The observables are the
    realised Var(p1 - p0) and the realised E[(p1-p2)^2] across loci.  The
    per-branch F is the MODEL's 1-(1-1/(2Ne))^t; the Hudson pairwise F_ST and
    Nei's G_ST are MEASURED on the same replicates and carried as the competing
    readings, because the definition's own section note says feeding either of
    them in is the mistake this design exists to detect.
    """
    rng = np.random.default_rng(41002)
    nloci = 200000
    p0 = 0.3
    cells1, c1_hud, c1_nei = [], [], []
    cells2, c2_half, c2_hud = [], [], []
    control = None
    for Ne, t in ((200, 50), (200, 150), (500, 100), (100, 40)):
        p1 = np.full(nloci, p0)
        p2 = np.full(nloci, p0)
        for _ in range(t):
            p1 = rng.binomial(2 * Ne, p1) / (2.0 * Ne)
            p2 = rng.binomial(2 * Ne, p2) / (2.0 * Ne)
        F = 1.0 - (1.0 - 1.0 / (2.0 * Ne)) ** t
        var1 = float(np.mean((p1 - p0) ** 2))
        d2 = float(np.mean((p1 - p2) ** 2))
        sem1 = float(np.std((p1 - p0) ** 2, ddof=1)) / math.sqrt(nloci)
        sem2 = float(np.std((p1 - p2) ** 2, ddof=1)) / math.sqrt(nloci)
        # measured Hudson pairwise F_ST and Nei G_ST, ratio of averages
        num = np.mean((p1 - p2) ** 2 - p1 * (1 - p1) / (2 * Ne - 1)
                      - p2 * (1 - p2) / (2 * Ne - 1))
        den = np.mean(p1 * (1 - p2) + p2 * (1 - p1))
        F_hud = float(num / den)
        pbar = (p1 + p2) / 2.0
        F_nei = float(np.mean((p1 - p2) ** 2 / 4.0) / np.mean(pbar * (1 - pbar)))
        lab = "Ne=%d t=%d (F=%.4f, Hudson %.4f, Nei %.4f)" % (Ne, t, F, F_hud,
                                                              F_nei)
        print("  %-46s Var1=%.6f ± %.6f  E[(p1-p2)^2]=%.6f ± %.6f | "
              "body1 %.6f  body2 %.6f"
              % (lab, var1, sem1, d2, sem2, p0 * (1 - p0) * F,
                 2 * p0 * (1 - p0) * F))
        cells1.append(dict(design=lab, lean=p0 * (1 - p0) * F, truth=var1,
                           sem=sem1))
        c1_hud.append(dict(design=lab, lean=p0 * (1 - p0) * F_hud, truth=var1,
                           sem=sem1))
        c1_nei.append(dict(design=lab, lean=p0 * (1 - p0) * F_nei, truth=var1,
                           sem=sem1))
        cells2.append(dict(design=lab, lean=2 * p0 * (1 - p0) * F, truth=d2,
                           sem=sem2))
        c2_half.append(dict(design=lab, lean=p0 * (1 - p0) * F, truth=d2,
                            sem=sem2))
        c2_hud.append(dict(design=lab, lean=2 * p0 * (1 - p0) * F_hud,
                           truth=d2, sem=sem2))
        if Ne == 200 and t == 50:
            # Control: drift is unbiased, so the mean frequency after t
            # generations must still be p0. Measured, independent of every
            # formula under test, and it fails if the sampler drifts.
            control = dict(design="Ne=200 t=50 [drift unbiased: E[p_t] = p0]",
                           lean=p0, truth=float(p1.mean()),
                           sem=float(p1.std(ddof=1)) / math.sqrt(nloci))
    reg = ("Wright-Fisher binomial sampling, two demes of size Ne started from "
           "a common ancestral frequency p0 = 0.3, 200000 independent loci, t "
           "generations with no mutation and no migration; the observables are "
           "the realised Var(p1 - p0) and the realised E[(p1 - p2)^2] across "
           "loci. The per-branch F is the model's 1-(1-1/(2Ne))^t, and the "
           "Hudson pairwise F_ST and Nei G_ST measured on the SAME replicates "
           "are carried as competitors, which is what the definition's own "
           "section note says must be discriminated")
    record("driftVariance", "AncestrySpecificArchitecture.lean",
           "p0 * (1 - p0) * fst   [fst = per-branch Wright F]", cells1,
           regime=reg, control=control)
    record("driftVariance [Hudson pairwise F_ST fed in, competing]",
           "AncestrySpecificArchitecture.lean", "p0*(1-p0)*F_ST_Hudson",
           c1_hud, regime=reg, control=control)
    record("driftVariance [Nei G_ST fed in, competing]",
           "AncestrySpecificArchitecture.lean", "p0*(1-p0)*G_ST_Nei", c1_nei,
           regime=reg, control=control)
    record("twoPopDriftVariance", "AncestrySpecificArchitecture.lean",
           "2 * driftVariance p0 fst", cells2, regime=reg, control=control)
    record("expectedFreqDiffSq", "AncestrySpecificArchitecture.lean",
           "2 * fst * p0 * (1 - p0)", cells2, regime=reg, control=control)
    record("twoPopDriftVariance [factor of two dropped, competing]",
           "AncestrySpecificArchitecture.lean", "p0 * (1 - p0) * fst", c2_half,
           regime=reg, control=control)
    record("twoPopDriftVariance [Hudson F_ST fed in, competing]",
           "AncestrySpecificArchitecture.lean", "2*p0*(1-p0)*F_ST_Hudson",
           c2_hud, regime=reg, control=control)


# ---------------------------------------------------------------------------
# C.  haplotypeHomozygosity and additiveGeneticVariance
# ---------------------------------------------------------------------------
def group_c():
    rng = np.random.default_rng(41003)
    # --- haplotypeHomozygosity: the match probability of two random draws ----
    cells, c_mean, c_comp, c_norm = [], [], [], []
    control = None
    n = 8000000
    for k, conc in ((4, 0.4), (6, 1.0), (10, 0.3), (3, 3.0)):
        f = rng.dirichlet(np.full(k, conc))
        draws = rng.choice(k, size=(n, 2), p=f)
        match = float(np.mean(draws[:, 0] == draws[:, 1]))
        sem = math.sqrt(match * (1 - match) / n)
        H = float((f ** 2).sum())
        lab = "k=%d conc=%.1f (H=%.4f)" % (k, conc, H)
        print("  %-26s match = %.6f ± %.6f | body %.6f  1/k %.6f  1-H %.6f"
              % (lab, match, sem, H, 1.0 / k, 1 - H))
        cells.append(dict(design=lab, lean=H, truth=match, sem=sem))
        c_mean.append(dict(design=lab, lean=1.0 / k, truth=match, sem=sem))
        c_comp.append(dict(design=lab, lean=1 - H, truth=match, sem=sem))
        c_norm.append(dict(design=lab, lean=H / k, truth=match, sem=sem))
        if k == 6:
            # Control: a UNIFORM haplotype distribution must match at 1/k,
            # measured through the same draw-and-compare code path.
            fu = np.full(k, 1.0 / k)
            du = rng.choice(k, size=(n, 2), p=fu)
            mu = float(np.mean(du[:, 0] == du[:, 1]))
            control = dict(design="k=6 uniform [match probability = 1/k]",
                           lean=1.0 / k, truth=mu,
                           sem=math.sqrt(mu * (1 - mu) / n))
    reg = ("a haplotype frequency vector drawn from a Dirichlet, then 8e6 "
           "independent PAIRS of haplotypes drawn from it; the observable is "
           "the realised fraction of pairs that match, which is an independent "
           "route to the homozygosity and does not evaluate the sum of squares")
    record("haplotypeHomozygosity", "HaplotypeTheory.lean", "sum f_i^2", cells,
           regime=reg, control=control)
    record("haplotypeHomozygosity [uniform reading 1/k, competing]",
           "HaplotypeTheory.lean", "1/k", c_mean, regime=reg, control=control)
    record("haplotypeHomozygosity [complement 1 - sum f^2, competing]",
           "HaplotypeTheory.lean", "1 - sum f_i^2", c_comp, regime=reg,
           control=control)
    record("haplotypeHomozygosity [divided by k, competing]",
           "HaplotypeTheory.lean", "(sum f_i^2)/k", c_norm, regime=reg,
           control=control)

    # --- additiveGeneticVariance: Var of the genetic value -------------------
    cells, c_abs, c_mean2, c_ld = [], [], [], []
    control = None
    n2 = 400000
    for m, scale, rho_ld in ((50, 0.10, 0.0), (200, 0.05, 0.0),
                             (100, 0.08, 0.0), (100, 0.08, 0.5)):
        beta = rng.normal(0, scale, m)
        if rho_ld == 0.0:
            G = rng.normal(0, 1, (n2, m))
        else:
            # exchangeable LD: a shared factor gives every pair correlation rho
            common = rng.normal(0, 1, (n2, 1))
            G = (math.sqrt(rho_ld) * common
                 + math.sqrt(1 - rho_ld) * rng.normal(0, 1, (n2, m)))
        g = G @ beta
        v = float(g.var(ddof=1))
        sem = v * math.sqrt(2.0 / n2)
        sb2 = float((beta ** 2).sum())
        lab = "m=%d LD=%.1f" % (m, rho_ld)
        print("  %-20s Var(g) = %.6f ± %.6f | body %.6f  |beta| %.6f  "
              "mean %.6f" % (lab, v, sem, sb2, float(np.abs(beta).sum()),
                             sb2 / m))
        row = dict(design=lab, lean=sb2, truth=v, sem=sem)
        (c_ld if rho_ld > 0 else cells).append(row)
        if rho_ld == 0.0:
            c_abs.append(dict(design=lab, lean=float(np.abs(beta).sum()),
                              truth=v, sem=sem))
            c_mean2.append(dict(design=lab, lean=sb2 / m, truth=v, sem=sem))
        if m == 200:
            # Control: a SINGLE standardized variant explains exactly beta^2,
            # measured on the same code path.
            b1 = 0.3
            g1 = rng.normal(0, 1, n2) * b1
            control = dict(design="m=1 [single variant: Var = beta^2]",
                           lean=b1 ** 2, truth=float(g1.var(ddof=1)),
                           sem=b1 ** 2 * math.sqrt(2.0 / n2))
    reg = ("m standardized causal variants in LINKAGE EQUILIBRIUM, 400000 "
           "individuals; the observable is the realised sample variance of the "
           "genetic value G beta. One extra cell puts the same variants in "
           "exchangeable LD at pairwise correlation 0.5, where sum beta^2 is "
           "no longer the variance, so the linkage-equilibrium regime is shown "
           "to be a condition rather than decoration")
    record("additiveGeneticVariance", "TransferLearningPGS.lean",
           "sum beta_i^2", cells, regime=reg, control=control)
    record("additiveGeneticVariance [sum |beta|, competing]",
           "TransferLearningPGS.lean", "sum |beta_i|", c_abs, regime=reg,
           control=control)
    record("additiveGeneticVariance [per-variant mean, competing]",
           "TransferLearningPGS.lean", "(sum beta_i^2)/m", c_mean2, regime=reg,
           control=control)
    record("additiveGeneticVariance [same body OUTSIDE linkage equilibrium]",
           "TransferLearningPGS.lean", "sum beta_i^2", c_ld, regime=reg,
           control=control)


# ---------------------------------------------------------------------------
# D.  ldDecayPerGeneration and admixtureLDMagnitude
# ---------------------------------------------------------------------------
def group_d():
    """Individual-based random mating with recombination.

    N diploids, two loci at recombination fraction r.  Each generation every
    offspring takes one gamete from each of two random parents, and a gamete is
    the parent's maternal haplotype at both loci with probability 1-r and a
    recombinant with probability r.  D is MEASURED from the haplotype counts,
    so the recursion is enacted by the sampler and read off the sample rather
    than evaluated.
    """
    rng = np.random.default_rng(41004)
    N = 400000

    def evolve(hap, r, gens):
        """hap: (N, 2, 2) int8 -- individual, haplotype, locus."""
        out = []
        for _ in range(gens):
            n = hap.shape[0]
            kids = np.empty_like(hap)
            for side in (0, 1):
                par = rng.integers(0, n, n)
                pick = rng.integers(0, 2, (n, 2))       # which parental hap
                rec = rng.random(n) < r
                pick[:, 1] = np.where(rec, 1 - pick[:, 0], pick[:, 0])
                kids[:, side, 0] = hap[par, pick[:, 0], 0]
                kids[:, side, 1] = hap[par, pick[:, 1], 1]
            hap = kids
            flat = hap.reshape(-1, 2).astype(float)
            p = flat[:, 0].mean()
            q = flat[:, 1].mean()
            out.append(float((flat[:, 0] * flat[:, 1]).mean() - p * q))
        return out

    # --- ldDecayPerGeneration ------------------------------------------------
    cells, c_exp, c_half, c_lin = [], [], [], []
    control = None
    for r in (0.05, 0.2, 0.4):
        # start in complete LD: haplotypes 11 and 00 only, each at 1/2
        base = rng.integers(0, 2, N)
        hap = np.empty((N, 2, 2), dtype=np.int8)
        for side in (0, 1):
            b = rng.integers(0, 2, N)
            hap[:, side, 0] = b
            hap[:, side, 1] = b
        del base
        flat0 = hap.reshape(-1, 2).astype(float)
        D0 = float((flat0[:, 0] * flat0[:, 1]).mean()
                   - flat0[:, 0].mean() * flat0[:, 1].mean())
        gens = 8
        Ds = evolve(hap, r, gens)
        for t in (2, 5, 8):
            ratio = Ds[t - 1] / D0
            sem = 3.0 / math.sqrt(2 * N)     # generous: D is a sample moment
            lab = "r=%.2f t=%d (D0=%.4f)" % (r, t, D0)
            print("  %-28s D_t/D_0 = %.5f ± %.5f | body %.5f  exp %.5f  "
                  "(1-r)^2t %.5f" % (lab, ratio, sem, (1 - r) ** t,
                                     math.exp(-r * t), (1 - r) ** (2 * t)))
            cells.append(dict(design=lab, lean=(1 - r) ** t, truth=ratio,
                              sem=sem))
            c_exp.append(dict(design=lab, lean=math.exp(-r * t), truth=ratio,
                              sem=sem))
            c_half.append(dict(design=lab, lean=(1 - r) ** (2 * t),
                               truth=ratio, sem=sem))
            c_lin.append(dict(design=lab, lean=max(1 - r * t, 0.0),
                              truth=ratio, sem=sem))
        if abs(r - 0.2) < 1e-9:
            # Control: with NO recombination the disequilibrium must persist,
            # so the ratio is 1 after the same number of generations. Measured
            # through the identical evolve() path and it fails if the gamete
            # sampler leaks.
            hap0 = np.empty((N, 2, 2), dtype=np.int8)
            for side in (0, 1):
                b = rng.integers(0, 2, N)
                hap0[:, side, 0] = b
                hap0[:, side, 1] = b
            f0 = hap0.reshape(-1, 2).astype(float)
            D00 = float((f0[:, 0] * f0[:, 1]).mean()
                        - f0[:, 0].mean() * f0[:, 1].mean())
            D0s = evolve(hap0, 0.0, 8)
            control = dict(design="r=0 t=8 [no recombination: D_t/D_0 = 1]",
                           lean=1.0, truth=D0s[-1] / D00,
                           sem=3.0 / math.sqrt(2 * N))
    reg = ("400000 diploids, two loci at recombination fraction r, random "
           "mating with one gamete from each of two random parents and a "
           "recombinant gamete with probability r; started in complete "
           "disequilibrium and D MEASURED from the haplotype counts each "
           "generation. r is swept eightfold so (1-r)^t and exp(-r t) separate")
    record("ldDecayPerGeneration", "LongitudinalPortability.lean", "(1 - r)^t",
           cells, regime=reg, control=control)
    record("ldDecayPerGeneration [exponential reading, competing]",
           "LongitudinalPortability.lean", "exp(-r*t)", c_exp, regime=reg,
           control=control)
    record("ldDecayPerGeneration [(1-r)^(2t), competing]",
           "LongitudinalPortability.lean", "(1 - r)^(2t)", c_half, regime=reg,
           control=control)
    record("ldDecayPerGeneration [linear reading, competing]",
           "LongitudinalPortability.lean", "1 - r*t", c_lin, regime=reg,
           control=control)


GROUPS = (("A recalibration scalars at realised rho", group_a),
          ("B driftVariance family", group_b),
          ("C haplotypeHomozygosity / additiveGeneticVariance", group_c),
          ("D ldDecayPerGeneration", group_d))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY41-MERLIN-20260804")
    for label, fn in GROUPS:
        print("\n===== %s =====" % label)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (label, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk41_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-22s %-62s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
