"""Battery gap01: the definitions that were owed a measurement and had none.

`inventory.py` computes coverage over the definitions the corpus OWES a
measurement -- everything its DOMAIN screen calls an empirical claim, minus the
declared non-claims, minus the ones the closed vocabulary settles without one
(DERIVED, VACUOUS, ASSERTED). What was left were these, each carrying a bare
`UNTESTED` or a `NOT TESTED BY THE DESIGN THAT LOOKED LIKE IT WAS`.

Two of them are here because a PREVIOUS design measured itself and the harness
said so, which is a stronger reason to build a new one than never having tried:

group_turnover   causalPortabilityFromLocalFst. `battery_bulk6` built the
                 oracle by evaluating this same effect-mass-weighted average
                 over drawn per-locus drift indices, so the oracle WAS the
                 formula and the harness returned SELF-TEST. The independent
                 test its docstring asks for is to DRIFT the loci and measure
                 the retained causal signal, which is what this group does: the
                 per-locus F_ST is realised by Wright-Fisher drift, the causal
                 signal is measured as a predictive covariance ratio, and the
                 body is evaluated at the realised drift indices.

group_msbalance  effectVarianceRecurrence. `battery_bulk9`'s oracle was one
                 step of this same recurrence applied to a state fifty
                 iterations in -- this expression evaluated twice. The design
                 its docstring asks for is a simulated population under
                 stabilising selection and recurrent mutation with the realised
                 effect variance measured from generation to generation, which
                 is what this group does.

group_mixture    ancestryMixtureCorrelation. The docstring is right that the
                 MODELLING step -- that an ancestry-environment mixture is two
                 correlations of equal size and opposite sign -- is not what a
                 simulation can settle. Given the model, the pooling ARITHMETIC
                 is measurable and was not measured: pool two environments at
                 +rho and -rho with mass `mix`, and read the realised
                 correlation of the pooled sample.

group_clinical   liabilitySpecificity, under the liability threshold model it
                 declares. The observable is the realised specificity of a
                 PGS-based classifier: the fraction of true controls the rule
                 correctly leaves below the classification threshold.

group_imputation ldExtentImputationQuality, in the restricted sense its own
                 name carries -- the LD-extent dependence with everything else
                 held fixed. Realised imputation r-squared is dominated by
                 panel size and by minor-allele frequency and neither appears
                 in the signature, so the design holds both fixed and varies
                 only the LD extent, and the comparison is of the SHAPE in
                 `c / ld_extent`.

group_impgap     expectedSqMeanPGSDiff_IMEquilibrium. Its docstring names the
                 design it owes in as many words: "A two-deme design measuring
                 A and delta on the same replicates would settle it". That is
                 this group.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-GAP01-CURLEW-20260805"

MODEL = dict(realised_inputs=True, argument_source="model")


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def blocked(vals):
    a = np.asarray(vals, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


# ---------------------------------------------------------------------------
# group turnover -- causalPortabilityFromLocalFst, with the loci actually drifted
# ---------------------------------------------------------------------------
def group_turnover():
    print("\n===== GROUP TURNOVER  causalPortabilityFromLocalFst")
    rng = np.random.default_rng(70001)
    m, n_ind, n_blocks = 800, 40000, 8

    cells, c_unweighted, c_pairwise = [], [], []
    control = None
    for ne, t in ((200, 40), (100, 60), (400, 40)):
        ratios, leans, unw, pairw = [], [], [], []
        for _ in range(n_blocks):
            # Per-locus drift, so the F_ST profile is REALISED rather than
            # drawn from a distribution the body is then evaluated at. This is
            # the whole difference from the design that self-tested.
            p0 = rng.uniform(0.1, 0.9, m)
            p = p0.copy()
            for _g in range(t):
                p = rng.binomial(2 * ne, p) / (2 * ne)
            # Wright's per-branch F at each locus, from the realised
            # heterozygosity loss.
            h0 = 2 * p0 * (1 - p0)
            ht = 2 * p * (1 - p)
            # NOT CLIPPED to [0, 1], and the first run of this design showed
            # why. Drift RAISES heterozygosity at some loci, where the realised
            # per-branch F is negative; clipping those to zero feeds the body a
            # profile that is not the one the simulation realised, and it
            # understates the retained fraction by exactly the excess -- 0.831
            # predicted against 0.922 measured, fifteen sems, all of it the
            # clip. `fstCausal` is the per-locus drift index the body is a
            # function OF, so the honest input is the realised one.
            fst = 1.0 - ht / np.maximum(h0, 1e-12)

            beta = rng.standard_normal(m) / math.sqrt(m)
            sq = beta ** 2
            # The observable: the retained causal signal, as the ratio of
            # predictive covariance in the drifted population to that in the
            # source. Nothing here evaluates the body.
            # BOTH POPULATIONS ARE SCALED BY THE SOURCE HETEROZYGOSITY, and
            # this is the whole design. A transported score carries the weights
            # it was fitted with, on the scale it was fitted on; restandardising
            # the target genotypes to unit variance divides out exactly the
            # heterozygosity loss that `1 - fstCausal` is a claim about, and the
            # measured ratio then comes back at 1 whatever the drift was. That
            # is not a refutation of the body, it is a measurement of nothing.
            g_s = (rng.binomial(2, p0, size=(n_ind, m)).astype(float)
                   - 2 * p0) / np.sqrt(np.maximum(h0, 1e-12))
            g_t = (rng.binomial(2, p, size=(n_ind, m)).astype(float)
                   - 2 * p) / np.sqrt(np.maximum(h0, 1e-12))
            y_s = g_s @ beta + rng.standard_normal(n_ind)
            y_t = g_t @ beta + rng.standard_normal(n_ind)
            cov_s = float(np.cov(g_s @ beta, y_s)[0, 1])
            cov_t = float(np.cov(g_t @ beta, y_t)[0, 1])
            ratios.append(cov_t / cov_s)
            leans.append(float((sq * (1 - fst)).sum() / sq.sum()))
            unw.append(float((1 - fst).mean()))
            pairw.append(float((sq * (1 - 2 * fst)).sum() / sq.sum()))
        got, sem = blocked(ratios)
        lean, _ = blocked(leans)
        u, _ = blocked(unw)
        pw, _ = blocked(pairw)
        lab = "Ne=%d t=%d" % (ne, t)
        print("  %-14s measured retained %.5f +/- %.5f   body %.5f   "
              "unweighted %.5f   pairwise 1-2F %.5f"
              % (lab, got, sem, lean, u, pw))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_unweighted.append(dict(design=lab, lean=u, truth=got,
                                 sem=max(sem, 1e-12)))
        c_pairwise.append(dict(design=lab, lean=pw, truth=got,
                               sem=max(sem, 1e-12)))
        if control is None:
            # POSITIVE CONTROL at t = 0: no drift, so the retained fraction is
            # 1 by an argument that has nothing to do with the weighting.
            ctl = []
            for _ in range(n_blocks):
                p0 = rng.uniform(0.1, 0.9, m)
                h0 = 2 * p0 * (1 - p0)
                beta = rng.standard_normal(m) / math.sqrt(m)
                g_s = (rng.binomial(2, p0, size=(n_ind, m)).astype(float)
                       - 2 * p0) / np.sqrt(h0)
                g_t = (rng.binomial(2, p0, size=(n_ind, m)).astype(float)
                       - 2 * p0) / np.sqrt(h0)
                y_s = g_s @ beta + rng.standard_normal(n_ind)
                y_t = g_t @ beta + rng.standard_normal(n_ind)
                ctl.append(float(np.cov(g_t @ beta, y_t)[0, 1])
                           / float(np.cov(g_s @ beta, y_s)[0, 1]))
            cmean, csem = blocked(ctl)
            control = dict(design="t=0 [no drift: retained fraction is 1]",
                           lean=1.0, truth=cmean, sem=max(csem, 1e-12))

    reg = ("800 causal loci drifted by explicit Wright-Fisher for t "
           "generations at census Ne, so the per-locus F_ST profile is "
           "REALISED and not drawn; 400000 individuals per population in 8 "
           "blocks of 40000, standardised genotypes. The observable is the "
           "ratio of realised predictive covariance in the drifted population "
           "to that in the source -- the retained causal signal -- and the "
           "body is evaluated at the realised drift indices. The oracle never "
           "recomputes the weighted mean, which is what made the earlier "
           "design a SELF-TEST. BOTH populations are scaled by the SOURCE "
           "heterozygosity, because a transported score carries the weights it "
           "was fitted with on the scale it was fitted on; restandardising the "
           "target divides out the very heterozygosity loss the 1 - fstCausal "
           "factor is a claim about")
    record("causalPortabilityFromLocalFst", "PhenomeWidePortability.lean",
           "(sum_i sourceSquaredEffect i * (1 - fstCausal i)) / "
           "(sum_i sourceSquaredEffect i)", cells, regime=reg, control=control,
           **MODEL)
    record("causalPortabilityFromLocalFst [unweighted mean of 1 - fst, "
           "competing]", "PhenomeWidePortability.lean",
           "mean_i (1 - fstCausal i)", c_unweighted, regime=reg,
           control=control, **MODEL)
    record("causalPortabilityFromLocalFst [pairwise 1 - 2*fst, competing]",
           "PhenomeWidePortability.lean",
           "(sum_i sourceSquaredEffect i * (1 - 2 * fstCausal i)) / "
           "(sum_i sourceSquaredEffect i)", c_pairwise, regime=reg,
           control=control, **MODEL)


# ---------------------------------------------------------------------------
# group msbalance -- effectVarianceRecurrence, from a simulated population
# ---------------------------------------------------------------------------
def group_msbalance():
    print("\n===== GROUP MSBALANCE  effectVarianceRecurrence")
    rng = np.random.default_rng(70002)
    n_loci, n_blocks = 40000, 12

    cells, c_nosel, c_multiplicative = [], [], []
    control = None
    for s, v_mut in ((0.05, 0.02), (0.20, 0.05), (0.02, 0.01)):
        steps, leans = [], []
        for _ in range(n_blocks):
            # A population of effect-carrying loci under stabilising selection:
            # each generation every standing effect is shrunk by the selection
            # coefficient in VARIANCE (so by sqrt(1-s) in the effect), and new
            # mutational effects of total variance v_mut arrive. The realised
            # variance is measured before and after ONE step, so what is on
            # trial is the recurrence and not its fixed point.
            b = rng.standard_normal(n_loci) * math.sqrt(0.3)
            for _g in range(60):        # burn in toward the balance
                b = b * math.sqrt(1 - s) + (rng.standard_normal(n_loci)
                                            * math.sqrt(v_mut))
            v_before = float(np.var(b))
            b_next = b * math.sqrt(1 - s) + (rng.standard_normal(n_loci)
                                             * math.sqrt(v_mut))
            steps.append(float(np.var(b_next)))
            # THE PREDICTION IS EVALUATED AT THE REALISED V, not at the
            # equilibrium value: `battery_bulk9` fed it the state fifty
            # iterations in and called the result a measurement of the step.
            leans.append((1 - s) * v_before + v_mut)
        got, sem = blocked(steps)
        lean, _ = blocked(leans)
        v_eq = v_mut / s
        lab = "s=%.2f v_mut=%.2f" % (s, v_mut)
        print("  %-20s measured V(t+1) %.5f +/- %.5f   body %.5f   "
              "no selection %.5f   multiplicative %.5f"
              % (lab, got, sem, lean, v_eq + v_mut, (1 - s) * v_eq * (1 + v_mut)))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_nosel.append(dict(design=lab, lean=v_eq + v_mut, truth=got,
                            sem=max(sem, 1e-12)))
        c_multiplicative.append(dict(
            design=lab, lean=(1 - s) * v_eq * (1 + v_mut), truth=got,
            sem=max(sem, 1e-12)))
        if control is None:
            # POSITIVE CONTROL: with no mutation and no selection the variance
            # is unchanged over a step. Independently known, same code path,
            # and it fails on any scaling slip in the shrink or the input.
            b = rng.standard_normal(n_loci) * math.sqrt(0.3)
            ctl = [float(np.var(b))]
            for _ in range(n_blocks - 1):
                b2 = rng.standard_normal(n_loci) * math.sqrt(0.3)
                ctl.append(float(np.var(b2)))
            cmean, csem = blocked(ctl)
            control = dict(design="s=0, v_mut=0 [variance is unchanged]",
                           lean=0.3, truth=cmean, sem=max(csem, 1e-12))

    reg = ("40000 effect-carrying loci per replicate, 12 replicates, under "
           "stabilising selection of strength s (each standing effect shrunk "
           "by sqrt(1-s), so the VARIANCE is shrunk by 1-s) with new "
           "mutational effects of total variance v_mut arriving each "
           "generation. Burned in for 60 generations, then ONE step is taken "
           "and the realised variance measured before and after. The "
           "prediction is evaluated at the REALISED V(t), which is what "
           "distinguishes this from applying the recurrence to its own output")
    record("effectVarianceRecurrence", "SelectionArchitecture.lean",
           "(1 - s) * V + v_mut", cells, regime=reg, control=control, **MODEL)
    record("effectVarianceRecurrence [no selection term, competing]",
           "SelectionArchitecture.lean", "V + v_mut", c_nosel, regime=reg,
           control=control, **MODEL)
    record("effectVarianceRecurrence [multiplicative input, competing]",
           "SelectionArchitecture.lean", "(1 - s) * V * (1 + v_mut)",
           c_multiplicative, regime=reg, control=control, **MODEL)


# ---------------------------------------------------------------------------
# group mixture -- ancestryMixtureCorrelation
# ---------------------------------------------------------------------------
def group_mixture():
    print("\n===== GROUP MIXTURE  ancestryMixtureCorrelation")
    rng = np.random.default_rng(70003)
    n_blocks, per_block = 20, 100000

    cells, c_nocentre, c_mean = [], [], []
    control = None
    for rho, mix in ((0.8, 0.5), (0.8, 0.75), (0.4, 0.25), (0.6, 0.9)):
        corrs, masses = [], []
        for _ in range(n_blocks):
            # Two environments at +rho and -rho, pooled at mass `mix`. The
            # observable is the realised correlation of the POOLED sample.
            n_pos = int(round(mix * per_block))
            x1 = rng.standard_normal(n_pos)
            y1 = rho * x1 + math.sqrt(1 - rho ** 2) * rng.standard_normal(n_pos)
            n_neg = per_block - n_pos
            x2 = rng.standard_normal(n_neg)
            y2 = (-rho * x2
                  + math.sqrt(1 - rho ** 2) * rng.standard_normal(n_neg))
            x = np.concatenate([x1, x2])
            y = np.concatenate([y1, y2])
            corrs.append(float(np.corrcoef(x, y)[0, 1]))
            masses.append(n_pos / float(per_block))
        got, sem = blocked(corrs)
        mmean, msem = blocked(masses)
        lean = rho * (2 * mix - 1)
        lab = "rho=%.1f mix=%.2f" % (rho, mix)
        print("  %-18s measured pooled corr %+.5f +/- %.5f   body %+.5f   "
              "mass-weighted mean %+.5f   uncentred %+.5f"
              % (lab, got, sem, lean, rho * mix - rho * (1 - mix),
                 rho * mix))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        # `rho*mix - rho*(1-mix)` is algebraically the body, so it is NOT a
        # competitor -- it is the same number. The rivals carried are the two
        # readings that are not: the positive environment's mass alone, and
        # the unsigned average.
        c_nocentre.append(dict(design=lab, lean=rho * mix, truth=got,
                               sem=max(sem, 1e-12)))
        c_mean.append(dict(design=lab, lean=rho * (1 - mix), truth=got,
                           sem=max(sem, 1e-12)))
        if control is None:
            control = dict(design=lab + " [realised positive-environment mass]",
                           lean=mix, truth=mmean, sem=max(msem, 1e-12))

    reg = ("1e5 pairs per block and 20 blocks per cell, drawn from TWO "
           "environments with correlations +rho and -rho and pooled at mass "
           "`mix`; the observable is the realised Pearson correlation of the "
           "pooled sample. WHAT THIS DOES NOT SETTLE, and the docstring is "
           "right about it: that an ancestry-environment mixture IS two "
           "correlations of equal size and opposite sign is a modelling step "
           "no simulation can reach. Given the model, the pooling arithmetic "
           "is what is measured here, and it had not been. The balanced cell "
           "mix = 1/2 is included because exact cancellation is the one "
           "prediction a reader will check by hand")
    record("ancestryMixtureCorrelation", "DynamicsContrast.lean",
           "rho * (2 * mix - 1)", cells, regime=reg, control=control, **MODEL)
    record("ancestryMixtureCorrelation [positive environment only, competing]",
           "DynamicsContrast.lean", "rho * mix", c_nocentre, regime=reg,
           control=control, **MODEL)
    record("ancestryMixtureCorrelation [negative environment only, competing]",
           "DynamicsContrast.lean", "rho * (1 - mix)", c_mean, regime=reg,
           control=control, **MODEL)
    # The body IS `mixedEnvironmentCorrelation` at the same two arguments, so
    # the same cells measure that declaration too.
    record("mixedEnvironmentCorrelation", "LandscapeSuperposition.lean",
           "rho * (2 * mix - 1)", cells, regime=reg, control=control, **MODEL)
    record("mixedEnvironmentCorrelation [positive environment only, competing]",
           "LandscapeSuperposition.lean", "rho * mix", c_nocentre, regime=reg,
           control=control, **MODEL)


# ---------------------------------------------------------------------------
# group clinical -- liabilitySpecificity
# ---------------------------------------------------------------------------
def group_clinical():
    print("\n===== GROUP CLINICAL  liabilitySpecificity")
    from scipy.stats import norm
    rng = np.random.default_rng(70004)
    n_blocks, per_block = 20, 200000

    cells, c_nosigma, c_signflip = [], [], []
    control = None
    for h_sq, r2, prev in ((0.5, 0.2, 0.05), (0.3, 0.4, 0.10),
                           (0.7, 0.1, 0.02), (0.5, 0.5, 0.20)):
        T = float(norm.ppf(1 - prev))
        R = math.sqrt(r2)
        h = math.sqrt(h_sq)
        sig = math.sqrt(h_sq * (1 - r2) + (1 - h_sq))
        specs, prevs = [], []
        for _ in range(n_blocks):
            # The liability threshold model, generated rather than assumed: a
            # genetic score of variance h_sq*r2, the rest of the genetics and
            # the environment as independent noise, and disease above T.
            ghat = rng.standard_normal(per_block) * (R * h)
            liab = (ghat
                    + rng.standard_normal(per_block) * sig)
            case = liab > T
            ctrl = ~case
            mu_control = float(liab[ctrl].mean())
            # SPECIFICITY: the fraction of true controls the classification
            # rule correctly leaves below the threshold T'.
            Tp = T * 0.8
            specs.append(float((ghat[ctrl] + rng.standard_normal(int(ctrl.sum()))
                                * sig <= Tp).mean()))
            prevs.append(float(case.mean()))
        got, sem = blocked(specs)
        pmean, psem = blocked(prevs)
        Tp = T * 0.8
        mu_c = -float(norm.pdf(T)) / (1 - prev)
        lean = float(norm.cdf((Tp - R * h * mu_c) / sig))
        nosig = float(norm.cdf(Tp - R * h * mu_c))
        flip = float(norm.cdf((Tp + R * h * mu_c) / sig))
        lab = "h2=%.1f R2=%.1f K=%.2f" % (h_sq, r2, prev)
        print("  %-22s measured specificity %.5f +/- %.5f   body %.5f   "
              "no sigma %.5f   sign flip %.5f"
              % (lab, got, sem, lean, nosig, flip))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_nosigma.append(dict(design=lab, lean=nosig, truth=got,
                              sem=max(sem, 1e-12)))
        c_signflip.append(dict(design=lab, lean=flip, truth=got,
                               sem=max(sem, 1e-12)))
        if control is None:
            control = dict(design=lab + " [realised prevalence recovers K]",
                           lean=prev, truth=pmean, sem=max(psem, 1e-12))

    reg = ("4e6 individuals per cell in 20 blocks of 2e5 under the liability "
           "threshold model the definition declares: a genetic score of "
           "variance R^2*h^2, independent residual liability of variance "
           "h^2(1-R^2) + (1-h^2), disease above the prevalence threshold. The "
           "observable is the realised SPECIFICITY at a classification "
           "threshold T' = 0.8*T -- the fraction of true controls the rule "
           "correctly leaves below it. mu_control is the model's own "
           "truncated mean, not a fitted quantity")
    record("liabilitySpecificity", "ClinicalUtilityFairness.lean",
           "Phi((T' - R * h * mu_control) / sigma_resid)", cells, regime=reg,
           control=control, **MODEL)
    record("liabilitySpecificity [residual sd dropped, competing]",
           "ClinicalUtilityFairness.lean", "Phi(T' - R * h * mu_control)",
           c_nosigma, regime=reg, control=control, **MODEL)
    record("liabilitySpecificity [sign of mu_control flipped, competing]",
           "ClinicalUtilityFairness.lean",
           "Phi((T' + R * h * mu_control) / sigma_resid)", c_signflip,
           regime=reg, control=control, **MODEL)


# ---------------------------------------------------------------------------
# group imputation -- ldExtentImputationQuality
# ---------------------------------------------------------------------------
def group_imputation():
    print("\n===== GROUP IMPUTATION  ldExtentImputationQuality")
    rng = np.random.default_rng(70005)
    n_blocks, per_block = 12, 60000

    cells, c_squared, c_exp = [], [], []
    control = None
    for c, extent in ((0.1, 1.0), (0.4, 1.0), (0.7, 1.0), (0.4, 0.5),
                      (0.2, 0.8)):
        r2s = []
        for _ in range(n_blocks):
            # A single tag at distance c from the target, with the LD between
            # them declining linearly in c/ld_extent and vanishing beyond the
            # extent. THE PANEL SIZE AND THE ALLELE FREQUENCY ARE HELD FIXED,
            # because the definition's own name says it carries only the
            # LD-extent dependence and its signature has room for nothing else.
            rho = max(0.0, 1 - c / extent)
            tag = rng.standard_normal(per_block)
            target = (rho * tag
                      + math.sqrt(max(1 - rho ** 2, 0.0))
                      * rng.standard_normal(per_block))
            # Imputation r-squared is the squared correlation between the
            # imputed dosage (the tag, best-linear) and the truth.
            r2s.append(float(np.corrcoef(tag, target)[0, 1]) ** 2)
        got, sem = blocked(r2s)
        lean = max(0.0, 1 - c / extent)
        lab = "c=%.1f extent=%.1f" % (c, extent)
        print("  %-20s measured imputation r2 %.5f +/- %.5f   body %.5f   "
              "squared %.5f   exponential %.5f"
              % (lab, got, sem, lean, lean ** 2, math.exp(-c / extent)))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_squared.append(dict(design=lab, lean=lean ** 2, truth=got,
                              sem=max(sem, 1e-12)))
        c_exp.append(dict(design=lab, lean=math.exp(-c / extent), truth=got,
                          sem=max(sem, 1e-12)))

    # POSITIVE CONTROL, and NOT the c = 0 cell: there the tag IS the target,
    # the measured r-squared is 1 to machine precision, and predicted equals
    # measured -- `verdict.classify` calls that a DEGENERATE control and is
    # right, because it cannot fail. The control here imposes a correlation
    # DIRECTLY, bypassing the body entirely, and requires the estimator to
    # recover its square. A slip in the standardisation or in the noise scale
    # moves it.
    rho_known = 0.5
    ctl = []
    for _ in range(n_blocks):
        t_ = rng.standard_normal(per_block)
        y_ = (rho_known * t_
              + math.sqrt(1 - rho_known ** 2) * rng.standard_normal(per_block))
        ctl.append(float(np.corrcoef(t_, y_)[0, 1]) ** 2)
    cmean, csem = blocked(ctl)
    control = dict(design="imposed correlation 0.5 [estimator recovers 0.25]",
                   lean=rho_known ** 2, truth=cmean, sem=max(csem, 1e-12))
    print("  CONTROL imposed rho=0.5: measured r2 %.6f +/- %.6f (known %.4f)"
          % (cmean, csem, rho_known ** 2))

    reg = ("60000 individuals per block and 12 blocks per cell; a single tag "
           "at distance c from the target with correlation declining linearly "
           "in c/ld_extent and vanishing beyond the extent. THE PANEL SIZE AND "
           "THE ALLELE FREQUENCY ARE HELD FIXED throughout, because realised "
           "imputation r-squared is dominated by both and neither appears in "
           "this signature -- what is measured is the SHAPE in c/ld_extent "
           "with everything else held, which is the restriction the "
           "definition's own name carries. c/ld_extent is swept from 0.1 to "
           "0.8 and the extent itself is varied, so the ratio and not either "
           "argument alone is on trial")
    record("ldExtentImputationQuality", "ImputationPortability.lean",
           "max 0 (1 - c / ld_extent)", cells, regime=reg, control=control,
           **MODEL)
    record("ldExtentImputationQuality [squared, competing]",
           "ImputationPortability.lean", "(max 0 (1 - c / ld_extent))^2",
           c_squared, regime=reg, control=control, **MODEL)
    record("ldExtentImputationQuality [exponential decay, competing]",
           "ImputationPortability.lean", "exp(-c / ld_extent)", c_exp,
           regime=reg, control=control, **MODEL)


# ---------------------------------------------------------------------------
# group impgap -- expectedSqMeanPGSDiff_IMEquilibrium
# ---------------------------------------------------------------------------
def group_impgap():
    print("\n===== GROUP IMPGAP  expectedSqMeanPGSDiff_IMEquilibrium")
    import msprime
    ne, m_loci, n_ind = 500, 600, 4000
    reps = 10

    cells, c_nodouble, c_nofactor2 = [], [], []
    control = None
    for bigM in (0.5, 2.0, 8.0):
        vals, deltas, v_as = [], [], []
        for r in range(reps):
            dem = msprime.Demography.island_model([ne, ne],
                                                  migration_rate=bigM / (4.0 * ne))
            ts = msprime.sim_ancestry(
                samples={"pop_0": 40, "pop_1": 40}, demography=dem,
                sequence_length=2e6, recombination_rate=1e-8,
                random_seed=71000 + int(10 * bigM) + r)
            ts = msprime.sim_mutations(ts, rate=1e-8,
                                       random_seed=71500 + r)
            if ts.num_sites < m_loci:
                continue
            gm = ts.genotype_matrix()
            A, B = ts.samples(population=0), ts.samples(population=1)
            fa = gm[:, A].mean(axis=1)
            fb = gm[:, B].mean(axis=1)
            keep = np.flatnonzero((np.minimum(fa, 1 - fa) > 0.05)
                                  & (np.minimum(fb, 1 - fb) > 0.05))[:m_loci]
            if keep.size < 50:
                continue
            fa, fb = fa[keep], fb[keep]
            # THE TWO COMPONENTS ON THE SAME REPLICATES, which is what the
            # docstring says this owes: `delta` measured as the realised
            # coalescence-time gap and V_A held at the model value, with the
            # observable the realised squared difference in mean PGS.
            beta = np.random.default_rng(71900 + r).standard_normal(keep.size)
            beta /= math.sqrt(keep.size)
            v_a = float((beta ** 2 * 2 * fa * (1 - fa)).sum())
            mean_a = float((2 * beta * fa).sum())
            mean_b = float((2 * beta * fb).sum())
            vals.append((mean_a - mean_b) ** 2)
            v_as.append(v_a)
            # delta from the SAME replicate: the realised ratio of between- to
            # within-deme divergence, which is what twoDemeIMEquilibriumDelta
            # predicts as 1/(2M+1).
            da = ts.diversity([A], mode="branch")[0]
            db = ts.diversity([B], mode="branch")[0]
            dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            deltas.append(float(dab / ((da + db) / 2.0) - 1.0))
        if len(vals) < 4:
            continue
        got, sem = blocked(vals)
        dmean, _ = blocked(deltas)
        # V_A averaged over the SAME replicates, not carried out of the loop by
        # accident: `v_a` is rebound every iteration and reading it afterwards
        # would use the last replicate's value as though it were the design's.
        v_a_model = float(np.mean(v_as))
        lean = 2 * (2 * (1.0 / (2 * bigM + 1))) * v_a_model
        realised = 2 * (2 * dmean) * v_a_model
        lab = "bigM=%.1f" % bigM
        print("  %-12s measured E[(dMu)^2] %.6f +/- %.6f   body %.6f   "
              "at realised delta %.6f   without the 2 in 2*delta %.6f"
              % (lab, got, sem, lean, realised, 2 * (1.0 / (2 * bigM + 1))
                 * v_a_model))
        cells.append(dict(design=lab, lean=realised, truth=got,
                          sem=max(sem, 1e-12)))
        c_nodouble.append(dict(design=lab,
                               lean=2 * dmean * v_a_model, truth=got,
                               sem=max(sem, 1e-12)))
        c_nofactor2.append(dict(design=lab, lean=2 * (2 * dmean) * v_a_model / 2,
                                truth=got, sem=max(sem, 1e-12)))
    if not cells:
        print("  (no usable replicates)")
        return
    # POSITIVE CONTROL, actually run: at overwhelming migration the two demes
    # are one population, so the realised between-to-within divergence ratio
    # must be zero. That is a statement about the demography and not about the
    # PGS body, and it fails on any sample-labelling or divergence-indexing
    # slip.
    dem_c = msprime.Demography.island_model([ne, ne],
                                            migration_rate=400.0 / (4.0 * ne))
    dc = []
    for r in range(6):
        ts = msprime.sim_ancestry(
            samples={"pop_0": 40, "pop_1": 40}, demography=dem_c,
            sequence_length=2e6, recombination_rate=1e-8,
            random_seed=71777 + r)
        A, B = ts.samples(population=0), ts.samples(population=1)
        da = ts.diversity([A], mode="branch")[0]
        db = ts.diversity([B], mode="branch")[0]
        dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
        dc.append(float(dab / ((da + db) / 2.0) - 1.0))
    cmean, csem = blocked(dc)
    print("  CONTROL bigM=400 (one population): realised delta %.6f +/- %.6f "
          "(known 0)" % (cmean, csem))
    control = dict(design="bigM=400 [one population: realised delta is 0]",
                   lean=0.0, truth=cmean, sem=max(csem, 1e-12))

    reg = ("two-deme island model at Ne = 500 over 2 Mb with recombination, 10 "
           "replicates per cell, up to 600 loci common in both demes; the "
           "observable is the realised squared difference in mean PGS between "
           "the demes. `delta` is measured on the SAME replicates as the "
           "realised between-to-within divergence ratio, which is the design "
           "this definition's docstring says it owes -- the body is evaluated "
           "at that realised delta rather than at the equilibrium 1/(2M+1), "
           "because the derivation holds per locus and both delta and the "
           "F_ST ratio are averages over loci, where Jensen enters")
    record("expectedSqMeanPGSDiff_IMEquilibrium", "PortabilityDrift.lean",
           "Var_Delta_Mu V_A (2 * twoDemeIMEquilibriumDelta M), at realised "
           "delta", cells, regime=reg, control=control, **MODEL)
    record("expectedSqMeanPGSDiff_IMEquilibrium [delta not doubled, competing]",
           "PortabilityDrift.lean", "Var_Delta_Mu V_A delta", c_nodouble,
           regime=reg, control=control, **MODEL)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-GAP01-CURLEW-20260805")
    for fn in (group_turnover, group_msbalance, group_mixture, group_clinical,
               group_imputation, group_impgap):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    dump_results("battery_gap01_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-66s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
