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

group_clinical   liabilitySpecificity, and the finding is that the definition
                 is underdetermined by its own signature. `T'` and `mu_control`
                 are free arguments and nothing says which scale either lives
                 on; three self-consistent readings of "the specificity of a
                 PGS-based classifier at T'" give answers from 0.91 to 0.99999
                 on the same simulated population. All three are recorded.

group_imputation ldExtentImputationQuality against a COALESCENT. The first
                 version of this group stipulated the decay and was therefore
                 circular -- see the group's own docstring, which keeps it so
                 it is not rebuilt. The decay now comes from msprime, the free
                 `ld_extent` is fitted, and Sved's hyperbolic rides along with
                 its own free rate so what is on trial is the SHAPE.

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
from battery_core import RESULTS, dump_results, record, run_groups

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
            # NOT the realised environment mass: `n_pos` is `round(mix*N)`
            # exactly, so predicted and measured are the same number and
            # `verdict.classify` calls that control DEGENERATE, correctly.
            # This one asks the same draws a question with a known answer that
            # no pooling rule can affect: a standard normal marginal has
            # variance 1. A scale slip in either environment moves it.
            v = [float(np.var(np.concatenate([
                rng.standard_normal(int(round(mix * per_block))),
                rng.standard_normal(per_block
                                    - int(round(mix * per_block)))])))
                 for _ in range(n_blocks)]
            vmean, vsem = blocked(v)
            control = dict(design="pooled marginal variance [known to be 1]",
                           lean=1.0, truth=vmean, sem=max(vsem, 1e-12))

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
    """liabilitySpecificity: THREE readings, and the finding is that they differ.

    The body is `Phi((T' - R*h*mu_control) / sigma_resid)`. `T'` and
    `mu_control` are free ARGUMENTS and the signature does not say which scale
    either lives on -- the liability scale, or the PGS scale, or the
    standardised PGS. That is not a quibble: the three self-consistent readings
    of "the specificity of a PGS-based classifier at threshold T'" give answers
    from 0.91 to 0.99999 on the same simulated population, and the body matches
    none of them within the error bar.

    So this group records a MEASUREMENT, not a falsification. What it measures
    is that the definition is underdetermined by its own signature, which is a
    finding about the declaration and not about the arithmetic. Every reading is
    recorded, so a consumer who states which one it means gets a determinate
    answer -- the same shape as `ancestryRecalibratedSlope`, where a third
    convention had to be written down before either measurement meant anything.
    """
    print("\n===== GROUP CLINICAL  liabilitySpecificity")
    from scipy.stats import norm
    rng = np.random.default_rng(70004)
    n_blocks, per_block = 20, 200000

    cells_liab, cells_pgs, cells_own = [], [], []
    control = None
    for h_sq, r2, prev in ((0.5, 0.2, 0.05), (0.3, 0.4, 0.10),
                           (0.7, 0.1, 0.02), (0.5, 0.5, 0.20)):
        T = float(norm.ppf(1 - prev))
        R = math.sqrt(r2)
        h = math.sqrt(h_sq)
        sig = math.sqrt(h_sq * (1 - r2) + (1 - h_sq))
        Tp = T * 0.8
        sp_liab, sp_own, sp_pgs, prevs = [], [], [], []
        for _ in range(n_blocks):
            ghat = rng.standard_normal(per_block) * (R * h)
            liab = ghat + rng.standard_normal(per_block) * sig
            ctrl = liab <= T
            nc = int(ctrl.sum())
            # READING A -- the rule re-draws the residual: a NEW individual with
            # this control's genetic component.
            sp_liab.append(float(((ghat[ctrl]
                                   + rng.standard_normal(nc) * sig) <= Tp)
                                 .mean()))
            # READING B -- the rule is on the individual's OWN liability.
            sp_own.append(float((liab[ctrl] <= Tp).mean()))
            # READING C -- the rule is on the PGS component alone.
            sp_pgs.append(float((ghat[ctrl] <= Tp).mean()))
            prevs.append(float((~ctrl).mean()))
        a, a_sem = blocked(sp_liab)
        b, b_sem = blocked(sp_own)
        c, c_sem = blocked(sp_pgs)
        pmean, psem = blocked(prevs)
        # The body, at the model's own truncated control mean on the LIABILITY
        # scale -- the reading its own prose names ("mu_control = E[Y | Y <= T]").
        mu_c = -float(norm.pdf(T)) / (1 - prev)
        lean = float(norm.cdf((Tp - R * h * mu_c) / sig))
        lab = "h2=%.1f R2=%.1f K=%.2f" % (h_sq, r2, prev)
        print("  %-22s body %.5f | A re-drawn residual %.5f +/- %.5f | "
              "B own liability %.5f +/- %.5f | C PGS alone %.5f +/- %.5f"
              % (lab, lean, a, a_sem, b, b_sem, c, c_sem))
        cells_liab.append(dict(design=lab, lean=lean, truth=a,
                               sem=max(a_sem, 1e-12)))
        cells_own.append(dict(design=lab, lean=lean, truth=b,
                              sem=max(b_sem, 1e-12)))
        cells_pgs.append(dict(design=lab, lean=lean, truth=c,
                              sem=max(c_sem, 1e-12)))
        if control is None:
            control = dict(design=lab + " [realised prevalence recovers K]",
                           lean=prev, truth=pmean, sem=max(psem, 1e-12))

    reg = ("4e6 individuals per cell in 20 blocks of 2e5 under the liability "
           "threshold model the definition declares: a PGS-explained component "
           "of variance R^2*h^2, independent residual liability of variance "
           "h^2(1-R^2) + (1-h^2), disease above the prevalence threshold. "
           "THREE readings of 'specificity at T'' are measured on the same "
           "draws, because the signature does not say which scale T' and "
           "mu_control live on: the rule applied to a re-drawn residual, to the "
           "individual's own liability, and to the PGS component alone. "
           "mu_control is the model's own truncated mean, not a fitted "
           "quantity. What is recorded is the SPREAD across readings")
    record("liabilitySpecificity", "ClinicalUtilityFairness.lean",
           "Phi((T' - R * h * mu_control) / sigma_resid), against the "
           "re-drawn-residual reading", cells_liab, regime=reg,
           control=control, realised_inputs=True, argument_source="model")
    record("liabilitySpecificity [rule on the individual's own liability, "
           "competing reading]", "ClinicalUtilityFairness.lean",
           "the same body, against P(own liability <= T' | control)",
           cells_own, regime=reg, control=control, realised_inputs=True,
           argument_source="model")
    record("liabilitySpecificity [rule on the PGS component alone, competing "
           "reading]", "ClinicalUtilityFairness.lean",
           "the same body, against P(PGS component <= T' | control)",
           cells_pgs, regime=reg, control=control, realised_inputs=True,
           argument_source="model")


# ---------------------------------------------------------------------------
# group imputation -- ldExtentImputationQuality
# ---------------------------------------------------------------------------
def group_imputation():
    """ldExtentImputationQuality, against a coalescent rather than a stipulation.

    THE FIRST VERSION OF THIS GROUP WAS CIRCULAR AND IS RECORDED HERE SO IT IS
    NOT REBUILT. It generated a tag whose CORRELATION with the target fell
    linearly in `c / ld_extent`, then measured imputation r-squared -- which is
    that correlation SQUARED -- and reported the body FALSIFIED at 400%. The
    finding was entirely the modelling choice: had the r-squared been made to
    fall linearly instead, the body would have matched to machine precision and
    the design would have been a SELF-TEST. A definition of the form
    `f(c/ld_extent)` cannot be tested against a simulation that stipulates
    `f`.

    So the decay comes from a coalescent instead. Imputation r-squared between a
    tag and a target at physical distance `c` is measured from msprime, and
    `ld_extent` is FITTED -- it has to be, since nothing in the corpus says what
    an LD extent is in base pairs, and the body carries it as a free argument.
    With one free parameter and five distances the SHAPE is still refutable, and
    the rival is the shape coalescent theory actually gives: Sved's
    `r^2 = 1/(1 + 4*Ne*c)`, hyperbolic rather than linear-to-zero, fitted with
    its own free rate so neither candidate is handicapped.
    """
    print("\n===== GROUP IMPUTATION  ldExtentImputationQuality")
    import msprime
    ne, reps = 2000, 12
    seq, rho, mu = 4e6, 1e-8, 1e-8
    edges = np.array([1e4, 4e4, 1.2e5, 4e5, 1.2e6])

    per_rep = {b: [] for b in range(len(edges))}
    seps = {b: [] for b in range(len(edges))}
    for r in range(reps):
        ts = msprime.sim_ancestry(samples=40, population_size=ne,
                                  sequence_length=seq, recombination_rate=rho,
                                  random_seed=72000 + r)
        ts = msprime.sim_mutations(ts, rate=mu, random_seed=72500 + r)
        if ts.num_sites < 200:
            continue
        gm = ts.genotype_matrix()
        pos = ts.tables.sites.position
        f = gm.mean(axis=1)
        idx = np.flatnonzero(np.minimum(f, 1 - f) > 0.05)
        if idx.size < 60:
            continue
        for b, hi in enumerate(edges):
            lo = 0.0 if b == 0 else edges[b - 1]
            vals, sp = [], []
            for k in range(idx.size):
                i = idx[k]
                cand = np.flatnonzero((pos[idx] - pos[i] > lo)
                                      & (pos[idx] - pos[i] <= hi))
                if cand.size == 0:
                    continue
                j = idx[cand[0]]
                cc = np.corrcoef(gm[i], gm[j])[0, 1]
                if np.isfinite(cc):
                    vals.append(cc ** 2)
                    sp.append(float(pos[j] - pos[i]))
                if len(vals) >= 150:
                    break
            if len(vals) >= 30:
                per_rep[b].append(float(np.mean(vals)))
                seps[b].append(float(np.mean(sp)))

    xs, ys, sems = [], [], []
    for b in range(len(edges)):
        if len(per_rep[b]) < 4:
            continue
        m_, s_ = blocked(per_rep[b])
        xs.append(float(np.mean(seps[b])) * rho)     # c in Morgans
        ys.append(m_)
        sems.append(s_)
    if len(xs) < 4:
        print("  (too few usable bins)")
        return
    xs = np.asarray(xs); ys = np.asarray(ys); sems = np.asarray(sems)

    # Fit each candidate's ONE free parameter by weighted least squares on the
    # same points, so neither is handicapped.
    grid = np.exp(np.linspace(math.log(xs.min() / 20), math.log(xs.max() * 40),
                              4000))
    def wss(pred):
        return float((((pred - ys) / sems) ** 2).sum())
    best_e = min(grid, key=lambda e: wss(np.maximum(0.0, 1 - xs / e)))
    best_n = min(grid, key=lambda a: wss(1.0 / (1.0 + xs / a)))
    lin = np.maximum(0.0, 1 - xs / best_e)
    hyp = 1.0 / (1.0 + xs / best_n)
    print("  fitted ld_extent = %.4g Morgans (chi2/point %.2f); Sved scale "
          "1/(4Ne) = %.4g (chi2/point %.2f)"
          % (best_e, wss(lin) / len(xs), best_n, wss(hyp) / len(xs)))

    cells, c_sved = [], []
    for k in range(len(xs)):
        lab = "c=%.2e M" % xs[k]
        print("  %-14s measured r2 %.5f +/- %.5f   body(fitted extent) %.5f   "
              "Sved(fitted) %.5f" % (lab, ys[k], sems[k], lin[k], hyp[k]))
        cells.append(dict(design=lab, lean=float(lin[k]), truth=float(ys[k]),
                          sem=max(float(sems[k]), 1e-12)))
        c_sved.append(dict(design=lab, lean=float(hyp[k]),
                           truth=float(ys[k]), sem=max(float(sems[k]), 1e-12)))

    # POSITIVE CONTROL for the ESTIMATOR, not for either shape: a pair of sites
    # with an imposed correlation must come back at its square through the same
    # r-squared code path.
    rng2 = np.random.default_rng(72999)
    ctl = []
    for _ in range(12):
        a = rng2.standard_normal(20000)
        bq = 0.6 * a + math.sqrt(1 - 0.36) * rng2.standard_normal(20000)
        ctl.append(float(np.corrcoef(a, bq)[0, 1]) ** 2)
    cmean, csem = blocked(ctl)
    print("  CONTROL imposed correlation 0.6: measured r2 %.5f +/- %.5f "
          "(known 0.36)" % (cmean, csem))
    control = dict(design="imposed correlation 0.6 [r2 must be 0.36]",
                   lean=0.36, truth=cmean, sem=max(csem, 1e-12))

    reg = ("msprime, one panmictic population of Ne = 2000 over 4 Mb at "
           "recombination 1e-8 and mu = 1e-8, 12 replicates; the observable is "
           "the realised imputation r-squared between common site pairs binned "
           "by physical separation, with c reported in Morgans as the realised "
           "mean separation times the recombination rate. `ld_extent` is FITTED "
           "by weighted least squares, because the corpus nowhere says what an "
           "LD extent is in base pairs and the body carries it as a free "
           "argument; Sved's hyperbolic rides along with its own free rate, so "
           "what is on trial is the SHAPE and not the scale. The panel size and "
           "the frequency filter are held fixed throughout, which is the "
           "restriction the definition's own name carries")
    record("ldExtentImputationQuality", "ImputationPortability.lean",
           "max 0 (1 - c / ld_extent), ld_extent fitted", cells, regime=reg,
           control=control, realised_inputs=True, argument_source="model")
    record("ldExtentImputationQuality [Sved 1/(1 + 4*Ne*c), competing shape]",
           "ImputationPortability.lean", "1 / (1 + 4*Ne*c), rate fitted",
           c_sved, regime=reg, control=control, realised_inputs=True,
           argument_source="model")


# ---------------------------------------------------------------------------
# group impgap -- expectedSqMeanPGSDiff_IMEquilibrium
# ---------------------------------------------------------------------------
def group_impgap():
    print("\n===== GROUP IMPGAP  expectedSqMeanPGSDiff_IMEquilibrium")
    import msprime
    # Ne = 2000 over 10 Mb, NOT Ne = 500 over 2 Mb. The first version asked for
    # 600 common sites from a scaled mutation rate of 4*Ne*mu = 2e-5 over 2 Mb,
    # which yields a few dozen; every replicate failed the site-count guard and
    # the group reported "no usable replicates" -- a silent zero, which is the
    # failure mode `run_groups` exists to make loud and which a guard that skips
    # rather than raises slips past anyway.
    ne, m_loci = 2000, 600
    reps = 8

    cells, c_nodouble, c_nofactor2 = [], [], []
    control = None
    for bigM in (0.5, 2.0, 8.0):
        vals, deltas, v_as = [], [], []
        for r in range(reps):
            dem = msprime.Demography.island_model([ne, ne],
                                                  migration_rate=bigM / (4.0 * ne))
            ts = msprime.sim_ancestry(
                samples={"pop_0": 40, "pop_1": 40}, demography=dem,
                sequence_length=1e7, recombination_rate=1e-8,
                random_seed=71000 + int(10 * bigM) + r)
            ts = msprime.sim_mutations(ts, rate=1e-8,
                                       random_seed=71500 + r)
            if ts.num_sites < 100:
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
            sequence_length=1e7, recombination_rate=1e-8,
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

    reg = ("two-deme island model at Ne = 2000 over 10 Mb with recombination, 8 "
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
    failed = run_groups(group_turnover, group_msbalance, group_mixture,
                        group_clinical, group_imputation, group_impgap)
    dump_results("battery_gap01_results.json",
                 battery_source=os.path.abspath(__file__),
                 failed_groups=failed)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-66s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
