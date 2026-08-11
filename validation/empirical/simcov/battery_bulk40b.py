"""Battery 40b: the four cells of battery 40 whose GATES failed, redone.

Battery 40 produced four results its own gates would not certify, and this file
fixes the designs rather than the write-ups:

  A `averageEffect`. The control was "set the dominance to zero and the slope
    must be a", and with `d = 0` the genotypic value is EXACTLY linear in
    dosage, so least squares returns `a` to machine precision. `verdict.py`
    correctly refused it as degenerate -- a control that cannot fail gates
    nothing -- and the competitors were downgraded to LEAD. The control here is
    the sampler's own mean dosage against `2p`, which carries sampling noise
    and would fail if the Hardy-Weinberg draw were wrong.

  C `effectiveGeneticEffect`. Both competitors were CONSTANT across the design
    (`bG`, `bG + bGxE`), so the harness reported NO POWER: a prediction that
    does not move cannot be said to have been rejected by a design that moves.
    A competitor that moves with `E_mean` is added -- the reading that takes the
    environment's second moment as well as its mean.

  E `effectiveFisherInformation`. Battery 40 read FALSIFIED at 3.2 sems and 7%,
    just past both gates, on n = 600 individuals per study. The estimator there
    is a RATIO (slope times variance over covariance) and a ratio is biased at
    order 1/n, so 7% at n = 600 is the estimator and not the definition. n is
    raised and swept, and the residual is reported AGAINST n: a bias that
    shrinks like 1/n is the estimator's, a bias that does not is the body's.
    That is a discrimination battery 40 could not make.

  F `multiAncestryEffectiveN`. Battery 40 rejected the body AND all three
    competitors, which is the signature of a broken observable rather than four
    wrong formulas. The MSE-equivalence inversion is dropped for a direct
    reading: the posterior precision of the target effect, minus the prior
    precision, which is the sample size the data contributed. That quantity is
    what "effective sample size" has to mean if it is to be compared with n1
    and n2 at all, and it is stated here rather than left implicit.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import json
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY40B-GOSHAWK-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def hwe_dosage(rng, p, n):
    return ((rng.random(n) < p).astype(np.int8)
            + (rng.random(n) < p).astype(np.int8)).astype(float)


def ols(x, y):
    n = len(x)
    xc = x - x.mean()
    sxx = float(xc @ xc)
    b = float(xc @ (y - y.mean())) / sxx
    resid = y - y.mean() - b * xc
    s2 = float(resid @ resid) / (n - 2)
    return b, math.sqrt(s2 / sxx)


def group_a():
    rng = np.random.default_rng(40101)
    n = 4000000
    a, d = 1.0, 0.8
    cells, c_1mp, c_p, c_a2 = [], [], [], []
    control = None
    for p in (0.2, 0.35, 0.5, 0.7, 0.85):
        g = hwe_dosage(rng, p, n)
        p_hat = float(g.mean()) / 2.0
        value = np.where(g == 0.0, -a, np.where(g == 1.0, d, a))
        b, se = ols(g, value)
        lab = "p=%.2f (realised %.4f)" % (p, p_hat)
        print("  %-26s slope = %+.5f ± %.5f | body %+.5f  (1-p) %+.5f  "
              "p %+.5f  2(1-2p) %+.5f"
              % (lab, b, se, a + d * (1 - 2 * p_hat), a + d * (1 - p_hat),
                 a + d * p_hat, a + 2 * d * (1 - 2 * p_hat)))
        cells.append(dict(design=lab, lean=a + d * (1 - 2 * p_hat), truth=b,
                          sem=se))
        c_1mp.append(dict(design=lab, lean=a + d * (1 - p_hat), truth=b,
                          sem=se))
        c_p.append(dict(design=lab, lean=a + d * p_hat, truth=b, sem=se))
        c_a2.append(dict(design=lab, lean=a + 2 * d * (1 - 2 * p_hat), truth=b,
                         sem=se))
        if p == 0.35:
            # Control with SAMPLING NOISE in it, so it can fail: the drawn
            # genotypes' mean dosage must be 2p under Hardy-Weinberg.
            control = dict(design="p=0.35 [Hardy-Weinberg mean dosage = 2p]",
                           lean=2 * 0.35, truth=float(g.mean()),
                           sem=math.sqrt(2 * 0.35 * 0.65 / n))
    reg = ("one diploid locus in Hardy-Weinberg proportions, 4e6 individuals, "
           "genotypic values -a / d / a on the three genotypes; the observable "
           "is the realised OLS slope of genotypic value on alt-allele dosage. "
           "p is swept across 1/2 so 1-2p changes sign, and every prediction "
           "uses the REALISED allele frequency")
    record("averageEffect", "BlindnessRegistry.lean", "a + d * (1 - 2 * p)",
           cells, regime=reg, control=control, realised_inputs=True)
    record("averageEffect [dominance factor 1-p, competing]",
           "BlindnessRegistry.lean", "a + d * (1 - p)", c_1mp, regime=reg,
           control=control, realised_inputs=True)
    record("averageEffect [dominance factor p, competing]",
           "BlindnessRegistry.lean", "a + d * p", c_p, regime=reg,
           control=control, realised_inputs=True)
    record("averageEffect [dominance factor doubled, competing]",
           "BlindnessRegistry.lean", "a + 2*d*(1 - 2*p)", c_a2, regime=reg,
           control=control, realised_inputs=True)


def group_c():
    rng = np.random.default_rng(40103)
    n = 2000000
    bG, bE, bGxE, sE = 0.4, 0.3, 0.25, 1.0
    cells, c_second, c_half = [], [], []
    control = None
    for E_mean in (-1.5, -0.5, 0.0, 1.0, 2.5):
        g = rng.normal(0, 1, n)
        E = rng.normal(E_mean, sE, n)
        y = bG * g + bE * E + bGxE * g * E + rng.normal(0, 1, n)
        b, se = ols(g, y)
        E_hat = float(E.mean())
        v_hat = float(E.var(ddof=1))
        lab = "E_mean=%+.1f (realised %+.4f)" % (E_mean, E_hat)
        print("  %-30s slope = %+.5f ± %.5f | body %+.5f  +var %+.5f  "
              "half %+.5f" % (lab, b, se, bG + bGxE * E_hat,
                              bG + bGxE * (E_hat + v_hat),
                              bG + bGxE * E_hat / 2))
        cells.append(dict(design=lab, lean=bG + bGxE * E_hat, truth=b, sem=se))
        # Competitors that MOVE with the design, so a rejection is a rejection
        # of a functional form and not of a constant.
        c_second.append(dict(design=lab, lean=bG + bGxE * (E_hat + v_hat),
                             truth=b, sem=se))
        c_half.append(dict(design=lab, lean=bG + bGxE * E_hat / 2, truth=b,
                           sem=se))
        if E_mean == 1.0:
            # Control: the environment's realised mean must be E_mean. Carries
            # sampling noise and fails if the draw is wrong.
            control = dict(design="E_mean=+1.0 [realised mean of E]",
                           lean=1.0, truth=E_hat, sem=sE / math.sqrt(n))
    reg = ("the file's own linear GxE model Y = bG G + bE E + bGxE G E + eps, "
           "2e6 individuals, G standardized and E independent of G with unit "
           "variance; the observable is the realised marginal OLS slope of Y "
           "on G. E_mean is swept through zero and negative, and both "
           "competitors MOVE across the design so a rejection is of a form")
    record("effectiveGeneticEffect", "GeneEnvironmentInterplay.lean",
           "beta_G + beta_GxE * E_mean", cells, regime=reg, control=control,
           realised_inputs=True)
    record("effectiveGeneticEffect [environment second moment too, competing]",
           "GeneEnvironmentInterplay.lean",
           "beta_G + beta_GxE * (E_mean + Var E)", c_second, regime=reg,
           control=control, realised_inputs=True)
    record("effectiveGeneticEffect [half the interaction, competing]",
           "GeneEnvironmentInterplay.lean", "beta_G + beta_GxE * E_mean / 2",
           c_half, regime=reg, control=control, realised_inputs=True)


def group_e():
    """Information about the causal effect through a tag, with n SWEPT.

    The estimator is a ratio and therefore biased at order 1/n. Reporting the
    residual against n separates an estimator artefact from a defect in the
    body: the first shrinks like 1/n, the second does not.
    """
    rng = np.random.default_rng(40105)
    p = q = 0.35
    beta = 0.5
    cells, c_r1, c_r4 = [], [], []
    control = None

    def draw(r_target, n_ind):
        D = r_target * math.sqrt(p * (1 - p) * q * (1 - q))
        h = np.array([p * q + D, p * (1 - q) - D,
                      (1 - p) * q - D, (1 - p) * (1 - q) + D])
        h = np.clip(h, 1e-12, None)
        h /= h.sum()
        idx = rng.choice(4, size=(n_ind, 2), p=h)
        causal = ((idx == 0) | (idx == 1)).sum(axis=1).astype(float)
        tag = ((idx == 0) | (idx == 2)).sum(axis=1).astype(float)
        return causal, tag

    # WHICH AVERAGE OVER STUDIES THE BODY IS PREDICTING, derived before the run
    # rather than chosen after it.
    #
    # Write the estimator out. `b_tag = Cov(tag,y)/Var(tag)` and `y = beta*causal
    # + eps`, so `est = Cov(tag,y)/Cov(tag,causal) = beta + Cov(tag,eps) /
    # Cov(tag,causal)`. Conditional on one study's drawn dosages,
    # `Var(Cov(tag,eps)) = sigma^2 Var(tag)/n` and `Cov(tag,causal)^2 = r2 *
    # Var(tag) * Var(causal)`, so
    #
    #     Var(est | that study's design) = sigma^2 / (n * Var(causal) * r2)
    #
    # and with `sigma = 1` that is `1/(n * H * r2)` for THAT study. The oracle is
    # one over the variance of `est` ACROSS studies, and the across-study
    # variance is the MEAN of the per-study variances (the estimator is
    # conditionally unbiased, so the between-study term vanishes). So
    #
    #     info = 1 / E_j[1/(n H_j r2_j)] = n / E_j[1/(H_j r2_j)]
    #
    # -- a HARMONIC mean of `H_j r2_j`, not the product of two arithmetic means.
    #
    # THE PREDICTION I WROTE HERE BEFORE RUNNING IT WAS WRONG AND THE ROW IS
    # KEPT SO THAT IT STAYS WRONG IN PUBLIC. I expected the Jensen gap between
    # the two averages to be roughly constant in n, on the reasoning that it is
    # a property of the spread of `H_j r2_j` across studies, and therefore to
    # be separable from the order-1/n estimator bias this group was built to
    # isolate. It is not. That spread is itself sampling scatter WITHIN each
    # study -- `r2_j` and `H_j` are estimated from n individuals apiece -- so it
    # falls like 1/n and the gap falls with it: measured at 1.39, 0.34 and 0.09
    # percent across n = 600, 2400, 9600 at fixed r. The harmonic correction is
    # a COMPONENT of the order-1/n family, not an alternative to it, and this
    # design cannot separate the two because they have the same n-dependence.
    #
    # Both readings are computed and printed in every cell. The HARMONIC one is
    # scored, because it is the one the functional above predicts, and the
    # product-of-means figure is carried beside it so the size of the choice is
    # never something a reader has to take on trust.
    gaps = []
    for r, n, reps in ((0.6, 600, 6000), (0.6, 2400, 6000),
                       (0.6, 9600, 6000), (0.9, 2400, 6000)):
        ests, r2_real, h_real = [], [], []
        for _ in range(reps):
            causal, tag = draw(r, n)
            if tag.std() == 0 or causal.std() == 0:
                continue
            y = beta * causal + rng.normal(0, 1.0, n)
            b_tag, _ = ols(tag, y)
            cov = float(np.cov(tag, causal, ddof=1)[0, 1])
            if abs(cov) < 1e-9:
                continue
            ests.append(b_tag * float(tag.var(ddof=1)) / cov)
            r2_real.append(float(np.corrcoef(tag, causal)[0, 1]) ** 2)
            # the causal variant's REALISED heterozygosity in this study: for a
            # diploid dosage that is exactly the dosage variance, and it is the
            # quantity `2p(1-p)` names. The nominal table frequency was what
            # this group used, and it is the one argument that kept the whole
            # prediction from being declarable as realised.
            h_real.append(float(causal.var(ddof=1)))
        ests = np.asarray(ests)
        r2j = np.asarray(r2_real)
        hj = np.asarray(h_real)
        r2_hat = float(np.mean(r2j))
        h_hat = float(np.mean(hj))
        info = 1.0 / float(ests.var(ddof=1))
        sem = info * math.sqrt(2.0 / (len(ests) - 1))

        def harmonic(w):
            """n / E_j[1/(H_j w_j)], the average the functional predicts."""
            return n / float(np.mean(1.0 / (hj * w)))

        lean = harmonic(r2j)
        prod_of_means = n * h_hat * r2_hat
        gaps.append(100.0 * (prod_of_means / lean - 1.0))
        lab = "r=%.1f n=%d (realised r2=%.4f)" % (r, n, r2_hat)
        print("  %-34s I = %.2f ± %.2f | body %.2f (%.2f%% off)  "
              "[product-of-means %.2f, %.2f%% above the harmonic]  r^1 %.2f  "
              "r^4 %.2f"
              % (lab, info, sem, lean, 100 * (lean / info - 1), prod_of_means,
                 gaps[-1], harmonic(np.sqrt(r2j)), harmonic(r2j ** 2)))
        cells.append(dict(design=lab, lean=lean, truth=info, sem=sem))
        c_r1.append(dict(design=lab, lean=harmonic(np.sqrt(r2j)), truth=info,
                         sem=sem))
        c_r4.append(dict(design=lab, lean=harmonic(r2j ** 2), truth=info,
                         sem=sem))
        if r == 0.9 and n == 2400:
            # Control: with the CAUSAL variant observed directly the estimator
            # is ordinary least squares and the information must be n*2p(1-p).
            ests0, h0 = [], []
            for _ in range(2000):
                causal, _tag = draw(r, n)
                y = beta * causal + rng.normal(0, 1.0, n)
                b0, _ = ols(causal, y)
                ests0.append(b0)
                h0.append(float(causal.var(ddof=1)))
            i0 = 1.0 / float(np.var(ests0, ddof=1))
            control = dict(design="causal variant observed [I = n 2p(1-p)]",
                           lean=n / float(np.mean(1.0 / np.asarray(h0))),
                           truth=i0,
                           sem=i0 * math.sqrt(2.0 / (len(ests0) - 1)))
    reg = ("two linked diploid loci from an explicit haplotype-frequency table "
           "so the dosage correlation is constructed and then REMEASURED, 6000 "
           "independent studies per cell, Y = beta * causal dosage + "
           "unit-variance Gaussian noise; the observable is the inverse "
           "variance across studies of the causal effect estimated through the "
           "tag with realised moments. n is swept SIXTEENFOLD at fixed r so an "
           "order-1/n estimator bias is separated from a defect in the body. "
           "BOTH arguments are realised: the LD r-squared and the causal "
           "variant's heterozygosity are each remeasured from the drawn "
           "dosages of the same studies the oracle is taken over, the "
           "heterozygosity as the realised dosage variance. The estimand form "
           "is n over the MEAN OF THE RECIPROCALS of H*r2 across studies, "
           "which is what an inverse across-study variance predicts; the "
           "product of the two arithmetic means is a different average and is "
           "printed beside it")
    note = ("both averages over studies are computed in every cell and the "
            "HARMONIC one is scored, because that is what the conditional "
            "variance of the ratio estimator predicts: the across-study "
            "variance is the MEAN of the per-study variances, and each of those "
            "is one over n*H_j*r2_j. The product of arithmetic means sits %s "
            "percent above it across the four cells. That gap SHRINKS with n "
            "(1.39 to 0.09 percent from n=600 to n=9600 at fixed r), because "
            "the spread it comes from is sampling scatter within each study "
            "rather than a property of the design -- so it is a component of "
            "the order-1/n family this group was built to isolate and not an "
            "alternative to it, and this design cannot tell the two apart"
            % "/".join("%.2f" % g for g in gaps))
    record("effectiveFisherInformation", "AncestrySpecificPower.lean",
           "n * (2*p*(1-p)) * r2_ld", cells, regime=reg, control=control,
           realised_inputs=True, note=note)
    record("effectiveFisherInformation [r^1 attenuation, competing]",
           "AncestrySpecificPower.lean", "n * (2*p*(1-p)) * r", c_r1,
           regime=reg, control=control, realised_inputs=True)
    record("effectiveFisherInformation [r^4 attenuation, competing]",
           "AncestrySpecificPower.lean", "n * (2*p*(1-p)) * r2^2", c_r4,
           regime=reg, control=control, realised_inputs=True)


def group_f():
    """Effective sample size read as the data's contribution to precision.

    Convention, stated because it is the whole question: N_eff is the posterior
    PRECISION of the target effect minus the prior precision 1/tau2, i.e. the
    precision the two studies contributed.  With target data alone that number
    is exactly n1, which is what makes it comparable with n1 and n2 and is
    checked as the control.  Both are measured from the realised MSE of the
    posterior mean over replicates.
    """
    rng = np.random.default_rng(40106)
    reps = 600000
    cells, c_lin, c_sum, c_solo, c_naive = [], [], [], [], []
    control = None
    designs = ((3000, 12000, 0.9, 3e-5), (3000, 12000, 0.6, 3e-5),
               (3000, 12000, 0.9, 3e-4), (6000, 6000, 0.7, 3e-5))
    for n1, n2, rg, tau2 in designs:
        bt = rng.normal(0, math.sqrt(tau2), reps)
        bo = rg * bt + math.sqrt(max(1 - rg ** 2, 0.0) * tau2) * rng.normal(
            0, 1, reps)
        rg_hat = float(np.corrcoef(bt, bo)[0, 1])
        b1 = bt + rng.normal(0, 1 / math.sqrt(n1), reps)
        b2 = bo + rng.normal(0, 1 / math.sqrt(n2), reps)
        v2 = (1 - rg_hat ** 2) * tau2 + 1.0 / n2
        est = ((n1 * b1 + (rg_hat / v2) * b2)
               / (1.0 / tau2 + n1 + rg_hat ** 2 / v2))
        mse = float(np.mean((est - bt) ** 2))
        n_eff = 1.0 / mse - 1.0 / tau2
        sem = (1.0 / mse) * math.sqrt(2.0 / (reps - 1))
        lab = ("n1=%d n2=%d rg=%.1f n2*tau2=%.2f (realised rg %.4f)"
               % (n1, n2, rg, n2 * tau2, rg_hat))
        print("  %-52s N_eff = %.0f ± %.0f | body %.0f  lin %.0f  sum %.0f  "
              "solo %.0f" % (lab, n_eff, sem, n1 + rg_hat ** 2 * n2,
                             n1 + rg_hat * n2, n1 + n2, n1))
        # THE BODY, which is the posterior-precision form this battery's own
        # regime paragraph describes and which the corpus adopted after the
        # naive `n1 + rg^2 * n2` was rejected here. `BayesianPGSTheory.lean`
        # reads `n_target + rg^2 / ((1 - rg^2) * priorVariance + 1/n_other)`,
        # and `v2` two lines up is exactly that denominator -- the battery has
        # been computing it all along to form the posterior mean, and recording
        # a different formula as the corpus row.
        cells.append(dict(design=lab, lean=n1 + rg_hat ** 2 / v2, truth=n_eff,
                          sem=sem))
        c_naive.append(dict(design=lab, lean=n1 + rg_hat ** 2 * n2,
                            truth=n_eff, sem=sem))
        c_lin.append(dict(design=lab, lean=n1 + rg_hat * n2, truth=n_eff,
                          sem=sem))
        c_sum.append(dict(design=lab, lean=float(n1 + n2), truth=n_eff,
                          sem=sem))
        c_solo.append(dict(design=lab, lean=float(n1), truth=n_eff, sem=sem))
        if rg == 0.9 and n1 == 3000 and tau2 == 3e-5:
            # Control: with the OTHER ancestry discarded the contributed
            # precision must be exactly n1. Measured through the same posterior
            # mean and the same inversion, and it fails if the convention or
            # the estimator is wrong.
            est0 = b1 * (tau2 / (tau2 + 1.0 / n1))
            mse0 = float(np.mean((est0 - bt) ** 2))
            control = dict(design="target data alone [contributed N = n1]",
                           lean=float(n1), truth=1.0 / mse0 - 1.0 / tau2,
                           sem=(1.0 / mse0) * math.sqrt(2.0 / (reps - 1)))
    reg = ("two ancestries, one locus, effects from a Gaussian prior of "
           "variance tau2; the other ancestry's effect is rg times the "
           "target's PLUS independent scatter, which is what a genetic "
           "correlation below one means. 600000 replicates; N_eff is the "
           "posterior precision of the target effect MINUS the prior "
           "precision, i.e. the precision the data contributed, which is the "
           "reading under which target data alone gives exactly n1 -- checked "
           "as the control. n2*tau2 is swept across 1, the boundary at which "
           "the scatter term (1-rg^2)tau2 overtakes the sampling term 1/n2")
    record("multiAncestryEffectiveN", "BayesianPGSTheory.lean",
           "n_target + rg^2 / ((1 - rg^2) * priorVariance + 1/n_other)", cells,
           regime=reg, control=control, realised_inputs=True)
    record("multiAncestryEffectiveN [the superseded n_t + rg^2 * n_o, "
           "competing]", "BayesianPGSTheory.lean",
           "n_target + rg^2 * n_other", c_naive, regime=reg, control=control,
           realised_inputs=True)
    record("multiAncestryEffectiveN [n_t + rg*n_o, competing]",
           "BayesianPGSTheory.lean", "n_target + rg * n_other", c_lin,
           regime=reg, control=control, realised_inputs=True)
    record("multiAncestryEffectiveN [n_t + n_o, competing]",
           "BayesianPGSTheory.lean", "n_target + n_other", c_sum, regime=reg,
           control=control, realised_inputs=True)
    record("multiAncestryEffectiveN [no borrowing, competing]",
           "BayesianPGSTheory.lean", "n_target", c_solo, regime=reg,
           control=control, realised_inputs=True)


GROUPS = (("A averageEffect (control fixed)", group_a),
          ("C effectiveGeneticEffect (moving competitors)", group_c),
          ("E effectiveFisherInformation (n swept)", group_e),
          ("F multiAncestryEffectiveN (stated N_eff convention)", group_f))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY40B-GOSHAWK-20260804")
    for label, fn in GROUPS:
        print("\n===== %s =====" % label)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (label, e))
            import traceback
            traceback.print_exc()
    dump_results("battery_bulk40b_results.json")
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-22s %-62s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
