"""Battery 29: participation ratio done properly, plus tagged heritability.

  A. `effectivePolygenicityOfEffects` = (sum b^2)^2 / sum b^4, RETRIED. Battery
     28 compared it against the count of nonzero effects and missed by 281 sems.
     That was the design's fault, not the body's: for k iid GAUSSIAN effects the
     participation ratio is k/3, because E[b^4] = 3 sigma^4. The "effective
     number of loci" reading is only unambiguous when the effects are
     EQUAL IN MAGNITUDE, where the ratio is exactly k. So the architecture here
     is equal-magnitude with random signs, and the oracle is the count.
     Competitors: the Gaussian-architecture value k/3, carried explicitly so the
     dependence on the effect distribution is visible rather than assumed, and
     the wrong power sum b^2 / sum b^4.

  B. `gwasHeritability` = h2_true * avg_r2_tag. A GWAS that reads TAGS rather
     than causal variants recovers a fraction of the heritability set by the
     squared tag correlation. Oracle: simulate causal variants and tags at known
     r, build the phenotype from the CAUSAL variants, then measure the variance
     the TAG-based score explains. Competitor: `h2_true * avg_r_tag`, the
     unsquared form -- the same exponent question that `taggedEffect` got wrong,
     and here the answer should be the square, because heritability is quadratic
     in the effect.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def group_a():
    rng = np.random.default_rng(29001)
    cells, cells_third, cells_pow = [], [], []
    control = None
    M = 5000
    for k in (20, 100, 500, 2000):
        b = np.zeros(M)
        idx = rng.choice(M, size=k, replace=False)
        # EQUAL MAGNITUDE, random sign: the only architecture in which
        # "effective number of loci" has one unambiguous value
        b[idx] = rng.choice([-1.0, 1.0], size=k)
        s2 = float(np.sum(b ** 2))
        s4 = float(np.sum(b ** 4))
        lean = s2 ** 2 / s4
        truth = float(np.count_nonzero(b))
        lab = "k=%d of M=%d (equal magnitude)" % (k, M)
        print("  %-34s participation %.1f  nonzero %d" % (lab, lean, int(truth)))
        cells.append(dict(design=lab, lean=lean, truth=truth, sem=1e-9))
        cells_third.append(dict(design=lab, lean=k / 3.0, truth=truth,
                                sem=1e-9))
        cells_pow.append(dict(design=lab, lean=s2 / s4, truth=truth, sem=1e-9))
        if k == 100:
            # control: a GAUSSIAN architecture at the same k, where the known
            # value is k/3 -- an independent classical result on the same code
            g = np.zeros(M)
            g[rng.choice(M, size=k, replace=False)] = rng.normal(0, 1, k)
            reps = []
            for _ in range(400):
                gg = rng.normal(0, 1, k)
                reps.append(float(np.sum(gg ** 2) ** 2 / np.sum(gg ** 4)))
            control = dict(design="k=100 Gaussian [participation = k/3]",
                           lean=k / 3.0, truth=float(np.mean(reps)),
                           sem=float(np.std(reps, ddof=1) / math.sqrt(400)))
    reg = ("M = 5000 variants of which k carry EQUAL-MAGNITUDE effects with "
           "random signs and the rest are exactly zero; the oracle is the count "
           "of nonzero effects. Equal magnitude is what makes 'effective number "
           "of loci' unambiguous -- under Gaussian effects the ratio is k/3, "
           "and that value is carried as a competing cell so the dependence on "
           "the effect distribution is explicit")
    record("effectivePolygenicityOfEffects", "PolygenicArchitecture.lean",
           "(sum b^2)^2 / sum b^4", cells, regime=reg, control=control)
    record("effectivePolygenicity [k/3, the Gaussian value, competing]",
           "PolygenicArchitecture.lean", "k / 3", cells_third, regime=reg,
           control=control)
    record("effectivePolygenicity [sum b^2 / sum b^4, competing]",
           "PolygenicArchitecture.lean", "sum b^2 / sum b^4", cells_pow,
           regime=reg, control=control)


def group_b():
    rng = np.random.default_rng(29002)
    cells, cells_unsq = [], []
    control = None
    n, m = 300000, 200
    for r_tag in (0.9, 0.7, 0.5, 0.3):
        h2 = 0.5
        beta = rng.normal(0, math.sqrt(h2 / m), m)
        Gc = rng.normal(0, 1, (n, m))                  # causal variants
        # tags at correlation r_tag with their causal partners
        Gt = r_tag * Gc + math.sqrt(max(1 - r_tag ** 2, 0)) * rng.normal(
            0, 1, (n, m))
        g = Gc @ beta
        y = g + rng.normal(0, math.sqrt(max(1 - g.var(), 1e-6)), n)
        var_y = float(y.var(ddof=1))
        # REALISED heritability, not the nominal 0.5. With m = 200 the drawn
        # sum of squared effects departs from h2 by ~5%, which at these error
        # bars is tens of sems -- it voided the first run of this group by
        # failing its own control.
        h2_real = float(g.var(ddof=1)) / var_y
        # the best tag-based linear predictor: regress y on the tags
        # (they are independent of each other, so marginal slopes suffice)
        slopes = np.array([float(np.cov(Gt[:, j], y, ddof=1)[0, 1]
                                 / Gt[:, j].var(ddof=1)) for j in range(m)])
        pgs_tag = Gt @ slopes
        truth = float(np.cov(pgs_tag, y, ddof=1)[0, 1] ** 2
                      / (pgs_tag.var(ddof=1) * var_y))
        sem = 2 * truth * math.sqrt(max(1 - truth, 1e-6) / n)
        lean = h2_real * r_tag ** 2
        lab = "r_tag=%.1f (r2=%.2f)" % (r_tag, r_tag ** 2)
        print("  %-22s tag-based R2 = %.5f ± %.5f | lean h2*r2 = %.5f  "
              "alt h2*r = %.5f" % (lab, truth, sem, lean, h2_real * r_tag))
        cells.append(dict(design=lab, lean=lean, truth=truth,
                          sem=max(sem, 1e-9)))
        cells_unsq.append(dict(design=lab, lean=h2_real * r_tag, truth=truth,
                               sem=max(sem, 1e-9)))
        if r_tag == 0.9:
            # control: with the CAUSAL variants themselves the recovered R2 is
            # the heritability, measured on the same run
            pgs_c = Gc @ beta
            r2c = float(np.cov(pgs_c, y, ddof=1)[0, 1] ** 2
                        / (pgs_c.var(ddof=1) * var_y))
            control = dict(design=lab + " [causal variants recover h2]",
                           lean=h2_real, truth=r2c,
                           sem=2 * r2c * math.sqrt(max(1 - r2c, 1e-6) / n))
    reg = ("200 independent causal variants each with one tag at correlation "
           "r_tag, 300000 individuals; the phenotype is built from the CAUSAL "
           "variants and the observable is the variance explained by a score "
           "fitted on the TAGS. r_tag is swept so r and r^2 separate threefold")
    record("gwasHeritability", "AncestrySpecificArchitecture.lean",
           "h2_true * avg_r2_tag", cells, regime=reg, control=control)
    record("gwasHeritability [h2 * r unsquared, competing]",
           "AncestrySpecificArchitecture.lean", "h2_true * avg_r_tag",
           cells_unsq, regime=reg, control=control)


def main():
    for fn in (group_a, group_b):
        print("\n===== %s =====" % fn.__name__)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (fn.__name__, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk29_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
