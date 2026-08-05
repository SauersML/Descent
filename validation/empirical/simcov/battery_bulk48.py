"""Battery 48: the transport product, and the rare-variant heritability share.

Rebuilt because `neutralPortabilityRatioLD` and `rareHeritabilityShare` both
cite `simcov/battery_bulk48.py` for tables of sems, and no such file was ever
committed.

group_ratio  neutralPortabilityRatioLD = (1 - fst_additional) * ld_factor. The
             target differs from the source in TWO independent ways -- a
             fraction of variants stop being shared, and the score's tagging is
             scaled -- and the observable is the realised ratio of predictive
             covariance. That the two penalties MULTIPLY is what the design
             establishes: the ADDITIVE reading rides along, and the two
             separate only when BOTH penalties bite, which is why they are
             swept independently rather than one at a time.

group_rare   rareHeritabilityShare, with the arguments read as the classes'
             TOTAL effect masses. THE ARGUMENTS MUST BE REALISED MASSES, NOT
             NOMINAL ONES, and that is not a detail: a finite draw of
             `rareCount` effects realises a sum of squares off by
             O(1/sqrt(rareCount)), which at these error bars is hundreds of
             sems, and it is what VOIDed an earlier attempt. The prediction here
             is evaluated at the realised sums of squares, and the nominal
             reading rides along so the size of that gap is visible rather than
             asserted.

             Counts and per-variant variances are swept in OPPOSITE directions
             -- (2000, 0.001) against (200, 0.01) -- which is the only regime
             where the counts are visible at all; at equal class sizes the body
             and the bare variance ratio coincide exactly.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK48-OSPREY-20260805"


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
# group ratio -- neutralPortabilityRatioLD
# ---------------------------------------------------------------------------
def group_ratio():
    print("\n===== GROUP RATIO  neutralPortabilityRatioLD "
          "= (1 - fst_add) * ld_factor")
    rng = np.random.default_rng(48001)
    m, n_ind, n_blocks = 2000, 40000, 10

    cells, c_add = [], []
    control = None
    for fst_add, ld in ((0.0, 1.0), (0.2, 1.0), (0.0, 0.6),
                        (0.3, 0.5), (0.1, 0.8)):
        ratios = []
        for _ in range(n_blocks):
            beta = rng.standard_normal(m) / math.sqrt(m)
            shared = rng.random(m) >= fst_add
            g_s = rng.standard_normal((n_ind, m))
            g_t = rng.standard_normal((n_ind, m))
            y_s = g_s @ beta + rng.standard_normal(n_ind)
            # In the target the unshared variants carry no signal, and the
            # score's tagging of the shared ones is scaled by `ld_factor`.
            y_t = g_t @ (beta * shared) + rng.standard_normal(n_ind)
            score_s = g_s @ beta
            score_t = (g_t @ beta) * ld
            cov_s = float(np.cov(score_s, y_s)[0, 1])
            cov_t = float(np.cov(score_t, y_t)[0, 1])
            ratios.append(cov_t / cov_s)
        got, sem = blocked(ratios)
        lean = (1 - fst_add) * ld
        add = (1 - fst_add) + ld - 1
        lab = "fst_add=%.1f ld=%.1f" % (fst_add, ld)
        print("  %-20s measured %.5f +/- %.5f   product %.5f   additive %.5f"
              % (lab, got, sem, lean, add))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_add.append(dict(design=lab, lean=add, truth=got,
                          sem=max(sem, 1e-12)))
        if fst_add == 0.0 and ld == 1.0:
            # POSITIVE CONTROL: with neither penalty applied the target IS the
            # source design, and the ratio must be 1. It can fail -- a scale
            # slip in the score, an asymmetry between the two populations --
            # and it is the cell where both readings agree, so it is not the
            # discrimination under test.
            control = dict(design="fst_add=0 ld=1 [no penalty: ratio is 1]",
                           lean=1.0, truth=got, sem=max(sem, 1e-12))

    reg = ("2000 variants and 400000 individuals per population (10 blocks of "
           "40000), standardised genotypes; the target differs from the source "
           "in TWO independent ways -- a fraction fst_additional of variants "
           "stop carrying signal, and the score's tagging is scaled by "
           "ld_factor -- and the observable is the realised ratio of "
           "score-phenotype covariance. The two penalties are swept "
           "INDEPENDENTLY, because the product and the sum separate only when "
           "both bite")
    record("neutralPortabilityRatioLD", "PhenomeWidePortability.lean",
           "(1 - fst_additional) * ld_factor", cells, regime=reg,
           control=control, realised_inputs=True, argument_source="model")
    record("neutralPortabilityRatioLD [penalties added, competing]",
           "PhenomeWidePortability.lean",
           "(1 - fst_additional) + ld_factor - 1", c_add, regime=reg,
           control=control, realised_inputs=True, argument_source="model")


# ---------------------------------------------------------------------------
# group rare -- rareHeritabilityShare
# ---------------------------------------------------------------------------
def group_rare():
    print("\n===== GROUP RARE  rareHeritabilityShare")
    rng = np.random.default_rng(48002)
    n_ind, n_blocks = 50000, 10

    cells, c_bare, c_nominal = [], [], []
    control = None
    for rc, rv, cc, cv in ((2000, 0.001, 200, 0.01),
                           (200, 0.01, 2000, 0.001),
                           (1000, 0.002, 1000, 0.002),
                           (500, 0.004, 1500, 0.001)):
        shares, leans, noms = [], [], []
        for _ in range(n_blocks):
            b_r = rng.standard_normal(rc) * math.sqrt(rv)
            b_c = rng.standard_normal(cc) * math.sqrt(cv)
            g_r = rng.standard_normal((n_ind, rc))
            g_c = rng.standard_normal((n_ind, cc))
            v_r = float(np.var(g_r @ b_r))
            v_c = float(np.var(g_c @ b_c))
            shares.append(v_r / (v_r + v_c))
            # THE PREDICTION AT THE REALISED MASSES: sum of squares actually
            # drawn, not count times per-variant parameter.
            m_r, m_c = float(b_r @ b_r), float(b_c @ b_c)
            leans.append(m_r / (m_r + m_c))
            noms.append((rc * rv) / (rc * rv + cc * cv))
        got, sem = blocked(shares)
        lean, _ = blocked(leans)
        nominal = noms[0]
        bare = rv / (rv + cv)
        lab = "rc=%d rv=%.3f cc=%d cv=%.3f" % (rc, rv, cc, cv)
        print("  %-34s measured %.5f +/- %.5f   realised-mass %.5f   "
              "nominal %.5f   bare-ratio %.5f"
              % (lab, got, sem, lean, nominal, bare))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_bare.append(dict(design=lab, lean=bare, truth=got,
                           sem=max(sem, 1e-12)))
        c_nominal.append(dict(design=lab, lean=nominal, truth=got,
                              sem=max(sem, 1e-12)))
        if control is None:
            # POSITIVE CONTROL: the total genetic variance must equal the total
            # realised effect mass, since the genotypes are standardised and
            # independent. Independently known, on the same draws, and nothing
            # to do with the SHARE.
            b_r = rng.standard_normal(rc) * math.sqrt(rv)
            g_r = rng.standard_normal((n_ind, rc))
            tot = [float(np.var(g_r @ b_r)) for _ in range(3)]
            cmean, csem = blocked(tot)
            control = dict(
                design="total genetic variance = realised sum of squares",
                lean=float(b_r @ b_r), truth=cmean, sem=max(csem, 1e-12))

    reg = ("500000 individuals per cell (10 blocks of 50000) with standardised "
           "independent genotypes in a rare and a common class; the observable "
           "is the realised share of genetic variance carried by the rare "
           "class. Counts and per-variant variances move in OPPOSITE "
           "directions across the design, which is the only regime where the "
           "counts are visible; at equal class sizes the body and the bare "
           "variance ratio coincide exactly. The prediction is evaluated at "
           "the REALISED sums of squares")
    record("rareHeritabilityShare", "RareVariantPortability.lean",
           "rareCount * rareVariance / (rareCount * rareVariance + "
           "commonCount * commonVariance), at the realised masses", cells,
           regime=reg, control=control, realised_inputs=True,
           argument_source="model")
    record("rareHeritabilityShare [bare variance ratio, counts dropped, "
           "competing]", "RareVariantPortability.lean",
           "rareVariance / (rareVariance + commonVariance)", c_bare,
           regime=reg, control=control, realised_inputs=True,
           argument_source="model")
    record("rareHeritabilityShare [nominal masses, competing]",
           "RareVariantPortability.lean",
           "the same body at NOMINAL count*variance", c_nominal, regime=reg,
           control=control, realised_inputs=False, argument_source="model")


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK48-OSPREY-20260805")
    group_ratio()
    group_rare()
    dump_results("battery_bulk48_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-64s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
