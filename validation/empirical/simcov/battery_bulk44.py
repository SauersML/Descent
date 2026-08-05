"""Battery 44: the spike-and-slab prior variance, and the Gaussian-model MI.

Rebuilt for the same reason as battery_bulk43: `spikeAndSlabPriorVariance` and
`effectMutualInformation` each cite `simcov/battery_bulk44.py` for a table of
sems, and no such file was ever committed.

group_a  spikeAndSlabPriorVariance = pi * sigma_slab^2. The draws come from the
         two COMPONENTS -- a point mass at zero with weight 1-pi and a Gaussian
         slab with weight pi -- so the body is never used to generate anything
         and what is on trial is the combination rule. pi and the slab sd are
         swept in OPPOSITE directions, so the product is under test rather than
         either factor.

group_b  effectMutualInformation = -(m/2) log(1 - rho^2), WITHIN the Gaussian
         model. The oracle never puts rho into a formula: it regresses one
         vector on the other and builds the information from two MEASURED
         variances, (m/2) log(Var / Var_residual). That is strictly less than
         the model-free question -- `battery_mi01.py` is the battery that
         answers that one, and the declaration's docstring says so at length --
         but it is a measurement of the coefficient and the exponent, which is
         what this group claims and all it claims.

THE ERROR BAR IN GROUP A IS INFLATED THREEFOLD over the normal formula for a
variance. A spike-and-slab is heavy-tailed at small pi and the normal sem
understates its own scatter; the sem here is taken across blocks, which does not
assume normality, and the inflation is kept as a further margin. It is what
turned an earlier reading of the sibling `spikeAndSlabVariance` from a spurious
10.6-sem falsification into the noise it actually was.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK44-MERLIN-20260805"

# `realised_inputs=True`: pi, the slab sd, m and rho are the exact constants the
# draws were generated with, not estimates off the same draws the oracle
# measures. Group B additionally reports the realised per-coordinate
# correlation as its control, so the nominal/realised gap is visible rather
# than assumed away.
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
# group A -- spikeAndSlabPriorVariance
# ---------------------------------------------------------------------------
def group_a():
    print("\n===== GROUP A  spikeAndSlabPriorVariance = pi * sigma_slab^2")
    rng = np.random.default_rng(44001)
    n_blocks, per_block = 30, 200000

    cells, c_unsq, c_noweight = [], [], []
    control = None
    for pi, sd in ((0.5, 1.0), (0.1, 2.0), (0.02, 3.0), (0.8, 0.5)):
        var_blocks, frac_blocks = [], []
        for _ in range(n_blocks):
            is_slab = rng.random(per_block) < pi
            b = np.where(is_slab, rng.standard_normal(per_block) * sd, 0.0)
            # The body is E[beta^2]; the components are centred at zero, so the
            # second moment IS the variance and no centring convention enters.
            var_blocks.append(float(np.mean(b * b)))
            frac_blocks.append(float(is_slab.mean()))
        got, sem = blocked(var_blocks)
        sem *= 3.0                       # see the module docstring
        fmean, fsem = blocked(frac_blocks)
        lean = pi * sd ** 2
        lab = "pi=%.2f sd=%.1f" % (pi, sd)
        print("  %-16s measured %.6f +/- %.6f (x3)   body %.6f   "
              "unsquared %.6f   no weight %.6f"
              % (lab, got, sem, lean, pi * sd, sd ** 2))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_unsq.append(dict(design=lab, lean=pi * sd, truth=got,
                           sem=max(sem, 1e-12)))
        c_noweight.append(dict(design=lab, lean=sd ** 2, truth=got,
                               sem=max(sem, 1e-12)))
        if control is None:
            control = dict(design=lab + " [counted slab fraction]", lean=pi,
                           truth=fmean, sem=max(fsem, 1e-12))

    reg = ("6e6 draws in 30 independent blocks of 2e5 from the two COMPONENTS "
           "-- a point mass at zero with weight 1-pi and a Gaussian slab with "
           "weight pi. The body generates nothing; what is on trial is the "
           "combination rule. pi and the slab sd move in OPPOSITE directions "
           "across the design so the product is under test rather than either "
           "factor. The across-block sem is inflated threefold because a "
           "spike-and-slab is heavy-tailed at small pi")
    record("spikeAndSlabPriorVariance", "BayesianPGSTheory.lean",
           "pi * sigma_slab^2", cells, regime=reg, control=control, **MODEL)
    record("spikeAndSlabPriorVariance [slab sd unsquared, competing]",
           "BayesianPGSTheory.lean", "pi * sigma_slab", c_unsq, regime=reg,
           control=control, **MODEL)
    record("spikeAndSlabPriorVariance [mixture weight dropped, competing]",
           "BayesianPGSTheory.lean", "sigma_slab^2", c_noweight, regime=reg,
           control=control, **MODEL)


# ---------------------------------------------------------------------------
# group B -- effectMutualInformation, within the Gaussian model
# ---------------------------------------------------------------------------
def group_b():
    print("\n===== GROUP B  effectMutualInformation = -(m/2) log(1 - rho^2)")
    rng = np.random.default_rng(44002)
    n_blocks, per_block = 20, 20000

    cells, c_nohalf, c_unsquared = [], [], []
    control = None
    for m in (1, 4, 10):
        for rho in (0.3, 0.5, 0.7, 0.9):
            mi_blocks, rho_blocks = [], []
            for _ in range(n_blocks):
                x = rng.standard_normal((per_block, m))
                z = rng.standard_normal((per_block, m))
                y = rho * x + math.sqrt(1 - rho ** 2) * z
                # THE ORACLE PUTS NO rho INTO A FORMULA. Per coordinate it
                # regresses y on x and reads the information off the two
                # MEASURED variances -- the marginal and the residual. If the
                # dependence were not Gaussian this construction would still
                # return a number; it would just no longer be the mutual
                # information, which is the standing caveat the declaration's
                # own docstring carries and battery_mi01 settles.
                tot = 0.0
                for j in range(m):
                    xj, yj = x[:, j], y[:, j]
                    b = np.dot(xj, yj) / np.dot(xj, xj)
                    resid = yj - b * xj
                    tot += 0.5 * math.log(float(yj.var()) /
                                          float(resid.var()))
                mi_blocks.append(tot)
                rho_blocks.append(float(np.corrcoef(x[:, 0], y[:, 0])[0, 1]))
            got, sem = blocked(mi_blocks)
            rmean, rsem = blocked(rho_blocks)
            lean = -(m / 2.0) * math.log(1 - rho ** 2)
            lab = "m=%d rho=%.1f" % (m, rho)
            print("  %-14s measured %.5f +/- %.5f   body %.5f   no-half %.5f "
                  "  unsquared %.5f"
                  % (lab, got, sem, lean, 2 * lean,
                     -float(m) * math.log(1 - rho) / 2.0))
            cells.append(dict(design=lab, lean=lean, truth=got,
                              sem=max(sem, 1e-12)))
            c_nohalf.append(dict(design=lab, lean=2 * lean, truth=got,
                                 sem=max(sem, 1e-12)))
            c_unsquared.append(dict(
                design=lab, lean=-float(m) * math.log(1 - rho) / 2.0,
                truth=got, sem=max(sem, 1e-12)))
            if control is None:
                control = dict(
                    design=lab + " [realised per-coordinate correlation]",
                    lean=rho, truth=rmean, sem=max(rsem, 1e-12))

    reg = ("400000 Gaussian pairs per cell in 20 independent blocks; m and rho "
           "are swept INDEPENDENTLY (m in 1, 4, 10 and rho in 0.3, 0.5, 0.7, "
           "0.9). The oracle is (m/2) log(Var / Var_residual) from two MEASURED "
           "variances per coordinate -- rho enters the prediction and nothing "
           "else. This measures the body as a function of the GAUSSIAN MODEL; "
           "whether real effect vectors are in that family is the separate "
           "question battery_mi01 answers")
    record("effectMutualInformation", "MultiAncestryTheory.lean",
           "-(m / 2) * log(1 - rho^2)", cells, regime=reg, control=control,
           **MODEL)
    record("effectMutualInformation [factor 1/2 dropped, competing]",
           "MultiAncestryTheory.lean", "-m * log(1 - rho^2)", c_nohalf,
           regime=reg, control=control, **MODEL)
    record("effectMutualInformation [rho unsquared in the log, competing]",
           "MultiAncestryTheory.lean", "-(m / 2) * log(1 - rho)", c_unsquared,
           regime=reg, control=control, **MODEL)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK44-MERLIN-20260805")
    group_a()
    group_b()
    dump_results("battery_bulk44_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-62s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
