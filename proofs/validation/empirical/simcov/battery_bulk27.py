"""Battery 27: the diagonal-LD transfer R-squared family.

Under `standardizedDiagonalLD` the three bodies reduce to

  sourceSelfR2DiagonalLD b var_y        = (sum b^2)^2 / (sum b^2 * var_y)
  transportedTargetR2DiagonalLD bs bt   = (sum bs*bt)^2 / (sum bs^2 * var_y)
  targetOracleR2DiagonalLD bt var_y     = (sum bt^2)^2 / (sum bt^2 * var_y)

each an instance of `pgsR2 cov var_pgs var_y = cov^2 / (var_pgs * var_y)`.

The oracle simulates individuals -- standardized independent genotypes, effects
drawn per population at a set genetic correlation, phenotypes built -- and reads
the REALISED squared correlation between score and phenotype. No body is
evaluated to produce it.

COMPETITOR TEST, carried because a MATCH without one is worthless (an oracle
pinned to the body cannot reject anything). Two wrong forms ride on every cell:

  `cov / (var_pgs * var_y)`        -- the covariance unsquared
  `cov^2 / var_y`                  -- the score variance omitted

Both are dimensionally plausible and differ from the body by factors that move
across the design, so if the oracle were pinned they would match too.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def main():
    rng = np.random.default_rng(27001)
    n, m = 300000, 300
    cells_self, cells_trans, cells_oracle = [], [], []
    cells_nosq, cells_novar = [], []
    control = None
    for h2, rg in ((0.5, 0.9), (0.3, 0.6), (0.7, 0.4), (0.5, 1.0)):
        bs = rng.normal(0, math.sqrt(h2 / m), m)
        bt = rg * bs + math.sqrt(max(1 - rg ** 2, 0)) * rng.normal(
            0, math.sqrt(h2 / m), m)
        G = rng.normal(0, 1, (n, m))
        pgs_s = G @ bs
        g_t = G @ bt
        y = g_t + rng.normal(0, math.sqrt(max(1 - g_t.var(), 1e-6)), n)
        var_y = float(y.var(ddof=1))
        Sbs2 = float(np.sum(bs ** 2))
        Sbt2 = float(np.sum(bt ** 2))
        Sbsbt = float(np.dot(bs, bt))
        # realised R^2 of the SOURCE-weighted score against the target phenotype
        r2_trans = float(np.corrcoef(pgs_s, y)[0, 1] ** 2)
        # realised R^2 of the target's own true score against the phenotype
        r2_oracle = float(np.corrcoef(g_t, y)[0, 1] ** 2)
        sem_t = 2 * r2_trans * math.sqrt(max(1 - r2_trans, 1e-6) / n)
        sem_o = 2 * r2_oracle * math.sqrt(max(1 - r2_oracle, 1e-6) / n)
        lab = "h2=%.1f rg=%.1f" % (h2, rg)
        lean_trans = Sbsbt ** 2 / (Sbs2 * var_y)
        lean_oracle = Sbt2 ** 2 / (Sbt2 * var_y)
        print("  %-16s transported lean %.5f sim %.5f | oracle lean %.5f "
              "sim %.5f" % (lab, lean_trans, r2_trans, lean_oracle, r2_oracle))
        cells_trans.append(dict(design=lab, lean=lean_trans, truth=r2_trans,
                                sem=max(sem_t, 1e-9)))
        cells_oracle.append(dict(design=lab, lean=lean_oracle,
                                 truth=r2_oracle, sem=max(sem_o, 1e-9)))
        # sourceSelfR2 read in the SOURCE population: same shape, bs against its
        # own phenotype, so it is the rg = 1 corner of the same law
        y_s = pgs_s + rng.normal(0, math.sqrt(max(1 - pgs_s.var(), 1e-6)), n)
        var_ys = float(y_s.var(ddof=1))
        r2_self = float(np.corrcoef(pgs_s, y_s)[0, 1] ** 2)
        sem_s = 2 * r2_self * math.sqrt(max(1 - r2_self, 1e-6) / n)
        cells_self.append(dict(design=lab, lean=Sbs2 ** 2 / (Sbs2 * var_ys),
                               truth=r2_self, sem=max(sem_s, 1e-9)))
        # competitors on the transported cell
        cells_nosq.append(dict(design=lab, lean=Sbsbt / (Sbs2 * var_y),
                               truth=r2_trans, sem=max(sem_t, 1e-9)))
        cells_novar.append(dict(design=lab, lean=Sbsbt ** 2 / var_y,
                                truth=r2_trans, sem=max(sem_t, 1e-9)))
        if rg == 1.0:
            # control: at rg = 1 the transported score IS the oracle score, so
            # the two realised R^2 must coincide -- measured on both sides, not
            # asserted
            control = dict(design=lab + " [rg=1: transported = oracle]",
                           lean=r2_oracle, truth=r2_trans,
                           sem=max(sem_t, 1e-9))
    reg = ("300 independent standardized variants, 300000 individuals; effects "
           "drawn per population at genetic correlation rg. Every comparison "
           "target is a REALISED squared correlation between a simulated score "
           "and a simulated phenotype -- no body is evaluated to build it")
    record("sourceSelfR2DiagonalLD", "TransferLearningPGS.lean",
           "pgsR2 (sum b^2) (sum b^2) var_y", cells_self, regime=reg,
           control=control)
    record("transportedTargetR2DiagonalLD", "TransferLearningPGS.lean",
           "pgsR2 (sum bs*bt) (sum bs^2) var_y", cells_trans, regime=reg,
           control=control)
    record("targetOracleR2DiagonalLD", "TransferLearningPGS.lean",
           "pgsR2 (sum bt^2) (sum bt^2) var_y", cells_oracle, regime=reg,
           control=control)
    record("transportedTargetR2 [cov unsquared, competing]",
           "TransferLearningPGS.lean", "cov / (var_pgs * var_y)", cells_nosq,
           regime=reg, control=control)
    record("transportedTargetR2 [var_pgs omitted, competing]",
           "TransferLearningPGS.lean", "cov^2 / var_y", cells_novar,
           regime=reg, control=control)
    json.dump(RESULTS, open("battery_bulk27_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
