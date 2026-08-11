"""Why is battery_bulk7's heritabilityEnrichment row 17.4 sems off?

THE ROW. `heritabilityEnrichment = (h2_cat/M_cat) / (h2_total/M_total)`, held as
LEAD for want of a control. The design draws mc causal SNPs carrying h2c and mt
carrying h2rest, recovers per-SNP explained variance by regression in each
category separately, and forms the ratio.

THE CANDIDATE EXPLANATION, derived from the design rather than guessed. The
prediction is evaluated at the NOMINAL per-category heritabilities. The effects
are drawn as `N(0, sqrt(h2c/mc))`, so the REALISED effect mass `sum(beta^2)` has
relative standard deviation `sqrt(2/mc)` -- with mc = 100 that is FOURTEEN
PERCENT, on a single draw, against an asserted bar of `obs*sqrt(8/n)` = 0.63
percent. If that is the whole story the row is a nominal/realised gap and not a
statement about the body, and the repair is to feed the realised masses.

A SECOND, SMALLER DESIGN EFFECT is priced at the same time: `per_snp` reads the
IN-SAMPLE explained variance, which is inflated by `(m/n)(1 - R2)` and inflated
DIFFERENTLY in the two categories because they hold different numbers of SNPs, so
it biases the ratio even at realised inputs.

Four columns per cell: measured, the body at NOMINAL inputs (what the battery
scores), the body at REALISED masses, and the realised-input body with the
in-sample inflation applied. The bar is the block sem over REPS draws, since the
battery runs one draw and asserts its bar.
"""
import math

import numpy as np

DESIGNS = ((100, 900, 0.30, 0.30), (100, 900, 0.10, 0.50),
           (200, 800, 0.40, 0.20))
N, REPS = 200000, 6


def one_draw(mc, mt, h2c, h2rest, rng):
    Xa = rng.normal(0, 1, (N, mc))
    Xb = rng.normal(0, 1, (N, mt))
    ba = rng.normal(0, math.sqrt(h2c / mc), mc)
    bb = rng.normal(0, math.sqrt(h2rest / mt), mt)
    y = Xa @ ba + Xb @ bb + rng.normal(
        0, math.sqrt(max(1 - h2c - h2rest, 0.05)), N)
    vy = float(np.var(y))

    def per_snp(X):
        # The normal equations rather than lstsq's SVD. Same OLS solution -- the
        # design matrix is well conditioned here, being independent standard
        # normals with n far above m -- and roughly twenty times cheaper, which
        # is the difference between this probe finishing and not.
        Xc = X - X.mean(0)
        yc = y - y.mean()
        coef = np.linalg.solve(Xc.T @ Xc, Xc.T @ yc)
        return float(np.var(Xc @ coef) / vy / X.shape[1])

    pa, pb = per_snp(Xa), per_snp(Xb)
    total = (pa * mc + pb * mt) / (mc + mt)
    return (pa / total, float((ba ** 2).sum()), float((bb ** 2).sum()), vy)


def main():
    print("%-24s %10s %10s %10s %10s %10s"
          % ("cell", "measured", "nominal", "realised", "real+bias", "sem(reps)"))
    for mc, mt, h2c, h2rest in DESIGNS:
        rng = np.random.default_rng(16201)
        obs, nom, real, bias = [], [], [], []
        for _ in range(REPS):
            o, ha, hb, vy = one_draw(mc, mt, h2c, h2rest, rng)
            obs.append(o)
            nom.append((h2c / mc) / ((h2c + h2rest) / (mc + mt)))
            real.append((ha / mc) / ((ha + hb) / (mc + mt)))
            # in-sample inflation, per category, on the realised masses
            ia = (ha + (mc / N) * (vy - ha)) / mc
            ib = (hb + (mt / N) * (vy - hb)) / mt
            bias.append(ia / ((ia * mc + ib * mt) / (mc + mt)))
        m = float(np.mean(obs))
        sem = float(np.std(obs, ddof=1) / math.sqrt(REPS))
        print("%-24s %10.5f %10.5f %10.5f %10.5f %10.5f"
              % ("mc=%d h2c=%.2f h2r=%.2f" % (mc, h2c, h2rest), m,
                 float(np.mean(nom)), float(np.mean(real)),
                 float(np.mean(bias)), sem))
        print("%-24s %10s %10.2f %10.2f %10.2f"
              % ("", "sems off:", abs(m - np.mean(nom)) / sem,
                 abs(m - np.mean(real)) / sem, abs(m - np.mean(bias)) / sem))


if __name__ == "__main__":
    main()
