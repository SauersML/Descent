"""Battery 30: admixture LD between unlinked loci, with the exponents on trial.

`admixtureLD = alpha*(1-alpha)*dp1*dp2` is the disequilibrium a single admixture
pulse creates between two UNLINKED loci purely from ancestry mixing. Nothing in
the simulation implements this recursion: individuals are assigned an ancestry,
their alleles are drawn independently at each locus from that ancestry's
frequencies, and D is then MEASURED as E[l1*l2] - E[l1]E[l2] over the sample.
The formula is a derived consequence of that construction, not the construction
itself -- contrast battery 20c's decay design, where the recombination step WAS
the body's recursion.

Competitors on the same cells, so no exponent is taken on the name's authority:

  alpha*(1-alpha)*dp1          -- one frequency contrast dropped
  alpha*dp1*dp2                -- the (1-alpha) factor dropped, i.e. reading the
                                  mixing weight as linear rather than as a
                                  variance
  (alpha*(1-alpha))^2*dp1*dp2  -- the mixing weight squared

`alpha` is swept across and past 1/2 so `alpha*(1-alpha)` and `alpha` separate,
and the frequency contrasts are given opposite signs in one cell so a body that
lost a sign would show it.

`admixedAlleleFreq = alpha*p_A + (1-alpha)*p_B` rides along on the same draws,
measured as the realised allele frequency in the admixed sample.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def main():
    rng = np.random.default_rng(30001)
    n = 6000000
    cells, c_drop, c_lin, c_sq, cells_freq = [], [], [], [], []
    control = None
    designs = ((0.5, 0.8, 0.2, 0.75, 0.15),
               (0.2, 0.8, 0.2, 0.75, 0.15),
               (0.8, 0.9, 0.1, 0.30, 0.70),   # opposite-sign contrasts
               (0.35, 0.6, 0.4, 0.85, 0.25))
    for alpha, pA1, pB1, pA2, pB2 in designs:
        src = rng.random(n) < alpha                 # ancestry assignment
        l1 = np.where(src, rng.random(n) < pA1, rng.random(n) < pB1)
        l2 = np.where(src, rng.random(n) < pA2, rng.random(n) < pB2)
        l1 = l1.astype(float)
        l2 = l2.astype(float)
        D = float(np.mean(l1 * l2) - np.mean(l1) * np.mean(l2))
        sem = float(np.std(l1 * l2 - np.mean(l1) * l2, ddof=1) / math.sqrt(n))
        d1, d2 = pA1 - pB1, pA2 - pB2
        lean = alpha * (1 - alpha) * d1 * d2
        lab = "alpha=%.2f dp1=%+.2f dp2=%+.2f" % (alpha, d1, d2)
        print("  %-30s D = %+.6f ± %.6f   lean %+.6f" % (lab, D, sem, lean))
        cells.append(dict(design=lab, lean=lean, truth=D, sem=max(sem, 1e-12)))
        c_drop.append(dict(design=lab, lean=alpha * (1 - alpha) * d1, truth=D,
                           sem=max(sem, 1e-12)))
        c_lin.append(dict(design=lab, lean=alpha * d1 * d2, truth=D,
                          sem=max(sem, 1e-12)))
        c_sq.append(dict(design=lab, lean=(alpha * (1 - alpha)) ** 2 * d1 * d2,
                         truth=D, sem=max(sem, 1e-12)))
        # admixedAlleleFreq on the same draws
        f_obs = float(np.mean(l1))
        f_lean = alpha * pA1 + (1 - alpha) * pB1
        cells_freq.append(dict(design=lab, lean=f_lean, truth=f_obs,
                               sem=math.sqrt(f_obs * (1 - f_obs) / n)))
        if alpha == 0.5:
            # control: with IDENTICAL ancestral frequencies at locus 2 there is
            # no ancestry contrast there and D must vanish, whatever alpha is.
            l2n = (rng.random(n) < pA2).astype(float)
            Dn = float(np.mean(l1 * l2n) - np.mean(l1) * np.mean(l2n))
            control = dict(design="alpha=0.50 [no contrast at locus 2: D = 0]",
                           lean=0.0, truth=Dn,
                           sem=float(np.std(l1 * l2n - np.mean(l1) * l2n,
                                            ddof=1) / math.sqrt(n)))
    reg = ("one-pulse admixture, generation 0, two UNLINKED loci; ancestry is "
           "assigned per individual and alleles drawn independently from that "
           "ancestry's frequencies, then D is measured as "
           "E[l1*l2] - E[l1]*E[l2] over 6e6 individuals. alpha is swept across "
           "1/2 and one cell carries opposite-sign frequency contrasts")
    record("admixtureLD", "LDDecayTheory.lean", "alpha*(1-alpha)*dp1*dp2",
           cells, regime=reg, control=control)
    record("admixtureLD [one contrast dropped, competing]", "LDDecayTheory.lean",
           "alpha*(1-alpha)*dp1", c_drop, regime=reg, control=control)
    record("admixtureLD [mixing weight linear, competing]", "LDDecayTheory.lean",
           "alpha*dp1*dp2", c_lin, regime=reg, control=control)
    record("admixtureLD [mixing weight squared, competing]",
           "LDDecayTheory.lean", "(alpha*(1-alpha))^2*dp1*dp2", c_sq,
           regime=reg, control=control)
    record("admixedAlleleFreq", "DemographicHistory.lean",
           "alpha*p_A + (1-alpha)*p_B", cells_freq, regime=reg,
           control=control)
    json.dump(RESULTS, open("battery_bulk30_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
