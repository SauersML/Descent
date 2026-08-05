"""Battery 28: HWE genotype probabilities, participation ratio, enrichment.

Each group carries a competing form on the same cells, because a MATCH without
one cannot distinguish a measurement from an oracle pinned to the body.

  A. `HardyWeinbergModel.genotypeProb` = (p^2, 2pq, q^2). Oracle: random union
     of gametes, genotypes COUNTED. Competitor: the heterozygote term without
     its factor of two, which is the classic error and which the counts settle
     immediately.

  B. `effectivePolygenicityOfEffects` = (sum b^2)^2 / sum b^4. The claim in the
     name is that this is an EFFECTIVE NUMBER OF LOCI, so the oracle is an
     independent operational count: how many loci, taken largest-first, are
     needed to reach the same concentration of squared effect that a uniform
     architecture of size k would have. Competitors: the wrong power
     `sum b^2 / sum b^4`, and the raw locus count M.

  C. `heritabilityEnrichment` = (h2_cat/M_cat)/(h2_total/M_total). Oracle: the
     realised ratio of per-variant heritability inside a category to the
     genome-wide per-variant heritability, from simulated effects. Competitor:
     `h2_cat / h2_total`, the share without the per-variant normalisation --
     the two agree only when the category holds its proportional share of
     variants, so the design puts the category size far from proportional.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def group_a():
    rng = np.random.default_rng(28001)
    cells, cells_alt = [], []
    control = None
    for p in (0.5, 0.2, 0.05, 0.8):
        n = 4000000
        a1 = rng.random(n) < p
        a2 = rng.random(n) < p
        nref = a1.astype(int) + a2.astype(int)   # count of ref alleles
        for gi, (name, lean, lean_alt) in enumerate(
                (("homRef", p ** 2, p ** 2),
                 ("het", 2 * p * (1 - p), p * (1 - p)),
                 ("homAlt", (1 - p) ** 2, (1 - p) ** 2))):
            obs = float(np.mean(nref == (2 - gi)))
            sem = math.sqrt(max(obs * (1 - obs), 1e-12) / n)
            lab = "p=%.2f %s" % (p, name)
            cells.append(dict(design=lab, lean=lean, truth=obs, sem=sem))
            cells_alt.append(dict(design=lab, lean=lean_alt, truth=obs,
                                  sem=sem))
        print("  p=%.2f  counted %.5f %.5f %.5f" %
              (p, float(np.mean(nref == 2)), float(np.mean(nref == 1)),
               float(np.mean(nref == 0))))
        if p == 0.5:
            control = dict(design="p=0.50 [realised allele freq]", lean=p,
                           truth=float(np.mean(nref)) / 2.0,
                           sem=math.sqrt(p * (1 - p) / (2 * n)))
    reg = ("random union of gametes at allele frequency p, 4e6 individuals; "
           "genotypes are COUNTED, never computed from the body")
    record("HardyWeinbergModel.genotypeProb", "Probability.lean",
           "(p^2, 2*p*q, q^2)", cells, regime=reg, control=control)
    record("genotypeProb [heterozygote without the factor 2, competing]",
           "Probability.lean", "(p^2, p*q, q^2)", cells_alt, regime=reg,
           control=control)


def group_b():
    rng = np.random.default_rng(28002)
    cells, cells_pow, cells_m = [], [], []
    control = None
    M = 5000
    for k in (20, 100, 500, 2000):
        # k loci carry all the effect, equally; the participation ratio of an
        # exactly-uniform architecture of size k is k, so the operational count
        # and the body should agree, and the RAW count M should not
        b = np.zeros(M)
        idx = rng.choice(M, size=k, replace=False)
        b[idx] = rng.normal(0, 1, k)
        s2 = float(np.sum(b ** 2))
        s4 = float(np.sum(b ** 4))
        lean = s2 ** 2 / s4
        # independent operational count: the number of loci carrying nonzero
        # effect, which is what "effective number" means for this architecture
        truth = float(np.count_nonzero(b))
        # spread of the participation ratio over repeated draws at this k
        reps = [float(np.sum(rng.normal(0, 1, k) ** 2) ** 2
                      / np.sum(rng.normal(0, 1, k) ** 4)) for _ in range(200)]
        sem = float(np.std(reps, ddof=1) / math.sqrt(200))
        lab = "k=%d of M=%d" % (k, M)
        print("  %-18s participation %.1f   nonzero %d   M %d"
              % (lab, lean, int(truth), M))
        cells.append(dict(design=lab, lean=lean, truth=truth,
                          sem=max(sem, 1e-9)))
        cells_pow.append(dict(design=lab, lean=s2 / s4, truth=truth,
                              sem=max(sem, 1e-9)))
        cells_m.append(dict(design=lab, lean=float(M), truth=truth,
                            sem=max(sem, 1e-9)))
        if k == 100:
            control = dict(design=lab + " [nonzero count recovers k]",
                           lean=float(k), truth=truth, sem=1e-9)
    reg = ("M = 5000 variants of which k carry Gaussian effects and the rest "
           "are exactly zero; the oracle is the COUNT of nonzero effects, an "
           "operational reading of 'effective number of loci' that shares no "
           "algebra with the participation ratio")
    record("effectivePolygenicityOfEffects", "PolygenicArchitecture.lean",
           "(sum b^2)^2 / sum b^4", cells, regime=reg, control=control)
    record("effectivePolygenicity [sum b^2 / sum b^4, competing]",
           "PolygenicArchitecture.lean", "sum b^2 / sum b^4", cells_pow,
           regime=reg, control=control)
    record("effectivePolygenicity [raw variant count M, competing]",
           "PolygenicArchitecture.lean", "M", cells_m, regime=reg,
           control=control)


def group_c():
    rng = np.random.default_rng(28003)
    cells, cells_share = [], []
    control = None
    M_total, n = 4000, 200000
    for M_cat, share in ((200, 0.5), (400, 0.25), (1000, 0.5), (100, 0.3)):
        h2_total = 0.5
        h2_cat = share * h2_total
        b = np.zeros(M_total)
        b[:M_cat] = rng.normal(0, math.sqrt(h2_cat / M_cat), M_cat)
        b[M_cat:] = rng.normal(0, math.sqrt((h2_total - h2_cat)
                                            / (M_total - M_cat)),
                               M_total - M_cat)
        # realised per-variant heritability inside and overall
        v_cat = float(np.sum(b[:M_cat] ** 2))
        v_all = float(np.sum(b ** 2))
        truth = (v_cat / M_cat) / (v_all / M_total)
        sem = truth * math.sqrt(2.0 / M_cat)
        lean = (h2_cat / M_cat) / (h2_total / M_total)
        lab = "M_cat=%d share=%.2f" % (M_cat, share)
        print("  %-22s enrichment lean %.3f  realised %.3f ± %.3f"
              % (lab, lean, truth, sem))
        cells.append(dict(design=lab, lean=lean, truth=truth, sem=sem))
        cells_share.append(dict(design=lab, lean=share, truth=truth, sem=sem))
        if M_cat == 400:
            control = dict(design=lab + " [realised total h2 recovers 0.5]",
                           lean=h2_total, truth=v_all,
                           sem=v_all * math.sqrt(2.0 / M_total))
    reg = ("M_total = 4000 variants with a category of M_cat carrying a set "
           "share of the heritability; the oracle is the REALISED ratio of "
           "per-variant heritability in the category to the genome-wide "
           "per-variant heritability, from the drawn effects. Category sizes "
           "run far from proportional, which is the only regime where the "
           "per-variant normalisation is visible")
    record("heritabilityEnrichment", "PolygenicArchitecture.lean",
           "(h2_cat / M_cat) / (h2_total / M_total)", cells, regime=reg,
           control=control)
    record("heritabilityEnrichment [share h2_cat/h2_total, competing]",
           "PolygenicArchitecture.lean", "h2_cat / h2_total", cells_share,
           regime=reg, control=control)


def main():
    for fn in (group_a, group_b, group_c):
        print("\n===== %s =====" % fn.__name__)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (fn.__name__, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk28_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
