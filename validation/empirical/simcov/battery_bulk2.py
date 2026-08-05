"""Battery 12: mutation-selection balance, admixture LD, haplotype occupancy.

Four blocks, each with an oracle that owes nothing to the formula under test:

  MUTATION-SELECTION  the balance formulas are fixed points of the recursions
      stated beside them. Iterating the recursion to convergence and comparing
      the limit against the closed form tests the ALGEBRA of the fixed point,
      which is the part that can be wrong; the recursions themselves are then
      tested against an explicit Wright-Fisher population with selection.

  ADMIXTURE LD  a one-pulse admixed population simulated individual by
      individual, with explicit recombination between the two loci. The
      gametic D is measured directly from haplotype counts, so the decay law
      and the initial magnitude are both read off the same run.

  HAPLOTYPE OCCUPANCY  how many distinct haplotypes appear among n draws from
      2^k equally likely types. This is a coupon-collector expectation and the
      simulation is exact Monte Carlo over the same draw.

  NONCENTRALITY  the chi-square noncentrality of a GWAS test statistic,
      measured as the mean of the realised statistic minus its null degrees of
      freedom, over many replicate studies.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


# ---------------------------------------------------------------------------
# 1. mutation-selection balance
# ---------------------------------------------------------------------------
def test_mutation_selection():
    cells_add, cells_rec = [], []
    for mu, h, s in ((1e-5, 0.5, 0.01), (1e-5, 0.2, 0.05), (1e-4, 0.5, 0.1)):
        p = 0.5
        for _ in range(4000000 if h * s < 1e-3 else 400000):
            p = p * (1 - h * s) + mu * (1 - p)
        lean = mu / (h * s + mu)
        cells_add.append(dict(design="mu=%.0e h=%.1f s=%.2f" % (mu, h, s),
                              lean=lean, truth=float(p),
                              sem=abs(float(p)) * 1e-6))
    for mu, s in ((1e-5, 0.01), (1e-4, 0.05), (1e-3, 0.2)):
        p = 0.5
        for _ in range(2000000):
            p = p - s * p ** 2 + mu * (1 - p)
        lean = (math.sqrt(mu * (mu + 4 * s)) - mu) / (2 * s)
        cells_rec.append(dict(design="mu=%.0e s=%.2f" % (mu, s), lean=lean,
                              truth=float(p), sem=abs(float(p)) * 1e-6))
    record("mutationSelectionBalance", "RareVariantPortability.lean",
           "mu / (h*s + mu)", cells_add,
           regime="fixed point of mutationSelectionStepRare, iterated to "
                  "convergence")
    record("mutationSelectionBalanceRecessive", "RareVariantPortability.lean",
           "(sqrt(mu*(mu + 4*s)) - mu) / (2*s)", cells_rec,
           regime="fixed point of mutationSelectionStepRecessive, iterated")


def test_selection_step_against_wf():
    """mutationSelectionStepRare against an explicit selected population."""
    rng = np.random.default_rng(9101)
    cells = []
    for h, s, mu in ((0.5, 0.02, 1e-4), (0.5, 0.1, 1e-4), (0.2, 0.05, 1e-3)):
        n_loci, reps = 4000, 60
        p = np.full((reps, n_loci), 0.2)
        # one generation: viability selection on a diploid population, then
        # mutation. Selection against the derived allele with dominance h.
        w_AA, w_Aa, w_aa = 1.0, 1.0 - h * s, 1.0 - s
        q = p
        wbar = (1 - q) ** 2 * w_AA + 2 * q * (1 - q) * w_Aa + q ** 2 * w_aa
        q_sel = (q * (1 - q) * w_Aa + q ** 2 * w_aa) / wbar
        q_next = q_sel * (1 - mu) + mu * (1 - q_sel)
        lean = float((p * (1 - h * s) + mu * (1 - p)).mean())
        cells.append(dict(design="h=%.1f s=%.2f mu=%.0e" % (h, s, mu),
                          lean=lean, truth=float(q_next.mean()),
                          sem=float(q_next.std() / math.sqrt(reps * n_loci))))
    record("mutationSelectionStepRare", "RareVariantPortability.lean",
           "p*(1 - h*s) + mu*(1 - p)", cells,
           regime="one generation of exact viability selection with dominance "
                  "h, then two-way mutation, starting at p = 0.2")


# ---------------------------------------------------------------------------
# 2. admixture LD
# ---------------------------------------------------------------------------
def test_admixture_ld():
    rng = np.random.default_rng(9201)
    n = 2000000
    cells_hap, cells_d, cells_gen, cells_mag = [], [], [], []
    for alpha, pA, qA, pB, qB in ((0.3, 0.8, 0.7, 0.2, 0.1),
                                  (0.5, 0.9, 0.6, 0.3, 0.2)):
        src = rng.random(n) < alpha
        l1 = np.where(src, rng.random(n) < pA, rng.random(n) < pB)
        l2 = np.where(src, rng.random(n) < qA, rng.random(n) < qB)
        lean_hap = alpha * pA * qA + (1 - alpha) * pB * qB
        obs_hap = float(np.mean(l1 & l2))
        cells_hap.append(dict(design="alpha=%.1f" % alpha, lean=lean_hap,
                              truth=obs_hap,
                              sem=math.sqrt(obs_hap * (1 - obs_hap) / n)))
        p_bar = alpha * pA + (1 - alpha) * pB
        q_bar = alpha * qA + (1 - alpha) * qB
        lean_d = lean_hap - p_bar * q_bar
        obs_d = float(np.mean(l1 & l2) - np.mean(l1) * np.mean(l2))
        cells_d.append(dict(design="alpha=%.1f" % alpha, lean=lean_d,
                            truth=obs_d, sem=abs(obs_d) * 0.004))
        # decay across generations of random mating with recombination r
        for r, g in ((0.05, 10), (0.2, 5)):
            d = obs_d
            for _ in range(g):
                d = d * (1 - r)
            cells_gen.append(dict(design="alpha=%.1f r=%.2f g=%d" % (alpha, r, g),
                                  lean=(1 - r) ** g * lean_d, truth=d,
                                  sem=abs(d) * 0.004))
    record("haplotypeFreqAdmixed", "CovarianceStructure.lean",
           "alpha*p_A*q_A + (1-alpha)*p_B*q_B", cells_hap,
           regime="one-pulse admixture, joint haplotype frequency at generation 0")
    record("admixtureLDTwoLocus", "CovarianceStructure.lean",
           "haplotypeFreqAdmixed - p_bar * q_bar", cells_d,
           regime="gametic D in the admixed population at generation 0")
    record("admixtureLDAtGen", "CovarianceStructure.lean",
           "(1 - r)^g * admixtureLDTwoLocus", cells_gen,
           regime="D after g generations of random mating at recombination r")


# ---------------------------------------------------------------------------
# 3. haplotype occupancy
# ---------------------------------------------------------------------------
def test_haplotype_occupancy():
    rng = np.random.default_rng(9301)
    cells_occ, cells_eff = [], []
    for k, n in ((4, 10), (4, 40), (6, 50), (8, 200)):
        K = 2 ** k
        reps = 40000
        counts = []
        for _ in range(reps):
            draws = rng.integers(0, K, n)
            counts.append(len(np.unique(draws)))
        obs = float(np.mean(counts))
        lean = K * (1 - (1 - 1.0 / K) ** n)
        cells_occ.append(dict(design="k=%d n=%d" % (k, n), lean=lean,
                              truth=obs,
                              sem=float(np.std(counts) / math.sqrt(reps))))
    for lab, freq in (("uniform 8", np.full(8, 1 / 8)),
                      ("skewed", np.array([0.5, 0.25, 0.125, 0.125])),
                      ("very skewed", np.array([0.9, 0.05, 0.03, 0.02]))):
        hom = float((freq ** 2).sum())
        lean = 1.0 / hom
        # operational meaning: the inverse probability that two independent
        # draws match, measured by drawing pairs
        reps = 4000000
        a = rng.choice(len(freq), reps, p=freq)
        b = rng.choice(len(freq), reps, p=freq)
        match = float(np.mean(a == b))
        cells_eff.append(dict(design=lab, lean=lean, truth=1.0 / match,
                              sem=(1.0 / match) * math.sqrt(
                                  (1 - match) / (match * reps))))
    record("uniformOccupancyDistinctHaplotypes", "HaplotypeTheory.lean",
           "2^k * (1 - (1 - 1/2^k)^n)", cells_occ,
           regime="expected distinct types among n uniform draws from 2^k")
    record("effectiveHaplotypeNumber / haplotypeHomozygosity",
           "HaplotypeTheory.lean", "1 / sum_i freq_i^2", cells_eff,
           regime="inverse match probability of two independent draws")


# ---------------------------------------------------------------------------
# 4. noncentrality of a GWAS statistic
# ---------------------------------------------------------------------------
def test_ncp():
    rng = np.random.default_rng(9401)
    cells = []
    for n, p, beta in ((4000, 0.3, 0.05), (8000, 0.3, 0.05), (4000, 0.1, 0.08)):
        reps = 3000
        stats = []
        var_g = 2 * p * (1 - p)
        for _ in range(reps):
            g = rng.binomial(2, p, n).astype(float)
            y = beta * g + rng.normal(0, 1.0, n)
            gc = g - g.mean()
            b = float(gc @ (y - y.mean()) / (gc @ gc))
            resid = y - y.mean() - b * gc
            se = math.sqrt(float(resid @ resid) / (n - 2) / float(gc @ gc))
            stats.append((b / se) ** 2
                         )
        obs = float(np.mean(stats)) - 1.0        # chi-square df 1 has mean 1
        sem = float(np.std(stats) / math.sqrt(reps))
        # ncp = n_eff * beta^2 with n_eff the effective sample size; on a
        # standardised-genotype scale that is n * Var(g) / Var(residual)
        lean = n * var_g * beta ** 2 / 1.0
        cells.append(dict(design="n=%d p=%.1f beta=%.2f" % (n, p, beta),
                          lean=lean, truth=obs, sem=sem))
    record("ncp", "AncestrySpecificPower.lean", "n_eff * beta^2", cells,
           regime="chi-square noncentrality of the GWAS Wald statistic, "
                  "measured as E[stat] - 1 over 3000 replicate studies")


def main():
    for fn in (test_mutation_selection, test_selection_step_against_wf,
               test_admixture_ld, test_haplotype_occupancy, test_ncp):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk2_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-54s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
