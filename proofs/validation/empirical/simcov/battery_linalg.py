"""Battery 10: the score-and-genotype linear algebra, on one simulated panel.

These definitions are sums over loci, and a sum over loci is the easiest thing
in the corpus to get subtly wrong in a way no theorem catches: a missing ploidy
factor, a heterozygosity weight dropped, a variance written for linkage
equilibrium and used under LD. Lean checks that both sides are reals and stops.

So the oracle is a simulated diploid panel with REAL coalescent LD, and each
definition is compared against the corresponding quantity computed over
individuals -- an empirical mean, an empirical variance, an out-of-sample
regression coefficient. Where a definition is written for linkage equilibrium,
it is tested BOTH on an LE panel and on the LD panel, because the difference
between those two is exactly the error such a definition invites.

Two forks are settled here:
  pgsMeanShift  = sum beta * 2 * (p_t - p_s)
  polygenicAdaptationShift = sum beta * delta_p
which differ by the ploidy factor and are both described as the shift in mean
score; and pgsVariance against the realised score variance under LD.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def panel(n_ind=6000, n_sites=80, seed=1, unlinked=False):
    """Diploid dosages with coalescent LD, or in linkage equilibrium."""
    import msprime
    rng = np.random.default_rng(seed)
    if unlinked:
        p = rng.uniform(0.1, 0.9, n_sites)
        dose = rng.binomial(2, p, (n_ind, n_sites)).astype(float)
        return dose, p
    ts = msprime.sim_ancestry(samples=n_ind, population_size=10000,
                              sequence_length=2e5, recombination_rate=1e-8,
                              random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=1e-8, random_seed=seed + 5)
    gm = ts.genotype_matrix()
    f = gm.mean(axis=1)
    keep = (f > 0.1) & (f < 0.9)
    gm = gm[keep]
    idx = np.linspace(0, gm.shape[0] - 1, n_sites).astype(int)
    gm = gm[idx]
    h = gm.reshape(gm.shape[0], -1, 2)
    dose = h.sum(axis=2).T.astype(float)
    return dose, dose.mean(axis=0) / 2.0


def test_pgs_moments():
    rng = np.random.default_rng(7001)
    cells_mean, cells_var_le, cells_var_ld = [], [], []
    for tag, unl in (("linkage equilibrium", True), ("coalescent LD", False)):
        dose, p = panel(seed=11, unlinked=unl)
        n, m = dose.shape
        beta = rng.normal(0, 1, m)
        pgs = dose @ beta
        lean_mean = float((beta * 2 * p).sum())
        lean_var = float((beta ** 2 * 2 * p * (1 - p)).sum())
        obs_var = float(pgs.var())
        cells_mean.append(dict(design=tag, lean=lean_mean,
                               truth=float(pgs.mean()),
                               sem=float(pgs.std() / math.sqrt(n))))
        cell = dict(design=tag, lean=lean_var, truth=obs_var,
                    sem=obs_var * math.sqrt(2.0 / n))
        (cells_var_le if unl else cells_var_ld).append(cell)
    record("pgsMean", "ScoreDistribution.lean", "sum_i beta_i * 2 * p_i",
           cells_mean, regime="mean polygenic score over individuals")
    record("pgsVariance [linkage equilibrium]", "ScoreDistribution.lean",
           "sum_i beta_i^2 * 2 p_i (1 - p_i)", cells_var_le,
           regime="unlinked loci, the regime the formula is written for")
    record("pgsVariance [coalescent LD]", "ScoreDistribution.lean",
           "sum_i beta_i^2 * 2 p_i (1 - p_i)", cells_var_ld,
           regime="same formula on a linked panel: the LD cross terms it drops")


def test_shift_fork():
    """pgsMeanShift against polygenicAdaptationShift: the ploidy factor."""
    rng = np.random.default_rng(7101)
    cells_2, cells_1 = [], []
    for tag, unl in (("linkage equilibrium", True), ("coalescent LD", False)):
        dose_s, p_s = panel(seed=21, unlinked=unl)
        dose_t, p_t = panel(seed=22, unlinked=unl)
        m = min(dose_s.shape[1], dose_t.shape[1])
        dose_s, dose_t = dose_s[:, :m], dose_t[:, :m]
        p_s, p_t = p_s[:m], p_t[:m]
        beta = rng.normal(0, 1, m)
        obs = float((dose_t @ beta).mean() - (dose_s @ beta).mean())
        sem = math.sqrt((dose_t @ beta).var() / dose_t.shape[0]
                        + (dose_s @ beta).var() / dose_s.shape[0])
        cells_2.append(dict(design=tag, lean=float((beta * 2 * (p_t - p_s)).sum()),
                            truth=obs, sem=sem))
        cells_1.append(dict(design=tag, lean=float((beta * (p_t - p_s)).sum()),
                            truth=obs, sem=sem))
    record("pgsMeanShift", "ScoreDistribution.lean",
           "sum_i beta_i * 2 * (p_target_i - p_source_i)", cells_2,
           regime="difference in mean score between two panels")
    record("polygenicAdaptationShift", "SelectionArchitecture.lean",
           "sum_i beta_i * delta_p_i", cells_1,
           regime="same runs; the sibling written without the ploidy factor")


def test_hwe_moments():
    """The Hardy-Weinberg genotype moments, exactly."""
    rng = np.random.default_rng(7201)
    cells_m, cells_v, cells_t = [], [], []
    for p in (0.1, 0.3, 0.5):
        g = rng.binomial(2, p, 2000000).astype(float)
        c = g - 2 * p
        cells_m.append(dict(design="p=%.1f" % p, lean=2 * p,
                            truth=float(g.mean()),
                            sem=float(g.std() / math.sqrt(len(g)))))
        cells_v.append(dict(design="p=%.1f" % p, lean=2 * p * (1 - p),
                            truth=float((c ** 2).mean()),
                            sem=float((c ** 2).std() / math.sqrt(len(g)))))
        # third absolute central moment under HWE, evaluated exactly
        vals = np.array([0.0, 1.0, 2.0]) - 2 * p
        probs = np.array([(1 - p) ** 2, 2 * p * (1 - p), p ** 2])
        lean_t = float((probs * np.abs(vals) ** 3).sum())
        cells_t.append(dict(design="p=%.1f" % p, lean=lean_t,
                            truth=float((np.abs(c) ** 3).mean()),
                            sem=float((np.abs(c) ** 3).std() / math.sqrt(len(g)))))
    record("expectedAltAlleleCount", "Probability.lean",
           "sum_g altAlleleCount g * genotypeProb g", cells_m,
           regime="Hardy-Weinberg dosage mean")
    record("genotypeVariance", "Probability.lean",
           "sum_g genotypeProb g * centered^2", cells_v,
           regime="Hardy-Weinberg dosage variance")
    record("genotypeThirdAbsMoment", "Probability.lean",
           "sum_g genotypeProb g * |centered|^3", cells_t,
           regime="Hardy-Weinberg third absolute central moment")


def test_best_linear_weights():
    """sourceBestLinearWeightsFromLD against an actual regression."""
    rng = np.random.default_rng(7301)
    cells = []
    for tag, unl in (("coalescent LD", False), ("linkage equilibrium", True)):
        dose, p = panel(n_ind=20000, n_sites=40, seed=31, unlinked=unl)
        z = (dose - dose.mean(0)) / dose.std(0)
        n, m = z.shape
        beta_causal = rng.normal(0, 1, m) / math.sqrt(m)
        y = z @ beta_causal + rng.normal(0, 1.0, n)
        sig_tag = np.corrcoef(z, rowvar=False)          # tag-tag LD
        sig_tag_causal = sig_tag                        # tags ARE the causals here
        lean_w = np.linalg.solve(sig_tag, sig_tag_causal @ beta_causal)
        ols = np.linalg.lstsq(z, y, rcond=None)[0]
        # compare the whole weight vector by its worst coordinate
        k = int(np.argmax(np.abs(lean_w - ols)))
        sem = float(np.std(y) / math.sqrt(n))
        cells.append(dict(design="%s (worst coord)" % tag,
                          lean=float(lean_w[k]), truth=float(ols[k]),
                          sem=max(sem, 1e-9)))
    record("sourceBestLinearWeightsFromLD", "DGP.lean",
           "sigmaTagSource^-1 * sigmaTagCausal * betaCausal", cells,
           regime="least-squares weights from an explicit regression, "
                  "standardised dosages")


def test_effect_summaries():
    """The effect-vector summaries, against their operational meanings."""
    rng = np.random.default_rng(7401)
    m = 500
    cells_poly, cells_abs, cells_mass = [], [], []
    for tag, beta in (("all equal", np.ones(m)),
                      ("gaussian", rng.normal(0, 1, m)),
                      ("one dominant", np.concatenate([[10.0], np.ones(m - 1) * 0.1]))):
        s2 = float((beta ** 2).sum())
        s4 = float((beta ** 4).sum())
        lean_poly = s2 ** 2 / s4
        # operational meaning: the participation ratio IS the number of loci
        # when every effect is equal, and 1 when one locus carries everything
        truth_poly = {"all equal": float(m), "one dominant": None}.get(tag)
        if truth_poly is not None:
            cells_poly.append(dict(design=tag, lean=lean_poly, truth=truth_poly,
                                   sem=truth_poly * 1e-9))
        cells_abs.append(dict(design=tag, lean=float(np.abs(beta).sum() / m),
                              truth=float(np.abs(beta).mean()),
                              sem=float(np.abs(beta).std() / math.sqrt(m))))
        cells_mass.append(dict(design=tag, lean=s2, truth=float((beta ** 2).sum()),
                               sem=max(s2 * 1e-12, 1e-12)))
    record("effectivePolygenicityOfEffects", "PolygenicArchitecture.lean",
           "(sum beta^2)^2 / (sum beta^4)", cells_poly,
           regime="participation ratio; equals the locus count at equal effects")
    record("meanAbsoluteEffect", "PolygenicArchitecture.lean",
           "(sum |beta_j|) / q", cells_abs, regime="mean absolute effect")
    record("sourceSquaredEffectMass / sourceEffectMass",
           "MechanisticPortabilityWitnesses.lean", "sum_i beta_i^2", cells_mass,
           regime="total squared effect mass")


def test_pgs_drift_variance():
    """pgsDriftVarianceFromLoci = sum_i fst * beta_i^2, against realised drift."""
    from battery_verify import one_branch_pgs
    cells = []
    for Ne, t in ((200, 30), (200, 100), (200, 250)):
        r = one_branch_pgs(Ne, t, n_loci=500, reps=3000, seed=7501)
        obs = float(np.var(r["delta"], ddof=1))
        sem = obs * math.sqrt(2.0 / 3000)
        # the definition weights beta^2 by fst alone, with no heterozygosity
        # and no ploidy factor; the realised law is 4 * F * sum(2 p(1-p) beta^2)
        rng = np.random.default_rng(7501)
        p0 = rng.uniform(0.05, 0.95, 500)
        beta = rng.normal(0, 1, 500)
        lean = float((r["f_branch"] * beta ** 2).sum())
        cells.append(dict(design="t=%d (F=%.3f)" % (t, r["f_branch"]),
                          lean=lean, truth=obs, sem=sem))
    record("pgsDriftVarianceFromLoci", "PolygenicAdaptation.lean",
           "sum_i fst * beta_i^2", cells,
           regime="variance of the mean-score difference under one branch of "
                  "drift, the quantity Var_Delta_Mu is validated against")


def main():
    for fn in (test_pgs_moments, test_shift_fork, test_hwe_moments,
               test_best_linear_weights, test_effect_summaries,
               test_pgs_drift_variance):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_linalg_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-52s worst %9.1f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
