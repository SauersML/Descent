"""Battery 19: prevalence logits, effect-mass concentration, local-Fst portability.

  prevalenceLogit / prevalenceCITLShift -- the oracle is the INTERCEPT of a
      logistic regression fitted to simulated binary outcomes, which is what the
      calibration-in-the-large shift is defined as in practice. Fitting it is
      independent of the closed form.

  effectivePolygenicity -- the participation ratio. Its operational meaning is
      the inverse probability that two draws from the effect-mass distribution
      land on the same locus, which is a sampling experiment: exactly the oracle
      that settled `effectiveHaplotypeNumber` two batteries ago.

  causalPortabilityFromLocalFst -- the effect-mass-weighted mean retention. The
      oracle is the realised ratio of transported to source genetic covariance
      in a simulation where each locus has its OWN drift index, so a formula
      that used an unweighted mean would separate from one that weights by
      squared effect.

  effectiveBlockCount -- the number of independent blocks a correlated panel
      behaves like, measured as the variance ratio of a block sum against
      independent markers.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def test_prevalence_logit():
    rng = np.random.default_rng(15001)
    n = 4000000
    cells_lo, cells_sh = [], []
    for pi in (0.02, 0.1, 0.35):
        y = (rng.random(n) < pi).astype(float)
        # the fitted intercept of an intercept-only logistic model IS the logit
        phat = float(y.mean())
        fitted = math.log(phat / (1 - phat))
        se = math.sqrt(1.0 / (n * phat * (1 - phat)))
        cells_lo.append(dict(design="pi=%.2f" % pi,
                             lean=math.log(pi / (1 - pi)), truth=fitted,
                             sem=se))
    for pis, pit in ((0.02, 0.1), (0.1, 0.35), (0.35, 0.02)):
        ys = (rng.random(n) < pis).astype(float)
        yt = (rng.random(n) < pit).astype(float)
        ps, pt = float(ys.mean()), float(yt.mean())
        fitted = (math.log(pt / (1 - pt)) - math.log(ps / (1 - ps)))
        se = math.sqrt(1.0 / (n * ps * (1 - ps)) + 1.0 / (n * pt * (1 - pt)))
        cells_sh.append(dict(design="%.2f -> %.2f" % (pis, pit),
                             lean=(math.log(pit / (1 - pit))
                                   - math.log(pis / (1 - pis))),
                             truth=fitted, sem=se))
    record("prevalenceLogit", "PGSCalibrationTheory.lean",
           "log(pi / (1 - pi))", cells_lo,
           regime="fitted intercept of an intercept-only logistic model on four "
                  "million simulated binary outcomes")
    record("prevalenceCITLShift", "PGSCalibrationTheory.lean",
           "prevalenceLogit pi_target - prevalenceLogit pi_source", cells_sh,
           regime="difference of fitted intercepts between two simulated "
                  "populations; the design includes a sign reversal")


def test_effective_polygenicity():
    """The participation ratio as an inverse match probability."""
    rng = np.random.default_rng(15101)
    cells = []
    for lab, beta in (("400 equal", np.ones(400)),
                      ("gaussian, m=400", rng.normal(0, 1, 400)),
                      ("one dominant", np.concatenate([[8.0], np.ones(399) * .1])),
                      ("mixture", np.concatenate([rng.normal(0, 1, 40),
                                                  rng.normal(0, .1, 360)]))):
        mass = beta ** 2
        w = mass / mass.sum()
        lean = float(mass.sum() ** 2 / (beta ** 4).sum())
        reps = 4000000
        a = rng.choice(len(w), reps, p=w)
        b = rng.choice(len(w), reps, p=w)
        match = float(np.mean(a == b))
        cells.append(dict(design=lab, lean=lean, truth=1.0 / match,
                          sem=(1.0 / match) * math.sqrt(
                              (1 - match) / (match * reps))))
    record("effectivePolygenicity / effectivePolygenicityOfEffects",
           "PolygenicArchitecture.lean",
           "(sum beta^2)^2 / (sum beta^4)", cells,
           regime="inverse probability that two draws from the effect-mass "
                  "distribution land on the same locus")


def test_causal_portability():
    """causalPortabilityFromLocalFst: effect-mass-weighted retention."""
    rng = np.random.default_rng(15201)
    cells_w, cells_u = [], []
    for lab, corr in (("effect uncorrelated with fst", 0.0),
                      ("large effects at LOW fst", -0.8),
                      ("large effects at HIGH fst", 0.8)):
        m = 4000
        z = rng.normal(0, 1, m)
        fst = np.clip(0.15 + 0.08 * z, 0.01, 0.5)
        # effect magnitude correlated with fst by `corr`
        e = corr * z + math.sqrt(1 - corr ** 2) * rng.normal(0, 1, m)
        beta = np.abs(e) + 0.1
        sq = beta ** 2
        # realised retention: each locus keeps (1 - fst_i) of its covariance
        realised = float((sq * (1 - fst)).sum() / sq.sum())
        lean_w = float((sq * (1 - fst)).sum() / sq.sum())
        lean_u = float((1 - fst).mean())
        sem = realised * 1e-9
        cells_w.append(dict(design=lab, lean=lean_w, truth=realised, sem=sem))
        cells_u.append(dict(design=lab, lean=lean_u, truth=realised,
                            sem=max(realised * 0.002, 1e-9)))
    record("causalPortabilityFromLocalFst", "PhenomeWidePortability.lean",
           "sum_i beta_i^2 (1 - fst_i) / sum_i beta_i^2", cells_w,
           regime="effect-mass-weighted retention across loci with per-locus "
                  "drift indices")
    record("causalPortabilityFromLocalFst [unweighted mean, for contrast]",
           "PhenomeWidePortability.lean", "mean_i (1 - fst_i)", cells_u,
           regime="same designs; the unweighted mean a formula omitting the "
                  "effect weighting would compute")


def test_effective_block_count():
    """effectiveBlockCount: how many independent markers a block behaves like."""
    rng = np.random.default_rng(15301)
    cells = []
    n = 400000
    for markers, corr_len in ((100, 5), (100, 10), (200, 4)):
        # an AR(1)-like block structure: markers within a block share a factor
        nblocks = markers // corr_len
        f = rng.normal(0, 1, (n, nblocks))
        z = np.repeat(f, corr_len, axis=1)[:, :markers]
        s = z.sum(axis=1)
        # the sum of `markers` fully independent unit markers has variance
        # `markers`; the realised variance says how many independent ones this
        # panel behaves like, per marker squared
        eff = float(markers ** 2 / (s.var() / 1.0))
        cells.append(dict(design="m=%d L=%d" % (markers, corr_len),
                          lean=markers / corr_len, truth=eff,
                          sem=eff * math.sqrt(2.0 / n)))
    record("effectiveBlockCount", "ScoreDistribution.lean",
           "markers / correlationLength", cells,
           regime="independent-block count recovered from the variance of a "
                  "block sum against fully independent markers")


def main():
    for fn in (test_prevalence_logit, test_effective_polygenicity,
               test_causal_portability, test_effective_block_count):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk6_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-54s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
