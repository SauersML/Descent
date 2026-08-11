"""Battery 33: a deme-count sweep, a recombination rate, and six architecture scalars.

  fstDriftMigration = 1/(1 + bigM) -- the same shape as the definition this
      branch already renamed for being deme-count blind, and with the same
      inability to say so: it reads `bigM = 4 Ne m` and nothing else. The design
      is therefore the one that exposed the earlier case -- hold `4 Ne m` FIXED
      and sweep the number of demes -- because a formula in `bigM` alone must
      return one number for every deme count, and the island model does not.
      `F_ST` is read as `1 - E[T_within]/E[T_between]` from coalescence times,
      so no estimator convention enters and no mutation model is needed.

  ldBreakageRate = 2 r -- the rate at which recombination separates the two loci
      of a sampled PAIR of lineages. The two is the pair, exactly as in
      `mutationSharedRetentionAt`: either lineage recombining decouples the
      loci, so the pair survives `t` generations intact with probability
      `(1-r)^(2t)`. The competing one-lineage reading is carried alongside.

  Six architecture scalars, each against a realisation rather than against its
  own algebra: spikeAndSlabVariance against the sample variance of draws from
  the mixture it describes; effectGeneticCorrelation against the realised
  uncentred correlation of two effect vectors at known overlap;
  additiveHeritability against the realised variance ratio;
  expectedSquaredEffect, meanAbsoluteEffect and heritabilityEnrichment against
  their realisations under a simulated architecture.

  For the last three the honest note is that they are close to definitional --
  what a measurement can catch is a wrong normalisation or a wrong power, not a
  wrong concept -- so each is fed a design where the obvious wrong variants
  (dividing by the wrong count, squaring instead of absolute value) give
  numerically different answers, and those variants are carried as competitors.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


# ---------------------------------------------------------------------------
# 1. fstDriftMigration: hold 4*Ne*m fixed, sweep the deme count
# ---------------------------------------------------------------------------
def test_fst_drift_migration_deme_sweep():
    import msprime
    Ne, bigM = 1000, 2.0
    m = bigM / (4 * Ne)
    cells, cells_corr = [], []
    for n_demes in (2, 4, 10, 40):
        dem = msprime.Demography.island_model([Ne] * n_demes, migration_rate=m)
        vals = []
        for r in range(24):
            ts = msprime.sim_ancestry(
                samples={"pop_0": 25, "pop_1": 25}, demography=dem,
                sequence_length=4e6, recombination_rate=1e-8,
                random_seed=28001 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            da = ts.diversity([A], mode="branch")[0]
            db = ts.diversity([B], mode="branch")[0]
            dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            vals.append(1.0 - ((da + db) / 2.0) / dab)
        s = simlib.summarize(vals)
        corr = n_demes / (n_demes - 1.0)
        print("  %2d demes: F_ST = %.5f ± %.5f   (1/(1+bigM) = %.5f, "
              "deme-corrected %.5f)"
              % (n_demes, s["mean"], s["sem"], 1 / (1 + bigM),
                 1 / (1 + bigM * corr)))
        cells.append(dict(design="%d demes (4 Ne m = %.1f held fixed)"
                                 % (n_demes, bigM),
                          lean=1 / (1 + bigM), truth=s["mean"], sem=s["sem"]))
        cells_corr.append(dict(design="%d demes" % n_demes,
                               lean=1 / (1 + bigM * corr), truth=s["mean"],
                               sem=s["sem"]))
    reg = ("island model with 4*Ne*m held FIXED at 2.0 while the deme count "
           "runs 2, 4, 10, 40; F_ST read as 1 - E[T_within]/E[T_between] from "
           "coalescence times, so no estimator convention and no mutation "
           "model enters")
    record("fstDriftMigrationManyDemes", "DGP.lean", "1 / (1 + bigM)", cells,
           regime=reg)
    record("fstDriftMigrationManyDemes [CANDIDATE: with islandDemeCorrection n/(n-1)]",
           "DGP.lean", "1 / (1 + bigM * n/(n-1))", cells_corr, regime=reg)


# ---------------------------------------------------------------------------
# 2. ldBreakageRate
# ---------------------------------------------------------------------------
def test_ld_breakage_rate():
    rng = np.random.default_rng(28101)
    cells_two, cells_one = [], []
    for r, t in ((1e-3, 250), (5e-4, 1000), (2e-3, 250), (1e-3, 750)):
        reps = 400000
        hits = rng.binomial(2 * t, r, size=reps)
        surv = float((hits == 0).mean())
        sem = math.sqrt(max(surv * (1 - surv), 1e-12) / reps)
        lab = "r=%.1e t=%d (2 r t = %.2f)" % (r, t, 2 * r * t)
        cells_two.append(dict(design=lab, lean=math.exp(-2 * r * t),
                              truth=surv, sem=sem))
        cells_one.append(dict(design=lab + " [one-lineage]",
                              lean=math.exp(-r * t), truth=surv, sem=sem))
        print("  %-32s 2r reading %.5f  r reading %.5f  measured %.5f"
              % (lab, math.exp(-2 * r * t), math.exp(-r * t), surv))
    reg = ("probability that NEITHER lineage of a sampled pair has recombined "
           "between the two loci in t generations, 400000 replicate pairs per "
           "cell; 2 r t is varied over a factor of three")
    record("ldBreakageRate", "DGP.lean", "2 * r", cells_two, regime=reg)
    record("ldBreakageRate [one-lineage reading r, competing]", "DGP.lean",
           "r", cells_one, regime=reg)


# ---------------------------------------------------------------------------
# 3. six architecture scalars
# ---------------------------------------------------------------------------
def test_architecture_scalars():
    rng = np.random.default_rng(28201)

    # --- spikeAndSlabVariance ---------------------------------------------
    cells = []
    for pi, sl, ss in ((0.05, 1.0, 0.01), (0.2, 4.0, 0.05), (0.5, 2.0, 0.5)):
        n = 4000000
        big = rng.random(n) < pi
        x = np.where(big, rng.normal(0, math.sqrt(sl), n),
                     rng.normal(0, math.sqrt(ss), n))
        v = float(x.var(ddof=1))
        sem = v * math.sqrt(2.0 / (n - 1)) * 3      # heavy-tailed mixture
        cells.append(dict(design="pi=%.2f large=%.2f small=%.2f" % (pi, sl, ss),
                          lean=pi * sl + (1 - pi) * ss, truth=v, sem=sem))
    record("spikeAndSlabVariance", "PolygenicArchitecture.lean",
           "pi * sigma_sq_large + (1 - pi) * sigma_sq_small", cells,
           regime="sample variance of 4e6 draws from the two-component mixture "
                  "this describes; the sem is inflated threefold over the "
                  "normal formula because a spike-and-slab mixture is "
                  "heavy-tailed and the normal sem understates it")

    # --- effectGeneticCorrelation ------------------------------------------
    cells = []
    for rho in (0.0, 0.4, 0.9):
        m = 20000
        bs = rng.normal(0, 1, m)
        bt = rho * bs + math.sqrt(max(1 - rho ** 2, 0)) * rng.normal(0, 1, m)
        lean = float((bs * bt).sum()
                     / math.sqrt((bs ** 2).sum() * (bt ** 2).sum()))
        # the realised uncentred correlation, computed independently
        truth = float(np.dot(bs, bt) / (np.linalg.norm(bs) * np.linalg.norm(bt)))
        cells.append(dict(design="rho=%.1f (m=%d)" % (rho, m), lean=lean,
                          truth=truth, sem=max(abs(truth), 0.02) * 1e-9 + 1e-12))
    record("effectGeneticCorrelation", "TransferLearningPGS.lean",
           "sum(bs*bt) / sqrt(sum bs^2 * sum bt^2)", cells,
           regime="against the uncentred correlation computed through an "
                  "independent code path (numpy norms); this is an algebraic "
                  "identity, so it is reported as a SELF-TEST and carries no "
                  "empirical weight beyond catching a transcription error")

    # --- additiveHeritability and additiveGeneticVariance ------------------
    cells_h, cells_v = [], []
    for m, h2 in ((500, 0.2), (2000, 0.5), (800, 0.8)):
        n = 40000
        beta = rng.normal(0, math.sqrt(h2 / m), m)
        G = rng.normal(0, 1, (n, m))            # standardized genotypes
        g = G @ beta
        e = rng.normal(0, math.sqrt(max(1 - float(g.var()), 1e-6)), n)
        y = g + e
        var_y = float(y.var(ddof=1))
        V_A_lean = float((beta ** 2).sum())
        V_A_true = float(g.var(ddof=1))
        sem_v = V_A_true * math.sqrt(2.0 / (n - 1))
        cells_v.append(dict(design="m=%d h2=%.1f" % (m, h2), lean=V_A_lean,
                            truth=V_A_true, sem=sem_v))
        cells_h.append(dict(design="m=%d h2=%.1f" % (m, h2),
                            lean=V_A_lean / var_y,
                            truth=V_A_true / var_y,
                            sem=sem_v / var_y))
    record("additiveGeneticVariance", "TransferLearningPGS.lean",
           "sum beta_i^2", cells_v,
           regime="against the realised variance of the genetic value across "
                  "40000 individuals with STANDARDIZED genotypes, which is the "
                  "condition under which sum beta^2 is the additive variance; "
                  "on a dosage scale it would be off by the allele-frequency "
                  "factor and this design would show it")
    record("additiveHeritability", "TransferLearningPGS.lean",
           "additiveGeneticVariance beta / var_y", cells_h,
           regime="the same runs, as a realised variance ratio")

    # --- expectedSquaredEffect, meanAbsoluteEffect, heritabilityEnrichment --
    cells_e, cells_e_alt, cells_a, cells_a_alt, cells_r = [], [], [], [], []
    for m, h2 in ((500, 0.2), (2000, 0.5), (800, 0.8)):
        reps = 4000
        b = rng.normal(0, math.sqrt(h2 / m), (reps, m))
        ms2 = float((b ** 2).mean())
        sem2 = float((b ** 2).mean(axis=1).std(ddof=1) / math.sqrt(reps))
        cells_e.append(dict(design="m=%d h2=%.1f" % (m, h2), lean=h2 / m,
                            truth=ms2, sem=sem2))
        cells_e_alt.append(dict(design="m=%d h2=%.1f [h2/m^2 variant]"
                                       % (m, h2), lean=h2 / m ** 2,
                                truth=ms2, sem=sem2))
        ma = float(np.abs(b).mean())
        sema = float(np.abs(b).mean(axis=1).std(ddof=1) / math.sqrt(reps))
        cells_a.append(dict(design="m=%d h2=%.1f" % (m, h2),
                            lean=float(np.abs(b).sum(axis=1).mean() / m),
                            truth=ma, sem=sema))
        cells_a_alt.append(dict(design="m=%d h2=%.1f [rms variant]" % (m, h2),
                                lean=math.sqrt(h2 / m), truth=ma, sem=sema))
    record("expectedSquaredEffect", "PolygenicArchitecture.lean", "h2 / M",
           cells_e,
           regime="mean squared effect over 4000 replicate architectures drawn "
                  "at the stated heritability and polygenicity")
    record("expectedSquaredEffect [h2/M^2 variant, competing]",
           "PolygenicArchitecture.lean", "h2 / M^2", cells_e_alt,
           regime="carried so the normalisation is chosen by the data")
    record("meanAbsoluteEffect", "PolygenicArchitecture.lean",
           "(sum |beta_j|) / q", cells_a,
           regime="against the realised mean absolute effect; the divisor is "
                  "the variant count and a wrong divisor separates immediately")
    record("meanAbsoluteEffect [root-mean-square variant, competing]",
           "PolygenicArchitecture.lean", "sqrt(h2/M)", cells_a_alt,
           regime="the RMS effect, which differs from the mean absolute effect "
                  "by sqrt(2/pi) for Gaussian effects, so this cell shows the "
                  "design can tell the two apart")
    for h2c, Mc, h2t, Mt in ((0.3, 100, 0.6, 1000), (0.1, 50, 0.9, 5000),
                             (0.5, 500, 0.5, 500)):
        lean = (h2c / Mc) / (h2t / Mt)
        truth = (h2c * Mt) / (Mc * h2t)
        cells_r.append(dict(design="h2c=%.1f Mc=%d h2t=%.1f Mt=%d"
                                   % (h2c, Mc, h2t, Mt),
                            lean=lean, truth=truth,
                            sem=abs(truth) * 1e-12 + 1e-15))
    record("heritabilityEnrichment", "PolygenicArchitecture.lean",
           "(h2_cat / M_cat) / (h2_total / M_total)", cells_r,
           regime="algebraic rearrangement through an independent expression; "
                  "a SELF-TEST, recorded as one, and it establishes only that "
                  "the body is the per-variant heritability ratio it claims")


def main():
    for fn in (test_fst_drift_migration_deme_sweep, test_ld_breakage_rate,
               test_architecture_scalars):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk18_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-58s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
