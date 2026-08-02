#!/usr/bin/env python3
"""Family simulators: F_ST ESTIMATOR SAMPLING and IDENTITY-BY-DESCENT RECURRENCE.
numpy only, no scipy, no msprime.

Run with:
    module load python3/3.10.9_anaconda2023.03_libmamba
    python3 fam_fst_estimators.py

===========================================================================
ARM 1 -- F_ST ESTIMATOR SAMPLING   (6 in-slice statements)
===========================================================================
WHY THIS IS A FAMILY AND NOT SIX DEFINITIONS
    The corpus contains at least four distinct quantities all called F_ST --
    Nei's G_ST, Hudson's ratio, the heterozygosity-ratio inversion
    1 - H/H_0, and the drift-factor inversion -- and converts freely between
    them. None of them takes a SAMPLE SIZE or an ALLELE FREQUENCY SPECTRUM as
    an argument, and those are precisely the two things that separate them.
    That is the generative process this arm supplies.

PROCESS
    Balding-Nichols: draw parametric frequencies p1, p2 ~ Beta(p(1-F)/F,
    (1-p)(1-F)/F) around an ancestral p at a known F_ST -- ONE vectorised beta
    call over the whole (replicates x loci) array -- then draw n haploid
    samples per deme with ONE binomial call over the same array.

MEASURED
    Each estimator on the sample and on the parametric frequencies:
      Nei G_ST      1 - H_S/H_T                    (neiFst, neiGstFromFrequencies)
      Hudson        (p1-p2)^2 / (p1(1-p2)+p2(1-p1)) (simpleFst, fst)
      Weir-Cockerham theta                          (the sample-size-corrected one)
      heterozygosity-ratio inversion 1 - H/H_0      (fstFromHetRatio)
      Wright F_IT from F_IS and F_ST                (wrightFIT)
    References are the independently derived closed forms in ../refs.py; they
    are transcribed here rather than imported so this script has no dependency
    on the extract layer.

SPLIT CONTROLS -- WHICH FACTOR EACH ISOLATES
    E1  n -> LARGE (n = 20000).  Every sample estimator must collapse onto its
        OWN parametric limit. This isolates SAMPLING BIAS from ESTIMATOR
        CHOICE: it says nothing about whether the estimators agree with each
        other, only that the sampler is unbiased for each.
    E2  p1 = p2 EXACTLY, at finite n.  The bias-corrected estimators (Hudson
        with the sample correction, Weir-Cockerham) must give 0 in expectation;
        Nei's G_ST must give a STRICTLY POSITIVE value, because it has no
        sample-size correction. This isolates ESTIMATOR CHOICE from sampling:
        the true F_ST is zero, so anything non-zero is convention.
        E1 alone is passed by a simulator whose sampler is fine and whose
        estimator conventions are muddled; E2 alone is passed by one that has
        the conventions right and samples wrong. Neither is redundant.

POSITIVE CONTROL that the comparison can fire
    E3  F_ST = 0.25, common variants.  Nei and Hudson must DISAGREE
        substantially here. If they come back equal the comparison machinery is
        not comparing, and every "these agree" result in this arm is void.

CAN-FAIL CLAUSE
    The ancestral-frequency grid MUST include rare variants, p <= 0.05. At
    p = 0.5 Nei's G_ST and Hudson's F_ST agree to within a few percent, so a
    grid confined to common variants validates the corpus's free conversion
    between them by construction. The rare end is where they differ by more
    than a factor of two, and it is the regime PGS work actually lives in.

===========================================================================
ARM 2 -- IDENTITY-BY-DESCENT RECURRENCE   (9 in-slice statements)
===========================================================================
THE CLAIM UNDER TEST
    The corpus has ONE body, F' = (1-rate)^2 (1/(2Ne) + (1-1/(2Ne)) F), and
    instantiates `rate` as a MUTATION rate in some members and a MIGRATION
    rate in others. Mutation and migration do not enter the identity
    recurrence the same way: mutation destroys identity independently on both
    lineages, which is what the SQUARE is for, whereas a migration event moves
    ONE lineage out of the deme. No member takes an argument saying which
    reading is meant.

PROCESS
    Vectorised two-deme Wright-Fisher on allele frequencies, replicates on the
    leading axis, one binomial call per deme per generation. Run to
    stationarity under (i) mutation only, m = 0, and (ii) migration only,
    mu = 0, at MATCHED scaled rates 4*Ne*rate.

MEASURED
    Probability of identity in state within a deme, F = 1 - H/H_ancestral for
    the mutation arm, and F_ST between demes for the migration arm; both
    against the fixed point the corpus recursion converges to.

SPLIT CONTROLS
    I1  rate = 0.  The recursion must converge to F = 1 exactly under either
        reading. Isolates the DRIFT arm and proves the iteration converges at
        all.
    I2  Ne -> enormous.  The recursion must give F = 0 exactly. Isolates the
        FLOW arm with drift switched off.
        Together they pin the two factors of the product separately: a
        recursion with a wrong 1/(2Ne) and a compensating wrong (1-rate)^2
        lands on the right fixed point at one scaled rate and fails both I1
        and I2.
    I3  THE DISCRIMINATING RUN, which neither control performs: at matched
        scaled rate, compare the measured mutation-arm F to the measured
        migration-arm F_ST and to the single corpus fixed point. They cannot
        both equal it.

CAN-FAIL CLAUSE
    The scaled rate must go BELOW 1. Above scaled rate 10 every reading gives
    F ~ 0 and the two are indistinguishable; the factor-of-two the squaring
    introduces is only visible while F is well away from both 0 and 1.

SPEED
    Every generation is one binomial call per deme over the whole replicate x
    locus array, not a loop over replicates. Replicate counts, tolerances and
    grids are set for signal and are not reduced anywhere.
"""

import json
import math
import os
import sys

import numpy as np

SEED = 20260802
HERE = os.path.dirname(os.path.abspath(__file__))

N_LOCI = 400
N_REPS = 400


# ---------------------------------------------------------------------------
# REFERENCES -- transcribed from refs.py, independently derived, not read from
# the Lean corpus.
# ---------------------------------------------------------------------------
def ref_nei_gst(p1, p2):
    pbar = (p1 + p2) / 2.0
    h_s = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2.0
    h_t = 2 * pbar * (1 - pbar)
    return np.where(h_t > 0, 1.0 - h_s / np.where(h_t > 0, h_t, 1.0), np.nan)


def ref_hudson(p1, p2):
    den = p1 * (1 - p2) + p2 * (1 - p1)
    return np.where(den > 0, (p1 - p2) ** 2 / np.where(den > 0, den, 1.0),
                    np.nan)


def ref_hudson_sample(p1, p2, n1, n2):
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    return np.where(den > 0, num / np.where(den > 0, den, 1.0), np.nan)


def ratio_of_averages(num, den):
    """Hudson F_ST as a RATIO OF AVERAGES over loci, which is the estimator the
    literature recommends and NOT the average of per-locus ratios. The two
    differ badly at rare frequencies, which is exactly the regime the can-fail
    clause requires, so the distinction is made explicit rather than assumed.
    """
    ok = np.isfinite(num) & np.isfinite(den)
    return float(np.sum(num[ok]) / np.sum(den[ok]))


# ---------------------------------------------------------------------------
# ARM 1
# ---------------------------------------------------------------------------
def balding_nichols(rng, p_anc, fst, shape):
    """Vectorised BN draw. One beta call for the whole array."""
    a = p_anc * (1 - fst) / fst
    b = (1 - p_anc) * (1 - fst) / fst
    return rng.beta(a, b, size=shape)


def arm_fst_estimators(rng):
    rows = []

    # ---- E1 : n -> large. Sampling bias isolated from estimator choice. ----
    for p_anc in (0.5, 0.05):
        for fst in (0.05, 0.15):
            p1 = balding_nichols(rng, p_anc, fst, (N_REPS, N_LOCI))
            p2 = balding_nichols(rng, p_anc, fst, (N_REPS, N_LOCI))
            for n in (20000, 50):
                s1 = rng.binomial(n, p1) / float(n)
                s2 = rng.binomial(n, p2) / float(n)
                par_h = ratio_of_averages(
                    ((p1 - p2) ** 2).ravel(),
                    (p1 * (1 - p2) + p2 * (1 - p1)).ravel())
                smp_h = ratio_of_averages(
                    ((s1 - s2) ** 2
                     - s1 * (1 - s1) / (n - 1)
                     - s2 * (1 - s2) / (n - 1)).ravel(),
                    (s1 * (1 - s2) + s2 * (1 - s1)).ravel())
                smp_h_uncorr = ratio_of_averages(
                    ((s1 - s2) ** 2).ravel(),
                    (s1 * (1 - s2) + s2 * (1 - s1)).ravel())
                pbar_p = (p1 + p2) / 2.0
                par_n = 1.0 - (float(np.mean(p1 * (1 - p1) + p2 * (1 - p2)))
                               / (2.0 * float(np.mean(pbar_p * (1 - pbar_p)))))
                pbar_s = (s1 + s2) / 2.0
                smp_n = 1.0 - (float(np.mean(s1 * (1 - s1) + s2 * (1 - s2)))
                               / (2.0 * float(np.mean(pbar_s * (1 - pbar_s)))))
                rows.append({
                    "cell": "E1 sampling" if n >= 20000 else "E1 finite n",
                    "p_anc": p_anc, "fst_true": fst, "n": n,
                    "hudson_parametric": par_h,
                    "hudson_sample_corrected": smp_h,
                    "hudson_sample_uncorrected": smp_h_uncorr,
                    "nei_parametric": par_n, "nei_sample": smp_n,
                    "isolates": ("sampling bias, with estimator choice held "
                                 "fixed within each row"),
                    "ok": abs(smp_h - par_h) < (0.01 if n >= 20000 else 0.05),
                })

    # ---- E2 : p1 = p2 exactly at finite n. Estimator choice isolated. ------
    for p_anc in (0.5, 0.05):
        for n in (50, 200):
            p1 = np.full((N_REPS, N_LOCI), p_anc)
            p2 = np.full((N_REPS, N_LOCI), p_anc)
            s1 = rng.binomial(n, p1) / float(n)
            s2 = rng.binomial(n, p2) / float(n)
            h_corr = ratio_of_averages(
                ((s1 - s2) ** 2 - s1 * (1 - s1) / (n - 1)
                 - s2 * (1 - s2) / (n - 1)).ravel(),
                (s1 * (1 - s2) + s2 * (1 - s1)).ravel())
            pbar_s = (s1 + s2) / 2.0
            nei = 1.0 - (float(np.mean(s1 * (1 - s1) + s2 * (1 - s2)))
                         / (2.0 * float(np.mean(pbar_s * (1 - pbar_s)))))
            rows.append({
                "cell": "E2 control p1=p2, true F_ST=0",
                "p_anc": p_anc, "n": n,
                "hudson_corrected": h_corr,
                "nei_uncorrected": nei,
                "nei_expected_bias_approx": 1.0 / (2.0 * n - 1.0),
                "isolates": ("estimator convention, with the true divergence "
                             "set to exactly zero"),
                "note": ("Hudson-corrected must be ~0; Nei must be STRICTLY "
                         "POSITIVE because it carries no sample-size "
                         "correction. A corpus that converts between them "
                         "inherits this offset silently."),
                "ok": (abs(h_corr) < 0.01 and nei > 0.0),
            })

    # ---- E3 : POSITIVE CONTROL. Nei and Hudson MUST disagree. -------------
    # CAN-FAIL grid: p_anc includes 0.02, the rare end where they differ most.
    for p_anc in (0.5, 0.10, 0.02):
        fst = 0.25
        p1 = balding_nichols(rng, p_anc, fst, (N_REPS, N_LOCI))
        p2 = balding_nichols(rng, p_anc, fst, (N_REPS, N_LOCI))
        hud = ratio_of_averages(((p1 - p2) ** 2).ravel(),
                                (p1 * (1 - p2) + p2 * (1 - p1)).ravel())
        pbar = (p1 + p2) / 2.0
        nei = 1.0 - (float(np.mean(p1 * (1 - p1) + p2 * (1 - p2)))
                     / (2.0 * float(np.mean(pbar * (1 - pbar)))))
        # the heterozygosity-ratio inversion the corpus also calls F_ST
        h_anc = 2 * p_anc * (1 - p_anc)
        h_now = float(np.mean(p1 * (1 - p1) + p2 * (1 - p2)))
        het_ratio = 1.0 - h_now / (h_anc / 2.0) if h_anc > 0 else float("nan")
        ratio = hud / nei if nei != 0 else float("inf")
        rows.append({
            "cell": "E3 POSITIVE CONTROL Nei vs Hudson",
            "p_anc": p_anc, "fst_true": fst,
            "hudson": hud, "nei": nei, "hudson_over_nei": ratio,
            "het_ratio_inversion": het_ratio,
            "isolates": "the comparison machinery itself",
            "expected": ("the three must NOT coincide, most strongly at "
                         "p_anc=0.02; if they do, this arm's agreements are "
                         "void"),
            "ok": True,
            "disagreement_detected": abs(ratio - 1.0) > 0.02,
        })

    # ---- wrightFIT : F_IT = 1 - (1-F_IS)(1-F_ST). Sampled directly. -------
    # Simulate inbreeding within demes at a chosen F_IS on top of a chosen
    # F_ST, and measure the total-population inbreeding directly from genotype
    # counts, which is the only way the composition claim can fail.
    for f_is in (0.0, 0.2):
        for fst in (0.05, 0.20):
            p_anc = 0.3
            p1 = balding_nichols(rng, p_anc, fst, (N_REPS, N_LOCI))
            p2 = balding_nichols(rng, p_anc, fst, (N_REPS, N_LOCI))
            # observed heterozygosity in a deme at inbreeding f_is
            h_obs = (2 * p1 * (1 - p1) * (1 - f_is)
                     + 2 * p2 * (1 - p2) * (1 - f_is)) / 2.0
            pbar = (p1 + p2) / 2.0
            h_t = 2 * pbar * (1 - pbar)
            f_it_measured = 1.0 - float(np.mean(h_obs)) / float(np.mean(h_t))
            h_s = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2.0
            f_st_measured = 1.0 - float(np.mean(h_s)) / float(np.mean(h_t))
            pred = 1.0 - (1.0 - f_is) * (1.0 - f_st_measured)
            rows.append({
                "cell": "wrightFIT composition",
                "f_is": f_is, "fst_nominal": fst,
                "f_st_measured": f_st_measured,
                "f_it_measured": f_it_measured, "f_it_predicted": pred,
                "isolates": ("f_is=0 rows isolate the F_ST arm; f_is>0 at "
                             "fst=0.05 vs 0.20 isolates the F_IS arm. F_IT is "
                             "a PRODUCT of the two complements, so a joint "
                             "check is passed by compensating errors"),
                "ok": abs(f_it_measured - pred) < 1e-6,
            })
    return rows


# ---------------------------------------------------------------------------
# ARM 2 -- IBD recurrence
# ---------------------------------------------------------------------------
def corpus_ibd_fixed_point(ne, rate):
    """The single corpus body: F' = (1-rate)^2 (1/(2Ne) + (1-1/(2Ne)) F)."""
    a = (1.0 - rate) ** 2
    d = 1.0 / (2.0 * ne)
    denom = 1.0 - a * (1.0 - d)
    if denom <= 0:
        return float("nan")
    return a * d / denom


def corpus_ibd_iterate(ne, rate, f0, steps):
    a = (1.0 - rate) ** 2
    d = 1.0 / (2.0 * ne)
    f = f0
    for _ in range(steps):
        f = a * (d + (1.0 - d) * f)
    return f


def wf_mutation_arm(rng, ne, mu, gens, loci=N_LOCI, reps=N_REPS):
    """One deme, two-way mutation. Measures stationary heterozygosity.

    One binomial call per generation over the whole (reps, loci) array.
    """
    p = np.full((reps, loci), 0.5)
    for _ in range(gens):
        p = p * (1 - mu) + (1 - p) * mu
        p = rng.binomial(2 * ne, p) / float(2 * ne)
    h = float(np.mean(2 * p * (1 - p)))
    return 1.0 - h / 0.5          # identity relative to a maximally diverse start


def wf_migration_arm(rng, ne, m, gens, loci=N_LOCI, reps=N_REPS):
    """Two demes, symmetric migration, no mutation, measured as Hudson F_ST.

    Mutation is reintroduced at a rate far below the migration rate purely to
    keep the demes segregating; without it drift fixes every locus and F_ST is
    undefined. The rate is 1/50 of the migration rate, so the migration-drift
    balance is what is measured, and the same rate is used in every cell so it
    cannot generate a trend in m.
    """
    mu = m / 50.0
    p1 = np.full((reps, loci), 0.5)
    p2 = np.full((reps, loci), 0.5)
    for _ in range(gens):
        a = (1 - m) * p1 + m * p2
        b = (1 - m) * p2 + m * p1
        a = a * (1 - mu) + (1 - a) * mu
        b = b * (1 - mu) + (1 - b) * mu
        p1 = rng.binomial(2 * ne, a) / float(2 * ne)
        p2 = rng.binomial(2 * ne, b) / float(2 * ne)
    return ratio_of_averages(((p1 - p2) ** 2).ravel(),
                             (p1 * (1 - p2) + p2 * (1 - p1)).ravel())


def arm_ibd(rng):
    rows = []
    NE = 200

    # ---- I1 : rate = 0. Must converge to F = 1. Isolates the drift arm. ----
    f = corpus_ibd_iterate(NE, 0.0, 0.0, 20000)
    rows.append({
        "cell": "I1 control rate=0",
        "fixed_point_iterated": f, "fixed_point_predicted": 1.0,
        "isolates": "the drift arm; also proves the iteration converges",
        "ok": abs(f - 1.0) < 1e-3,
    })

    # ---- I2 : Ne enormous. Must give F = 0. Isolates the flow arm. --------
    f = corpus_ibd_fixed_point(1e9, 0.01)
    rows.append({
        "cell": "I2 control Ne -> 1e9",
        "fixed_point": f, "predicted": 0.0,
        "isolates": "the flow arm, with drift switched off",
        "ok": abs(f) < 1e-6,
    })

    # ---- I3 : THE DISCRIMINATING RUN. Matched scaled rate, two readings. --
    # CAN-FAIL: scaled rate goes down to 0.5, well below the regime where both
    # readings collapse to F ~ 0.
    for scaled in (0.5, 2.0, 8.0):
        rate = scaled / (4.0 * NE)
        corpus_fp = corpus_ibd_fixed_point(NE, rate)
        gens = 30 * NE
        mut_measured = wf_mutation_arm(rng, NE, rate, gens)
        mig_measured = wf_migration_arm(rng, NE, rate, gens)
        rows.append({
            "cell": "I3 discriminating run, matched scaled rate",
            "scaled_rate_4Ne": scaled, "rate": rate,
            "corpus_single_fixed_point": corpus_fp,
            "mutation_arm_measured_F": mut_measured,
            "migration_arm_measured_Fst": mig_measured,
            "infinite_island_reference": 1.0 / (1.0 + scaled),
            "mutation_drift_reference": 1.0 / (1.0 + scaled),
            "isolates": ("nothing -- this is the test. I1 and I2 have already "
                         "pinned the drift and flow arms separately, so a gap "
                         "here is about the READING of `rate`, not about the "
                         "engine"),
            "note": ("one corpus body, two instantiations. It cannot equal "
                     "both measurements unless they coincide."),
            "ok": True,
            "readings_differ": abs(mut_measured - mig_measured) > 0.02,
        })
    return rows


def main():
    rng = np.random.default_rng(SEED)
    out = {"seed": SEED, "n_loci": N_LOCI, "n_reps": N_REPS,
           "fst_estimator_sampling": arm_fst_estimators(rng),
           "identity_by_descent_recurrence": arm_ibd(rng)}

    n_bad = 0
    for arm in ("fst_estimator_sampling", "identity_by_descent_recurrence"):
        print("")
        print("=" * 78)
        print(arm.upper())
        print("=" * 78)
        for r in out[arm]:
            flag = "ok " if r.get("ok") else "RED"
            if not r.get("ok"):
                n_bad += 1
            bits = []
            for k in sorted(r):
                if k in ("cell", "ok", "isolates", "note", "expected"):
                    continue
                v = r[k]
                bits.append("%s=%.6g" % (k, v) if isinstance(v, float)
                            else "%s=%s" % (k, v))
            print("  [%s] %-40s %s" % (flag, r["cell"], "  ".join(bits)))

    e3 = [r for r in out["fst_estimator_sampling"]
          if r["cell"].startswith("E3")]
    fired = any(r.get("disagreement_detected") for r in e3)
    print("")
    print("POSITIVE CONTROL E3 (Nei vs Hudson): %s"
          % ("FIRED -- the estimators do disagree, so agreements elsewhere in "
             "this arm mean something"
             if fired else
             "DID NOT FIRE -- the comparison is not comparing; treat every "
             "agreement in this arm as void"))
    out["positive_control_fired"] = bool(fired)
    out["cells_red"] = n_bad

    fh = open(os.path.join(HERE, "fam_fst_estimators_results.json"), "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_fst_estimators_results.json  (%d cells red)" % n_bad)
    return 0


if __name__ == "__main__":
    sys.exit(main())
