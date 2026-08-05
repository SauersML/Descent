#!/usr/bin/env python3
"""FAMILY fst_estimator_sampling -- INDEPENDENT-IMPLEMENTATION CROSS-CHECK.

Companion to cluster/fam_fst_estimators.py, which is self-contained numpy. This
one brings in scikit-allel, whose Hudson and Weir-Cockerham estimators were
written by other people for other reasons, so an agreement here is evidence and
not a restatement of my own algebra.

EVERY NUMBER IN THIS FILE IS LABELLED WITH THE ESTIMATOR IT BELONGS TO.
An F_ST comparison that does not name the estimator is meaningless, and this
family is where that bites: the corpus now explicitly distinguishes `neiGst`
from `hudsonFst`.

    NEI_GST_corpus   1 - (p1(1-p1)+p2(1-p2)) / (2*pbar*(1-pbar))
                     = Descent.Conventions.neiGst
                     = Descent.PopulationGeneticsFoundations.simpleFst
                     = ...neiGstFromFrequencies
    HUDSON_corpus    (p1-p2)^2 / (p1(1-p2)+p2(1-p1))
                     = Descent.Conventions.hudsonFst
    HUDSON_allel     scikit-allel hudson_fst, ratio of averages over loci
    WC_allel         scikit-allel weir_cockerham_fst, ratio of averages

CLAIMS UNDER TEST
    C1  HUDSON_corpus == HUDSON_allel in the large-sample limit.  A positive
        control on the corpus's Hudson body against foreign code.
    C2  The exact conversion proved in Conventions.hudsonFst_eq_of_neiGst,
        HUDSON = 2*NEI_GST/(1 + NEI_GST), holds pointwise.
    C3  THE DOCSTRING CLAIM.  Conventions.neiGst says the two denominators
        "differ by (p1-p2)^2/2, so they agree only when p1 = p2 OR pbar = 1/2".
        The second disjunct is a claim about a regime and is checked here on a
        grid built specifically to sit ON pbar = 1/2 with p1 != p2.  From C2,
        2G/(1+G) = G iff G = 0 or G = 1, so pbar = 1/2 cannot be a coincidence
        locus unless the arithmetic says otherwise -- which is exactly why it is
        measured rather than argued.
    C4  Sampling: at n = 20 diploids per deme the SAMPLE estimators depart from
        their own parametric limits, and by different amounts. This is what
        makes C1's agreement at n = 5000 informative rather than automatic.

CONTROLS AND HOW EACH CAN FAIL
    K1  p1 = p2, true divergence exactly zero.  HUDSON_allel and WC_allel must
        return ~0 (they carry sample-size corrections); NEI_GST computed on the
        SAMPLE must return a strictly positive number, because it has none.
        FAILS IF the sampler is broken (K1 nonzero for Hudson) or if my Nei
        transcription silently acquired a correction (K1 zero for Nei).
    K2  POSITIVE CONTROL that the comparison machinery compares: at the point
        the Lean docstring names, p1 = 0.2, p2 = 0.6, NEI_GST must be 0.1667 and
        HUDSON 0.2857, a +71.4% gap.  If these come back equal, every agreement
        in this file is void.
    K3  DEGENERACY DEMONSTRATION / can-fail clause.  At p1 = p2 all four
        estimators agree to 0 by construction; a grid confined there validates
        nothing.  Reported explicitly so the reach of the real grid is visible.

CAN-FAIL CLAUSE ON THE GRID
    The grid must reach BOTH the rare end (pbar <= 0.05, where NEI_GST and
    HUDSON differ by close to the full factor 2 of the G -> 0 limit of
    2G/(1+G)) AND large divergence (where the factor shrinks toward 1).  A grid
    at a single divergence would fit any constant recalibration factor and could
    not show that the conversion is NOT a constant, which is the whole content
    of the conversion theorem.

SPEED
    Sample sizes, loci, replicates, grids and tolerances in this file were
    chosen for signal and have not been reduced.  The draws are batched only
    over loci and individuals, where the batched draw is the same draw: every
    element of rng.binomial(1, P) with P an array is an independent Bernoulli
    at its own element's probability, which is exactly the per-individual
    per-locus draw a loop would make.
"""

import json
import os
import sys

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import numpy as np
import allel

SEED = 20260802
HERE = os.path.dirname(os.path.abspath(__file__))
N_LOCI = 500


# --------------------------------------------------------------------------
# CORPUS BODIES, transcribed from Lean.  Named for what they COMPUTE, with the
# Lean name that spells them recorded next to it.
# --------------------------------------------------------------------------
def nei_gst_corpus(p1, p2):
    """Descent.Conventions.neiGst: Nei's G_ST."""
    pbar = (p1 + p2) / 2.0
    return 1.0 - (p1 * (1 - p1) + p2 * (1 - p2)) / (2.0 * pbar * (1 - pbar))


def hudson_corpus(p1, p2):
    """Descent.Conventions.hudsonFst -- Hudson's parametric F_ST."""
    return (p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1))


def conversion_from_nei(g):
    """Conventions.hudsonFst_eq_of_neiGst : Hudson = 2G/(1+G)."""
    return 2.0 * g / (1.0 + g)


# --------------------------------------------------------------------------
def draw_genotypes(rng, p, n_dip, n_loci):
    """(n_loci, n_dip, 2) haplotype array at parametric frequency p."""
    return rng.binomial(1, p, size=(n_loci, n_dip, 2)).astype("i1")


def allel_estimates(rng, p1, p2, n_dip, n_loci=N_LOCI):
    """HUDSON_allel and WC_allel, both as RATIOS OF AVERAGES over loci."""
    h1 = draw_genotypes(rng, p1, n_dip, n_loci)
    h2 = draw_genotypes(rng, p2, n_dip, n_loci)
    g = allel.GenotypeArray(np.concatenate([h1, h2], axis=1))
    subpops = [list(range(n_dip)), list(range(n_dip, 2 * n_dip))]
    ac1 = g.count_alleles(subpop=subpops[0], max_allele=1)
    ac2 = g.count_alleles(subpop=subpops[1], max_allele=1)

    num, den = allel.hudson_fst(ac1, ac2)
    hud = float(np.nansum(num) / np.nansum(den))

    a, b, c = allel.weir_cockerham_fst(g, subpops, max_allele=1)
    wc = float(np.nansum(a) / np.nansum(a + b + c))

    # NEI'S G_ST on the SAME sample, computed with the corpus body applied to
    # sample frequencies.  No sample-size correction anywhere -- that is the
    # point of the K1 control.
    s1 = ac1[:, 1] / ac1.sum(axis=1)
    s2 = ac2[:, 1] / ac2.sum(axis=1)
    sbar = (s1 + s2) / 2.0
    hs = np.mean(s1 * (1 - s1) + s2 * (1 - s2))
    ht = np.mean(2.0 * sbar * (1 - sbar))
    nei = float(1.0 - hs / ht) if ht > 0 else float("nan")
    return hud, wc, nei


def main():
    rng = np.random.default_rng(SEED)
    rows = []

    # ---- C1 / C2 / C4 : the main grid. ----------------------------------
    # CAN-FAIL: reaches pbar = 0.03 (rare) through pbar = 0.7, and divergences
    # from small to large, so the conversion is tested where it is a factor
    # near 2 AND where it is near 1.  A constant recalibration factor cannot
    # fit both ends.
    GRID = [(0.02, 0.04), (0.01, 0.10), (0.05, 0.30),
            (0.20, 0.60), (0.30, 0.50), (0.40, 0.90),
            (0.70, 0.75), (0.10, 0.90)]
    for (p1, p2) in GRID:
        g_nei = nei_gst_corpus(p1, p2)
        f_hud = hudson_corpus(p1, p2)
        conv = conversion_from_nei(g_nei)
        for n_dip in (5000, 20):
            hud_a, wc_a, nei_s = allel_estimates(rng, p1, p2, n_dip)
            rows.append({
                "cell": ("C1 large-n cross-check" if n_dip >= 5000
                         else "C4 finite-n sampling departure"),
                "p1": p1, "p2": p2, "pbar": (p1 + p2) / 2.0,
                "n_diploids_per_deme": n_dip,
                "NEI_GST_corpus_parametric": g_nei,
                "HUDSON_corpus_parametric": f_hud,
                "HUDSON_from_conversion_2G_over_1plusG": conv,
                "conversion_relerr": abs(conv - f_hud) / max(abs(f_hud), 1e-12),
                "HUDSON_allel_sample": hud_a,
                "WC_allel_sample": wc_a,
                "NEI_GST_sample": nei_s,
                "HUDSON_allel_vs_HUDSON_corpus_relerr":
                    abs(hud_a - f_hud) / max(abs(f_hud), 1e-12),
                "HUDSON_over_NEI_parametric": f_hud / g_nei if g_nei else None,
                # C1 is the assertion; at n = 20 no assertion is made about
                # closeness, the departure is the observation.
                "ok": (abs(hud_a - f_hud) <= 0.02 * max(abs(f_hud), 1e-12)
                       if n_dip >= 5000 else True),
            })

    # ---- C2 alone, exactly, with no sampling anywhere in it. ------------
    worst = 0.0
    for p1 in (0.01, 0.05, 0.2, 0.35, 0.5, 0.8, 0.95):
        for p2 in (0.02, 0.1, 0.3, 0.5, 0.6, 0.9, 0.99):
            if p1 == p2:
                continue
            g = nei_gst_corpus(p1, p2)
            worst = max(worst, abs(conversion_from_nei(g) - hudson_corpus(p1, p2))
                        / max(abs(hudson_corpus(p1, p2)), 1e-12))
    rows.append({
        "cell": "C2 conversion theorem, exact, 42 points",
        "worst_relative_error": worst,
        "isolates": ("the conversion 2G/(1+G) alone, with no sampling and no "
                     "foreign library in the loop"),
        "ok": worst < 1e-12,
    })

    # ---- C3 : THE DOCSTRING'S REGIME CLAIM, ON pbar = 1/2 EXACTLY. -----
    # Conventions.neiGst asserts the estimators "agree only when p1 = p2 or
    # pbar = 1/2".  Every row below has pbar = 1/2 EXACTLY and p1 != p2.
    for d in (0.05, 0.2, 0.4, 0.8):
        p1, p2 = 0.5 + d / 2.0, 0.5 - d / 2.0
        g = nei_gst_corpus(p1, p2)
        f = hudson_corpus(p1, p2)
        rows.append({
            "cell": "C3 docstring regime claim, pbar = 1/2 exactly",
            "p1": p1, "p2": p2, "pbar": 0.5,
            "NEI_GST_corpus": g, "HUDSON_corpus": f,
            "HUDSON_over_NEI": f / g,
            "relative_gap": abs(f - g) / max(abs(f), 1e-12),
            "claim": ("Conventions.neiGst docstring: the two agree when "
                      "pbar = 1/2"),
            "isolates": ("the pbar = 1/2 disjunct alone -- p1 != p2 in every "
                         "row, so the first disjunct cannot be what is doing "
                         "the work"),
            # This row is OK if the claim HOLDS.  It is written so that it can
            # fail, and it is expected to.
            "ok": abs(f - g) <= 1e-9,
        })

    # ---- K1 : p1 = p2, true F_ST exactly zero. --------------------------
    for p in (0.5, 0.05):
        for n_dip in (25, 100):
            hud_a, wc_a, nei_s = allel_estimates(rng, p, p, n_dip)
            rows.append({
                "cell": "K1 control p1=p2, true F_ST=0",
                "p": p, "n_diploids_per_deme": n_dip,
                "HUDSON_allel_sample": hud_a, "WC_allel_sample": wc_a,
                "NEI_GST_sample_uncorrected": nei_s,
                "nei_predicted_bias_1_over_2n_minus_1":
                    1.0 / (2.0 * 2 * n_dip - 1.0),
                "isolates": ("estimator convention with divergence held at "
                             "exactly zero -- separates convention from "
                             "sampling, which C1/C4 cannot"),
                "ok": (abs(hud_a) < 0.01 and abs(wc_a) < 0.01 and nei_s > 0.0),
            })

    # ---- K2 : POSITIVE CONTROL at the point the Lean docstring names. ---
    g = nei_gst_corpus(0.2, 0.6)
    f = hudson_corpus(0.2, 0.6)
    hud_a, wc_a, _ = allel_estimates(rng, 0.2, 0.6, 5000)
    rows.append({
        "cell": "K2 POSITIVE CONTROL at the docstring's own point",
        "p1": 0.2, "p2": 0.6,
        "NEI_GST_corpus": g, "docstring_says_NEI": 0.1667,
        "HUDSON_corpus": f, "docstring_says_HUDSON": 0.2857,
        "HUDSON_allel_sample_n5000": hud_a, "WC_allel_sample_n5000": wc_a,
        "percent_gap": 100.0 * (f - g) / g,
        "docstring_says_percent_gap": 71.4,
        "isolates": "the comparison machinery itself",
        "ok": (abs(g - 0.1667) < 5e-4 and abs(f - 0.2857) < 5e-4
               and abs(100.0 * (f - g) / g - 71.4) < 0.2),
        "disagreement_detected": abs(f / g - 1.0) > 0.02,
    })

    # ---- K3 : degeneracy demonstration. --------------------------------
    g0 = nei_gst_corpus(0.3, 0.3)
    f0 = hudson_corpus(0.3, 0.3)
    rows.append({
        "cell": "K3 degeneracy demo p1=p2, why the grid must leave it",
        "NEI_GST_corpus": g0, "HUDSON_corpus": f0,
        "note": ("both exactly 0: a grid confined to p1=p2 validates the "
                 "corpus's free conversion between the two estimators by "
                 "construction and decides nothing"),
        "ok": abs(g0) < 1e-15 and abs(f0) < 1e-15,
    })

    out = {"seed": SEED, "n_loci": N_LOCI,
           "scikit_allel_version": allel.__version__,
           "rows": rows}
    n_bad = 0
    print("=" * 78)
    print("FST ESTIMATOR CROSS-CHECK vs scikit-allel %s" % allel.__version__)
    print("=" * 78)
    for r in rows:
        if not r.get("ok"):
            n_bad += 1
        bits = []
        for k in sorted(r):
            if k in ("cell", "ok", "isolates", "note", "claim"):
                continue
            v = r[k]
            bits.append("%s=%.6g" % (k, v) if isinstance(v, float)
                        else "%s=%s" % (k, v))
        print("  [%s] %-46s %s" % ("ok " if r.get("ok") else "RED",
                                   r["cell"], "  ".join(bits)))
    c3 = [r for r in rows if r["cell"].startswith("C3")]
    print("")
    print("C3 VERDICT: the docstring's 'or pbar = 1/2' disjunct is %s"
          % ("SUPPORTED" if all(r["ok"] for r in c3) else
             "REFUTED -- at pbar = 1/2 with p1 != p2 the two estimators "
             "differ; they coincide only at p1 = p2, since 2G/(1+G) = G "
             "iff G in {0,1}"))
    k2 = [r for r in rows if r["cell"].startswith("K2")][0]
    print("K2 POSITIVE CONTROL: %s"
          % ("FIRED, the estimators do disagree"
             if k2["disagreement_detected"] else
             "DID NOT FIRE -- treat every agreement here as void"))
    out["cells_red"] = n_bad
    out["c3_docstring_claim_supported"] = all(r["ok"] for r in c3)
    out["k2_positive_control_fired"] = bool(k2["disagreement_detected"])
    fh = open(os.path.join(HERE, "fam_fst_allel_crosscheck_results.json"), "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_fst_allel_crosscheck_results.json  (%d cells red)" % n_bad)
    return 0


if __name__ == "__main__":
    sys.exit(main())
