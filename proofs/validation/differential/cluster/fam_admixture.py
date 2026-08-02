#!/usr/bin/env python3
"""Family simulator: ADMIXTURE. numpy only, no msprime, no scipy.

Six in-slice definitions, none previously simulated. Vectorised over LOCI in
part A and over REPLICATES in part B, so both parts are array arithmetic and
the file runs in well under a minute.

    admixedAlleleFreq     p_C = alpha p_A + (1-alpha) p_B
    admixedFst            F_ST(C,A) = (1-alpha)^2 F_ST(A,B)
    admixtureLD           D = alpha(1-alpha) dp1 dp2
    admixtureLDTwoLocus   D = f(AB) - f(A) f(B)   [= the same, proved in Lean]
    admixtureLDDecay      (1-r)^g
    admixtureLDBoost      admixtureLDDecay / equilibrium_ld

  also evaluated, because they are the same family and the engine already
  produces them:
    admixtureLDAtGen, admixtureLDMagnitude, steppingStoneFstQuadratic's
    sibling steppingStoneFst are NOT here -- that is the other simulator.

PART A -- admixedFst OVER A FREQUENCY SPECTRUM

  `admixedFst` is the definition the analytic tier scores at -44%, and the
  differential check `admixedFst-ratio-not-numerator` evaluates it at ONE
  frequency pair at a time. F_ST as anyone computes it is a RATIO OF AVERAGES
  over a whole spectrum of loci, and the sign and size of the averaging
  correction is not deducible from a single pair. Nothing in the corpus has
  ever run it over a spectrum. This does.

  Model: draw n_loci ancestral frequencies from a spectrum, drift A and B
  independently for t generations at size Ne (one rng.binomial call per
  population per generation, over all loci at once), then form the pulse
  admixture p_C = alpha p_A + (1-alpha) p_B and optionally drift C for g
  generations more.

  Reported for each cell: Hudson and Nei ratio-of-averages F_ST, plus the
  DECOMPOSITION that says where (1-alpha)^2 comes from and where it goes:

      measured F_ST(C,A) / F_ST(A,B)
        = [ E[(p_C-p_A)^2] / E[(p_B-p_A)^2] ]  /  [ E[den_CA] / E[den_AB] ]
        =            (1-alpha)^2               /   denominator_ratio

  The first bracket is an exact per-locus algebraic identity -- it is the step
  `admixed_freq_diff` proves in Lean -- and control A4a checks it holds to
  machine precision. The second bracket is the part the definition omits. So
  the run does not merely report a discrepancy, it says which factor of the
  derivation survives contact with a spectrum and which does not.

  THREE SPECTRA, because the answer depends on the spectrum and a
  single-spectrum run would not reveal that: a neutral-SFS-like density
  proportional to 1/p (strongly asymmetric, dominated by rare variants), a
  uniform density (symmetric about 1/2), and Beta(1/2,1/2) (symmetric,
  U-shaped). The differential check's can-fail clause says a symmetric
  frequency pair makes the (1-alpha)^2 scaling exactly right; running all
  three shows directly whether that carries over from a pair to a spectrum.

PART B -- ADMIXTURE LD

  A two-locus haplotype pool, both sources in linkage equilibrium internally,
  mixed at proportion alpha, then evolved by recombination r and drift Ne with
  the four haplotype frequencies as a (reps, 4) array.

  Settles `admixtureLD` / `admixtureLDTwoLocus` at generation 0 exactly, and
  measures the per-generation retention of E[D] against `admixtureLDDecay`'s
  (1-r)^g.

CONTROLS -- SEVEN, EACH ISOLATING ONE FACTOR, NONE FITTED

  A1  MIXING ALONE.  The admixed population is built BY SAMPLING ANCESTRY --
      2 n_C gametes, each of A ancestry with probability alpha, each then
      carrying the allele with the frequency of its own source. Nothing in
      that path evaluates alpha p_A + (1-alpha) p_B, so comparing its mean
      against `admixedAlleleFreq` is a real test and not a restatement: it
      fails at once on a reversed alpha convention, on a wrong ploidy, or on
      ancestry drawn per locus instead of per gamete. Required: |bias| under
      4 standard errors, at two values of n_C so the standard error itself
      moves.
  A2  ENDPOINTS.  alpha = 1 makes C identical to A, so F_ST(C,A) must be
      exactly 0; alpha = 0 makes C identical to B, so F_ST(C,A) must equal
      F_ST(B,A) exactly. Pins the F_ST estimator without assuming any formula
      for intermediate alpha.
  A3  DRIFT ALONE.  After t generations of independent drift from a common
      ancestral spectrum, Hudson ratio-of-averages F_ST(A,B) is exactly
      1 - (1 - 1/(2 Ne))^t for ANY ancestral spectrum -- the spectrum cancels
      between numerator and denominator. Pins drift and the estimator jointly
      against a closed form with nothing fitted, and it is spectrum-free, so
      it cannot be passed by a spectrum that happens to suit.
  A4a POSITIVE CONTROL, IDENTITY.  In the main grid the mixing is
      deterministic (the infinite-n_C limit A1 has just validated), so the
      numerator ratio must equal (1-alpha)^2 to 1e-12. This is the corpus's
      own derivation step, `admixed_freq_diff`; if it failed, the
      disagreement below would be about the simulator and not the formula.
  A4b POSITIVE CONTROL, THE CHECK CAN FAIL.  The same comparison is re-run
      with alpha perturbed by 1% inside the corpus formula only. The reported
      error must move by more than the tolerance. A null result from part A is
      only worth reading if this fires.
  B1  RECOMBINATION ALONE.  Ne infinite. E[D] must decay by exactly (1-r) per
      generation.
  B2  DRIFT ALONE.  r = 0, finite Ne. E[D] must decay by exactly
      (1 - 1/(2 Ne)) per generation.
      B1 and B2 split the two factors of the true retention
      (1-r)(1-1/(2 Ne)). `admixtureLDDecay` contains only the B1 factor, so
      the pair of controls is exactly what says whether that is a regime or an
      error.

CAN-FAIL CLAUSES

  alpha:  the grid spans both sides of 1/2 and includes 0.8, where the
      analytic tier's error is largest. A grid confined to small alpha sits
      where (1-alpha)^2 ~ 1 - 2 alpha and the ratio-versus-numerator
      distinction is second order in alpha.
  divergence:  t/(2 Ne) reaches 1.0. At low F_ST(A,B) every scaling of a
      near-zero number is a near-zero number and the relative error is noise.
  spectrum:  at least one asymmetric spectrum is required; on a spectrum
      symmetric about 1/2 the two denominators move together and the check
      loses most of its power. Both kinds are run so the difference is visible
      rather than assumed.
  r:  the recombination grid straddles 1/(2 Ne). Where r >> 1/(2 Ne) the drift
      factor is invisible and (1-r)^g is indistinguishable from the truth;
      where r << 1/(2 Ne) recombination is invisible. Only near r ~ 1/(2 Ne)
      do both factors matter at once.
"""

import json
import math
import sys

import numpy as np

SEED = 20260802


# ===========================================================================
# spectra
# ===========================================================================

def draw_spectrum(kind, n, rng, eps=1e-3):
    if kind == "sfs_1_over_p":
        u = rng.random(n)
        return eps * (((1.0 - eps) / eps) ** u)
    if kind == "uniform":
        return rng.random(n)
    if kind == "beta_half_half":
        # Beta(1/2,1/2) by the arcsine transform -- no scipy needed
        return np.sin(0.5 * math.pi * rng.random(n)) ** 2
    raise ValueError(kind)


def admix_sampled(p_a, p_b, alpha, n_c, rng):
    """Build the admixed population BY SAMPLING ancestry, not by the formula.

    2*n_c gametes are drawn; each is of A ancestry with probability alpha, and
    then carries the derived allele with the probability of ITS OWN source.
    Nothing here evaluates alpha*p_A + (1-alpha)*p_B, which is the point:
    control A1 compares this against `admixedAlleleFreq` and can therefore
    fail -- it would fail immediately, for instance, on the alpha/(1-alpha)
    convention being the other way round.
    """
    n = 2 * n_c
    na = rng.binomial(n, alpha, size=p_a.shape)
    ka = rng.binomial(na, np.clip(p_a, 0.0, 1.0))
    kb = rng.binomial(n - na, np.clip(p_b, 0.0, 1.0))
    return (ka + kb).astype(np.float64) / n


def drift(p, ne, gens, rng):
    """t generations of Wright-Fisher drift over ALL loci at once."""
    if ne is None or gens == 0:
        return p
    n = 2 * ne
    for _ in range(gens):
        p = rng.binomial(n, np.clip(p, 0.0, 1.0)).astype(np.float64) / n
    return p


# ===========================================================================
# F_ST estimators, ratio of averages over loci
# ===========================================================================

def hudson_parts(p1, p2):
    """Numerator and denominator of Hudson F_ST for parametric frequencies."""
    num = (p1 - p2) ** 2
    den = p1 * (1.0 - p2) + p2 * (1.0 - p1)
    return num, den


def hudson_fst(p1, p2):
    num, den = hudson_parts(p1, p2)
    d = float(den.mean())
    if d <= 0:
        return float("nan")
    return float(num.mean()) / d


def nei_gst(p1, p2):
    pbar = 0.5 * (p1 + p2)
    ht = 2.0 * pbar * (1.0 - pbar)
    hs = p1 * (1.0 - p1) + p2 * (1.0 - p2)
    t = float(ht.mean())
    if t <= 0:
        return float("nan")
    return (t - float(hs.mean())) / t


# ===========================================================================
# PART B engine -- two-locus haplotype pool
# ===========================================================================

def admixed_pool(alpha, p_a, q_a, p_b, q_b, reps):
    """(reps, 4) haplotype frequencies for a pulse admixture at generation 0.

    Both sources are internally in linkage equilibrium, so every bit of LD in
    the pool is admixture LD.
    """
    ha = np.array([p_a * q_a, p_a * (1 - q_a), (1 - p_a) * q_a,
                   (1 - p_a) * (1 - q_a)])
    hb = np.array([p_b * q_b, p_b * (1 - q_b), (1 - p_b) * q_b,
                   (1 - p_b) * (1 - q_b)])
    x = alpha * ha + (1 - alpha) * hb
    return np.tile(x, (reps, 1))


def d_of(x):
    return x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]


def pool_step(x, ne, r, rng):
    D = d_of(x)
    x = x + r * np.stack([-D, D, D, -D], axis=1)
    x = np.clip(x, 0.0, None)
    x /= x.sum(axis=1, keepdims=True)
    if ne is None:
        return x
    n = 2 * ne
    return rng.multinomial(n, x).astype(np.float64) / n


def ld_retention(alpha, p_a, q_a, p_b, q_b, ne, r, gens, reps, rng):
    """Per-generation geometric retention of E[D], and the trajectory."""
    x = admixed_pool(alpha, p_a, q_a, p_b, q_b, reps)
    traj = [float(np.mean(d_of(x)))]
    for _ in range(gens):
        x = pool_step(x, ne, r, rng)
        traj.append(float(np.mean(d_of(x))))
    a = np.array(traj)
    ok = a > 1e-12
    if int(ok.sum()) < 3:
        return None, traj
    t = np.arange(len(a))[ok]
    slope = np.polyfit(t, np.log(a[ok]), 1)[0]
    return math.exp(slope), traj


# ===========================================================================

def main():
    rng = np.random.default_rng(SEED)
    out = {}

    NLOCI = 200000
    NE = 500

    # ------------------------------------------------------------------
    print("CONTROLS -- PART A")

    # A1 mixing alone -- sampled admixture against the closed form
    p_a = draw_spectrum("sfs_1_over_p", NLOCI, rng)
    p_b = draw_spectrum("sfs_1_over_p", NLOCI, rng)
    a1rows = []
    a1 = True
    for alpha in (0.1, 0.3, 0.5, 0.8):
        for n_c in (200, 5000):
            ps = admix_sampled(p_a, p_b, alpha, n_c, rng)
            ref = alpha * p_a + (1 - alpha) * p_b
            bias = float(np.mean(ps - ref))
            # standard error of that mean, from the sampling variance of ps
            se = float(np.std(ps - ref) / math.sqrt(NLOCI))
            a1rows.append({"alpha": alpha, "n_C": n_c, "mean_bias": bias,
                           "standard_error": se, "z": bias / se if se else None})
            if se > 0 and abs(bias) > 4.0 * se:
                a1 = False
    worst = max(abs(r["mean_bias"]) for r in a1rows)
    worstz = max(abs(r["z"]) for r in a1rows if r["z"] is not None)
    print("  A1 mixing alone (admixedAlleleFreq, SAMPLED ancestry):")
    print("     max |bias| %.3e, max |z| %.2f (must be < 4) -> %s"
          % (worst, worstz, "PASS" if a1 else "FAIL"))

    # A3 drift alone -- exact and spectrum-free
    a3rows = []
    a3 = True
    for kind in ("sfs_1_over_p", "uniform", "beta_half_half"):
        for t in (100, 500, 1000):
            p0 = draw_spectrum(kind, NLOCI, rng)
            pa = drift(p0, NE, t, rng)
            pb = drift(p0, NE, t, rng)
            meas = hudson_fst(pa, pb)
            want = 1.0 - (1.0 - 1.0 / (2.0 * NE)) ** t
            rel = (meas - want) / want
            a3rows.append({"spectrum": kind, "t": t, "fst_measured": meas,
                           "fst_exact_1_minus_retention": want, "rel_err": rel})
            if abs(rel) > 0.02:
                a3 = False
    print("  A3 drift alone      : max |rel err| vs 1-(1-1/2Ne)^t %.4f -> %s"
          % (max(abs(r["rel_err"]) for r in a3rows), "PASS" if a3 else "FAIL"))

    # A2 endpoints, and A4a/A4b, are computed inside the main grid below.

    # ------------------------------------------------------------------
    print("")
    print("A. admixedFst OVER A FREQUENCY SPECTRUM   F_ST(C,A) = (1-a)^2 F_ST(A,B)")
    rowsA = []
    a2 = True
    a4a = True
    a4b = True
    for kind in ("sfs_1_over_p", "uniform", "beta_half_half"):
        for t in (250, 1000):                      # t/(2Ne) = 0.25 and 1.0
            p0 = draw_spectrum(kind, NLOCI, rng)
            pa = drift(p0, NE, t, rng)
            pb = drift(p0, NE, t, rng)
            fst_ab = hudson_fst(pa, pb)
            gst_ab = nei_gst(pa, pb)
            num_ab, den_ab = hudson_parts(pa, pb)
            print("  spectrum=%-14s t=%-5d F_ST(A,B)=%.4f (Nei %.4f)"
                  % (kind, t, fst_ab, gst_ab))
            print("    %-6s %-7s %-10s %-10s %-9s %-9s %-9s"
                  % ("alpha", "g_C", "fst_meas", "corpus", "rel_err",
                     "num_ratio", "den_ratio"))
            for alpha in (0.0, 0.1, 0.25, 0.5, 0.75, 0.8, 0.9, 1.0):
                for g_c in (0, 20):
                    pc = alpha * pa + (1 - alpha) * pb
                    pc = drift(pc, NE, g_c, rng)
                    fst_ca = hudson_fst(pc, pa)
                    gst_ca = nei_gst(pc, pa)
                    num_ca, den_ca = hudson_parts(pc, pa)
                    num_ratio = float(num_ca.mean()) / float(num_ab.mean())
                    den_ratio = float(den_ca.mean()) / float(den_ab.mean())
                    corpus = (1.0 - alpha) ** 2 * fst_ab
                    rel = None if fst_ca < 1e-9 else (corpus - fst_ca) / fst_ca
                    row = {"spectrum": kind, "t": t, "alpha": alpha, "g_C": g_c,
                           "fst_AB": fst_ab, "gst_AB": gst_ab,
                           "fst_CA_measured": fst_ca, "gst_CA_measured": gst_ca,
                           "fst_CA_corpus": corpus,
                           "rel_err_corpus": rel,
                           "numerator_ratio": num_ratio,
                           "numerator_ratio_expected_(1-a)^2": (1 - alpha) ** 2,
                           "denominator_ratio": den_ratio,
                           "reconstructed_ratio": (num_ratio / den_ratio)
                           if den_ratio else None,
                           "measured_ratio": (fst_ca / fst_ab) if fst_ab else None}
                    rowsA.append(row)
                    # A4a: the numerator identity, exact only without post-drift
                    if g_c == 0:
                        if abs(num_ratio - (1 - alpha) ** 2) > 1e-12:
                            a4a = False
                        # A2 endpoints
                        if alpha == 1.0 and abs(fst_ca) > 1e-9:
                            a2 = False
                        if alpha == 0.0 and abs(fst_ca - fst_ab) > 1e-9:
                            a2 = False
                    if alpha in (0.1, 0.25, 0.5, 0.75, 0.8, 0.9):
                        print("    %-6.2f %-7d %-10.5f %-10.5f %-9s %-9.5f %-9.5f"
                              % (alpha, g_c, fst_ca, corpus,
                                 "None" if rel is None else "%+.4f" % rel,
                                 num_ratio, den_ratio))
            # A4b: perturb alpha 1% inside the corpus formula only
            alpha = 0.5
            pc = alpha * pa + (1 - alpha) * pb
            fst_ca = hudson_fst(pc, pa)
            base = ((1 - alpha) ** 2 * fst_ab - fst_ca) / fst_ca
            pert = ((1 - 1.01 * alpha) ** 2 * fst_ab - fst_ca) / fst_ca
            if abs(pert - base) < 5e-3:
                a4b = False
            print("    A4b alpha perturbed 1%%: rel err %+.5f -> %+.5f (moves %.5f)"
                  % (base, pert, abs(pert - base)))
    print("  A2 endpoints        : %s" % ("PASS" if a2 else "FAIL"))
    print("  A4a numerator ident.: %s" % ("PASS" if a4a else "FAIL"))
    print("  A4b check can fail  : %s" % ("PASS" if a4b else "FAIL"))
    out["A_admixed_fst"] = rowsA
    out["controls_partA"] = {
        "A1_mixing_sampled": a1rows, "A1_pass": bool(a1),
        "A2_endpoints_pass": bool(a2),
        "A3_drift_only": a3rows, "A3_pass": bool(a3),
        "A4a_numerator_identity_pass": bool(a4a),
        "A4b_check_can_fail_pass": bool(a4b),
    }

    # ------------------------------------------------------------------
    print("")
    print("CONTROLS -- PART B (the two factors of (1-r)(1-1/2Ne), split)")
    REPS_B, GENS_B = 4000, 40
    PA, QA, PB, QB, AL = 0.8, 0.7, 0.2, 0.15, 0.5

    ret, _ = ld_retention(AL, PA, QA, PB, QB, None, 0.02, GENS_B, 50, rng)
    b1 = ret is not None and abs(ret - 0.98) < 1e-9
    print("  B1 recombination only: retention %.9f vs (1-r) %.9f -> %s"
          % (ret, 0.98, "PASS" if b1 else "FAIL"))

    NE_B = 200
    ret2, _ = ld_retention(AL, PA, QA, PB, QB, NE_B, 0.0, GENS_B, 30000, rng)
    want2 = 1.0 - 1.0 / (2.0 * NE_B)
    b2 = ret2 is not None and abs(ret2 - want2) < 0.004
    print("  B2 drift only        : retention %.6f vs (1-1/2Ne) %.6f -> %s"
          % (ret2, want2, "PASS" if b2 else "FAIL"))

    out["controls_partB"] = {"B1_recomb_only": ret, "B1_expected": 0.98,
                             "B1_pass": bool(b1),
                             "B2_drift_only": ret2, "B2_expected": want2,
                             "B2_pass": bool(b2)}

    # ------------------------------------------------------------------
    print("")
    print("B. ADMIXTURE LD AT GENERATION 0  (admixtureLD, admixtureLDTwoLocus)")
    rowsB0 = []
    b0worst = 0.0
    for alpha in (0.1, 0.25, 0.5, 0.75, 0.9):
        for (pa_, qa_, pb_, qb_) in ((0.9, 0.8, 0.1, 0.2), (0.5, 0.5, 0.2, 0.9),
                                     (0.3, 0.7, 0.25, 0.65)):
            x = admixed_pool(alpha, pa_, qa_, pb_, qb_, 1)
            meas = float(d_of(x)[0])
            corpus = alpha * (1 - alpha) * (pa_ - pb_) * (qa_ - qb_)
            b0worst = max(b0worst, abs(meas - corpus))
            rowsB0.append({"alpha": alpha, "p_A": pa_, "q_A": qa_, "p_B": pb_,
                           "q_B": qb_, "D_measured": meas,
                           "D_corpus_admixtureLD": corpus,
                           "abs_err": abs(meas - corpus)})
    b0 = b0worst < 1e-14
    print("  D(0) vs alpha(1-alpha) dp dq: max abs err %.3e -> %s"
          % (b0worst, "EXACT" if b0 else "MISMATCH"))
    out["B0_ld_at_gen0"] = {"rows": rowsB0, "max_abs_err": b0worst,
                            "exact": bool(b0)}

    print("")
    print("C. ADMIXTURE LD DECAY  (admixtureLDDecay = (1-r)^g)")
    print("   r grid straddles 1/(2Ne) = %.5f" % (1.0 / (2.0 * NE_B)))
    print("   %-8s %-11s %-11s %-11s %-9s %-9s"
          % ("r", "measured", "corpus(1-r)", "(1-r)(1-1/2N)", "err_corp", "err_true"))
    rowsC = []
    for r in (0.0, 0.00125, 0.0025, 0.005, 0.02, 0.1, 0.5):
        ret, traj = ld_retention(AL, PA, QA, PB, QB, NE_B, r, GENS_B, 30000, rng)
        if ret is None:
            continue
        corpus = 1.0 - r
        truth = (1.0 - r) * (1.0 - 1.0 / (2.0 * NE_B))
        rowsC.append({"r": r, "Ne": NE_B, "retention_measured": ret,
                      "retention_corpus_admixtureLDDecay": corpus,
                      "retention_with_drift": truth,
                      "rel_err_corpus": (corpus - ret) / ret,
                      "rel_err_with_drift": (truth - ret) / ret,
                      "D_trajectory_head": traj[:6]})
        print("   %-8.5f %-11.6f %-11.6f %-11.6f %-+9.4f %-+9.4f"
              % (r, ret, corpus, truth, (corpus - ret) / ret, (truth - ret) / ret))
    out["C_ld_decay"] = rowsC

    # admixtureLDBoost: the quotient inherits the numerator's bias exactly
    print("")
    print("D. admixtureLDBoost = admixtureLDDecay / equilibrium_ld")
    rowsD = []
    for r in (0.0025, 0.02, 0.1):
        for g in (5, 20, 40):
            eq = 0.25
            corpus_boost = (1.0 - r) ** g / eq
            true_boost = ((1.0 - r) * (1.0 - 1.0 / (2.0 * NE_B))) ** g / eq
            rowsD.append({"r": r, "g": g, "equilibrium_ld": eq,
                          "boost_corpus": corpus_boost,
                          "boost_with_drift": true_boost,
                          "rel_err": (corpus_boost - true_boost) / true_boost})
            print("   r=%-8.4f g=%-4d corpus %.5f  with drift %.5f  rel %+.4f"
                  % (r, g, corpus_boost, true_boost,
                     (corpus_boost - true_boost) / true_boost))
    out["D_ld_boost"] = {
        "note": "admixtureLDBoost is a quotient whose denominator is supplied "
                "by the caller, so it has no error of its own; it inherits "
                "the numerator's, which is what the column shows. The "
                "equilibrium_ld = 0.25 here is an arbitrary stand-in and the "
                "relative error is independent of it.",
        "rows": rowsD}

    ok_all = bool(a1 and a2 and a3 and a4a and a4b and b1 and b2)
    out["READ_THE_TEST"] = ok_all
    print("")
    print("READ_THE_TEST (all seven controls): %s" % ok_all)
    fh = open("fam_admixture_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_admixture_results.json")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
