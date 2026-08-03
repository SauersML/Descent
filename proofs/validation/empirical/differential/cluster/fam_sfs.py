#!/usr/bin/env python3
"""Family simulator: SITE FREQUENCY SPECTRUM (coalescent, msprime).

Run with the popgen venv:
    /projects/standard/hsiehph/sauer354/popgenv/bin/python fam_sfs.py

WHY THIS FILE EXISTS
    families.py records site_frequency_spectrum as an EMPTY family: the
    reference `refs.sfs_expected_counts` exists and checks nothing, because
    `singletonProportion` was removed from the corpus. An empty family is not
    coverage, and a reference that checks nothing is not a check. Rather than
    leave it empty, this file goes and FINDS the corpus's frequency-spectrum
    claims, which do not have "spectrum" in their names:

      expectedNewMutations (θ t) = θ t / 2
          PopulationGeneticsFoundations.lean:772. Its docstring says outright
          "the expected number of new segregating sites is ~θt/2" -- a claim
          about the spectrum, stated in the language of mutation influx.
          Empirical status in the corpus: UNTESTED.
      expectedFreqDiffSq (fst p0) = 2 fst p0 (1-p0)
          AncestrySpecificArchitecture.lean. A claim about the SECOND MOMENT
          of the frequency distribution after divergence.
      scaledMutationRate / theta = 4 Ne μ
          checked here only as the bridge that makes the two above
          commensurable with a simulated population; it belongs to the
          mutation_drift_balance family and no verdict about it is claimed.

THE DISTINCTION THE FIRST DEFINITION DOES NOT DRAW
    "New mutations that ARISE" and "sites that are SEGREGATING" are different
    numbers by a large factor, and θt/2 is the first. Under neutrality a new
    mutation is lost with probability 1 - 1/(2N) per generation of its early
    life; the standing count of segregating sites in a SAMPLE of n is
    θ · Σ_{i=1}^{n-1} 1/i, which does not grow with t at all once equilibrium
    is reached. So the definition and the observable it is named for agree only
    while t is short enough that nothing has been lost or fixed. The simulator
    varies t across that boundary, which is the axis the definition cannot see:
    IT TAKES t BUT NOT n AND NOT Ne SEPARATELY FROM θ.

CONTROLS -- split so each isolates one factor
    C1 SPECTRUM SHAPE, EXACT AND CANONICAL: E[η_i] = θ/i for i = 1..n-1.
       This is exact under the standard neutral model, so a deviation is a
       simulator defect, not a modelling choice. Isolates: does the SHAPE of
       the simulated spectrum match the coalescent?
    C2 SPECTRUM SCALE: E[S] = θ Σ 1/i (Watterson). Isolates the TOTAL, which
       C1 normalises away. C1 and C2 are split on purpose: a simulator with
       the mutation rate wrong by 2x passes C1 (shape is right) and fails C2.
    C3 SINGLETON PROPORTION = (1/1)/Σ 1/i, sample-size dependent and free of θ.
       Isolates n-dependence from θ-dependence. Together C2 and C3 pin the two
       factors that C1 alone confounds.
    C4 POSITIVE CONTROL: the same comparison is run against a spectrum from a
       population with exponential growth, where E[η_i] = θ/i is KNOWN to be
       wrong (growth shifts weight to singletons). The check must REJECT it.
       Without C4, "C1 passed" would be consistent with a check that passes on
       everything.

CAN-FAIL CLAUSE ON THE GRID
    The t axis runs from t = 0.02·(2Ne) to t = 8·(2Ne). Below the first, almost
    nothing has been lost and θt/2 is nearly right; above the last the sample
    spectrum has been stationary for generations. A grid confined to either end
    would validate a formula that is wrong at the other. Both ends are run.

SPEED
    Mutations are placed with msprime.sim_mutations on ancestries that are
    simulated once per cell; the SFS comes from ts.allele_frequency_spectrum,
    which is computed inside tskit rather than in Python. Nothing loops over
    replicates in Python except the ancestry calls themselves.
"""

import os

# PIN THE THREAD POOLS BEFORE numpy IS IMPORTED. numpy/BLAS otherwise take
# every core on a SHARED node, and with several agents on one machine that
# contention gets misdiagnosed as someone else's deadlock. These workloads are
# memory-bound, so single-threading costs essentially nothing here. Set in the
# script rather than only on the command line, because an invocation that
# forgets the environment would silently go back to taking the whole node.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import json
import math
import os
import sys

import msprime
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.normpath(os.path.join(HERE, "..", "..", "extract"))
DIFF = os.path.normpath(os.path.join(HERE, ".."))
for _p in (EXTRACT, DIFF):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import api      # noqa: E402  -- corpus bodies, not my retyping of them
import refs     # noqa: E402  -- the closed-form SFS reference already in-tree


def call(name, *pos):
    """Evaluate a corpus definition POSITIONALLY.

    Not by keyword: `api.callable_for` returns the PYTHON names, and Lean
    binders like `θ` and `μ` are renamed by translate.pyname, so a keyword call
    would break on exactly the two definitions this file exists to check.
    Positional order is the Lean signature's explicit-binder order.
    """
    fn, args = api.callable_for(name)
    if len(pos) != len(args):
        raise RuntimeError("%s takes %d args %r, got %d"
                           % (name, len(args), args, len(pos)))
    return float(fn(*pos))


# Replicates are the unit of independence: sites along a recombining sequence
# are linked, so 3500 segregating sites are nowhere near 3500 observations and
# the standard error has to come from the spread ACROSS replicates. Eight was
# too few to give that spread a shape; thirty is the number the sigma-based
# controls below are judged with.
REPS = 30
SEQ = 5_000_000
RHO = 1e-8


def sfs_of(ts, n):
    """Unfolded, un-normalised SFS counts η_1..η_{n-1} for n sample haplotypes."""
    a = ts.allele_frequency_spectrum(mode="site", polarised=True,
                                     span_normalise=False)
    return np.asarray(a[1:n])


# ===========================================================================
# CONTROLS 1-3: neutral spectrum shape, scale and singleton proportion.
# ===========================================================================

def controls_neutral():
    """EACH CONTROL IS JUDGED AGAINST ITS OWN MONTE CARLO NOISE.

    A fixed threshold on a Monte Carlo quantity reports the run's precision
    rather than its correctness -- the mistake fam_coalescent.py records having
    made at its t = 0 cell. Sites along a recombining sequence are LINKED, so
    the number of sites is not the number of independent observations and a
    binomial standard error would be far too small. The replicate is the unit
    of independence here, so every statistic is computed PER REPLICATE and the
    spread across replicates supplies the standard error.

    Cells also get INDEPENDENT SEEDS. Sharing seeds across the mu = 1e-8 and
    mu = 2e-8 cells would place the same trees under both, and three cells that
    agree because they are the same trees would look like three confirmations.
    """
    rows = []
    for cell, (Ne, mu, n) in enumerate(((5000, 1e-8, 20), (5000, 2e-8, 20),
                                        (5000, 1e-8, 40))):
        theta_per_site = call("scaledMutationRate", float(Ne), mu)
        theta_total = theta_per_site * SEQ
        per_rep = []
        for r in range(REPS):
            seed = 1_000_000 * (cell + 1) + r
            ts = msprime.sim_ancestry(samples=n // 2, population_size=Ne,
                                      sequence_length=SEQ,
                                      recombination_rate=RHO,
                                      random_seed=seed)
            ts = msprime.sim_mutations(ts, rate=mu, random_seed=seed + 7)
            per_rep.append(sfs_of(ts, n))
        per_rep = np.asarray(per_rep)                  # (REPS, n-1)
        eta = per_rep.mean(axis=0)
        pred = np.asarray(refs.sfs_expected_counts(n, theta_total))

        # --- C2 SCALE: total segregating sites vs Watterson -----------------
        S_rep = per_rep.sum(axis=1)
        S_meas = float(S_rep.mean())
        S_sem = float(S_rep.std(ddof=1)) / np.sqrt(REPS)
        S_pred = float(pred.sum())
        scale_rel = (S_pred - S_meas) / S_meas
        scale_sigmas = (S_pred - S_meas) / S_sem if S_sem else float("inf")

        # --- C1 SHAPE: normalised spectrum, worst bin, in sigmas ------------
        shape_rep = per_rep / S_rep[:, None]
        shape_meas = shape_rep.mean(axis=0)
        shape_sem = shape_rep.std(axis=0, ddof=1) / np.sqrt(REPS)
        shape_pred = pred / pred.sum()
        shape_sig = np.abs(shape_meas - shape_pred) / np.where(shape_sem > 0,
                                                               shape_sem, 1e-12)
        worst = int(np.argmax(shape_sig))
        shape_err = float(np.max(np.abs(shape_meas - shape_pred)))

        # --- C3 SINGLETONS: proportion, n only, theta-free ------------------
        sing_rep = per_rep[:, 0] / S_rep
        sing_meas = float(sing_rep.mean())
        sing_sem = float(sing_rep.std(ddof=1)) / np.sqrt(REPS)
        sing_pred = refs.sfs_singleton_proportion(n)
        sing_sigmas = (sing_pred - sing_meas) / sing_sem if sing_sem \
            else float("inf")

        rows.append({"Ne": Ne, "mu": mu, "n": n, "replicates": REPS,
                     "theta_total": theta_total,
                     "S_measured": S_meas, "S_sem": S_sem,
                     "S_watterson": S_pred,
                     "scale_rel_err": scale_rel,
                     "scale_deviation_in_sems": scale_sigmas,
                     "shape_max_abs_dev": shape_err,
                     "shape_worst_bin": worst + 1,
                     "shape_worst_deviation_in_sems": float(shape_sig[worst]),
                     "singleton_prop_measured": sing_meas,
                     "singleton_prop_sem": sing_sem,
                     "singleton_prop_expected": sing_pred,
                     "singleton_rel_err": (sing_pred - sing_meas) / sing_meas,
                     "singleton_deviation_in_sems": sing_sigmas})
        print("  Ne=%d mu=%.0e n=%d | S %.1f+-%.1f vs Watterson %.1f "
              "(%+.2f%%, %.2f sems) | shape worst bin %d at %.2f sems "
              "(max abs dev %.4f) | singletons %.4f+-%.4f vs %.4f "
              "(%+.2f%%, %.2f sems)"
              % (Ne, mu, n, S_meas, S_sem, S_pred, 100 * scale_rel,
                 scale_sigmas, worst + 1, shape_sig[worst], shape_err,
                 sing_meas, sing_sem, sing_pred,
                 100 * (sing_pred - sing_meas) / sing_meas, sing_sigmas))
    SIG = 4.0
    c1 = all(abs(r["shape_worst_deviation_in_sems"]) < SIG for r in rows)
    c2 = all(abs(r["scale_deviation_in_sems"]) < SIG for r in rows)
    c3 = all(abs(r["singleton_deviation_in_sems"]) < SIG for r in rows)
    print("  CONTROL 1 spectrum SHAPE  (theta/i, normalised): %s"
          % ("PASS" if c1 else "FAIL"))
    print("  CONTROL 2 spectrum SCALE  (Watterson total):     %s"
          % ("PASS" if c2 else "FAIL"))
    print("  CONTROL 3 SINGLETON proportion (n only, no theta): %s"
          % ("PASS" if c3 else "FAIL"))
    print("  (all three at %.0f standard errors of the replicate spread, not "
          "a fixed percentage)" % SIG)
    return (c1, c2, c3), rows


# ===========================================================================
# CONTROL 4 -- POSITIVE CONTROL. The same check, run where theta/i is WRONG.
# ===========================================================================

def control_positive():
    """The SAME sigma criterion that stayed silent on neutral data, on growth.

    Deliberately the identical statistic and the identical 4-sigma rule as
    controls 1 and 3. If the threshold were relaxed here, or the statistic
    changed, "it passed there and failed here" would be about the threshold
    rather than about the data.
    """
    Ne, mu, n = 5000, 1e-8, 20
    per_rep = []
    for r in range(REPS):
        d = msprime.Demography()
        d.add_population(name="A", initial_size=Ne, growth_rate=0.01)
        ts = msprime.sim_ancestry(samples={"A": n // 2}, demography=d,
                                  sequence_length=SEQ, recombination_rate=RHO,
                                  random_seed=4_000_000 + r)
        ts = msprime.sim_mutations(ts, rate=mu, random_seed=4_000_007 + r)
        per_rep.append(sfs_of(ts, n))
    per_rep = np.asarray(per_rep)
    S_rep = per_rep.sum(axis=1)
    shape_rep = per_rep / S_rep[:, None]
    shape_meas = shape_rep.mean(axis=0)
    shape_sem = shape_rep.std(axis=0, ddof=1) / np.sqrt(REPS)
    pred = np.asarray(refs.sfs_expected_counts(n, 1.0))
    shape_pred = pred / pred.sum()
    sig = np.abs(shape_meas - shape_pred) / np.where(shape_sem > 0, shape_sem,
                                                     1e-12)
    worst = int(np.argmax(sig))
    dev = float(np.max(np.abs(shape_meas - shape_pred)))
    sing_rep = per_rep[:, 0] / S_rep
    sing_meas = float(sing_rep.mean())
    sing_sem = float(sing_rep.std(ddof=1)) / np.sqrt(REPS)
    sing_pred = refs.sfs_singleton_proportion(n)
    sing_sig = abs(sing_pred - sing_meas) / sing_sem if sing_sem else float("inf")
    rejected = bool(float(sig[worst]) >= 4.0)
    print("  C4 exponential growth (r=0.01): worst bin %d at %.2f sems "
          "(max abs dev %.4f) | singletons %.4f+-%.4f vs neutral %.4f "
          "(%.2f sems) -> %s"
          % (worst + 1, sig[worst], dev, sing_meas, sing_sem, sing_pred,
             sing_sig, "REJECTED as required" if rejected else "NOT REJECTED"))
    print("  CONTROL 4 positive control (check can fail): %s"
          % ("PASS" if rejected else "FAIL"))
    return rejected, {"shape_max_abs_dev": dev,
                      "shape_worst_bin": worst + 1,
                      "shape_worst_deviation_in_sems": float(sig[worst]),
                      "singleton_prop_measured": sing_meas,
                      "singleton_prop_sem": sing_sem,
                      "singleton_prop_neutral": sing_pred,
                      "singleton_deviation_in_sems": sing_sig,
                      "rejected": rejected}


# ===========================================================================
# DEFINITION 1 -- expectedNewMutations (θ t) = θ t / 2, whose docstring reads
# "the expected number of new segregating sites is ~θt/2".
#
# Measured: mutations that AROSE in the last t generations and are still
# SEGREGATING in a sample of n, from a population at equilibrium. Both counts
# are reported, because the gap between them IS the finding.
# ===========================================================================

def definition_expected_new_mutations():
    out = []
    Ne, mu, n = 2000, 1e-8, 20
    theta_per_site = call("scaledMutationRate", float(Ne), mu)
    theta_total = theta_per_site * SEQ
    twoNe = 2.0 * Ne
    for tfrac in (0.02, 0.1, 0.5, 2.0, 8.0):
        t = tfrac * twoNe
        arose, segregating = [], []
        for r in range(REPS):
            ts = msprime.sim_ancestry(samples=n // 2, population_size=Ne,
                                      sequence_length=SEQ,
                                      recombination_rate=RHO,
                                      random_seed=200 + r)
            ts = msprime.sim_mutations(ts, rate=mu, random_seed=400 + r)
            recent = 0
            recent_seg = 0
            for site in ts.sites():
                for m in site.mutations:
                    if m.time <= t:
                        recent += 1
            # count sites whose (single) mutation is younger than t and which
            # are polymorphic in the sample
            for v in ts.variants():
                if v.genotypes.sum() == 0 or v.genotypes.sum() == n:
                    continue
                ms = ts.site(v.site.id).mutations
                if ms and min(mm.time for mm in ms) <= t:
                    recent_seg += 1
            arose.append(recent)
            segregating.append(recent_seg)
        # theta*t/2 with t in units of generations and theta the POPULATION
        # scaled rate over the same sequence.
        pred = call("expectedNewMutations", theta_total, t)
        m_seg = float(np.mean(segregating))
        m_arose = float(np.mean(arose))
        # THE OTHER READING, stated so the finding cannot be mistaken for a
        # claim that the arithmetic is wrong. The number of mutations that
        # ARISE anywhere in the population over t generations is
        # 2*Ne*mu*L*t, and theta*t/2 = (4 Ne mu L) t / 2 is exactly that. So
        # the formula is EXACT for mutations-that-arise and the docstring
        # names a different observable ("new segregating sites"). The gap
        # below is the gap between the two observables, not an algebra error.
        population_arisings = 2.0 * Ne * mu * SEQ * t
        out.append({"Ne": Ne, "n": n, "t_generations": t,
                    "population_wide_arisings_2_Ne_mu_L_t":
                        population_arisings,
                    "identity_check_theta_t_over_2_equals_arisings":
                        abs(pred - population_arisings) <= 1e-6 * pred,
                    "t_over_2Ne": tfrac,
                    "theta_total": theta_total,
                    "corpus_expectedNewMutations": pred,
                    "measured_mutations_in_sample_genealogy_younger_than_t":
                        m_arose,
                    "measured_segregating_sites_younger_than_t": m_seg,
                    "watterson_equilibrium_S":
                        theta_total * sum(1.0 / i for i in range(1, n)),
                    "ratio_prediction_over_segregating":
                        pred / m_seg if m_seg else None})
        print("  t=%8.0f (%.2f x 2Ne)  corpus theta*t/2 = %10.1f  |  "
              "segregating-in-sample younger than t = %8.1f  |  ratio %8.1fx"
              % (t, tfrac, pred, m_seg, pred / m_seg if m_seg else float("nan")))
    print("  Watterson equilibrium S for this sample = %.1f -- the observable "
          "the docstring NAMES stops growing in t, while theta*t/2 does not."
          % (theta_total * sum(1.0 / i for i in range(1, n))))
    print("  theta*t/2 IS exactly 2*Ne*mu*L*t, the count of mutations that "
          "ARISE population-wide. The defect is scope, not arithmetic: the "
          "formula is right for one observable and the docstring names "
          "another.")
    return out


# ===========================================================================
# DEFINITION 2 -- expectedFreqDiffSq (fst p0) = 2 fst p0 (1-p0).
#
# THE CORPUS SCOPES ITS ARGUMENT AND THE FIRST VERSION OF THIS CHECK IGNORED
# IT. AncestrySpecificArchitecture.lean says in prose, above the definition,
# that p0 is "the ancestral frequency" and that F_ST is the DRIFT F_ST defined
# by Var(p_t - p0) = p0(1-p0)·F_ST. The first version used the mean of the two
# present-day frequencies as a stand-in for p0 and the Hudson estimator for
# F_ST, and got -11%, +15.7%, -2.2% -- numbers that move around because the
# stand-ins move around, not because the definition does. Reporting those as a
# discrepancy would have been a finding about my proxy.
#
# So the ancestral frequency is now OBSERVED, by drawing ANCIENT SAMPLES from
# the ancestral population at the split time. Nothing is proxied.
#
# SPLIT INTO TWO CONTROLS, because the definition makes two claims:
#   D2a SINGLE-POPULATION DRIFT. Var(p1 - p0) / [p0(1-p0)] must equal the drift
#       F_ST, 1 - exp(-t/(2Ne)). This is driftVariance's claim and it involves
#       no factor of 2 and no independence assumption.
#   D2b THE FACTOR OF 2 AND INDEPENDENCE. E[(p1-p2)^2] must be TWICE that.
#       This is the step the definition's own prose calls "independence of
#       drift".
# A combined check would pass if the drift variance were low by the same
# factor the independence step were high. The two are therefore separated, and
# the F_ST fed to the corpus definition is the THEORETICAL 1 - exp(-t/(2Ne)),
# not one estimated from the same data, so the comparison cannot be circular.
# ===========================================================================

def definition_expected_freq_diff_sq():
    """SAMPLING VARIANCE IS SUBTRACTED, NOT LEFT IN THE ANSWER.

    The uncorrected version of this measurement reported D2a off by -24.4% and
    the two-population/one-population ratio at 1.70 instead of 2 at the
    shortest divergence, and BOTH were my estimator rather than the corpus.
    Frequencies are estimated from finite samples, so

        E[(p1_hat - p2_hat)^2] = Var_drift(p1 - p2) + p1q1/(n1-1) + p2q2/(n2-1)

    and the sampling terms do not cancel in the ratio: the two-population
    contrast carries two of them and the ancestor contrast carries two as well
    while having only HALF the drift, so the ratio is dragged toward 1 exactly
    when drift is small. That is why the deviation shrank monotonically as t
    grew -- the signature of a sample-size artefact, not of a formula.

    Every second moment below is therefore the unbiased estimator with its
    sampling term removed, and the sample sizes are doubled so the residual
    correction is small compared with the quantity being corrected.
    """
    out = []
    Ne, n, n_anc = 2000, 200, 200
    for tfrac in (0.05, 0.2, 0.8):
        t = tfrac * 2.0 * Ne
        p1s, p2s, p0s = [], [], []
        for r in range(REPS):
            d = msprime.Demography()
            d.add_population(name="A", initial_size=Ne)
            d.add_population(name="B", initial_size=Ne)
            d.add_population(name="ANC", initial_size=Ne)
            d.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
            ts = msprime.sim_ancestry(
                samples=[
                    msprime.SampleSet(n // 2, population="A", time=0),
                    msprime.SampleSet(n // 2, population="B", time=0),
                    # ANCIENT SAMPLE: the ancestral population, AT the split
                    # time. This is p0 itself, not a stand-in for it.
                    msprime.SampleSet(n_anc // 2, population="ANC", time=t),
                ],
                demography=d, sequence_length=SEQ,
                recombination_rate=1e-8, random_seed=6_100_000 + r)
            ts = msprime.sim_mutations(ts, rate=2e-8,
                                       random_seed=6_200_000 + r)
            sa = ts.samples(population=0)
            sb = ts.samples(population=1)
            sanc = ts.samples(population=2)
            G = ts.genotype_matrix()
            p1s.append(G[:, sa].mean(axis=1))
            p2s.append(G[:, sb].mean(axis=1))
            p0s.append(G[:, sanc].mean(axis=1))
        p1 = np.concatenate(p1s)
        p2 = np.concatenate(p2s)
        p0 = np.concatenate(p0s)
        # Condition on being POLYMORPHIC IN THE ANCESTOR, which is the
        # population the definition's p0 refers to. Ascertaining on the
        # ancestral sample is the ascertainment the definition assumes; using
        # the descendants would condition on the very drift being measured.
        keep = (p0 > 0.05) & (p0 < 0.95)
        p1, p2, p0 = p1[keep], p2[keep], p0[keep]
        # UNBIASED SAMPLING-VARIANCE CORRECTIONS. n, n and n_anc are numbers of
        # HAPLOTYPES, so the per-site sampling variance of a frequency estimate
        # is p(1-p)/(n-1) and E[p_hat(1-p_hat)] = p(1-p)(n-1)/n.
        s1 = p1 * (1 - p1) / (n - 1.0)
        s2 = p2 * (1 - p2) / (n - 1.0)
        s0 = p0 * (1 - p0) / (n_anc - 1.0)
        het0 = float(np.mean(p0 * (1.0 - p0)) * n_anc / (n_anc - 1.0))
        het0_raw = float(np.mean(p0 * (1.0 - p0)))
        d2 = float(np.mean((p1 - p2) ** 2 - s1 - s2))
        d2_raw = float(np.mean((p1 - p2) ** 2))
        # D2a: single-population drift variance, averaged over the two
        # daughters so the two are not treated as one observation.
        var1 = float(np.mean((p1 - p0) ** 2 - s1 - s0))
        var2 = float(np.mean((p2 - p0) ** 2 - s2 - s0))
        var1_raw = float(np.mean((p1 - p0) ** 2))
        var2_raw = float(np.mean((p2 - p0) ** 2))
        fst_drift_measured = 0.5 * (var1 + var2) / het0
        fst_drift_uncorrected = 0.5 * (var1_raw + var2_raw) / het0_raw
        fst_theory = 1.0 - np.exp(-t / (2.0 * Ne))
        # D2b: the corpus definition, fed the THEORETICAL drift F_ST.
        # p0 enters as p0(1-p0), and E[p0(1-p0)] is NOT E[p0](1-E[p0]), so the
        # per-site form is summed rather than the mean substituted.
        pred = 2.0 * fst_theory * het0
        pred_via_corpus_body = float(np.mean(
            [call("expectedFreqDiffSq", float(fst_theory), float(x))
             for x in p0[:20000]]))
        out.append({"t_over_2Ne": tfrac, "t_generations": t, "Ne": Ne,
                    "n_haplotypes_per_daughter": n,
                    "n_haplotypes_ancestral": n_anc,
                    "n_sites_polymorphic_in_ancestor": int(p1.size),
                    "mean_p0_times_1_minus_p0": het0,
                    "sampling_corrections_applied": True,
                    "uncorrected_E_freq_diff_sq": d2_raw,
                    "uncorrected_drift_fst": fst_drift_uncorrected,
                    "measured_E_freq_diff_sq": d2,
                    "measured_single_pop_drift_var_A": var1,
                    "measured_single_pop_drift_var_B": var2,
                    "D2a_measured_drift_fst": fst_drift_measured,
                    "D2a_theory_drift_fst": float(fst_theory),
                    "D2a_rel_err": (float(fst_theory) - fst_drift_measured)
                        / fst_drift_measured,
                    "D2b_corpus_prediction": pred,
                    "D2b_corpus_prediction_per_site_body":
                        pred_via_corpus_body,
                    "D2b_rel_err": (pred - d2) / d2,
                    "D2b_ratio_two_pop_over_one_pop":
                        d2 / (0.5 * (var1 + var2))})
        print("  t=%.2f x 2Ne  sites=%6d  E[p0(1-p0)]=%.5f" %
              (tfrac, p1.size, het0))
        print("     D2a drift F_ST: measured %.5f  theory 1-exp(-t/2Ne) %.5f  "
              "(%+.2f%%)   [uncorrected estimator would say %.5f]"
              % (fst_drift_measured, fst_theory,
                 100 * (fst_theory - fst_drift_measured) / fst_drift_measured,
                 fst_drift_uncorrected))
        print("     D2b E[(p1-p2)^2] = %.5f   corpus 2*F*p0(1-p0) = %.5f "
              "(%+.2f%%)   two-pop/one-pop ratio %.4f (definition says 2)"
              % (d2, pred, 100 * (pred - d2) / d2,
                 d2 / (0.5 * (var1 + var2))))
    return out


def main():
    res = {"family": "site_frequency_spectrum",
           "was": "EMPTY -- no simulator and no definitions (families.py)",
           "covers": ["expectedNewMutations", "expectedFreqDiffSq"],
           "used_but_not_adjudicated": ["scaledMutationRate"]}
    print("CONTROLS 1-3 -- NEUTRAL SPECTRUM, SPLIT INTO SHAPE / SCALE / n")
    (c1, c2, c3), res["controls_neutral"] = controls_neutral()
    print("")
    print("CONTROL 4 -- POSITIVE CONTROL (theta/i must be REJECTED under growth)")
    c4, res["control_positive"] = control_positive()
    print("")
    print("DEFINITION -- expectedNewMutations, theta*t/2, docstring says "
          "'new segregating sites'")
    res["expected_new_mutations"] = definition_expected_new_mutations()
    print("")
    print("DEFINITION -- expectedFreqDiffSq, 2*fst*p0*(1-p0)")
    res["expected_freq_diff_sq"] = definition_expected_freq_diff_sq()

    res["controls"] = {"spectrum_shape_theta_over_i": bool(c1),
                       "spectrum_scale_watterson": bool(c2),
                       "singleton_proportion": bool(c3),
                       "positive_control_growth_rejected": bool(c4)}
    res["READ_THE_TEST"] = bool(c1 and c2 and c3 and c4)
    fh = open(os.path.join(HERE, "fam_sfs_results.json"), "w")
    json.dump(res, fh, indent=1)
    fh.close()
    print("")
    print("READ_THE_TEST: %s   -> fam_sfs_results.json" % res["READ_THE_TEST"])
    return 0 if res["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
