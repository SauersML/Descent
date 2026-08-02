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


REPS = 8
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
    rows = []
    for (Ne, mu, n) in ((5000, 1e-8, 20), (5000, 2e-8, 20), (5000, 1e-8, 40)):
        theta_per_site = call("scaledMutationRate", float(Ne), mu)
        acc = np.zeros(n - 1)
        for r in range(REPS):
            ts = msprime.sim_ancestry(samples=n // 2, population_size=Ne,
                                      sequence_length=SEQ,
                                      recombination_rate=RHO,
                                      random_seed=1000 + r)
            ts = msprime.sim_mutations(ts, rate=mu, random_seed=7000 + r)
            acc += sfs_of(ts, n)
        eta = acc / REPS
        theta_total = theta_per_site * SEQ
        pred = np.asarray(refs.sfs_expected_counts(n, theta_total))
        # C1 SHAPE: normalise both to sum 1 and compare.
        shape_meas = eta / eta.sum()
        shape_pred = pred / pred.sum()
        shape_err = float(np.max(np.abs(shape_meas - shape_pred)))
        # C2 SCALE: total segregating sites vs Watterson.
        S_meas = float(eta.sum())
        S_pred = float(pred.sum())
        scale_rel = (S_pred - S_meas) / S_meas
        # C3 SINGLETONS: proportion, sample-size dependent, theta-free.
        sing_meas = float(eta[0] / eta.sum())
        sing_pred = refs.sfs_singleton_proportion(n)
        rows.append({"Ne": Ne, "mu": mu, "n": n,
                     "theta_total": theta_total,
                     "S_measured": S_meas, "S_watterson": S_pred,
                     "scale_rel_err": scale_rel,
                     "shape_max_abs_dev": shape_err,
                     "singleton_prop_measured": sing_meas,
                     "singleton_prop_expected": sing_pred,
                     "singleton_rel_err": (sing_pred - sing_meas) / sing_meas})
        print("  Ne=%d mu=%.0e n=%d | S %.1f vs Watterson %.1f (%+.2f%%) | "
              "shape max dev %.4f | singletons %.4f vs %.4f (%+.2f%%)"
              % (Ne, mu, n, S_meas, S_pred, 100 * scale_rel, shape_err,
                 sing_meas, sing_pred,
                 100 * (sing_pred - sing_meas) / sing_meas))
    c1 = all(r["shape_max_abs_dev"] < 0.02 for r in rows)
    c2 = all(abs(r["scale_rel_err"]) < 0.06 for r in rows)
    c3 = all(abs(r["singleton_rel_err"]) < 0.05 for r in rows)
    print("  CONTROL 1 spectrum SHAPE  (theta/i, normalised): %s"
          % ("PASS" if c1 else "FAIL"))
    print("  CONTROL 2 spectrum SCALE  (Watterson total):     %s"
          % ("PASS" if c2 else "FAIL"))
    print("  CONTROL 3 SINGLETON proportion (n only, no theta): %s"
          % ("PASS" if c3 else "FAIL"))
    return (c1, c2, c3), rows


# ===========================================================================
# CONTROL 4 -- POSITIVE CONTROL. The same check, run where theta/i is WRONG.
# ===========================================================================

def control_positive():
    Ne, mu, n = 5000, 1e-8, 20
    acc = np.zeros(n - 1)
    for r in range(REPS):
        d = msprime.Demography()
        d.add_population(name="A", initial_size=Ne, growth_rate=0.01)
        ts = msprime.sim_ancestry(samples={"A": n // 2}, demography=d,
                                  sequence_length=SEQ, recombination_rate=RHO,
                                  random_seed=3000 + r)
        ts = msprime.sim_mutations(ts, rate=mu, random_seed=9000 + r)
        acc += sfs_of(ts, n)
    eta = acc / REPS
    shape_meas = eta / eta.sum()
    pred = np.asarray(refs.sfs_expected_counts(n, 1.0))
    shape_pred = pred / pred.sum()
    dev = float(np.max(np.abs(shape_meas - shape_pred)))
    sing_meas = float(shape_meas[0])
    sing_pred = refs.sfs_singleton_proportion(n)
    rejected = dev >= 0.02
    print("  C4 exponential growth (r=0.01): shape max dev %.4f (threshold "
          "0.02) singletons %.4f vs neutral %.4f -> %s"
          % (dev, sing_meas, sing_pred,
             "REJECTED as required" if rejected else "NOT REJECTED"))
    print("  CONTROL 4 positive control (check can fail): %s"
          % ("PASS" if rejected else "FAIL"))
    return rejected, {"shape_max_abs_dev": dev,
                      "singleton_prop_measured": sing_meas,
                      "singleton_prop_neutral": sing_pred,
                      "rejected": bool(rejected)}


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
        out.append({"Ne": Ne, "n": n, "t_generations": t,
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
          "STOPS GROWING while theta*t/2 does not."
          % (theta_total * sum(1.0 / i for i in range(1, n))))
    return out


# ===========================================================================
# DEFINITION 2 -- expectedFreqDiffSq (fst p0) = 2 fst p0 (1-p0).
# Measured: E[(p1-p2)^2] across independent sites after a clean split, with
# F_ST measured on the SAME data so the two sides are commensurable.
# ===========================================================================

def definition_expected_freq_diff_sq():
    out = []
    Ne, n = 2000, 100
    for tfrac in (0.05, 0.2, 0.8):
        t = tfrac * 2.0 * Ne
        p1s, p2s = [], []
        for r in range(REPS):
            d = msprime.Demography()
            d.add_population(name="A", initial_size=Ne)
            d.add_population(name="B", initial_size=Ne)
            d.add_population(name="ANC", initial_size=Ne)
            d.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
            ts = msprime.sim_ancestry(samples={"A": n // 2, "B": n // 2},
                                      demography=d, sequence_length=SEQ,
                                      recombination_rate=1e-8,
                                      random_seed=6100 + r)
            ts = msprime.sim_mutations(ts, rate=2e-8, random_seed=6200 + r)
            sa = ts.samples(population=0)
            sb = ts.samples(population=1)
            G = ts.genotype_matrix()
            p1s.append(G[:, sa].mean(axis=1))
            p2s.append(G[:, sb].mean(axis=1))
        p1 = np.concatenate(p1s)
        p2 = np.concatenate(p2s)
        pbar = 0.5 * (p1 + p2)
        keep = (pbar > 0.05) & (pbar < 0.95)      # ancestrally common sites
        p1, p2, pbar = p1[keep], p2[keep], pbar[keep]
        d2 = float(np.mean((p1 - p2) ** 2))
        # Hudson F_ST measured on the same sites, ratio of averages.
        num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n / 2 - 1) \
            - p2 * (1 - p2) / (n / 2 - 1)
        den = p1 * (1 - p2) + p2 * (1 - p1)
        fst = float(num.mean() / den.mean())
        p0 = float(pbar.mean())
        pred = call("expectedFreqDiffSq", fst, p0)
        # p0 in the definition is the ANCESTRAL frequency; using the mean of
        # the present-day mean is the closest observable, and E[p0(1-p0)] is
        # not E[p0](1-E[p0]) -- both are reported so the reader can see which
        # convention the number rests on.
        pred_exp = 2.0 * fst * float(np.mean(pbar * (1 - pbar)))
        out.append({"t_over_2Ne": tfrac, "n_sites": int(p1.size),
                    "measured_E_freq_diff_sq": d2,
                    "measured_hudson_fst": fst,
                    "mean_pbar": p0,
                    "corpus_at_mean_p0": pred,
                    "corpus_at_mean_of_p0_times_1_minus_p0": pred_exp,
                    "rel_err_mean_p0": (pred - d2) / d2,
                    "rel_err_expectation_form": (pred_exp - d2) / d2})
        print("  t=%.2f x 2Ne  sites=%6d  E[(p1-p2)^2]=%.5f  F_ST=%.5f  "
              "2*F*p0(1-p0)=%.5f (%+.1f%%)  2*F*E[p(1-p)]=%.5f (%+.1f%%)"
              % (tfrac, p1.size, d2, fst, pred, 100 * (pred - d2) / d2,
                 pred_exp, 100 * (pred_exp - d2) / d2))
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
