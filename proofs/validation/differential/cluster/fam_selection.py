#!/usr/bin/env python3
"""Family simulator: SELECTION REGIMES (forward Wright-Fisher, vectorized).

Run with the popgen venv:
    /projects/standard/hsiehph/sauer354/popgenv/bin/python fam_selection.py

WHY A FORWARD SIMULATOR
    Every member of this family is a DETERMINISTIC recursion or its fixed
    point. msprime cannot check any of them -- the coalescent is neutral. SLiM
    is not installed and is not needed: the models here are one-locus, so a
    Wright-Fisher generation is one line of array arithmetic.

WHAT IS COVERED
    continent-island (directional selection against migration):
        continentIslandStepSelectionFirst, continentIslandStepMigrationFirst,
        selectionMigrationEquilibrium,
        selectionMigrationEquilibriumMigrationFirst
    mutation-selection balance:
        mutationSelectionStepRare, mutationSelectionBalance,
        mutationSelectionStepRecessive, mutationSelectionBalanceRecessive
    stabilizing selection on a quantitative trait:
        effectVarianceRecurrence, equilibriumEffectVariance,
        stabilizingSelectedArchitectureVariance
    NOT covered, deliberately: selectedDriftFactor. `s_correction` is a free
    parameter no model in the corpus derives, so any measurement can be fitted.
    coverage.py already lists it UNREACHABLE and this run does not disturb that.

THE DIFFERENCE THE DEFINITIONS CANNOT SEE: POPULATION SIZE.
    Not one member of this family takes N. Every one therefore predicts the
    same equilibrium frequency in a population of 100 and of 10^6. Drift does
    not merely add noise around the deterministic fixed point: at a boundary it
    is absorbing, and near mutation-selection balance the stationary MEAN of a
    Wright-Fisher chain is not its deterministic fixed point. The N axis is the
    test. A single-N run cannot fail.

CONTROL DISCIPLINE -- each control isolates ONE factor
    C1 ALGEBRA ONLY, NO DRIFT, NO SELECTION-MIGRATION COUPLING.
       Iterate the corpus's own step map deterministically (N = infinity) and
       check it converges to the corpus's own closed form. This isolates
       "closed form solves the recurrence" from "the recurrence is right".
       It is the control that must pass before any disagreement below can be
       read as being about population genetics.
    C2 DRIFT-FREE LIMIT OF THE STOCHASTIC SIMULATOR.
       Run the SAME Wright-Fisher code at N = 10^7, where drift is negligible,
       and require it to reproduce C1. This isolates "the simulator implements
       the model" from "drift matters". If C2 failed, every N-dependence below
       would be a coding error rather than a finding.
    C3 SELECTION OFF.
       s = 0 with mutation only must give q -> mu_forward/(mu_forward +
       mu_back); with mu = 0 and s = 0 the mean frequency must be a martingale.
       Isolates the drift/mutation half of the update from the selection half.
    C4 MUTATION OFF, SELECTION ON, DETERMINISTIC.
       q must go to 0. Isolates the selection half.
    C1-C4 SPLIT WHAT A COMBINED "does the simulator reproduce mu/(hs)" CONTROL
    WOULD FUSE: a code that got the selection step wrong by the same factor it
    got the mutation step wrong would pass the combined check and fail C3/C4.

POSITIVE CONTROL ON THE NULL (C5)
    Where this run reports "no discrepancy", it must be shown the comparison
    COULD have found one. C5 feeds the checker a deliberately corrupted
    prediction (s -> 1.3 s) and requires it to be flagged. A check that cannot
    fail on a wrong input is not evidence about the right one.

CAN-FAIL CLAUSE ON THE GRID
    mu/(h*s + mu) and the textbook mu/(h*s) agree to within mu/(hs) of each
    other -- i.e. they CONVERGE as s grows. A grid confined to large s would
    validate both. The grid therefore runs down to h*s = 3e-4 with mu = 1e-5,
    where mu/(hs) = 0.0333 and mu/(hs+mu) = 0.0323: a 3.2% separation the
    run below resolves. Likewise the N axis spans 5x10^2 to 10^6, which at
    h*s = 3e-4 is 4N(hs) from 0.6 to 1200 -- drift-dominated to
    selection-dominated. The drift-free end is control 2, at N = 10^7.

SPEED
    VECTORIZED OVER REPLICATES. A Wright-Fisher generation for R independent
    replicates is ONE np.random.binomial call on an array of R, not a Python
    loop of R calls. Every regime below is (n_cells, n_replicates) arrays
    advanced together, so wall time scales with GENERATIONS, not with
    generations x replicates.

    The second lever is TIME-AVERAGING. Once burnt in, the chain is
    stationary, so each further generation is another draw and precision is
    bought with generations that are already being paid for. Every equilibrium
    number below is a per-replicate time average over a sampling window equal
    to the burn-in, then averaged across replicates. This RAISES precision at
    fixed cost; it is not a reduction of replicates, tolerances or grid.
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
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.normpath(os.path.join(HERE, "..", "..", "extract"))
if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

# THE PREDICTIONS ARE THE CORPUS'S OWN BODIES, NOT MY TRANSCRIPTION OF THEM.
# Retyping `max 0 ((s - m - m*s)/s)` into Python is a second chance to get it
# wrong, and a typo there would be reported as a population-genetics finding.
# api.callable_for compiles the Lean body itself.
import api  # noqa: E402


def lean(name):
    fn, args = api.callable_for(name)
    return fn, args


LEAN = {}
for _n in ("continentIslandStepSelectionFirst",
           "continentIslandStepMigrationFirst",
           "selectionMigrationEquilibrium",
           "selectionMigrationEquilibriumMigrationFirst",
           "mutationSelectionStepRare",
           "mutationSelectionBalance",
           "mutationSelectionStepRecessive",
           "mutationSelectionBalanceRecessive",
           "effectVarianceRecurrence",
           "equilibriumEffectVariance"):
    try:
        LEAN[_n] = lean(_n)
    except Exception as exc:                                # pragma: no cover
        LEAN[_n] = None
        print("WARNING: could not load %s from the corpus: %s" % (_n, exc))


def call(name, *pos):
    """Evaluate a corpus definition POSITIONALLY, in Lean binder order.

    Not by keyword: api.callable_for hands back the PYTHON names, and Lean
    binders that are not legal Python (θ, μ, p₁) are renamed by translate.
    Positional order is the one thing that is stable.
    """
    fn, args = LEAN[name]
    if len(pos) != len(args):
        raise RuntimeError("%s takes %d args %r, got %d"
                           % (name, len(args), args, len(pos)))
    return float(fn(*pos))


RNG = np.random.default_rng(20260802)


# ===========================================================================
# The two Wright-Fisher kernels. Both take and return an ARRAY of frequencies.
# ===========================================================================

def wf_continent_island(p, s, m, N, order):
    """One generation: deterministic step from the corpus, then binomial drift.

    `p` is an array of R replicate frequencies advanced simultaneously. `N` is
    the number of DIPLOID individuals, so 2N gene copies are sampled.
    N = None means the infinite-population (deterministic) limit.
    """
    if order == "selection_first":
        # selection: p(1+s)/(1+sp); then migration: (1-m)*p
        p = p * (1.0 + s) / (1.0 + s * p)
        p = (1.0 - m) * p
    else:
        p = (1.0 - m) * p
        p = p * (1.0 + s) / (1.0 + s * p)
    if N is None:
        return p
    return RNG.binomial(2 * N, np.clip(p, 0.0, 1.0)) / (2.0 * N)


def wf_mutation_selection(q, mu, s, h, N, recessive, mu_back=0.0):
    """One generation of mutation + selection + drift on the DERIVED allele q.

    Selection is applied on genotype frequencies under HWE with fitnesses
    (1, 1-hs, 1-s) for (AA, Aa, aa); the corpus's rare-allele step maps are the
    small-q limits of exactly this, which is the point of comparison.
    """
    if recessive:
        w = 1.0 - s * q * q
        q = (q * (1.0 - s * q)) / np.where(w <= 0, 1e-300, w)
    else:
        wbar = 1.0 - 2.0 * h * s * q * (1.0 - q) - s * q * q
        num = q * (1.0 - h * s) * (1.0 - q) + q * q * (1.0 - s)
        q = num / np.where(wbar <= 0, 1e-300, wbar)
    q = q * (1.0 - mu_back) + mu * (1.0 - q)
    if N is None:
        return q
    return RNG.binomial(2 * N, np.clip(q, 0.0, 1.0)) / (2.0 * N)


# ===========================================================================
# CONTROL 0 -- IS THE VECTORIZED DRAW THE SAME DRAW?
#
# Vectorizing over replicates is only sound if the batched form is
# DISTRIBUTIONALLY IDENTICAL to R separate simulations. It is fast either way;
# it is correct only if the draws are independent across replicates and have
# the same per-replicate law. The trap is shared random state -- a batched step
# that reuses one variate across replicates runs just as fast, agrees on the
# mean, and has error bars that mean nothing because the replicates are
# correlated.
#
# Selection makes this sharper than plain drift: the fitness reweighting is
# per-replicate, so the batched form has more places to differ. This control
# does not assume; it measures.
#
#   A. SAME LAW. Run the vectorized kernel for R replicates and a SCALAR loop
#      of R independent single-replicate simulations with the same parameters,
#      and compare the two samples with a two-sample Kolmogorov-Smirnov
#      statistic. Same mean is not enough -- a correlated batch matches the
#      mean exactly. The whole distribution is compared.
#   B. INDEPENDENT ACROSS REPLICATES. The mean absolute pairwise correlation
#      between replicate trajectories must be at the level expected from
#      finite trajectory length, not at the level of a shared variate.
#      A batch sharing one binomial draw would score near 1 here and near 0 on
#      the mean, which is exactly why A alone is not sufficient.
# ===========================================================================

def control_vectorization_identity():
    R, GENS = 600, 400
    s, m, N = 0.10, 0.05, 200

    # vectorized: one binomial call per generation over an array of R
    p_vec = np.full(R, 0.45)
    traj = np.empty((GENS, R))
    for g in range(GENS):
        p_vec = wf_continent_island(p_vec, s, m, N, "selection_first")
        traj[g] = p_vec

    # scalar: R independent single-replicate simulations, one at a time
    p_sca = np.empty(R)
    for i in range(R):
        p = np.array([0.45])
        for _ in range(GENS):
            p = wf_continent_island(p, s, m, N, "selection_first")
        p_sca[i] = p[0]

    # A. two-sample KS statistic
    a = np.sort(p_vec)
    b = np.sort(p_sca)
    allv = np.concatenate([a, b])
    cdf_a = np.searchsorted(a, allv, side="right") / R
    cdf_b = np.searchsorted(b, allv, side="right") / R
    ks = float(np.max(np.abs(cdf_a - cdf_b)))
    # 99.9% critical value for two samples of size R
    ks_crit = 1.949 * np.sqrt(2.0 / R)

    # B. independence across replicates, measured on the trajectories
    dev = traj[GENS // 2:] - traj[GENS // 2:].mean(axis=0, keepdims=True)
    sd = dev.std(axis=0)
    ok_cols = sd > 0
    C = np.corrcoef(dev[:, ok_cols].T)
    off = C[~np.eye(C.shape[0], dtype=bool)]
    mean_abs_corr = float(np.mean(np.abs(off)))
    # trajectories of length GENS/2 with autocorrelation give |r| ~ a few
    # times 1/sqrt(effective length); a SHARED variate would give ~1.
    corr_bound = 0.25

    ok = bool(ks < ks_crit and mean_abs_corr < corr_bound)
    print("  C0a KS(vectorized, scalar-loop) = %.4f   99.9%% critical %.4f  %s"
          % (ks, ks_crit, "PASS" if ks < ks_crit else "FAIL"))
    print("  C0a means %.6f vs %.6f, sds %.6f vs %.6f  (means alone cannot "
          "detect a shared variate; the KS statistic can)"
          % (p_vec.mean(), p_sca.mean(), p_vec.std(), p_sca.std()))
    print("  C0b mean |pairwise corr| across replicate trajectories = %.4f  "
          "(a shared draw would give ~1) %s"
          % (mean_abs_corr, "PASS" if mean_abs_corr < corr_bound else "FAIL"))
    print("  CONTROL 0 (vectorized draw is the same draw): %s"
          % ("PASS" if ok else "FAIL"))
    return ok, {"replicates": R, "generations": GENS,
                "ks_statistic": ks, "ks_critical_999": float(ks_crit),
                "mean_vectorized": float(p_vec.mean()),
                "mean_scalar_loop": float(p_sca.mean()),
                "sd_vectorized": float(p_vec.std()),
                "sd_scalar_loop": float(p_sca.std()),
                "mean_abs_pairwise_corr": mean_abs_corr,
                "corr_bound": corr_bound}


# ===========================================================================
# CONTROL 1 -- ALGEBRA. Deterministic iteration of the corpus step map must
# reach the corpus closed form. Isolates: does the closed form solve the
# recurrence? Nothing stochastic, nothing of mine, in this control.
# ===========================================================================

def control_algebra():
    rows = []
    for (s, m) in ((0.10, 0.05), (0.10, 0.08), (0.20, 0.02), (0.05, 0.04)):
        for order, stepname, eqname in (
                ("selection_first", "continentIslandStepSelectionFirst",
                 "selectionMigrationEquilibrium"),
                ("migration_first", "continentIslandStepMigrationFirst",
                 "selectionMigrationEquilibriumMigrationFirst")):
            fn, argn = LEAN[stepname]
            p = 0.5
            # convergence rate is at worst (1-m) per generation; 40000 steps is
            # e^-800 at the slowest cell on this grid.
            for _ in range(40000):
                p = float(fn(**dict(zip(argn, (s, m, p)))))
            closed = call(eqname, s, m)
            rows.append({"s": s, "m": m, "order": order,
                         "iterated_fixed_point": p, "closed_form": closed,
                         "abs_err": abs(p - closed)})
    for (mu, s, h) in ((1e-5, 0.01, 0.5), (1e-5, 3e-4 / 0.5, 0.5),
                       (1e-6, 0.001, 0.2)):
        fn, argn = LEAN["mutationSelectionStepRare"]
        q = 0.0
        # the map contracts at rate (1 - h*s - mu); iterate 40 e-foldings so
        # the residual is below 1e-17 relative, far under the 1e-6 tolerance.
        for _ in range(int(40.0 / (h * s + mu))):
            q = float(fn(**dict(zip(argn, (mu, s, h, q)))))
        closed = call("mutationSelectionBalance", mu, s, h)
        rows.append({"mu": mu, "s": s, "h": h, "order": "rare_additive",
                     "iterated_fixed_point": q, "closed_form": closed,
                     "abs_err": abs(q - closed)})
    for (mu, s) in ((1e-5, 0.01), (1e-6, 0.05)):
        fn, argn = LEAN["mutationSelectionStepRecessive"]
        closed = call("mutationSelectionBalanceRecessive", mu, s)
        q = 0.0
        # contraction rate near the fixed point is (1 - 2 s q* - mu).
        for _ in range(int(40.0 / (2 * s * closed + mu))):
            q = float(fn(**dict(zip(argn, (mu, s, q)))))
        rows.append({"mu": mu, "s": s, "order": "rare_recessive",
                     "iterated_fixed_point": q, "closed_form": closed,
                     "abs_err": abs(q - closed)})
    ok = all(r["abs_err"] <= 1e-9 + 1e-6 * abs(r["closed_form"]) for r in rows)
    for r in rows:
        print("  C1 %-22s %-16s iterated %.8g   closed %.8g   |d| %.2g"
              % (r["order"],
                 "s=%g m=%g" % (r["s"], r["m"]) if "m" in r
                 else "mu=%g s=%g" % (r["mu"], r["s"]),
                 r["iterated_fixed_point"], r["closed_form"], r["abs_err"]))
    print("  CONTROL 1 (closed form solves the corpus recurrence): %s"
          % ("PASS" if ok else "FAIL"))
    return ok, rows


# ===========================================================================
# CONTROL 2 -- the stochastic simulator at N = 10^7 must reproduce control 1.
# Isolates: is the Wright-Fisher code the same model as the recurrence?
# ===========================================================================

def control_driftfree():
    rows = []
    R = 400
    BIG = 10 ** 7
    for (s, m, order) in ((0.10, 0.05, "selection_first"),
                          (0.10, 0.05, "migration_first"),
                          (0.20, 0.02, "selection_first")):
        p = np.full(R, 0.5)
        for _ in range(4000):
            p = wf_continent_island(p, s, m, BIG, order)
        pred = call("selectionMigrationEquilibrium" if order == "selection_first"
                    else "selectionMigrationEquilibriumMigrationFirst", s, m)
        mean = float(p.mean())
        rows.append({"s": s, "m": m, "order": order, "N": BIG,
                     "measured": mean, "predicted": pred,
                     "rel_err": (pred - mean) / mean if mean else None})
        print("  C2 %-16s s=%.2f m=%.3f  N=1e7 measured %.6f  corpus %.6f  "
              "rel %+.4f%%" % (order, s, m, mean, pred,
                               100 * (pred - mean) / mean if mean else float("nan")))
    ok = all(abs(r["rel_err"]) < 0.002 for r in rows)
    print("  CONTROL 2 (simulator == recurrence when drift is off): %s"
          % ("PASS" if ok else "FAIL"))
    return ok, rows


# ===========================================================================
# CONTROL 3 -- SELECTION OFF. Isolates the mutation+drift half.
# CONTROL 4 -- MUTATION OFF, DETERMINISTIC. Isolates the selection half.
# ===========================================================================

def control_halves():
    rows = []
    # C3a: s = 0, two-way mutation -> q* = mu/(mu + nu), independent of N.
    mu, nu, N, R = 1e-3, 3e-3, 2000, 4000
    q = np.zeros(R)
    for _ in range(40000):
        q = wf_mutation_selection(q, mu, 0.0, 0.5, N, False, mu_back=nu)
    want = mu / (mu + nu)
    got = float(q.mean())
    c3a = abs(got - want) < 4.0 * float(q.std()) / np.sqrt(R) + 1e-3
    rows.append({"control": "s=0 two-way mutation", "measured": got,
                 "expected": want, "pass": bool(c3a)})
    print("  C3a s=0, mu=%.0e nu=%.0e: measured q=%.5f  expected %.5f  %s"
          % (mu, nu, got, want, "PASS" if c3a else "FAIL"))

    # C3b: s = 0, mu = 0 -> pure drift, E[q] is a martingale (mean preserved).
    q = np.full(20000, 0.3)
    for _ in range(500):
        q = wf_mutation_selection(q, 0.0, 0.0, 0.5, 500, False)
    got = float(q.mean())
    sem = float(q.std()) / np.sqrt(q.size)
    c3b = abs(got - 0.3) < 4 * sem
    rows.append({"control": "pure drift martingale", "measured": got,
                 "expected": 0.3, "sem": sem, "pass": bool(c3b)})
    print("  C3b pure drift: E[q] %.5f +- %.5f vs 0.30000  %s"
          % (got, sem, "PASS" if c3b else "FAIL"))

    # C4: mutation off, selection on, deterministic -> q -> 0.
    q = np.array([0.4])
    for _ in range(20000):
        q = wf_mutation_selection(q, 0.0, 0.02, 0.5, None, False)
    c4 = float(q[0]) < 1e-6
    rows.append({"control": "mu=0 deterministic selection -> 0",
                 "measured": float(q[0]), "expected": 0.0, "pass": bool(c4)})
    print("  C4  mu=0, s=0.02 deterministic: q=%.3g  %s"
          % (q[0], "PASS" if c4 else "FAIL"))
    ok = c3a and c3b and c4
    print("  CONTROLS 3-4 (halves isolated): %s" % ("PASS" if ok else "FAIL"))
    return ok, rows


# ===========================================================================
# REGIME 1 -- continent-island. Vary N, which no member takes.
#
# PRECISION COMES FROM TIME-AVERAGING, NOT FROM MORE REPLICATES. The chain is
# stationary after burn-in, so every subsequent generation is another draw from
# the stationary distribution. Averaging R replicates over G sampling
# generations is far more information than one snapshot of R x (something)
# replicates at the same cost, because the cost is set by GENERATIONS. The
# reported SEM is the between-replicate SEM of the per-replicate time average,
# which is honest about the within-chain autocorrelation that a naive
# R*G-independent-draws count would not be.
# ===========================================================================

def regime_continent_island():
    out = []
    R = 4000
    BURN, SAMP = 3000, 3000
    for (s, m) in ((0.10, 0.05), (0.10, 0.08), (0.05, 0.04)):
        for order in ("selection_first", "migration_first"):
            pred = call("selectionMigrationEquilibrium"
                        if order == "selection_first"
                        else "selectionMigrationEquilibriumMigrationFirst",
                        s, m)
            for N in (100, 1000, 10000, 10 ** 6):
                p = np.full(R, min(0.9, max(pred, 0.05)))
                for _ in range(BURN):
                    p = wf_continent_island(p, s, m, N, order)
                acc = np.zeros(R)
                lost_acc = np.zeros(R)
                for _ in range(SAMP):
                    p = wf_continent_island(p, s, m, N, order)
                    acc += p
                    lost_acc += (p <= 0)
                per_rep = acc / SAMP
                mean = float(per_rep.mean())
                sem = float(per_rep.std()) / np.sqrt(R)
                lost = float((lost_acc / SAMP).mean())
                out.append({"s": s, "m": m, "order": order, "N": N,
                            "replicates": R, "burn_in": BURN,
                            "sampling_generations": SAMP,
                            "measured_mean_freq": mean, "sem": sem,
                            "loss_fraction": lost,
                            "corpus_prediction": pred,
                            "rel_err": (pred - mean) / mean if mean > 0 else None})
                print("  s=%.2f m=%.3f %-16s N=%-8d  E[p]=%.5f +-%.5f  "
                      "lost=%4.1f%%  corpus %.5f  rel %+8.2f%%"
                      % (s, m, order, N, mean, sem, 100 * lost, pred,
                         100 * (pred - mean) / mean if mean > 0 else float("nan")))
    return out


# ===========================================================================
# REGIME 2 -- mutation-selection balance. Vary N and reach the regime where
# mu/(hs+mu) and the textbook mu/(hs) SEPARATE.
# ===========================================================================

def regime_mutation_selection():
    out = []
    R = 4000
    for (mu, hs) in ((1e-5, 3e-4), (1e-5, 1e-3), (1e-5, 1e-2), (1e-4, 1e-2)):
        h = 0.5
        s = hs / h
        corpus = call("mutationSelectionBalance", mu, s, h)
        textbook = mu / hs
        for N in (500, 5000, 50000, 10 ** 6):
            burn = int(6.0 / hs)
            samp = int(6.0 / hs)
            gens = burn + samp
            q = np.full(R, corpus)
            for _ in range(burn):
                q = wf_mutation_selection(q, mu, s, h, N, False)
            acc = np.zeros(R)
            for _ in range(samp):
                q = wf_mutation_selection(q, mu, s, h, N, False)
                acc += q
            q = acc / samp
            mean = float(q.mean())
            sem = float(q.std()) / np.sqrt(R)
            out.append({"mu": mu, "s": s, "h": h, "hs": hs, "N": N,
                        "gens": gens, "replicates": R,
                        "burn_in": burn, "sampling_generations": samp,
                        "measured_mean_freq": mean, "sem": sem,
                        "corpus_mutationSelectionBalance": corpus,
                        "textbook_mu_over_hs": textbook,
                        "rel_err_corpus": (corpus - mean) / mean if mean else None,
                        "rel_err_textbook": (textbook - mean) / mean if mean else None,
                        "corpus_vs_textbook_separation":
                            (textbook - corpus) / corpus})
            print("  mu=%.0e hs=%.0e N=%-8d E[q]=%.6f +-%.6f | corpus %.6f "
                  "(%+.2f%%) | mu/hs %.6f (%+.2f%%) | forms differ by %.2f%%"
                  % (mu, hs, N, mean, sem, corpus,
                     100 * (corpus - mean) / mean if mean else float("nan"),
                     textbook,
                     100 * (textbook - mean) / mean if mean else float("nan"),
                     100 * (textbook - corpus) / corpus))
    # recessive
    for (mu, s) in ((1e-5, 0.01), (1e-5, 0.001)):
        corpus = call("mutationSelectionBalanceRecessive", mu, s)
        textbook = np.sqrt(mu / s)
        for N in (5000, 50000, 10 ** 6):
            # contraction near q* is 2 s q*, so this is 6 e-foldings of burn-in
            # and 6 more of sampling.
            burn = int(6.0 / (2 * s * corpus))
            samp = burn
            gens = burn + samp
            q = np.full(R, corpus)
            for _ in range(burn):
                q = wf_mutation_selection(q, mu, s, None, N, True)
            acc = np.zeros(R)
            for _ in range(samp):
                q = wf_mutation_selection(q, mu, s, None, N, True)
                acc += q
            q = acc / samp
            mean = float(q.mean())
            sem = float(q.std()) / np.sqrt(R)
            out.append({"mu": mu, "s": s, "h": "recessive", "N": N,
                        "gens": gens, "replicates": R,
                        "burn_in": burn, "sampling_generations": samp,
                        "measured_mean_freq": mean, "sem": sem,
                        "corpus_mutationSelectionBalanceRecessive": corpus,
                        "textbook_sqrt_mu_over_s": float(textbook),
                        "rel_err_corpus": (corpus - mean) / mean if mean else None})
            print("  RECESSIVE mu=%.0e s=%.0e N=%-8d E[q]=%.6f +-%.6f | "
                  "corpus %.6f (%+.2f%%) | sqrt(mu/s) %.6f"
                  % (mu, s, N, mean, sem, corpus,
                     100 * (corpus - mean) / mean if mean else float("nan"),
                     textbook))
    return out


# ===========================================================================
# REGIME 3 -- stabilizing selection on a quantitative trait.
#
# effectVarianceRecurrence is `V' = (1-s) V + v_mut`, whose fixed point is
# `v_mut / s` = equilibriumEffectVariance. The algebra is one line, so a check
# that iterated the recurrence and got its own fixed point would measure
# nothing. THE CLAIM WITH CONTENT IS THE LINEARITY: the recurrence says the
# per-generation variance loss is a CONSTANT FRACTION `s` of standing variance,
# the same fraction at every V. Neither definition takes V, so both assert this.
#
# WHAT IS MEASURED: an individual-based population under Gaussian stabilizing
# selection, and the REALIZED loss fraction loss/V at several standing
# variances. If loss/V is flat in V, `s` is a parameter and the recurrence is
# structurally right. If loss/V rises with V, `s` is not a constant of the
# model and v_mut/s is a small-variance limit that neither signature declares.
#
# THIS CAN FAIL IN BOTH DIRECTIONS and nothing here is imposed: selection acts
# on sampled phenotypes by resampling parents in proportion to fitness, and the
# variance loss is read off afterwards rather than substituted in. An earlier
# draft of this function computed the loss from Bulmer's formula and then
# divided by V to get s -- that made v_mut/s = V an identity and would have
# passed for any model whatever. It is recorded here because the difference
# between the two versions is invisible in a results file.
# ===========================================================================

def regime_stabilizing():
    out = []
    L = 200            # loci
    N = 1000           # diploids
    REPS = 6
    Ve = 1.0
    for Vs in (2.0, 10.0, 50.0):
        eff = np.sqrt(1.0 / L) * np.ones(L)
        # start at several standing variances so loss/V is measured across a
        # RANGE of V rather than at one point -- the whole test is the slope.
        g0 = np.zeros((REPS, N, L), dtype=np.int8)
        for start_p in (0.5, 0.2, 0.05):
            g0[:] = (RNG.random((REPS, N, L)) < start_p).astype(np.int8) \
                + (RNG.random((REPS, N, L)) < start_p).astype(np.int8)
            g = g0.copy()
            rows_V, rows_loss = [], []
            for gen in range(40):
                z = g.astype(np.float32) @ eff.astype(np.float32)
                q = g.mean(axis=(1,)) / 2.0                 # (REPS, L)
                V_before = np.sum(2.0 * q * (1.0 - q) * eff ** 2, axis=1)
                z = z + RNG.normal(0.0, np.sqrt(Ve), size=z.shape)
                w = np.exp(-(z - z.mean(axis=1, keepdims=True)) ** 2
                           / (2.0 * Vs))
                w = w / w.sum(axis=1, keepdims=True)
                # sexual reproduction: two parents drawn w.p. proportional to
                # fitness, one gamete each, free recombination between loci.
                out_g = np.empty_like(g)
                for r in range(REPS):
                    pa = RNG.choice(N, size=N, p=w[r])
                    pb = RNG.choice(N, size=N, p=w[r])
                    ga = RNG.binomial(g[r][pa], 0.5)
                    gb = RNG.binomial(g[r][pb], 0.5)
                    out_g[r] = (ga + gb).astype(np.int8)
                g = out_g
                q2 = g.mean(axis=(1,)) / 2.0
                V_after = np.sum(2.0 * q2 * (1.0 - q2) * eff ** 2, axis=1)
                if gen >= 5:
                    rows_V.append(V_before)
                    rows_loss.append(V_before - V_after)
            Vbar = float(np.mean(rows_V))
            lossbar = float(np.mean(rows_loss))
            frac = lossbar / Vbar if Vbar else float("nan")
            out.append({"Vs": Vs, "N": N, "L": L, "start_p": start_p,
                        "mean_standing_variance_V": Vbar,
                        "mean_per_generation_loss": lossbar,
                        "realized_loss_fraction_s": frac})
            print("  Vs=%-5.1f start_p=%.2f  V=%.5f  loss/gen=%.6f  "
                  "realized s = loss/V = %.5f" % (Vs, start_p, Vbar, lossbar,
                                                  frac))
    # THE CLAIM UNDER TEST: is s constant across V at fixed Vs?
    verdict = []
    for Vs in (2.0, 10.0, 50.0):
        cells = [r for r in out if r["Vs"] == Vs]
        cells.sort(key=lambda r: r["mean_standing_variance_V"])
        lo, hi = cells[0], cells[-1]
        ratio = (hi["realized_loss_fraction_s"]
                 / lo["realized_loss_fraction_s"]
                 if lo["realized_loss_fraction_s"] else float("nan"))
        verdict.append({"Vs": Vs,
                        "V_low": lo["mean_standing_variance_V"],
                        "s_at_V_low": lo["realized_loss_fraction_s"],
                        "V_high": hi["mean_standing_variance_V"],
                        "s_at_V_high": hi["realized_loss_fraction_s"],
                        "s_ratio_high_over_low": ratio})
        print("  Vs=%-5.1f  s(V=%.4f)=%.5f  vs  s(V=%.4f)=%.5f   ratio %.3f"
              % (Vs, lo["mean_standing_variance_V"],
                 lo["realized_loss_fraction_s"],
                 hi["mean_standing_variance_V"],
                 hi["realized_loss_fraction_s"], ratio))
    print("  effectVarianceRecurrence asserts this ratio is 1.000 at every Vs.")
    return {"cells": out, "constancy_of_s": verdict}


# ===========================================================================
# CONTROL 5 -- POSITIVE CONTROL. The comparison must be able to fail.
# ===========================================================================

def control_positive(ms_rows):
    """Corrupt the corpus prediction and require the checker to flag it.

    Applied to the largest-N (10^6) mutation-selection cells, which is exactly where
    this run reports agreement. If a 30% corruption is not flagged there, the
    "no discrepancy" verdict at those cells measures nothing.
    """
    flagged = 0
    tested = 0
    for r in ms_rows:
        if r["N"] != 10 ** 6 or "corpus_mutationSelectionBalance" not in r:
            continue
        tested += 1
        good = r["corpus_mutationSelectionBalance"]
        bad = call("mutationSelectionBalance", r["mu"], 1.3 * r["s"], r["h"])
        m = r["measured_mean_freq"]
        if abs((bad - m) / m) > 0.05 >= abs((good - m) / m):
            flagged += 1
    ok = tested > 0 and flagged == tested
    print("  CONTROL 5 positive control: %d/%d corrupted predictions rejected "
          "while the true one passed: %s"
          % (flagged, tested, "PASS" if ok else "FAIL"))
    return ok, {"tested": tested, "flagged": flagged}


def main():
    res = {"family": "selection_regimes",
           "covers": ["continentIslandStepSelectionFirst",
                      "continentIslandStepMigrationFirst",
                      "selectionMigrationEquilibrium",
                      "selectionMigrationEquilibriumMigrationFirst",
                      "mutationSelectionStepRare", "mutationSelectionBalance",
                      "mutationSelectionStepRecessive",
                      "mutationSelectionBalanceRecessive",
                      "effectVarianceRecurrence",
                      "equilibriumEffectVariance"],
           "not_covered": {"selectedDriftFactor":
                           "free parameter s_correction; already UNREACHABLE "
                           "in coverage.py and not disturbed here"}}
    print("CONTROL 0 -- IS THE VECTORIZED DRAW THE SAME DRAW?")
    c0, res["control_vectorization_identity"] = control_vectorization_identity()
    print("")
    print("CONTROL 1 -- ALGEBRA (no drift, no simulator)")
    c1, res["control_algebra"] = control_algebra()
    print("")
    print("CONTROL 2 -- DRIFT-FREE LIMIT OF THE SIMULATOR")
    c2, res["control_driftfree"] = control_driftfree()
    print("")
    print("CONTROLS 3-4 -- HALVES ISOLATED")
    c34, res["control_halves"] = control_halves()
    print("")
    print("REGIME 1 -- CONTINENT-ISLAND (axis: N, which no member takes)")
    res["continent_island"] = regime_continent_island()
    print("")
    print("REGIME 2 -- MUTATION-SELECTION BALANCE (axis: N; grid reaches where "
          "mu/(hs+mu) and mu/(hs) separate)")
    res["mutation_selection"] = regime_mutation_selection()
    print("")
    print("REGIME 3 -- STABILIZING SELECTION")
    res["stabilizing"] = regime_stabilizing()
    print("")
    print("CONTROL 5 -- POSITIVE CONTROL ON THE NULL")
    c5, res["control_positive"] = control_positive(res["mutation_selection"])

    res["controls"] = {"vectorized_draw_is_the_same_draw": bool(c0),
                       "algebra_closed_form_solves_recurrence": bool(c1),
                       "simulator_equals_recurrence_without_drift": bool(c2),
                       "halves_isolated": bool(c34),
                       "positive_control_can_fail": bool(c5)}
    res["READ_THE_TEST"] = bool(c0 and c1 and c2 and c34 and c5)
    fh = open(os.path.join(HERE, "fam_selection_results.json"), "w")
    json.dump(res, fh, indent=1)
    fh.close()
    print("")
    print("READ_THE_TEST: %s   -> fam_selection_results.json"
          % res["READ_THE_TEST"])
    return 0 if res["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
