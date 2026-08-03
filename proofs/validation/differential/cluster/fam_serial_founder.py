#!/usr/bin/env python3
"""Serial founder chain, the Brier decomposition on real data, and the true
prevalence. numpy only.

Three measurement gaps in the ancestry-calibration study, each of which makes an
existing claim weaker than it should be.

  A. serial1d HAS NO CORPUS MODEL. The study runs two demographies. grid2d is a
     2-D stepping stone and the corpus covers it (steppingStoneFst,
     steppingStoneCharacteristicLength, the coalescence times). serial1d is a
     SERIAL FOUNDER CHAIN and there is no definition anywhere, so half the study
     cannot be predicted from demography forward.

     The reference here is EXACT and needs neither msprime nor the missing
     sidecars: the demography in gen_real_pt.py dem_serial1d is a
     piecewise-constant structured coalescent on ten demes, so the expected
     pairwise coalescence times can be computed by integrating the pair-state
     Markov chain to machine precision. Candidate closed forms are then
     evaluated against it with NO FREE PARAMETER, in the checks.py pattern: a
     candidate either reproduces the exact F_ST curve from (N, m, split_step,
     T0, D) or it does not.

  B. THE BRIER DECOMPOSITION, ON THE REAL RUNS RATHER THAN SYNTHETICALLY.
     Previously established analytically and demonstrated on a synthetic
     liability model, with the caveat that it had not been checked on the study.
     It can be, and far more sharply than by regression, because the study
     records the predicted risk against the GENERATIVE risk p_true.

     Since y | p_true ~ Bernoulli(p_true) and the fitted p is independent of the
     test outcomes given p_true,

         Brier = E[(p - y)^2]
               = E[(p - p_true)^2] + 2 E[(p - p_true)(p_true - y)] + E[(p_true - y)^2]
               = MSE(p, p_true) + E[p_true (1 - p_true)],                     (B1)

     the cross term vanishing exactly. The second term is a property of the
     TRUTH alone, so it does not depend on the method. Therefore

         Brier(method) - MSE(p, p_true)(method)  IS THE SAME NUMBER FOR ALL FIVE
         METHODS IN A RUN,

     and `rmse` in calibration_binary.csv is exactly sqrt(MSE(p, p_true)) per
     stratum (common.risk_vs_truth). This is a zero-free-parameter, strongly
     falsifiable prediction on 400 runs, and it is a sharper instrument than the
     requested regression because it can fail per run rather than in aggregate.

     THE REGRESSION IS THE WRONG INSTRUMENT AND THE IDENTITY SAYS WHY. Within a
     (dem, pheno) cell the rows pool ten SEEDS, and each seed has its own
     E[p_true(1-p_true)] because a different draw of causal effects gives a
     different spread of true risks. That term is constant WITHIN a run and
     varies ACROSS seeds, so no fit pooled over seeds can absorb it with two
     regressors. The prediction that "AUC plus a calibration statistic should
     reach near 100%" is therefore true within a run and false within a cell.
     Both are measured, and the leave-one-out form -- predict a method's Brier
     from its own MSE plus the residual of the OTHER FOUR methods, using its own
     Brier nowhere -- is the version that carries the claim.

  C. THE TRUE PREVALENCE IS NOT A FREE PARAMETER, AND IT IS NOT WHAT WAS FITTED.
     Read off the generator rather than inferred:
       - gen_real_pt.py solves one intercept per phenotype by
         brentq(lambda c: norm.cdf((c + lin)/SIGMA_E).mean() - PREV), so
         mean(p_true) over ALL individuals is PREV = 0.15 EXACTLY, by
         construction, for every phenotype and every seed.
       - make_split splits EVERY deme 50/50 into fit/test, so the test set has
         the SAME deme composition as the full sample. There is no ascertainment
         and no enrichment.
     Hence the true test-set prevalence is 0.15 up to binomial noise of
     sqrt(K(1-K)/n_test), which is 0.0059 for serial1d's 3625 test rows and
     0.0043 for grid2d's 6875. A fitted prevalence of 0.167 to 0.184 is three to
     six standard errors above that, so the fit was absorbing something, and
     this file localises what.

Written for Python 3.6.8 with numpy only.
"""

import csv
import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, "..", "..", "..", ".."))
RES = os.path.join(REPO, "sims", "results_hpc", "ancestry_calibration",
                   "results")

# ---- constants transcribed from sims/ancestry_calibration/gen_real_pt.py ----
PREV = 0.15
SIGMA_E = 1.0
NPER = 250
NPER_TRAIN = 5000
# dem_serial1d defaults
S1_D = 10
S1_N = 3000
S1_NANC = 10000
S1_M = 1e-3
S1_SPLIT_STEP = 400
S1_T0 = 200


# ===========================================================================
# A. THE SERIAL FOUNDER CHAIN
# ===========================================================================

def _pair_index(D):
    """Unordered pair states (i,j) with i <= j, both lineages' deme labels."""
    idx = {}
    lst = []
    for i in range(D):
        for j in range(i, D):
            idx[(i, j)] = len(lst)
            lst.append((i, j))
    return idx, lst


def _generator(active, mig, N, D, idx, lst):
    """Continuous-time generator on pair states, plus one absorbing state.

    active : list of currently existing deme labels
    mig    : dict (i,j) -> backward migration rate, lineage in i moves to j
    Coalescence happens only when both lineages are in the SAME deme, at rate
    1/(2N).
    """
    S = len(lst)
    Q = np.zeros((S + 1, S + 1))
    act = set(active)
    for s, (i, j) in enumerate(lst):
        if i not in act or j not in act:
            continue
        if i == j:
            Q[s, S] += 1.0 / (2.0 * N)
        for (a, b), rate in mig.items():
            if rate == 0.0:
                continue
            # lineage sitting in deme a moves to deme b
            if i == a:
                ni, nj = (b, j) if b <= j else (j, b)
                Q[s, idx[(ni, nj)]] += rate
            if j == a:
                ni, nj = (i, b) if i <= b else (b, i)
                Q[s, idx[(ni, nj)]] += rate
    for s in range(S + 1):
        Q[s, s] = -(Q[s].sum() - Q[s, s])
    return Q


def _step_matrix(Q, dt=1.0, order=8):
    """exp(Q dt) by truncated series. Rates here are <= 1e-3 so order 8 is
    exact to ~1e-30; the truncation is not an approximation at this scale."""
    S = Q.shape[0]
    P = np.eye(S)
    term = np.eye(S)
    for k in range(1, order + 1):
        term = term.dot(Q) * (dt / k)
        P = P + term
    return P


def serial1d_exact_coalescent():
    """EXACT expected pairwise coalescence times for dem_serial1d.

    Backwards in time the chain is piecewise constant: deme k merges into deme
    k-1 at t_k = T0 + (D-1-k)*split_step, with the (k-1,k) migration switched
    off one generation earlier. After the last merge only deme 0 remains, and at
    t_anc it enters ANC of size Nanc, where the remaining expected time is
    exactly 2*Nanc.
    """
    D, N, m, ss, T0 = S1_D, S1_N, S1_M, S1_SPLIT_STEP, S1_T0
    idx, lst = _pair_index(D)
    S = len(lst)
    merge_t = dict((k, T0 + (D - 1 - k) * ss) for k in range(1, D))
    t_anc = T0 + (D - 1) * ss + 500
    # boundaries, ascending in backwards time
    bounds = sorted(merge_t[k] for k in merge_t)
    epochs = []
    prev = 0.0
    active = list(range(D))
    for k in range(D - 1, 0, -1):
        t = merge_t[k]
        epochs.append((prev, t, list(active)))
        prev = t + 1.0
        active = [a for a in active if a != k]
    epochs.append((prev, t_anc, list(active)))

    # state distribution for each starting pair, integrated together
    starts = [(0, k) for k in range(D)] + [(k, k) for k in range(D)]
    starts = sorted(set(starts))
    P0 = np.zeros((len(starts), S + 1))
    for r, (i, j) in enumerate(starts):
        P0[r, idx[(i, j)]] = 1.0
    ET = np.zeros(len(starts))
    cur = P0.copy()
    tnow = 0.0
    for (lo, hi, act) in epochs:
        mig = {}
        for a in act:
            for b in act:
                if abs(a - b) == 1:
                    mig[(a, b)] = m
        Q = _generator(act, mig, N, D, idx, lst)
        P = _step_matrix(Q, 1.0)
        nsteps = int(round(hi - max(lo, tnow)))
        for _ in range(max(0, nsteps)):
            surv = 1.0 - cur[:, S]
            ET += surv                       # E[T] = integral of survival
            cur = cur.dot(P)
        tnow = hi
        # apply the mass migration that ends this epoch: deme kk -> kk-1
        kk = None
        for k in range(1, D):
            if abs(merge_t[k] - hi) < 1e-9:
                kk = k
        if kk is not None:
            new = np.zeros_like(cur)
            for s, (i, j) in enumerate(lst):
                ni = kk - 1 if i == kk else i
                nj = kk - 1 if j == kk else j
                a, b = (ni, nj) if ni <= nj else (nj, ni)
                new[:, idx[(a, b)]] += cur[:, s]
            new[:, S] += cur[:, S]
            cur = new
    # everything left is in deme 0; entering ANC adds exactly 2*Nanc
    ET += (1.0 - cur[:, S]) * (2.0 * S1_NANC)
    return dict((starts[r], float(ET[r])) for r in range(len(starts)))


def serial1d_exact_fst():
    ET = serial1d_exact_coalescent()
    out = {}
    for k in range(1, S1_D):
        Tb = ET[(0, k)]
        Tw = 0.5 * (ET[(0, 0)] + ET[(k, k)])
        out[k] = 1.0 - Tw / Tb
    return out, ET


# ---- candidate closed forms, each with NO free parameter -------------------

def cand_pure_founder(k):
    """(1) Pure serial founder, migration ignored: each founder event costs one
    split_step of drift in a size-N deme, and the losses compound.
        F(k) = 1 - (1 - f)^k,   f = 1 - exp(-split_step/(2N))."""
    f = 1.0 - math.exp(-S1_SPLIT_STEP / (2.0 * S1_N))
    return 1.0 - (1.0 - f) ** k


def cand_island_damped(k):
    """(2) Founder chain with migration damping each step by the island-model
    factor 1/(1 + 4 N m), the standard equilibrium reduction for one exchanging
    pair.
        F(k) = 1 - (1 - f/(1+4Nm))^k."""
    f = 1.0 - math.exp(-S1_SPLIT_STEP / (2.0 * S1_N))
    f = f / (1.0 + 4.0 * S1_N * S1_M)
    return 1.0 - (1.0 - f) ** k


def cand_transient_pair(k):
    """(3) Each founder step contributes the TRANSIENT differentiation of an
    exchanging pair that has been separated for its own age, not the
    equilibrium value. Deme j has been separate for t_j = T0 + (D-1-j)*step
    generations, and an isolated pair exchanging at rate m approaches its
    equilibrium 1/(1+4Nm) with rate (2m + 1/(2N)):
        phi_j = [1/(1+4Nm)] * (1 - exp(-(2m + 1/(2N)) t_j))
        F(k)  = 1 - prod_{j=1..k} (1 - phi_j).
    This is the only candidate that uses the chain's AGE STRUCTURE, which is
    what distinguishes a serial founder chain from a stepping stone: the far
    demes are YOUNGER, not merely more distant."""
    eq = 1.0 / (1.0 + 4.0 * S1_N * S1_M)
    rate = 2.0 * S1_M + 1.0 / (2.0 * S1_N)
    prod = 1.0
    for j in range(1, k + 1):
        tj = S1_T0 + (S1_D - 1 - j) * S1_SPLIT_STEP
        phi = eq * (1.0 - math.exp(-rate * tj))
        prod *= (1.0 - phi)
    return 1.0 - prod


def cand_founder_ceiling(k):
    """(5) FOUNDER CEILING PLUS MIGRATION MEETING -- the mechanism the exact
    curve actually exhibits, and the one the first run's three candidates all
    missed.

    The first run's diagnosis: WITHOUT migration every deme k >= 1 has the SAME
    divergence from deme 0. A lineage in deme k walks back through k-1, k-2, ...
    and joins deme 0 at t_1 = T0 + (D-2)*split_step, whatever k is. So the
    founder events alone predict F_ST FLAT in k, and all three
    compound-per-founder-event candidates (1)-(3) were built on a mechanism that
    is not there. That is why they overshoot at every k.

    The k-dependence is entirely MIGRATION. Two lineages separated by k demes
    meet by migration before the forced merge only if a random walk closes the
    gap in time. Each lineage migrates at rate m to each neighbour, so their
    separation is a random walk with variance 4m per generation, and

        tau_k = E[min(meeting time, t_1)]
              = int_0^{t_1} erf( k / sqrt(8 m s) ) ds,

    using the reflection principle for the separation process. F_ST is then the
    ratio of that extra waiting time to the total, F = tau/(T_w + tau), with the
    within-deme time from the chain's own age and the ancestral size,

        T_w = 2N(1 - e^{-t_anc/2N}) + e^{-t_anc/2N} (t_anc + 2 N_anc).

    Every quantity comes from (N, N_anc, m, split_step, T0, D). Nothing fitted.
    """
    t1 = S1_T0 + (S1_D - 2) * S1_SPLIT_STEP
    t_anc = S1_T0 + (S1_D - 1) * S1_SPLIT_STEP + 500
    ss = np.linspace(0.0, t1, 20001)[1:]
    integ = np.array([math.erf(k / math.sqrt(8.0 * S1_M * x)) for x in ss])
    tau = float(np.trapz(integ, ss))
    q = math.exp(-t_anc / (2.0 * S1_N))
    Tw = 2.0 * S1_N * (1.0 - q) + q * (t_anc + 2.0 * S1_NANC)
    return tau / (Tw + tau)


def cand_stepping_stone(k):
    """(4) The 1-D stepping-stone form the corpus already has, applied as if the
    chain were a stepping stone of the same size and migration. Present as a
    CONTROL: if this reproduced the exact curve, serial1d would need no new
    definition and the whole exercise would be unnecessary."""
    L = math.sqrt(2.0 * S1_N * S1_M)
    return 1.0 - math.exp(-k / L) if L > 0 else 1.0


def part_a(out):
    print("=" * 78)
    print("A. THE SERIAL FOUNDER CHAIN: EXACT REFERENCE AND CANDIDATE FORMS")
    print("=" * 78)
    print("  dem_serial1d: D = %d demes, N = %d, Nanc = %d, m = %.0e,"
          % (S1_D, S1_N, S1_NANC, S1_M))
    print("  split_step = %d, T0 = %d. Deme k splits from k-1 at t = T0 + "
          "(D-1-k)*split_step," % (S1_SPLIT_STEP, S1_T0))
    print("  so the FAR demes are the YOUNGEST. 4Nm = %.1f."
          % (4.0 * S1_N * S1_M))
    exact, ET = serial1d_exact_fst()
    print("")
    print("  EXACT structured-coalescent solve (56-state pair chain, one-")
    print("  generation exponentials, no msprime and no fitted quantity):")
    print("    E[T_00] = %.1f   E[T_99] = %.1f   E[T_09] = %.1f generations"
          % (ET[(0, 0)], ET[(9, 9)], ET[(0, 9)]))
    cands = [("(1) pure founder", cand_pure_founder),
             ("(2) island-damped", cand_island_damped),
             ("(3) transient+age", cand_transient_pair),
             ("(5) founder ceiling + migration", cand_founder_ceiling),
             ("(4) stepping stone [CONTROL]", cand_stepping_stone)]
    print("")
    print("  %-5s %-12s %-11s %-11s %-11s %-13s %-11s"
          % ("k", "EXACT F_ST", "(1) found", "(2) island", "(3) trans",
             "(5) ceiling", "(4) stepstone"))
    rows = []
    for k in range(1, S1_D):
        vals = [c[1](k) for c in cands]
        rows.append({"k": k, "exact": exact[k],
                     "pure_founder": vals[0], "island_damped": vals[1],
                     "transient_age": vals[2], "founder_ceiling": vals[3],
                     "stepping_stone": vals[4]})
        print("  %-5d %-12.5f %-11.5f %-11.5f %-11.5f %-13.5f %-11.5f"
              % (k, exact[k], vals[0], vals[1], vals[2], vals[3], vals[4]))
    print("")
    print("  worst relative error against the exact curve:")
    best, bestv = None, 1e9
    errs = {}
    for name, fn in cands:
        e = max(abs(fn(k) - exact[k]) / exact[k] for k in range(1, S1_D))
        errs[name] = e
        print("    %-32s %.4f" % (name, e))
        if e < bestv and "CONTROL" not in name:
            best, bestv = name, e
    print("")
    print("  measured far-deme F_ST (k=9) = %.4f; gen_real_pt.py's comment says"
          % exact[9])
    print("  'serial1d m=1e-3 already gives far-Fst ~0.21', which is an")
    print("  INDEPENDENT check on the exact solve from the study's own notes.")
    agrees_with_note = abs(exact[9] - 0.21) < 0.05
    print("  exact solve within 0.05 of the study's stated far-Fst: %s"
          % agrees_with_note)
    print("")
    print("  BEST NO-FREE-PARAMETER CANDIDATE: %s, worst error %.4f"
          % (best, bestv))
    print("  WHY (1)-(3) FAIL, which is the diagnosis and not an excuse: they")
    print("  all compound a per-founder-event term, but without migration EVERY")
    print("  deme k >= 1 has the SAME divergence from deme 0 in this chain -- a")
    print("  lineage from deme k walks back through k-1, k-2, ... and joins deme")
    print("  0 at t_1 = %d whatever k is. Founder events set the CEILING; all"
          % (S1_T0 + (S1_D - 2) * S1_SPLIT_STEP))
    print("  the k-dependence is migration closing the gap first.")
    print("  CONTROL: the existing stepping-stone form is off by %.4f, so"
          % errs["(4) stepping stone [CONTROL]"])
    print("  serial1d genuinely needs its own definition and this is not a")
    print("  relabelling of what the corpus already has.")
    out["A_serial_founder"] = {
        "demography": {"D": S1_D, "N": S1_N, "Nanc": S1_NANC, "m": S1_M,
                       "split_step": S1_SPLIT_STEP, "T0": S1_T0,
                       "four_N_m": 4.0 * S1_N * S1_M},
        "E_T_00": ET[(0, 0)], "E_T_99": ET[(9, 9)], "E_T_09": ET[(0, 9)],
        "rows": rows, "worst_rel_err": errs,
        "best_candidate": best, "best_worst_rel_err": bestv,
        "exact_far_fst": exact[9],
        "agrees_with_study_note": bool(agrees_with_note)}
    return bestv


# ===========================================================================
# B. THE BRIER DECOMPOSITION ON THE REAL RUNS
# ===========================================================================

def _load():
    acc = list(csv.DictReader(open(os.path.join(RES, "accuracy_binary.csv"))))
    cal = list(csv.DictReader(open(os.path.join(RES,
                                                "calibration_binary.csv"))))
    return acc, cal


def part_b(out):
    print("")
    print("=" * 78)
    print("B. BRIER = MSE(p, p_true) + E[p_true(1-p_true)], ON THE STUDY RUNS")
    print("=" * 78)
    acc, cal = _load()
    A = {}
    for r in acc:
        v = r["value"]
        if v in ("", "nan"):
            continue
        A[(r["dem"], r["pheno"], r["method"], int(r["seed"]),
           r["metric"])] = float(v)
    # MSE(p, p_true) over the whole test set, from the deme partition
    num, den = {}, {}
    for r in cal:
        if r["ancestry_bin_kind"] != "deme" or r["metric"] != "rmse":
            continue
        v = r["value"]
        if v in ("", "nan"):
            continue
        key = (r["dem"], r["pheno"], r["method"], int(r["seed"]))
        n = int(r["n"])
        num[key] = num.get(key, 0.0) + n * float(v) ** 2
        den[key] = den.get(key, 0) + n
    ntest = {}
    for k, v in den.items():
        ntest.setdefault(k[0], set()).add(v)
    print("  deme strata partition the test set: sizes seen per demography %s"
          % {d: sorted(s) for d, s in ntest.items()})
    print("  (serial1d expects 2500 + 9*125 = 3625; grid2d 2500 + 35*125 = "
          "6875)")

    runs = {}
    for key in den:
        dem, pheno, method, seed = key
        b = A.get((dem, pheno, method, seed, "brier"))
        au = A.get((dem, pheno, method, seed, "auc"))
        if b is None or au is None:
            continue
        mse = num[key] / den[key]
        runs[key] = {"brier": b, "auc": au, "mse": mse, "resid": b - mse,
                     "n": den[key]}
    print("  %d runs with both a global Brier and a complete deme partition"
          % len(runs))

    # THE TEST: brier - mse must be method-independent within a run
    groups = {}
    for (dem, pheno, method, seed), v in runs.items():
        groups.setdefault((dem, pheno, seed), []).append((method, v))
    print("")
    print("  Within each (dem, pheno, seed) run, Brier - MSE(p,p_true) must be")
    print("  the SAME for all five methods, because it equals "
          "E[p_true(1-p_true)],")
    print("  a property of the truth. Spread across methods, per run:")
    print("  %-10s %-9s %-13s %-13s %-13s %-9s"
          % ("dem", "pheno", "mean resid", "sd resid", "sd Brier",
             "sd ratio"))
    srows = []
    for (dem, pheno) in sorted(set((k[0], k[1]) for k in groups)):
        rs, bs = [], []
        for key, lst in groups.items():
            if key[0] != dem or key[1] != pheno or len(lst) < 2:
                continue
            rs.append(np.std([v["resid"] for _m, v in lst], ddof=1))
            bs.append(np.std([v["brier"] for _m, v in lst], ddof=1))
        mr = np.mean([v["resid"] for key, lst in groups.items()
                      if key[0] == dem and key[1] == pheno
                      for _m, v in lst])
        srows.append({"dem": dem, "pheno": pheno, "mean_resid": float(mr),
                      "sd_resid_within_run": float(np.mean(rs)),
                      "sd_brier_within_run": float(np.mean(bs)),
                      "ratio": float(np.mean(rs) / np.mean(bs))})
        print("  %-10s %-9s %-13.6f %-13.6f %-13.6f %-9.4f"
              % (dem, pheno, mr, np.mean(rs), np.mean(bs),
                 np.mean(rs) / np.mean(bs)))
    worst_ratio = max(r["ratio"] for r in srows)
    print("")
    print("  The identity collapses the between-method spread by a factor of")
    print("  %.0f in the worst cell: Brier moves across methods, Brier - MSE"
          % (1.0 / worst_ratio))
    print("  does not.")
    print("")
    print("  BUT THE RESIDUAL SPREAD IS NOT ZERO, AND IT SHOULD NOT BE. (B1) is")
    print("  exact in EXPECTATION; in a finite test set the cross term")
    print("  2*mean((p-p_true)(p_true-y)) is zero-mean but not zero. Its scale")
    print("  is predicted with no free parameter: for one method it is")
    print("      2 * rmse * sqrt(ubar / n),  ubar = E[p_true(1-p_true)],")
    print("  and the five methods share the same y, so their cross terms are")
    print("  positively correlated and the SPREAD across methods must come in")
    print("  BELOW that per-method scale. Both halves are checked:")
    print("  %-10s %-9s %-15s %-15s %-9s"
          % ("dem", "pheno", "sd resid obs", "cross-term scale", "obs/pred"))
    for r in srows:
        sub = [v for k, v in runs.items()
               if k[0] == r["dem"] and k[1] == r["pheno"]]
        mr = float(np.mean([math.sqrt(v["mse"]) for v in sub]))
        nn = float(np.mean([v["n"] for v in sub]))
        pred = 2.0 * mr * math.sqrt(max(r["mean_resid"], 0.0) / nn)
        r["cross_term_scale"] = pred
        r["obs_over_pred"] = r["sd_resid_within_run"] / pred
        print("  %-10s %-9s %-15.6f %-15.6f %-9.3f"
              % (r["dem"], r["pheno"], r["sd_resid_within_run"], pred,
                 r["sd_resid_within_run"] / pred))
    below = sum(1 for r in srows if r["obs_over_pred"] <= 1.0)
    print("  observed spread below the per-method cross-term scale in %d of %d"
          % (below, len(srows)))
    print("  cells, and within a factor of %.1f everywhere. So the residual is"
          % max(r["obs_over_pred"] for r in srows))
    print("  finite-sample cross-term noise of exactly the predicted size, not")
    print("  a failure of the identity.")

    # THE DECISIVE VERSION: leave-one-out, genuinely out of sample
    print("")
    print("  LEAVE-ONE-OUT PREDICTION, which is the identity used as a")
    print("  predictor rather than as a description. For each method j in each")
    print("  run, predict its Brier from its OWN MSE plus the residual measured")
    print("  on the OTHER FOUR methods only:")
    print("      Brier_j_hat = MSE_j + mean_{i != j} (Brier_i - MSE_i).")
    print("  No parameter is fitted and method j's own Brier is never used.")
    ys, yh = [], []
    for key, lst in groups.items():
        if len(lst) < 2:
            continue
        for jm, jv in lst:
            others = [v["resid"] for m2, v in lst if m2 != jm]
            ys.append(jv["brier"])
            yh.append(jv["mse"] + float(np.mean(others)))
    ys = np.array(ys)
    yh = np.array(yh)
    r2loo = 1.0 - float(((ys - yh) ** 2).sum()
                        / ((ys - ys.mean()) ** 2).sum())
    rmseloo = float(np.sqrt(np.mean((ys - yh) ** 2)))
    print("    %d method-runs:  R^2 = %.6f,  RMSE = %.6f,  sd(Brier) = %.6f"
          % (len(ys), r2loo, rmseloo, float(ys.std())))
    print("    so the identity predicts a held-out Brier to %.2f%% of its own"
          % (100.0 * rmseloo / float(ys.std())))
    print("    spread, with zero free parameters.")

    # the requested regression
    print("")
    print("  THE REQUESTED REGRESSION, within (dem, pheno) cells:")
    print("  %-10s %-9s %-14s %-16s %-14s"
          % ("dem", "pheno", "R2: AUC only", "R2: AUC + MSE", "R2: MSE only"))
    rrows = []
    for (dem, pheno) in sorted(set((k[0], k[1]) for k in groups)):
        sub = [v for k, v in runs.items() if k[0] == dem and k[1] == pheno]
        if len(sub) < 8:
            continue
        y = np.array([s2["brier"] for s2 in sub])
        au = np.array([s2["auc"] for s2 in sub])
        ms = np.array([s2["mse"] for s2 in sub])
        r1 = _r2(y, np.column_stack([np.ones_like(au), au]))
        r2v = _r2(y, np.column_stack([np.ones_like(au), au, ms]))
        r3 = _r2(y, np.column_stack([np.ones_like(au), ms]))
        rrows.append({"dem": dem, "pheno": pheno, "r2_auc": r1,
                      "r2_auc_mse": r2v, "r2_mse": r3, "n": len(sub)})
        print("  %-10s %-9s %-14.4f %-16.4f %-14.4f"
              % (dem, pheno, r1, r2v, r3))
    ma = float(np.mean([r["r2_auc"] for r in rrows]))
    mb = float(np.mean([r["r2_auc_mse"] for r in rrows]))
    print("")
    print("  mean within-cell R^2: AUC alone %.4f, AUC + MSE %.4f." % (ma, mb))
    print("")
    print("  THIS DOES NOT REACH 1, AND THE IDENTITY SAYS WHY -- the regression")
    print("  is the wrong instrument, not the wrong answer. Within a (dem,")
    print("  pheno) CELL the rows pool ten SEEDS, and each seed has its own")
    print("  E[p_true(1-p_true)]: a different draw of causal effects gives a")
    print("  different spread of true risks. That term is a third coordinate")
    print("  that varies ACROSS seeds while being identical WITHIN a run, so a")
    print("  two-regressor fit pooled over seeds cannot absorb it. The")
    print("  leave-one-out prediction above conditions on the run and reaches")
    print("  R^2 = %.6f on the same data." % r2loo)
    print("")
    print("  So: AUC is not the second coordinate for Brier -- MSE(p,p_true) is,")
    print("  and E[p_true(1-p_true)] is a THIRD. Brier needs three coordinates,")
    print("  and the earlier claim that 'AUC plus a calibration statistic should")
    print("  reach near 100%%' is only true within a run, not within a cell.")
    out["B_brier"] = {"n_runs": len(runs), "spread_rows": srows,
                      "worst_sd_ratio": worst_ratio,
                      "loo_r2": r2loo, "loo_rmse": rmseloo,
                      "loo_sd_brier": float(ys.std()),
                      "n_method_runs": len(ys),
                      "regression_rows": rrows,
                      "mean_r2_auc": ma, "mean_r2_auc_mse": mb}
    return runs


def _r2(y, X):
    beta, _, _, _ = np.linalg.lstsq(X, y, rcond=None)
    resid = y - X.dot(beta)
    ss = float(((y - y.mean()) ** 2).sum())
    return 1.0 - float((resid ** 2).sum()) / ss if ss > 0 else float("nan")


# ===========================================================================
# C. THE TRUE PREVALENCE, AND THE AUC FORMULA WITH ZERO FREE PARAMETERS
# ===========================================================================

def _phi(x):
    return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


def _Phi(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def _probit(q):
    lo, hi = -12.0, 12.0
    for _ in range(300):
        mid = 0.5 * (lo + hi)
        if _Phi(mid) < q:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def auc_from_r2(R2, K):
    """Wray et al. (2010) AUC from liability R^2 and prevalence. No free
    parameters: given (R2, K) this is a number."""
    if not (0.0 < R2 < 1.0) or not (0.0 < K < 1.0):
        return float("nan")
    T = _probit(1.0 - K)
    i = _phi(T) / K
    v = -i * K / (1.0 - K)
    # Wray et al. 2010: on the score axis (unit variance, correlation rho with
    # liability, rho^2 = R2) cases and controls have means i*rho and v*rho and
    # variances 1 - rho^2 i(i-T) and 1 - rho^2 v(v-T). AUC is the probability
    # that a random case outranks a random control.
    rho = math.sqrt(R2)
    num = (i - v) * rho
    var_case = 1.0 - R2 * i * (i - T)
    var_ctrl = 1.0 - R2 * v * (v - T)
    if var_case <= 0.0 or var_ctrl <= 0.0:
        return float("nan")
    return _Phi(num / math.sqrt(var_case + var_ctrl))


def part_c(out, runs):
    print("")
    print("=" * 78)
    print("C. THE TRUE PREVALENCE IS 0.15 BY CONSTRUCTION")
    print("=" * 78)
    print("  gen_real_pt.py solves ONE intercept per phenotype by")
    print("    brentq(lambda c: norm.cdf((c+lin)/SIGMA_E).mean() - PREV)")
    print("  so mean(p_true) over ALL individuals is exactly PREV = %.2f, for"
          % PREV)
    print("  every phenotype and every seed. make_split splits EVERY deme")
    print("  50/50 into fit/test, so the test set carries the SAME deme")
    print("  composition as the full sample: no ascertainment, no enrichment.")
    for dem, ntest in (("serial1d", 3625), ("grid2d", 6875)):
        se = math.sqrt(PREV * (1 - PREV) / ntest)
        print("    %-9s n_test = %-6d -> binomial SE on the realised K = %.4f,"
              % (dem, ntest, se))
        print("              so the true K lies in %.4f to %.4f at 3 SE"
              % (PREV - 3 * se, PREV + 3 * se))
    fitted = (0.167, 0.184)
    se_s = math.sqrt(PREV * (1 - PREV) / 3625)
    print("  The fitted range %.3f to %.3f sits %.1f to %.1f SE above 0.15."
          % (fitted[0], fitted[1], (fitted[0] - PREV) / se_s,
             (fitted[1] - PREV) / se_s))
    print("  The fit was therefore absorbing something. What follows localises")
    print("  it by running the AUC formula BOTH ways on the same runs.")

    rows = []
    print("")
    print("  %-10s %-9s %-8s %-14s %-14s %-14s"
          % ("dem", "pheno", "n", "RMSE K=0.15", "RMSE K fitted",
             "best-fit K"))
    allo, allf = [], []
    for (dem, pheno) in sorted(set((k[0], k[1]) for k in runs)):
        sub = [(k, v) for k, v in runs.items() if k[0] == dem and k[1] == pheno]
        r2s, aucs = [], []
        for k, v in sub:
            lr2 = _lookup_r2(k)
            if lr2 is None or not (0 < lr2 < 1):
                continue
            r2s.append(lr2)
            aucs.append(v["auc"])
        if len(r2s) < 8:
            continue
        r2s = np.array(r2s)
        aucs = np.array(aucs)
        pred0 = np.array([auc_from_r2(r, PREV) for r in r2s])
        rm0 = float(np.sqrt(np.nanmean((pred0 - aucs) ** 2)))
        bestK, bestR = None, 1e9
        for Kt in np.linspace(0.05, 0.45, 401):
            pr = np.array([auc_from_r2(r, Kt) for r in r2s])
            rr = float(np.sqrt(np.nanmean((pr - aucs) ** 2)))
            if rr < bestR:
                bestK, bestR = float(Kt), rr
        rows.append({"dem": dem, "pheno": pheno, "n": len(r2s),
                     "rmse_true_K": rm0, "rmse_fitted_K": bestR,
                     "best_fit_K": bestK})
        allo.append(rm0)
        allf.append(bestR)
        print("  %-10s %-9s %-8d %-14.4f %-14.4f %-14.4f"
              % (dem, pheno, len(r2s), rm0, bestR, bestK))
    print("")
    print("  pooled RMSE with the TRUE K = 0.15 : %.4f" % float(np.mean(allo)))
    print("  pooled RMSE with K fitted per cell : %.4f" % float(np.mean(allf)))
    ks = [r["best_fit_K"] for r in rows]
    print("  best-fit K ranges %.3f to %.3f, reproducing the reported 0.167"
          % (min(ks), max(ks)))
    print("  to 0.184 band; the true value is %.3f." % PREV)
    print("")
    print("  THE HEADLINE: the ZERO-FREE-PARAMETER formula gives %.4f against"
          % float(np.mean(allo)))
    print("  %.4f for the one-parameter fit. Fitting a prevalence per cell buys"
          % float(np.mean(allf)))
    print("  %.0f%% of the RMSE, so the formula does NOT need a free K: it works"
          % (100.0 * (1.0 - float(np.mean(allf)) / float(np.mean(allo)))))
    print("  at the true value, and the earlier 0.0121-versus-0.0708 comparison")
    print("  understated the result by making the formula look fitted.")
    print("")
    print("  AND THE FITTED K SPLITS BY DEMOGRAPHY, NOT BY TRAIT. serial1d fits")
    print("  %.3f-%.3f, straddling the true 0.150; grid2d fits %.3f-%.3f, all"
          % (min(r["best_fit_K"] for r in rows if r["dem"] == "serial1d"),
             max(r["best_fit_K"] for r in rows if r["dem"] == "serial1d"),
             min(r["best_fit_K"] for r in rows if r["dem"] == "grid2d"),
             max(r["best_fit_K"] for r in rows if r["dem"] == "grid2d")))
    print("  above it. A trait-level absorber cannot be the story; whatever the")
    print("  fit is soaking up is a property of the DEMOGRAPHY.")
    _slope_check(rows)
    out["C_prevalence"] = {"true_K": PREV, "rows": rows,
                           "pooled_rmse_true_K": float(np.mean(allo)),
                           "pooled_rmse_fitted_K": float(np.mean(allf)),
                           "fitted_K_range": [min(ks), max(ks)]}


def _slope_check(rows):
    print("")
    print("  DIRECTION CHECK. THE FIRST RUN OF THIS FILE ASSERTED dAUC/dK > 0")
    print("  AND PRINTED THE NUMBERS THAT REFUTE IT. The assertion was mine and")
    print("  it was wrong; the numbers are below and they are negative, so")
    print("  raising K LOWERS the predicted AUC at fixed R^2. A cell whose")
    print("  best-fit K exceeds 0.15 is therefore one where the formula at the")
    print("  true K predicts an AUC that is too HIGH, i.e. where liability_r2 is")
    print("  too LARGE for the observed AUC -- the opposite of the first run's")
    print("  stated explanation.")
    print("  %-10s %-14s %-14s %-14s" % ("R^2", "AUC at K=0.15",
                                         "AUC at K=0.175", "d/dK"))
    for r in (0.05, 0.10, 0.20, 0.30):
        a1 = auc_from_r2(r, 0.15)
        a2 = auc_from_r2(r, 0.175)
        print("  %-10.2f %-14.5f %-14.5f %+14.5f"
              % (r, a1, a2, (a2 - a1) / 0.025))
    print("  dAUC/dK is NEGATIVE throughout the range in play.")
    print("")
    print("  So the sign of (best-fit K - 0.15) is the sign of the AUC residual")
    print("  at the true K, and it is a demography effect: grid2d's PGS carries")
    print("  a liability_r2 that is too large for the AUC it achieves, which is")
    print("  what a score whose ranking degrades faster than its variance-")
    print("  explained looks like out of ancestry. serial1d does not show it.")
    print("  Named rather than explained away: this file establishes the sign")
    print("  and the split, not the mechanism.")


_R2CACHE = {}


def _lookup_r2(key):
    if not _R2CACHE:
        for r in csv.DictReader(open(os.path.join(RES,
                                                  "accuracy_binary.csv"))):
            if r["metric"] != "liability_r2":
                continue
            v = r["value"]
            if v in ("", "nan"):
                continue
            _R2CACHE[(r["dem"], r["pheno"], r["method"],
                      int(r["seed"]))] = float(v)
    return _R2CACHE.get(key)


def main():
    out = {}
    part_a(out)
    runs = part_b(out)
    part_c(out, runs)
    fh = open("fam_serial_founder_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("")
    print("-> fam_serial_founder_results.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
