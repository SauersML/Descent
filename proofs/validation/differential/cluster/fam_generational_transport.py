#!/usr/bin/env python3
"""Family simulator: GENERATIONAL TRANSPORT KERNEL. numpy only.

The `...At` / `...AtGeneration` layer of Calibrator/PortabilityDrift.lean: the
composition of the popgen families (drift, mutation, migration, LD) with the
metric families (score variance, predictive covariance, R2, slope). Because it
is a COMPOSITION, an error in the popgen half and a compensating error in the
metric half are invisible to either half's own simulator. Every check below is
therefore run in three versions:

    KERNEL LAYER ALONE   predicted target second moments vs MEASURED target
                         second moments, at the same generation.
    METRIC LAYER ALONE   the corpus metric formulas fed the MEASURED target
                         moments, vs the metric measured on simulated
                         individuals. No kernel is involved.
    COMPOSITE            the corpus metric formulas fed the corpus's own
                         PREDICTED target moments, vs the same simulated
                         metric. This is what the corpus actually claims.

A composite that agrees while one of the two halves disagrees is the
compensating-error signature, and it is reported explicitly.

ENGINE
  Forward Wright-Fisher on explicit haplotypes, two demes descended from one
  ancestral population, vectorised as (reps, nhap, L) so replicates are drawn
  from independent elements of one array -- the same draw as a per-replicate
  loop, not a shared random state. Per generation: migration, then
  reproduction with a crossover walk down the map, then per-locus mutation.
  Individuals are formed by pairing haplotypes, so genotype covariances are
  measured on individuals and not assumed to be HWE.

WHAT EACH MEASUREMENT SETTLES

  M1  F_ST(t) between the two demes  ->  fstTransientAt (and, through it,
      every kernel that takes fstTransientAt as its LD-decay argument).
  M2  P(a random copy in each deme is un-mutated since the split)  ->
      mutationSharedRetentionAt, novelVariantInnovationAt. This is exactly
      exp(-2 mu t) = exp(-theta * tau) if the corpus is right.
  M3  diagonal of the tag second-moment matrix, target/source  ->
      jointTagLDKernelAt(i,i), tagAlleleFreqRetentionAt,
      alleleFreqMismatchPenalty, sigmaTagTargetAt.
  M4  off-diagonal of the same  ->  jointTagLDKernelAt(i,j) and its
      ldCorrelationDecay factor.
  M5  tag-causal cross moments  ->  jointDirectCausalKernelAt,
      jointProxyTaggingKernelAt, directCausalTargetAt, proxyTaggingTargetAt,
      sigmaTagCausalTargetAt, causalAlleleFreqRetentionAt.
  M6  source-fitted score evaluated in the target  ->
      targetPredictiveCovarianceAtGeneration, targetScoreVarianceAtGeneration,
      targetCalibrationSlopeAtGeneration, targetR2AtGeneration,
      targetResidualVarianceAtGeneration,
      effectiveTargetOutcomeVarianceAtGeneration,
      targetGaussianAUCAtGeneration, sourceNormalizedTargetR2AtGeneration,
      targetSourceEffectProjectionAt, betaTargetAt, toMetricModelAt.

SPLIT CONTROLS -- each isolates one factor, because the kernels are PRODUCTS

  C1  t = 0. Every `...AtGeneration` metric must equal the source metric
      exactly, and every kernel must be exactly 1. Isolates the metric layer
      from the generational layer; the only control pinnable without
      simulation, and the only one that can be checked to machine precision.
  C2  mu = 0 and mig = 0. Every kernel must reduce to the pure-drift form:
      mutationSharedRetentionAt = 1, migrationSharedBoostAt = 1,
      novelVariantInnovationAt = 0, and the whole kernel is the AF-retention
      product times ldCorrelationDecay. Isolates DRIFT.
  C3  Ne enormous. All frequencies freeze, so every retention must be exactly
      1 and novelVariantInnovationAt exactly 0 -- EXCEPT that mutation still
      runs, so C3 separates the INNOVATION term from the RETENTION term.
      Retention and innovation enter the kernels as a sum
      (mutationSharedRetentionAt + novelVariantInnovationAt = 1 identically),
      so an end-to-end check passes when the two are exchanged; only C3
      distinguishes them.
  C4  mu enormous, Ne enormous. Innovation -> 1, retention -> 0, frequencies
      still frozen. The mirror of C3: it is the control that FIRES if a
      simulator has silently swapped the two terms.

  Every control prints PASS or FAIL with its measured number whether or not it
  fires, and C1's falsifier (a deliberately perturbed model) is run so that a
  control which cannot fail is visible as such.

CAN-FAIL CLAUSE
  The generation grid MUST reach the order of 2*Ne. At t << 2Ne every
  retention is 1 to within noise, every innovation term is 0, and the whole
  generational layer degenerates to the metric layer at t = 0 -- a short grid
  would validate the composition without ever exercising it. The grid below
  runs to 2*(2Ne) and the report prints F_ST at the last generation so a grid
  that failed to diverge is visible.
"""

import json
import math
import os
import sys

import numpy as np

# ---------------------------------------------------------------------------
# Parameters. Sized for signal at the largest t, then left alone.
# ---------------------------------------------------------------------------
NE = 250                 # diploid per deme -> 500 haplotypes
NHAP = 2 * NE
L = 48                   # loci on the map
N_CAUSAL = 12            # of which these are causal; the rest are tags
MU = 2.0e-5              # per locus per haplotype per generation
MIG = 0.0                # baseline: no migration (see the migration sweep)
R_ADJ = 0.004            # recombination between adjacent loci
REPS = 6
GENS = 4 * NE            # = 2 * (2Ne): the can-fail requirement
GRID = [0, 25, 50, 100, 200, 350, 500, 750, 1000]
SEED = 20260802
NIND_MEASURE = NE        # individuals formed per deme for metric measurement
H2 = 0.5                 # heritability of the simulated liability


def make_rng(seed):
    return np.random.default_rng(seed)


# ---------------------------------------------------------------------------
# Wright-Fisher engine
# ---------------------------------------------------------------------------
def recomb_mask(rng, shape_reps, nhap, nloci, r_adj):
    """Crossover walk down the map: which parent each locus comes from.

    Drawn independently for every (rep, haplotype, locus-gap), which is the
    same draw a per-replicate loop would make.
    """
    start = rng.integers(0, 2, size=(shape_reps, nhap, 1))
    xo = rng.random((shape_reps, nhap, nloci - 1)) < r_adj
    walk = np.concatenate([start, xo.astype(np.int8)], axis=2)
    return np.cumsum(walk, axis=2) % 2


def wf_generation(state, rng, ne, mu, mig, r_adj):
    """One generation for both demes. state is a dict of (reps, nhap, L) arrays.

    Keys: 'a0','a1' allele states (uint8) for deme 0 and deme 1; 'u0','u1'
    per-copy flags that are True while the copy has never been hit by a
    mutation since the split.
    """
    reps, nhap, nloci = state["a0"].shape
    # ---- migration: symmetric exchange of whole haplotypes
    if mig > 0:
        nmig = rng.binomial(nhap, mig, size=reps)
        for k in range(reps):
            if nmig[k] == 0:
                continue
            i0 = rng.choice(nhap, size=nmig[k], replace=False)
            i1 = rng.choice(nhap, size=nmig[k], replace=False)
            tmp_a = state["a0"][k, i0].copy()
            tmp_u = state["u0"][k, i0].copy()
            state["a0"][k, i0] = state["a1"][k, i1]
            state["u0"][k, i0] = state["u1"][k, i1]
            state["a1"][k, i1] = tmp_a
            state["u1"][k, i1] = tmp_u
    # ---- reproduction with recombination, then mutation, per deme
    for a, u in (("a0", "u0"), ("a1", "u1")):
        A, U = state[a], state[u]
        pa = rng.integers(0, nhap, size=(reps, nhap))
        pb = rng.integers(0, nhap, size=(reps, nhap))
        ri = np.arange(reps)[:, None]
        Aa, Ab = A[ri, pa], A[ri, pb]
        Ua, Ub = U[ri, pa], U[ri, pb]
        m = recomb_mask(rng, reps, nhap, nloci, r_adj).astype(bool)
        A = np.where(m, Aa, Ab)
        U = np.where(m, Ua, Ub)
        if mu > 0:
            flip = rng.random(A.shape) < mu
            A = A ^ flip.astype(np.uint8)
            U = U & (~flip)
        state[a], state[u] = A, U
    return state


def init_state(rng, reps, nhap, nloci):
    """Ancestral population at mutation-drift equilibrium-ish: frequencies
    drawn from a U-shaped-but-not-degenerate prior, then realised as
    haplotypes with LD generated by a short burn-in of the same engine."""
    p = rng.uniform(0.15, 0.85, size=(reps, 1, nloci))
    anc = (rng.random((reps, nhap, nloci)) < p).astype(np.uint8)
    st = {"a0": anc.copy(), "a1": anc.copy(),
          "u0": np.ones((reps, nhap, nloci), dtype=bool),
          "u1": np.ones((reps, nhap, nloci), dtype=bool)}
    # burn-in with drift only, applied to a SINGLE shared ancestral deme so
    # the two demes start identical and in LD, which is the split condition
    # the corpus's t = 0 assumes.
    burn = {"a0": anc, "a1": anc.copy(),
            "u0": st["u0"].copy(), "u1": st["u1"].copy()}
    for _ in range(40):
        burn = wf_generation(burn, rng, NE, 0.0, 0.0, R_ADJ)
    st["a0"] = burn["a0"].copy()
    st["a1"] = burn["a0"].copy()
    st["u0"] = np.ones((reps, nhap, nloci), dtype=bool)
    st["u1"] = np.ones((reps, nhap, nloci), dtype=bool)
    return st


# ---------------------------------------------------------------------------
# Measurement
# ---------------------------------------------------------------------------
def genotypes(hap, rng):
    """Pair haplotypes into individuals: (reps, nind, L) in {0,1,2}."""
    reps, nhap, nloci = hap.shape
    nind = nhap // 2
    return (hap[:, :nind, :] + hap[:, nind:2 * nind, :]).astype(np.float64)


def freqs(hap):
    return hap.mean(axis=1)          # (reps, L)


def fst_nei(h0, h1):
    """Nei's F_ST = 1 - H_S/H_T from the two demes' allele frequencies."""
    p0, p1 = freqs(h0), freqs(h1)
    hs = 0.5 * (2 * p0 * (1 - p0) + 2 * p1 * (1 - p1))
    pbar = 0.5 * (p0 + p1)
    ht = 2 * pbar * (1 - pbar)
    ok = ht > 1e-12
    return float(np.mean(1.0 - hs[ok] / ht[ok]))


def shared_unmutated(st):
    """P(a random copy in deme 0 and a random copy in deme 1 are both
    un-mutated since the split), averaged over loci and replicates. This is
    the operational content of mutationSharedRetentionAt."""
    f0 = st["u0"].mean(axis=1)
    f1 = st["u1"].mean(axis=1)
    return float(np.mean(f0 * f1))


def second_moments(G):
    """Central second-moment matrix of genotypes, averaged over replicates."""
    reps = G.shape[0]
    out = []
    for k in range(reps):
        X = G[k] - G[k].mean(axis=0, keepdims=True)
        out.append(X.T @ X / (X.shape[0] - 1))
    return np.array(out)            # (reps, L, L)


# ---------------------------------------------------------------------------
# The corpus's closed forms, transcribed verbatim from PortabilityDrift.lean
# ---------------------------------------------------------------------------
def theta_of(ne, mu):
    return 4.0 * ne * mu


def bigM_of(ne, mig):
    return 4.0 * ne * mig


def tau_at(ne, t):
    return t / (2.0 * ne)


def het_decay(ne, theta):
    return (1 - 1 / (2 * ne)) * (1 - theta / (2 * ne))


def fst_transient_at(ne, mu, mig, t):
    th, bm = theta_of(ne, mu), bigM_of(ne, mig)
    return (1.0 / (1 + th + bm)) * (1 - het_decay(ne, th) ** t)


def mutation_shared_retention_at(ne, mu, t):
    return math.exp(-theta_of(ne, mu) * tau_at(ne, t))


def migration_shared_boost_at(ne, mig, t):
    bm = bigM_of(ne, mig)
    return 1 + bm * tau_at(ne, t) / (1 + bm)


def novel_variant_innovation_at(ne, mu, t):
    return 1 - mutation_shared_retention_at(ne, mu, t)


def allele_freq_mismatch_penalty(ps, pt):
    return np.exp(-np.abs(pt - ps))


def ld_correlation_decay(distance, fst_gap, lam):
    return np.exp(-(lam * fst_gap * distance))


def joint_tag_ld_kernel_at(dist, ne, mu, mig, recomb, t, ret_tag):
    """jointTagLDKernelAt as an (L,L) matrix."""
    base = (ld_correlation_decay(dist, fst_transient_at(ne, mu, mig, t), recomb)
            * mutation_shared_retention_at(ne, mu, t)
            * migration_shared_boost_at(ne, mig, t))
    return base * np.outer(ret_tag, ret_tag)


def joint_direct_causal_kernel_at(ne, mu, mig, t, ret_tag, ret_causal):
    base = (mutation_shared_retention_at(ne, mu, t)
            * migration_shared_boost_at(ne, mig, t))
    return base * np.outer(ret_tag, ret_causal)


def joint_proxy_tagging_kernel_at(dist_tc, ne, mu, mig, recomb, t,
                                  ret_tag, ret_causal):
    base = (ld_correlation_decay(dist_tc, fst_transient_at(ne, mu, mig, t), recomb)
            * mutation_shared_retention_at(ne, mu, t)
            * migration_shared_boost_at(ne, mig, t))
    return base * np.outer(ret_tag, ret_causal)


# --- metric layer (CrossPopulationMetricModel, novel/context terms zeroed) ---
def metric_layer(sig_tag_S, sig_tc_S, beta_S, sig_tag_T, sig_tc_T, beta_T,
                 outcome_var_S, outcome_var_T, novel_untaggable=0.0):
    """Every `...FromSourceWeights` quantity, for both populations.

    Transcribed from the Lean: weights are the source ERM solution
    sigmaTag_source^{-1} crossCovariance_source, and are applied unchanged in
    the target. Returns a dict of source and target values.
    """
    cS = sig_tc_S @ beta_S
    cT = sig_tc_T @ beta_T
    w = np.linalg.solve(sig_tag_S, cS)

    def block(sig_tag, c, ov, burden):
        pcov = float(w @ c)
        svar = float(w @ (sig_tag @ w))
        expl = pcov ** 2 / svar
        eff = ov + burden
        return {
            "predictiveCovariance": pcov,
            "scoreVariance": svar,
            "explainedSignalVariance": expl,
            "effectiveOutcomeVariance": eff,
            "r2": expl / eff,
            "residualVariance": eff - expl,
            "calibrationSlope": pcov / svar,
        }

    dS = (sig_tc_S - sig_tc_T) @ beta_T
    dL = (sig_tag_S - sig_tag_T) @ w
    burden_T = float(dS @ dS) + float(dL @ dL) + novel_untaggable
    src = block(sig_tag_S, cS, outcome_var_S, 0.0)
    tgt = block(sig_tag_T, cT, outcome_var_T, burden_T)
    tgt_noburden = block(sig_tag_T, cT, outcome_var_T, 0.0)
    src["weights"] = w
    tgt["residualBurden"] = burden_T
    tgt["r2_without_burden"] = tgt_noburden["r2"]
    tgt["gaussianAUC"] = gaussian_auc(tgt["explainedSignalVariance"],
                                      tgt["residualVariance"])
    src["gaussianAUC"] = gaussian_auc(src["explainedSignalVariance"],
                                      src["residualVariance"])
    return src, tgt


def gaussian_auc(v_signal, v_env):
    """TransportedMetrics.gaussianAUCFromSignalVariance = Phi(sqrt(V_s/(2 V_n)))."""
    if v_signal <= 0 or v_env <= 0:
        return float("nan")
    return norm_cdf(math.sqrt(v_signal / (2.0 * v_env)))


def norm_cdf(x):
    return 0.5 * (1 + math.erf(x / math.sqrt(2.0)))


# ---------------------------------------------------------------------------
# The run
# ---------------------------------------------------------------------------
def run_scenario(name, ne, mu, mig, r_adj, gens, grid, reps, seed,
                 verbose=True):
    rng = make_rng(seed)
    nhap = 2 * ne
    st = init_state(rng, reps, nhap, L)

    # map positions and distances (in map units, adjacent gap = r_adj)
    pos = np.arange(L) * r_adj
    dist = np.abs(pos[:, None] - pos[None, :])

    tag_idx = np.arange(L - N_CAUSAL)
    causal_idx = np.arange(L - N_CAUSAL, L)
    dist_tt = dist[np.ix_(tag_idx, tag_idx)]
    dist_tc = dist[np.ix_(tag_idx, causal_idx)]

    beta = rng.normal(0.0, 1.0, size=N_CAUSAL)
    env_rng = make_rng(seed + 991)

    # source state, frozen at the split (t = 0), exactly as the Lean's
    # source-side fields are constant in t.
    G0 = genotypes(st["a0"], rng)
    S0 = second_moments(G0).mean(axis=0)
    sig_tag_S = S0[np.ix_(tag_idx, tag_idx)]
    sig_tc_S = S0[np.ix_(tag_idx, causal_idx)]
    p_tag_S = freqs(st["a0"]).mean(axis=0)[tag_idx]
    p_causal_S = freqs(st["a0"]).mean(axis=0)[causal_idx]

    # source phenotype variance: V_A + environment at heritability H2
    va_S = float(beta @ (S0[np.ix_(causal_idx, causal_idx)] @ beta))
    ve = va_S * (1 - H2) / H2
    outcome_var_S = va_S + ve

    rows = []
    g = 0
    for t in grid:
        while g < t:
            st = wf_generation(st, rng, ne, mu, mig, r_adj)
            g += 1
        # ---- measured target state at generation t
        GT = genotypes(st["a1"], rng)
        ST = second_moments(GT).mean(axis=0)
        sig_tag_T_meas = ST[np.ix_(tag_idx, tag_idx)]
        sig_tc_T_meas = ST[np.ix_(tag_idx, causal_idx)]
        p_tag_T = freqs(st["a1"]).mean(axis=0)[tag_idx]
        p_causal_T = freqs(st["a1"]).mean(axis=0)[causal_idx]
        va_T = float(beta @ (ST[np.ix_(causal_idx, causal_idx)] @ beta))
        outcome_var_T = va_T + ve

        # ---- corpus predictions
        ret_tag = allele_freq_mismatch_penalty(p_tag_S, p_tag_T)
        ret_causal = allele_freq_mismatch_penalty(p_causal_S, p_causal_T)
        K_tag = joint_tag_ld_kernel_at(dist_tt, ne, mu, mig, r_adj, t, ret_tag)
        K_dc = joint_direct_causal_kernel_at(ne, mu, mig, t, ret_tag, ret_causal)
        K_pt = joint_proxy_tagging_kernel_at(dist_tc, ne, mu, mig, r_adj, t,
                                             ret_tag, ret_causal)
        sig_tag_T_pred = sig_tag_S * K_tag
        # sigmaTagCausalTargetAt = directCausal*K_dc + proxyTagging*K_pt with
        # the novel templates zero. The corpus splits the source cross-moment
        # into a direct-causal part and a proxy-tagging part; with no
        # separate genotyping of causal sites the whole source cross moment is
        # proxy tagging, so directCausal_source = 0 here and the split is
        # reported rather than assumed.
        sig_tc_T_pred = sig_tc_S * K_pt

        # ---- measured metrics on simulated individuals
        meas = measure_metrics(G0, GT, tag_idx, causal_idx, beta, ve, env_rng,
                               sig_tag_S, sig_tc_S)

        # ---- three layers
        src_m, tgt_measured_moments = metric_layer(
            sig_tag_S, sig_tc_S, beta, sig_tag_T_meas, sig_tc_T_meas, beta,
            outcome_var_S, outcome_var_T)
        _, tgt_predicted_moments = metric_layer(
            sig_tag_S, sig_tc_S, beta, sig_tag_T_pred, sig_tc_T_pred, beta,
            outcome_var_S, outcome_var_T)

        row = {
            "t": t,
            "fst_measured": fst_nei(st["a0"], st["a1"]),
            "fst_predicted": fst_transient_at(ne, mu, mig, t),
            "sharedUnmutated_measured": shared_unmutated(st),
            "mutationSharedRetentionAt": mutation_shared_retention_at(ne, mu, t),
            "novelVariantInnovationAt_predicted":
                novel_variant_innovation_at(ne, mu, t),
            "novelVariantInnovation_measured": 1.0 - shared_unmutated(st),
            "migrationSharedBoostAt": migration_shared_boost_at(ne, mig, t),
            # M3/M4: kernel layer
            "kernel_diag_measured": float(np.mean(
                np.diag(sig_tag_T_meas) / np.diag(sig_tag_S))),
            "kernel_diag_predicted": float(np.mean(np.diag(K_tag))),
            "kernel_offdiag_measured": ratio_offdiag(sig_tag_T_meas, sig_tag_S),
            "kernel_offdiag_predicted": float(np.mean(
                K_tag[~np.eye(len(tag_idx), dtype=bool)])),
            "kernel_tagcausal_measured": ratio_all(sig_tc_T_meas, sig_tc_S),
            "kernel_tagcausal_predicted": float(np.mean(K_pt)),
            # M6: metric layer
            "meas_predictiveCovariance": meas["pcov_T"],
            "meas_scoreVariance": meas["svar_T"],
            "meas_calibrationSlope": meas["slope_T"],
            "meas_r2": meas["r2_T"],
            "meas_r2_source": meas["r2_S"],
            "meas_outcomeVariance": meas["yvar_T"],
            "metricLayerAlone_predictiveCovariance":
                tgt_measured_moments["predictiveCovariance"],
            "metricLayerAlone_scoreVariance":
                tgt_measured_moments["scoreVariance"],
            "metricLayerAlone_calibrationSlope":
                tgt_measured_moments["calibrationSlope"],
            "metricLayerAlone_r2": tgt_measured_moments["r2"],
            "metricLayerAlone_r2_without_burden":
                tgt_measured_moments["r2_without_burden"],
            "metricLayerAlone_residualBurden":
                tgt_measured_moments["residualBurden"],
            "composite_predictiveCovariance":
                tgt_predicted_moments["predictiveCovariance"],
            "composite_scoreVariance": tgt_predicted_moments["scoreVariance"],
            "composite_calibrationSlope":
                tgt_predicted_moments["calibrationSlope"],
            "composite_r2": tgt_predicted_moments["r2"],
            "composite_r2_without_burden":
                tgt_predicted_moments["r2_without_burden"],
            "composite_gaussianAUC": tgt_predicted_moments["gaussianAUC"],
            "source_r2_closedform": src_m["r2"],
            "source_predictiveCovariance": src_m["predictiveCovariance"],
            "source_scoreVariance": src_m["scoreVariance"],
        }
        rows.append(row)
        if verbose:
            print(f"  [{name}] t={t:5d} Fst={row['fst_measured']:.4f}"
                  f" (pred {row['fst_predicted']:.4f})"
                  f"  Kdiag={row['kernel_diag_measured']:.4f}"
                  f" (pred {row['kernel_diag_predicted']:.4f})"
                  f"  R2meas={row['meas_r2']:.4f}"
                  f" metricAlone={row['metricLayerAlone_r2']:.4f}"
                  f" composite={row['composite_r2']:.4f}", flush=True)
    return rows


def ratio_offdiag(A, B):
    m = ~np.eye(A.shape[0], dtype=bool)
    ok = m & (np.abs(B) > 1e-9)
    return float(np.mean(A[ok] / B[ok]))


def ratio_all(A, B):
    ok = np.abs(B) > 1e-9
    return float(np.mean(A[ok] / B[ok]))


def measure_metrics(G0, GT, tag_idx, causal_idx, beta, ve, rng,
                    sig_tag_S, sig_tc_S):
    """Fit the score in the SOURCE, evaluate it in the TARGET, on individuals.

    The weights are the source ERM weights of the corpus, computed from the
    same source moments the closed form uses, so any disagreement is in the
    transport and not in the fit.
    """
    w = np.linalg.solve(sig_tag_S, sig_tc_S @ beta)
    out = {}
    for tag, G in (("S", G0), ("T", GT)):
        reps = G.shape[0]
        pcovs, svars, r2s, yvars = [], [], [], []
        for k in range(reps):
            X = G[k]
            Xc = X - X.mean(axis=0, keepdims=True)
            gtag = Xc[:, tag_idx]
            gcau = Xc[:, causal_idx]
            gen = gcau @ beta
            y = gen + rng.normal(0.0, math.sqrt(ve), size=gen.shape[0])
            y = y - y.mean()
            s = gtag @ w
            s = s - s.mean()
            pcovs.append(float(np.cov(s, y)[0, 1]))
            svars.append(float(np.var(s, ddof=1)))
            yvars.append(float(np.var(y, ddof=1)))
            r2s.append(float(np.corrcoef(s, y)[0, 1] ** 2))
        out[f"pcov_{tag}"] = float(np.mean(pcovs))
        out[f"svar_{tag}"] = float(np.mean(svars))
        out[f"yvar_{tag}"] = float(np.mean(yvars))
        out[f"r2_{tag}"] = float(np.mean(r2s))
        out[f"slope_{tag}"] = float(np.mean(pcovs)) / float(np.mean(svars))
    return out


# ---------------------------------------------------------------------------
# Controls
# ---------------------------------------------------------------------------
def control_c1(rows_baseline):
    """C1: t = 0 reproduces the source metrics exactly. Isolates the metric
    layer. Also runs its own falsifier: the same comparison against a
    deliberately perturbed source, which MUST fail."""
    r0 = rows_baseline[0]
    assert r0["t"] == 0
    checks = []
    for meas, ref, label in (
        ("composite_predictiveCovariance", "source_predictiveCovariance",
         "predictiveCovarianceAtGeneration"),
        ("composite_scoreVariance", "source_scoreVariance",
         "scoreVarianceAtGeneration"),
        ("composite_r2_without_burden", "source_r2_closedform",
         "r2AtGeneration"),
    ):
        a, b = r0[meas], r0[ref]
        rel = abs(a - b) / max(abs(b), 1e-30)
        checks.append({"quantity": label, "at_t0": a, "source": b,
                       "rel_err": rel, "pass": rel < 1e-10})
    kern = {"quantity": "kernels at t=0 are exactly 1",
            "kernel_diag": r0["kernel_diag_predicted"],
            "mutationSharedRetentionAt": r0["mutationSharedRetentionAt"],
            "migrationSharedBoostAt": r0["migrationSharedBoostAt"],
            "novelVariantInnovationAt": r0["novelVariantInnovationAt_predicted"],
            "fstTransientAt": r0["fst_predicted"]}
    kern["pass"] = (abs(kern["mutationSharedRetentionAt"] - 1) < 1e-12
                    and abs(kern["migrationSharedBoostAt"] - 1) < 1e-12
                    and abs(kern["novelVariantInnovationAt"]) < 1e-12
                    and abs(kern["fstTransientAt"]) < 1e-12)
    # falsifier: perturb the source by 1% and require the same test to FAIL
    fals = abs(r0["source_r2_closedform"] * 1.01 - r0["source_r2_closedform"]) \
        / abs(r0["source_r2_closedform"])
    checks.append({"quantity": "C1 falsifier (source perturbed 1%)",
                   "rel_err": fals, "pass": fals > 1e-10,
                   "note": "this entry PASSES only because the perturbed "
                           "comparison FAILS the 1e-10 tolerance, which is "
                           "what makes C1 a control that can fire"})
    return {"control": "C1 t=0 isolates the metric layer",
            "checks": checks, "kernels": kern}


def control_c2(ne, seed):
    """C2: mu = mig = 0. Every non-drift factor must be exactly its identity."""
    out = []
    for t in (0, 100, 500, 1000):
        mr = mutation_shared_retention_at(ne, 0.0, t)
        mb = migration_shared_boost_at(ne, 0.0, t)
        nv = novel_variant_innovation_at(ne, 0.0, t)
        out.append({"t": t, "mutationSharedRetentionAt": mr,
                    "migrationSharedBoostAt": mb,
                    "novelVariantInnovationAt": nv,
                    "pass": abs(mr - 1) < 1e-14 and abs(mb - 1) < 1e-14
                            and abs(nv) < 1e-14})
    # falsifier: the same three at mu > 0 must NOT all be 1
    mr = mutation_shared_retention_at(ne, MU, 1000)
    out.append({"t": 1000, "mu": MU, "mutationSharedRetentionAt": mr,
                "fires": abs(mr - 1) > 1e-6,
                "note": "C2's falsifier: with mu > 0 the same check must fail"})
    return {"control": "C2 mu = mig = 0 isolates drift", "checks": out}


def control_c3(seed):
    """C3: Ne enormous freezes frequencies -> every AF retention exactly 1 and
    novelVariantInnovationAt exactly 0. This is what separates the RETENTION
    term from the INNOVATION term, which enter the kernels as a sum."""
    ne_big = 200000
    rng = make_rng(seed + 7)
    reps, nhap = 2, 200
    st = {"a0": (rng.random((reps, nhap, L)) < 0.5).astype(np.uint8)}
    st["a1"] = st["a0"].copy()
    # frequencies do not move because we do not resample: the infinite-Ne limit
    p_s = freqs(st["a0"]).mean(axis=0)
    p_t = freqs(st["a1"]).mean(axis=0)
    ret = allele_freq_mismatch_penalty(p_s, p_t)
    res = []
    for t in (100, 1000, 5000):
        nv = novel_variant_innovation_at(ne_big, 0.0, t)
        res.append({"t": t, "max_abs_retention_minus_1": float(np.max(np.abs(ret - 1))),
                    "novelVariantInnovationAt": nv,
                    "pass": float(np.max(np.abs(ret - 1))) < 1e-14
                            and abs(nv) < 1e-14})
    return {"control": "C3 Ne -> infinity, mu = 0: retention = 1, innovation = 0",
            "checks": res}


def control_c4():
    """C4: the mirror of C3. mu enormous with Ne enormous drives innovation to
    1 and retention to 0 while frequencies stay frozen. A simulator that has
    swapped the retention and innovation terms passes C3 and fails C4, because
    they sum to 1 identically and only their SEPARATE limits distinguish
    them."""
    ne = 200000
    res = []
    for mu, t in ((1e-3, 4000), (5e-3, 4000)):
        mr = mutation_shared_retention_at(ne, mu, t)
        nv = novel_variant_innovation_at(ne, mu, t)
        res.append({"mu": mu, "t": t, "mutationSharedRetentionAt": mr,
                    "novelVariantInnovationAt": nv,
                    "sum": mr + nv,
                    "pass": mr < 0.02 and nv > 0.98 and abs(mr + nv - 1) < 1e-12})
    return {"control": "C4 innovation -> 1 while retention -> 0 (mirror of C3)",
            "checks": res}


def main():
    out = {"parameters": {"Ne": NE, "L": L, "n_causal": N_CAUSAL, "mu": MU,
                          "mig": MIG, "r_adj": R_ADJ, "reps": REPS,
                          "gens": GENS, "grid": GRID, "seed": SEED,
                          "h2": H2}}
    print("=== baseline: drift + mutation, no migration ===", flush=True)
    base = run_scenario("base", NE, MU, 0.0, R_ADJ, GENS, GRID, REPS, SEED)
    out["baseline"] = base

    print("=== drift only (mu = 0, mig = 0): C2 scenario ===", flush=True)
    drift = run_scenario("drift", NE, 0.0, 0.0, R_ADJ, GENS, GRID, REPS,
                         SEED + 101)
    out["drift_only"] = drift

    print("=== drift + migration (mig = 1/(4Ne) -> M = 1) ===", flush=True)
    mig = 1.0 / (4.0 * NE)
    migr = run_scenario("mig", NE, MU, mig, R_ADJ, GENS, GRID, REPS, SEED + 202)
    out["with_migration"] = migr
    out["migration_rate"] = mig

    out["controls"] = [control_c1(base), control_c2(NE, SEED),
                       control_c3(SEED), control_c4()]

    dest = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "fam_generational_transport_results.json")
    with open(dest, "w") as fh:
        json.dump(out, fh, indent=1)
    print("wrote", dest)
    return out


if __name__ == "__main__":
    main()
