"""Battery clean01: the composed clean two-branch split transport prediction.

WHAT IS UNDER TEST.  `PhenomeWidePortability.cleanSplitFst`,
`cleanSplitTargetR2` and `cleanSplitTargetAUC` compose four separately measured
stages into one end-to-end prediction for the simplest demography a portability
law can be asked about: one ancestral population, two closed branches, no
migration and no mutation.  Every stage carries its own verdict; THE JOIN does
not, and the join is the whole content of this battery.

    cleanSplitFst NeS NeT t  =  (1 - (1-1/(2 NeS))^t) + (1 - (1-1/(2 NeT))^t)
    cleanSplitTargetR2       =  neutralPortability r2_0 (cleanSplitFst) * ld
    cleanSplitTargetAUC      =  liabilityThresholdAUCFromExplainedR2 (that) K

THE SUMMATION CONVENTION IS THE CLAIM, and the docstrings say so at length: the
two PER-BRANCH Wright `F` values against the ancestor are ADDED, and a design
that fed a pairwise Hudson `F_ST` here would repeat an error the corpus records
as having produced a factor-of-four false falsification twice.  So per-branch
`F` is measured HERE THE SAME WAY `fstFromDriftFactor` was validated -- as the
realised heterozygosity LOSS `1 - H_branch/H_ancestor` within one lineage --
and the pairwise Hudson reading is carried in the same cells AS A COMPETITOR,
where it can be seen to be the other number rather than assumed to be.

THE ENGINE IS THE ONE `neutralDriftFactor` WAS VALIDATED ON: forward
Wright-Fisher resampling of allele frequencies, `p <- Binomial(2 Ne, p)/(2 Ne)`,
one closed branch per lineage, no mutation and no migration.  msprime is not
used and the reason is regime rather than taste: msprime needs mutation to
produce genotypes at all, and mutations falling AFTER the split are
branch-private variants the composed prediction does not describe.  A forward
frequency engine instantiates "closed populations, no mutation" exactly, and it
carries no linkage, which is the `ldFactor = 1` cell the main test wants.

WHY THE ARCHITECTURE CARRIES TRUE EFFECTS.  The bodies predict the retention of
a GIVEN source `r2_0`; they say nothing about how well a GWAS estimates
effects.  A design with a P+T pipeline in it would measure the sum of the two
and attribute it here.  So the source's effect estimates are the true causal
effects, and `r2_0` is fixed by construction at `V_A/(V_A+V_E) = 1/2`, realised
exactly in every block.

TWO SCORE CONSTRUCTIONS, because the body's `fst` slot does not by itself say
which one it describes, and the source branch's drift reaches the target
through only one of them:

  PER-ALLELE.  The GWAS reports per-allele effects; the score is `sum b_j g_j`
      over the variants still POLYMORPHIC IN THE SOURCE, since a variant fixed
      in the source cannot be discovered there.  This is what a real PGS is.
      The source branch enters only by removing source-fixed variants from the
      score, and their signal stays in the target phenotype as unexplained
      heritable variance.

  SOURCE-STANDARDISED.  The GWAS reports effects per source-genotype SD and the
      target score restandardises by target frequencies, so the weight carries
      `sqrt(h_S/h_T)`.  This is the frequency-mismatch construction, it is
      symmetric in the two branches, and it is the one under which a SUMMED
      index has a mechanism.  Giving the body its best case is the point:
      a falsification that only holds in the construction least favourable to
      it is a report about the design.

Both are recorded, on the same replicates, against the same body.

CONTROLS.  Every group is gated on a cell whose answer is known independently of
any of the three bodies and which fails on an engine error rather than on
sampling noise:

  * the drift group is gated on ONE branch's realised heterozygosity retention
    against `neutralDriftFactor`, a separately VALIDATED body, on the same
    resampling code path.  A wrong `2 Ne`, a wrong number of generations or a
    mis-seeded resampler moves it.
  * the transport and AUC groups are gated on the `t = 0` cell, where no drift
    has happened and the measured target `R^2` must be the constructed
    `V_A/(V_A+V_E) = 1/2` and the measured AUC must be the already-VALIDATED
    chart's value at that `R^2`.  It fails on a variance-scaling slip, a
    genotype-generation slip or a correlation slip.

POWER.  `NeS = 2000` and `NeT = 500` with `t` running 100 to 1100 keeps
`cleanSplitFst` inside `cleanSplitFst_lt_one_iff`'s admissible range -- the
battery asserts the bound rather than trusting the grid -- while the summed
index sweeps 0.12 to 0.91 and the predicted target `R^2` sweeps 0.468 down to
0.084.  The two readings of the index that could be meant, summed and
target-branch-only, are 0.084 and 0.250 at the far cell, so the design
separates them by a factor of three and cannot validate both.

RIVALS, both already falsified elsewhere and both carried here so that a design
in which they PASSED would be known to be broken:

  * the superseded LINEAR retention `r2_0 * max 0 (1 - 2*fst)`, FALSIFIED at 101
    sems by `battery_bulk56`;
  * the ADDITIVE drift-and-LD combination, FALSIFIED at 41 sems by
    `battery_bulk48`, exercised in the LD group where it differs from the
    product at all.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-CLEAN01-KESTREL-20260810"

LEAN_FILE = "PhenomeWidePortability.lean"

# --- the design -----------------------------------------------------------
NE_S, NE_T = 2000.0, 500.0
T_GRID = (100, 250, 500, 800, 1100)
M_LOCI = 20000
N_IND = 40000
BLOCKS = 10
CHUNK = 500
R2_0 = 0.5
PREVALENCE = 0.05


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


# ---------------------------------------------------------------------------
# The Lean bodies, transcribed literally.
# ---------------------------------------------------------------------------
def neutral_drift_factor(ne, t):
    """`neutralDriftFactor Ne t = (1 - 1/(2*Ne))^t`."""
    return (1.0 - 1.0 / (2.0 * ne)) ** t


def fst_from_drift_factor(d):
    """`fstFromDriftFactor d = 1 - d`."""
    return 1.0 - d


def clean_split_fst(ne_s, ne_t, t):
    """`cleanSplitFst NeS NeT t`, the SUM of the two per-branch coefficients."""
    return (fst_from_drift_factor(neutral_drift_factor(ne_s, t))
            + fst_from_drift_factor(neutral_drift_factor(ne_t, t)))


def neutral_portability(r2_0, fst):
    """`neutralPortability r2_0 fst = r2_0(1-fst) / ((1-fst) r2_0 + (1-r2_0))`."""
    return r2_0 * (1.0 - fst) / ((1.0 - fst) * r2_0 + (1.0 - r2_0))


def clean_split_target_r2_at(r2_0, fst, ld):
    """`cleanSplitTargetR2` with its drift index supplied directly."""
    return neutral_portability(r2_0, fst) * ld


def linear_retention_at(r2_0, fst, ld):
    """The SUPERSEDED linear form in `neutralPortability`'s place."""
    return r2_0 * max(0.0, 1.0 - 2.0 * fst) * ld


def implied_fst(r2_0, r2_measured):
    """The `fst` that `neutralPortability` would need to return `r2_measured`.

    A diagnostic, carrying no verdict: it says in the body's own coordinate
    which reading of the index the measurement is asking for.
    """
    x = r2_measured * (1.0 - r2_0) / (r2_0 * (1.0 - r2_measured))
    return 1.0 - x


# --- the liability-threshold chart, transcribed from PresentDayMoments -----
def phi(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def phi_inv(u):
    from scipy.stats import norm
    return float(norm.ppf(u))


def std_normal_pdf(x):
    return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


def liability_threshold(k):
    return phi_inv(1.0 - k)


def liability_case_mean(k):
    return std_normal_pdf(liability_threshold(k)) / k


def liability_control_mean(k):
    return -liability_case_mean(k) * k / (1.0 - k)


def liability_case_variance(r2, k):
    i = liability_case_mean(k)
    return 1.0 - r2 * i * (i - liability_threshold(k))


def liability_control_variance(r2, k):
    ic = liability_control_mean(k)
    return 1.0 - r2 * ic * (ic - liability_threshold(k))


def liability_threshold_auc(r2, k):
    """`liabilityThresholdAUCFromExplainedR2 r2 K`."""
    num = (liability_case_mean(k) - liability_control_mean(k)) * math.sqrt(r2)
    den = math.sqrt(liability_case_variance(r2, k)
                    + liability_control_variance(r2, k))
    return phi(num / den)


# ---------------------------------------------------------------------------
# The engine.
# ---------------------------------------------------------------------------
def ancestral_frequencies(m, rng):
    """A neutral site-frequency spectrum, density proportional to 1/p."""
    lo, hi = math.log(0.01), math.log(0.99)
    return np.exp(rng.random(m) * (hi - lo) + lo)


def drift(p, ne, t, rng):
    """Closed-population Wright-Fisher on frequencies: no mutation, no migration."""
    two_n = int(round(2 * ne))
    for _ in range(t):
        p = rng.binomial(two_n, p) / two_n
    return p


def het(p):
    return 2.0 * p * (1.0 - p)


def genotypes(p, n_ind, rng):
    """Diploid dosages under Hardy-Weinberg, as the SUM OF TWO BERNOULLI draws.

    `rng.binomial(2, p, size=(n, m))` with a vector `p` is the obvious spelling
    and is the one this design cannot afford: it re-enters the binomial
    generator once per entry, and the transport groups need 3e9 entries. Two
    uniform comparisons draw the same distribution -- a dosage is the count of
    two independent alleles, each carried with probability `p` -- at roughly
    forty times the rate.
    """
    return ((rng.random((n_ind, p.size)) < p).astype(np.float64)
            + (rng.random((n_ind, p.size)) < p).astype(np.float64))


def hudson_fst(p1, p2):
    """The PAIRWISE Hudson estimator, ratio of averages -- the reading the
    docstrings record as the wrong one to feed `cleanSplitFst`.

    Written on TRUE frequencies, which is what this engine carries, so it takes
    no finite-sample correction: the correction exists to remove the sampling
    noise of an estimated frequency and there is none here.
    """
    num = (p1 - p2) ** 2
    den = p1 * (1 - p2) + p2 * (1 - p1)
    return float(np.sum(num) / np.sum(den))


def auc_from_ranks(score, case):
    """Mann-Whitney AUC: P(score of a case exceeds score of a control)."""
    order = np.argsort(score, kind="mergesort")
    ranks = np.empty(len(score), dtype=np.float64)
    ranks[order] = np.arange(1, len(score) + 1, dtype=np.float64)
    n1 = int(case.sum())
    n0 = len(score) - n1
    r1 = float(ranks[case].sum())
    return (r1 - n1 * (n1 + 1) / 2.0) / (n1 * n0)


def one_block(t, rng, ld_targets=()):
    """One independent replicate at generation count `t`.

    Returns the realised drift indices and the measured transport quantities.
    Everything the prediction is evaluated at comes from THIS block's own
    realised draw, never from the nominal parameter.
    """
    p0 = ancestral_frequencies(M_LOCI, rng)
    beta = rng.standard_normal(M_LOCI) / math.sqrt(M_LOCI)
    h0 = het(p0)
    va0 = float(np.sum(beta ** 2 * h0))
    ve = va0 * (1.0 - R2_0) / R2_0          # so the ancestral R^2 is exactly R2_0

    p_s = drift(p0, NE_S, t, rng)
    p_t = drift(p0, NE_T, t, rng)
    h_s, h_t = het(p_s), het(p_t)

    # PER-BRANCH Wright F, read as the heterozygosity LOSS against the ancestor,
    # which is the reading `fstFromDriftFactor` was validated at.
    f_s = 1.0 - float(np.mean(h_s)) / float(np.mean(h0))
    f_t = 1.0 - float(np.mean(h_t)) / float(np.mean(h0))
    ret_s = float(np.mean(h_s)) / float(np.mean(h0))
    hud = hudson_fst(p_s, p_t)

    poly_s = (p_s > 0.0) & (p_s < 1.0)
    w_pa = np.where(poly_s, beta, 0.0)
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(h_t > 0.0, h_s / np.maximum(h_t, 1e-300), 0.0)
    w_std = np.where(poly_s & (h_t > 0.0), beta * np.sqrt(ratio), 0.0)

    gv = np.zeros(N_IND)
    s_pa = np.zeros(N_IND)
    s_std = np.zeros(N_IND)
    for lo in range(0, M_LOCI, CHUNK):
        hi = min(lo + CHUNK, M_LOCI)
        g = genotypes(p_t[lo:hi], N_IND, rng)
        gv += g @ beta[lo:hi]
        s_pa += g @ w_pa[lo:hi]
        s_std += g @ w_std[lo:hi]
    y = gv + rng.standard_normal(N_IND) * math.sqrt(ve)

    r2_pa = float(np.corrcoef(s_pa, y)[0, 1]) ** 2
    r2_std = float(np.corrcoef(s_std, y)[0, 1]) ** 2

    # AUC on the per-allele score at the required prevalence, cases being the
    # upper tail of the realised liability.
    thresh = float(np.quantile(y, 1.0 - PREVALENCE))
    case = y > thresh
    auc = auc_from_ranks(s_pa, case)

    # The LD stage, isolated: the same score carrying independent tagging noise,
    # with the realised LD factor measured rather than assumed.
    ld_rows = []
    v_s = float(np.var(s_pa))
    for lam in ld_targets:
        noise = rng.standard_normal(N_IND) * math.sqrt(v_s * (1.0 - lam) / lam)
        s_ld = s_pa + noise
        ld_meas = float(np.corrcoef(s_ld, s_pa)[0, 1]) ** 2
        r2_ld = float(np.corrcoef(s_ld, y)[0, 1]) ** 2
        ld_rows.append((lam, ld_meas, r2_ld))

    return dict(f_s=f_s, f_t=f_t, ret_s=ret_s, hudson=hud, r2_pa=r2_pa,
                r2_std=r2_std, auc=auc, ld=ld_rows,
                fixed_s=float(np.mean(~poly_s)),
                signal_lost_s=1.0 - float(np.sum(beta ** 2 * h_t * poly_s)
                                          / max(np.sum(beta ** 2 * h_t), 1e-300)))


def blocked(vals):
    a = np.asarray(vals, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


def paired(pred, meas):
    """(mean prediction, mean measurement, sem of the PAIRED difference).

    The prediction is re-evaluated in every block at that block's own realised
    drift index, so the block-to-block scatter shared by the two sides cancels
    and the error bar is the one the comparison actually needs.
    """
    p = np.asarray(pred, float)
    m = np.asarray(meas, float)
    d = m - p
    return (float(p.mean()), float(m.mean()),
            float(d.std(ddof=1) / math.sqrt(d.size)))


# ---------------------------------------------------------------------------
def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-CLEAN01-KESTREL-20260810")

    # THE ADMISSIBLE RANGE, asserted rather than assumed.  `cleanSplitFst_lt_one_iff`
    # says the composition is defined exactly where the two retentions sum above one.
    print("\nadmissibility (cleanSplitFst_lt_one_iff: retentions must sum above 1):")
    for t in T_GRID:
        s = neutral_drift_factor(NE_S, t) + neutral_drift_factor(NE_T, t)
        print("  t=%-5d retention sum %.4f   cleanSplitFst %.4f  %s"
              % (t, s, clean_split_fst(NE_S, NE_T, t),
                 "ADMISSIBLE" if s > 1.0 else "OUT OF RANGE"))
        assert s > 1.0, "t=%d leaves the admissible range" % t

    rng = np.random.default_rng(20260810)
    runs = {}
    for t in (0,) + T_GRID:
        lam = (0.5, 0.7, 0.9) if t in (0, 500) else ()
        runs[t] = [one_block(t, rng, ld_targets=lam) for _ in range(BLOCKS)]
        b = runs[t]
        print("\n  t=%-5d F_S %.4f  F_T %.4f  sum %.4f   Hudson pairwise %.4f"
              % (t, np.mean([x["f_s"] for x in b]),
                 np.mean([x["f_t"] for x in b]),
                 np.mean([x["f_s"] + x["f_t"] for x in b]),
                 np.mean([x["hudson"] for x in b])))
        r2pa = float(np.mean([x["r2_pa"] for x in b]))
        r2std = float(np.mean([x["r2_std"] for x in b]))
        print("          target R2 per-allele %.4f (implied fst %.4f)   "
              "standardised %.4f (implied fst %.4f)"
              % (r2pa, implied_fst(R2_0, r2pa), r2std, implied_fst(R2_0, r2std)))
        print("          source-fixed loci %.3f, of the target's signal %.4f; "
              "measured AUC %.4f"
              % (np.mean([x["fixed_s"] for x in b]),
                 np.mean([x["signal_lost_s"] for x in b]),
                 np.mean([x["auc"] for x in b])))

    # ---- CONTROLS ---------------------------------------------------------
    # One branch's realised heterozygosity retention against `neutralDriftFactor`,
    # a separately VALIDATED body, on this battery's own resampling path.
    b = runs[T_GRID[-1]]
    cm, cs = blocked([x["ret_s"] for x in b])
    drift_control = dict(
        design="source branch retention at t=%d must be neutralDriftFactor "
               "(1-1/(2*NeS))^t" % T_GRID[-1],
        lean=neutral_drift_factor(NE_S, T_GRID[-1]), truth=cm,
        sem=max(cs, 1e-12))
    print("\n  CONTROL %s: predicted %.6f measured %.6f +/- %.6f"
          % (drift_control["design"], drift_control["lean"],
             drift_control["truth"], drift_control["sem"]))

    # At t = 0 nothing has drifted, so the measured target R^2 must be the
    # constructed V_A/(V_A+V_E).
    cm, cs = blocked([x["r2_pa"] for x in runs[0]])
    r2_control = dict(
        design="t=0 [target R2 must be the constructed r2_0 = V_A/(V_A+V_E)]",
        lean=R2_0, truth=cm, sem=max(cs, 1e-12))
    print("  CONTROL %s: predicted %.6f measured %.6f +/- %.6f"
          % (r2_control["design"], r2_control["lean"], r2_control["truth"],
             r2_control["sem"]))

    cm, cs = blocked([x["auc"] for x in runs[0]])
    auc_control = dict(
        design="t=0 [AUC must be the already-VALIDATED chart at r2_0]",
        lean=liability_threshold_auc(R2_0, PREVALENCE), truth=cm,
        sem=max(cs, 1e-12))
    print("  CONTROL %s: predicted %.6f measured %.6f +/- %.6f"
          % (auc_control["design"], auc_control["lean"], auc_control["truth"],
             auc_control["sem"]))

    # ---- GROUP: cleanSplitFst --------------------------------------------
    sum_cells, hud_cells = [], []
    for t in T_GRID:
        b = runs[t]
        lean = clean_split_fst(NE_S, NE_T, t)
        m, s = blocked([x["f_s"] + x["f_t"] for x in b])
        lab = "t=%d NeS=%d NeT=%d" % (t, NE_S, NE_T)
        sum_cells.append(dict(design=lab, lean=lean, truth=m, sem=max(s, 1e-12)))
        hm, hs = blocked([x["hudson"] for x in b])
        hud_cells.append(dict(design=lab, lean=lean, truth=hm,
                              sem=max(hs, 1e-12)))

    reg_fst = (
        "clean two-branch split, forward Wright-Fisher on allele frequencies, "
        "%d loci from a neutral 1/p spectrum, NeS=%d and NeT=%d closed, no "
        "mutation and no migration, %d independent blocks. The oracle is the "
        "realised PER-BRANCH heterozygosity loss 1 - H_branch/H_ancestor summed "
        "over the two lineages, which is the reading fstFromDriftFactor was "
        "validated at; the prediction is evaluated at the model's Ne and t, "
        "which the simulation realises exactly. Every cell stays inside "
        "cleanSplitFst_lt_one_iff's admissible range, asserted in the run"
        % (M_LOCI, NE_S, NE_T, BLOCKS))
    record("cleanSplitFst", LEAN_FILE,
           "fstFromDriftFactor (neutralDriftFactor NeS t) + "
           "fstFromDriftFactor (neutralDriftFactor NeT t)",
           sum_cells, regime=reg_fst, control=drift_control,
           realised_inputs=True, argument_source="model")
    record("cleanSplitFst [read as the PAIRWISE Hudson F_ST between the two "
           "branches, the convention the docstrings forbid, competing]",
           LEAN_FILE,
           "same body, oracle replaced by the pairwise Hudson estimator",
           hud_cells, regime=reg_fst, control=drift_control,
           realised_inputs=True, argument_source="model",
           note="carried so the two conventions can be seen to be different "
                "numbers rather than assumed to be")

    # ---- GROUP: cleanSplitTargetR2 ---------------------------------------
    reg_r2 = (
        "same engine and same blocks, %d target individuals each. TRUE causal "
        "effects with no estimation noise, so no GWAS-inefficiency confound is "
        "present and r2_0 is fixed by construction at V_A/(V_A+V_E) = %.2f, "
        "realised exactly in every block because the environmental variance is "
        "set from that block's own realised ancestral V_A. "
        "ldFactor = 1: the frequency engine carries no linkage, so the "
        "score is perfectly tagging by construction and the LD slot is "
        "exercised, not measured, here. The prediction is re-evaluated in each "
        "block at that block's own realised summed per-branch F, and the error "
        "bar is the sem of the PAIRED difference across blocks. The observable "
        "is the realised squared correlation between the source-built score and "
        "the target phenotype" % (N_IND, R2_0))

    for tag, key, extra in (
            ("", "r2_pa",
             "PER-ALLELE score over the variants still polymorphic in the "
             "source, which is what a real PGS is: the source branch enters "
             "only by removing source-fixed variants from the score, and their "
             "signal remains in the target phenotype as unexplained heritable "
             "variance"),
            (" [SOURCE-STANDARDISED score, the construction under which a "
             "summed index has a mechanism]", "r2_std",
             "the GWAS reports effects per source-genotype SD and the target "
             "restandardises by target frequencies, so the weight carries "
             "sqrt(h_S/h_T). This construction is SYMMETRIC in the two "
             "branches and is the body's best case; it is recorded so that a "
             "falsification cannot be a report about the score construction")):
        preds, meas, lin_preds = [], [], []
        cells, lin_cells = [], []
        for t in T_GRID:
            b = runs[t]
            fsts = [x["f_s"] + x["f_t"] for x in b]
            p = [clean_split_target_r2_at(R2_0, f, 1.0) for f in fsts]
            lp = [linear_retention_at(R2_0, f, 1.0) for f in fsts]
            mm = [x[key] for x in b]
            lean, truth, sem = paired(p, mm)
            lab = "t=%d (summed F %.3f)" % (t, float(np.mean(fsts)))
            cells.append(dict(design=lab, lean=lean, truth=truth,
                              sem=max(sem, 1e-12)))
            lean_l, _, sem_l = paired(lp, mm)
            lin_cells.append(dict(design=lab, lean=lean_l, truth=truth,
                                  sem=max(sem_l, 1e-12)))
            preds.append(lean)
            meas.append(truth)
            lin_preds.append(lean_l)
        record("cleanSplitTargetR2" + tag, LEAN_FILE,
               "neutralPortability r2_0 (cleanSplitFst NeS NeT t) * ldFactor",
               cells, regime=reg_r2, control=r2_control, note=extra,
               realised_inputs=True, argument_source="model")
        record("cleanSplitTargetR2 [the SUPERSEDED linear retention "
               "r2_0*max 0 (1-2*fst) in neutralPortability's place, "
               "competing%s]" % (", standardised score" if tag else ""),
               LEAN_FILE, "r2_0 * max 0 (1 - 2 * cleanSplitFst) * ldFactor",
               lin_cells, regime=reg_r2, control=r2_control,
               realised_inputs=True, argument_source="model",
               note="FALSIFIED at 101 sems by battery_bulk56; carried so that a "
                    "design in which it passed would be known to be broken")

    # The reading in which only the TARGET branch's index enters, carried as a
    # competitor so the record says which convention the measurement asks for.
    for tag, key in (("", "r2_pa"), (", standardised score", "r2_std")):
        cells = []
        for t in T_GRID:
            b = runs[t]
            p = [clean_split_target_r2_at(R2_0, x["f_t"], 1.0) for x in b]
            mm = [x[key] for x in b]
            lean, truth, sem = paired(p, mm)
            cells.append(dict(design="t=%d (target-branch F %.3f)"
                                     % (t, float(np.mean([x["f_t"] for x in b]))),
                              lean=lean, truth=truth, sem=max(sem, 1e-12)))
        record("cleanSplitTargetR2 [the TARGET-BRANCH-ONLY index in the fst "
               "slot, not the sum, competing%s]" % tag, LEAN_FILE,
               "neutralPortability r2_0 (fstFromDriftFactor "
               "(neutralDriftFactor NeT t)) * ldFactor",
               cells, regime=reg_r2, control=r2_control,
               realised_inputs=True, argument_source="model",
               note="the alternative reading of the composition's fst slot")

    # The DECOMPOSITION, recorded so that the falsification above says WHERE the
    # composition parts from the measurement rather than only that it does.
    #
    # It is not a candidate law and must not be read as one: both of its factors
    # are measured on the same replicates, so it has the standing of the "drift
    # stage measured" row in the LD group below -- a statement about which two
    # effects the residual is made of, addressed to whoever writes the
    # replacement. Writing a body from it would be fitting a law to the
    # simulation that was supposed to test one.
    cells = []
    for t in T_GRID:
        b = runs[t]
        p = [clean_split_target_r2_at(R2_0, x["f_t"], 1.0)
             * (1.0 - x["signal_lost_s"]) for x in b]
        mm = [x["r2_pa"] for x in b]
        lean, truth, sem = paired(p, mm)
        cells.append(dict(design="t=%d (target-branch F %.3f, source-polymorphic "
                                 "signal %.3f)"
                                 % (t, float(np.mean([x["f_t"] for x in b])),
                                    1 - float(np.mean([x["signal_lost_s"]
                                                       for x in b]))),
                          lean=lean, truth=truth, sem=max(sem, 1e-12)))
    record("cleanSplitTargetR2 [DECOMPOSITION, both factors measured: the "
           "target-branch index through the chart, times the fraction of the "
           "target's signal still polymorphic in the source, competing]",
           LEAN_FILE,
           "neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor "
           "NeT t)) * (measured source-polymorphic signal fraction)",
           cells, regime=reg_r2, control=r2_control,
           realised_inputs=True, argument_source="model",
           note="NOT A CANDIDATE BODY -- it carries a measured factor and so "
                "cannot be evaluated from a law's arguments. It is here to name "
                "the two effects the summed reading conflates: the target "
                "branch's own heterozygosity loss, which the chart handles, and "
                "the source branch's fixation, which removes variants from the "
                "score without removing their variance from the target "
                "phenotype")

    # ---- GROUP: the LD stage, isolated -----------------------------------
    # The drift stage is taken from the MEASURED no-LD target R^2, so this group
    # asks only whether the LD retention MULTIPLIES that or ADDS to it, which is
    # `cleanSplitTargetR2_eq_ratioLD_scaling`'s content.
    mult_cells, add_cells = [], []
    for t in (0, 500):
        b = runs[t]
        for i, lam in enumerate((0.5, 0.7, 0.9)):
            base = [x["r2_pa"] for x in b]
            ldm = [x["ld"][i][1] for x in b]
            meas = [x["ld"][i][2] for x in b]
            mp = [a * l for a, l in zip(base, ldm)]
            ap = [max(0.0, a + l - 1.0) for a, l in zip(base, ldm)]
            lab = "t=%d ldFactor=%.2f" % (t, lam)
            lean, truth, sem = paired(mp, meas)
            mult_cells.append(dict(design=lab, lean=lean, truth=truth,
                                   sem=max(sem, 1e-12)))
            lean_a, _, sem_a = paired(ap, meas)
            add_cells.append(dict(design=lab, lean=lean_a, truth=truth,
                                  sem=max(sem_a, 1e-12)))
    reg_ld = (
        "the LD stage isolated: the drift stage is the MEASURED no-LD target "
        "R-squared on the same replicates, so only the combination rule is "
        "under test. The score carries independent tagging noise and the "
        "realised LD factor is MEASURED as its squared correlation with the "
        "untagged score, not assumed. The multiplicative reading follows from "
        "the tag affecting the phenotype only through the causal score, which "
        "this design instantiates, so the group's content is the REJECTION of "
        "the additive reading and the check that the drift penalty is not "
        "applied a second time inside the LD stage")
    record("cleanSplitTargetR2 [LD stage MULTIPLICATIVE, drift stage measured, "
           "competing]", LEAN_FILE,
           "(measured no-LD target R2) * ldFactor", mult_cells,
           regime=reg_ld, control=r2_control, realised_inputs=True,
           argument_source="model")
    record("cleanSplitTargetR2 [LD stage ADDITIVE, the reading FALSIFIED at 41 "
           "sems by battery_bulk48, competing]", LEAN_FILE,
           "(measured no-LD target R2) + ldFactor - 1", add_cells,
           regime=reg_ld, control=r2_control, realised_inputs=True,
           argument_source="model")

    # ---- GROUP: cleanSplitTargetAUC --------------------------------------
    auc_cells, auc_lin_cells = [], []
    for t in T_GRID:
        b = runs[t]
        fsts = [x["f_s"] + x["f_t"] for x in b]
        p = [liability_threshold_auc(
            max(clean_split_target_r2_at(R2_0, f, 1.0), 1e-9), PREVALENCE)
            for f in fsts]
        lp = [liability_threshold_auc(
            max(linear_retention_at(R2_0, f, 1.0), 1e-9), PREVALENCE)
            for f in fsts]
        mm = [x["auc"] for x in b]
        lean, truth, sem = paired(p, mm)
        lab = "t=%d K=%.2f (summed F %.3f)" % (t, PREVALENCE, float(np.mean(fsts)))
        auc_cells.append(dict(design=lab, lean=lean, truth=truth,
                              sem=max(sem, 1e-12)))
        lean_l, _, sem_l = paired(lp, mm)
        auc_lin_cells.append(dict(design=lab, lean=lean_l, truth=truth,
                                  sem=max(sem_l, 1e-12)))
    reg_auc = (
        "same replicates and the same per-allele score. Cases are the upper "
        "%.0f%% of the realised target liability and the observable is the "
        "Mann-Whitney AUC of the score between cases and controls. Prevalence "
        "is supplied to the chart as the body requires it to be; the chart "
        "itself is separately VALIDATED at pooled RMSE 0.0121, so what this "
        "group adds is whether the R-squared the clean-split law computes is "
        "the explained-variance fraction that chart's argument expects"
        % (100 * PREVALENCE))
    record("cleanSplitTargetAUC", LEAN_FILE,
           "liabilityThresholdAUCFromExplainedR2 (cleanSplitTargetR2 r2_0 NeS "
           "NeT t ldFactor) K", auc_cells, regime=reg_auc, control=auc_control,
           realised_inputs=True, argument_source="model")
    record("cleanSplitTargetAUC [the SUPERSEDED linear retention carried "
           "through the same chart, competing]", LEAN_FILE,
           "liabilityThresholdAUCFromExplainedR2 (r2_0 * max 0 (1 - 2*fst)) K",
           auc_lin_cells, regime=reg_auc, control=auc_control,
           realised_inputs=True, argument_source="model")

    dump_results("battery_clean01_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-34s %-64s worst %9.2f sems, %8.2f%% rel"
              % (r["verdict"], r["name"][:64], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
