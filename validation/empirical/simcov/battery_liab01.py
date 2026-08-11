"""Battery liab01: the probit liability model read at a score, and its index scale.

THREE DECLARATIONS, all of them compositions over an already-measured
threshold convention and all of them recorded as UNTESTED:

    liabilityRiskAtScore r2 K z  =  Phi((sqrt r2 * z - liabilityThreshold K)
                                        / sqrt (1 - r2))
    orPerSDFromLiability r2 K    =  odds(risk at z=1) / odds(risk at z=0)
    indexScaleTrueIndexR2 rho s  =  rho^2 / (rho^2 + s^2)

THE SIGN IS THE THING THE FIRST BODY IS ABOUT.  `liabilityThreshold K` is the
UPPER-tail quantile `Phi^{-1}(1-K)`, so the threshold enters the index with a
MINUS and the risk at zero explained variance is `Phi(-T) = K`.  The `+T`
reading returns `1 - K` instead -- a 95% risk at average score for a
5%-prevalence disease -- and is FALSIFIED at 3390 sems in `liabilityThreshold`'s
own record.  It is carried here as a competitor in the same cells, because the
two readings coincide at `K = 1/2` and at no other prevalence, and a design that
never ran it could not say which one it had confirmed.

THE ODDS RATIO IS THE FIRST STANDARD DEVIATION'S, AND THE ESTIMATOR RESPECTS
THAT.  The model is probit and the metric is logistic: an odds ratio is constant
per SD only under a logistic link, so `orPerSDFromLiability` is the ratio between
`z = 1` and `z = 0` specifically and not a slope that may be extrapolated.  The
measurement therefore bins NARROWLY around those two scores and takes the case
rate inside each bin.  A logistic regression fitted over the whole score range
is carried in the same cells AS A COMPETITOR, so the docstring's warning that
such a fit "will recover something between this and the odds ratio at other
points" is a measured statement rather than an expectation.  The RISK ratio is
carried the same way, since the docstring says the two agree only in the
rare-disease limit and the design sweeps prevalence from 0.05 to 0.20.  It stops
at 0.05 rather than going rarer, and the constant beside `GRID_K` records why:
below that the odds ratio's own denominator is too rare to measure inside the
harness's 2% relative floor, so a rarer cell could contribute a spurious
falsification and nothing else.

THE INDEX SCALE IS NOT THE RISK SCALE, and that is the whole content of the
third group.  `indexScaleTrueIndexR2` claims a squared correlation between two
PROBIT INDICES; a simulation reports most easily the squared correlation between
RISKS, which are the indices after the `Phi` warp, and `Phi` is not affine.  Both
are measured on the same draws and the same body is compared against each.  The
index-scale row is the corpus's claim; the risk-scale row is the design the
docstring warns a battery would reach for first, and it is recorded as a
competitor so the size of the gap is on the record.

WHAT THE INDEX GROUP CAN AND CANNOT ESTABLISH.  The projection identity is a
closed derivation, so agreement on the ratio is close to a construction check
and is not claimed as more.  What the group does decide is carried by the
rivals: `rho^2` alone (the standardised-score special case mistaken for the
general body) and `rho/(rho + s)` (the unsquared reading) are both run on cells
where `s^2 != 1 - rho^2`, which is exactly where they part company from the body,
and the slope-and-intercept cells decide the claim that the affine wrapper
cancels.  A design confined to standardised scores would validate all three.

CONTROLS, one per group, each independently known and each able to fail on an
engine error rather than on sampling noise:

  * the risk and odds groups are gated on the case rate inside the `z = 1` bin
    at `r2 = 0`, which must be the prevalence `K` itself.  It fails on a wrong
    threshold quantile, a wrong tail, a mis-built bin or a mis-drawn liability,
    and it is the boundary case `liabilityRiskAtScore_at_zero_r2_eq_prevalence`
    proves.
  * the index group is gated on `Var(rho z + s eps) = rho^2 + s^2`, the variance
    decomposition, which is not the body's ratio and fails on a draw slip.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-LIAB01-AVOCET-20260810"

LEAN_FILE = "PhenomeWidePortability.lean"

N_IND = 20_000_000
BLOCKS = 8

# THE RAREST PREVALENCE IS 0.05 AND THAT IS A PRECISION BOUND, NOT A CHOICE
# ABOUT THE BODY.  The odds ratio's denominator is the case rate inside the
# `z = 0` bin, and at `K = 0.01` with `r2 = 0.6` that rate is `1.2e-4`: the bin
# holds 4% of the draws, so 160 million individuals buy about 750 cases and a
# 4% relative error bar.  The harness clears a cell only when a disagreement
# exceeds BOTH 3 sems and 2% relative, so a cell whose own noise is 4% can
# never be cleared by the relative floor -- every 3-sem excursion it produces is
# automatically over 2%, and the only thing such a cell can contribute is a
# spurious falsification.  At `K = 0.05` the same corner rests on `4.6e-3`,
# about 29500 cases, and 3 sems is 1.8% -- inside the floor, so the floor does
# the job it exists for.  The rare-disease claim the docstring makes about the
# risk ratio is still decided, by the 0.05-to-0.20 contrast.
GRID_R2 = (0.10, 0.30, 0.60)
GRID_K = (0.05, 0.10, 0.20)


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
def phi(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def phi_arr(x):
    from scipy.special import ndtr
    return ndtr(x)


def liability_threshold(k):
    """`liabilityThreshold K = Function.invFun Phi (1 - K)`, the UPPER-tail
    quantile."""
    from scipy.stats import norm
    return float(norm.ppf(1.0 - k))


def liability_risk_at_score(r2, k, z):
    """`liabilityRiskAtScore r2 K z`."""
    return phi((math.sqrt(r2) * z - liability_threshold(k))
               / math.sqrt(1.0 - r2))


def liability_risk_at_score_plus_t(r2, k, z):
    """The `+T` sign slip, FALSIFIED at 3390 sems in liabilityThreshold's record."""
    return phi((math.sqrt(r2) * z + liability_threshold(k))
               / math.sqrt(1.0 - r2))


def odds(p):
    return p / (1.0 - p)


def or_per_sd_from_liability(r2, k, risk=liability_risk_at_score):
    """`orPerSDFromLiability r2 K`, with the risk body swappable for a rival."""
    return odds(risk(r2, k, 1.0)) / odds(risk(r2, k, 0.0))


def risk_ratio_per_sd(r2, k):
    """The RATIO OF RISKS in the odds ratio's place: the reading the docstring
    says agrees only in the rare-disease limit."""
    return liability_risk_at_score(r2, k, 1.0) / liability_risk_at_score(r2, k, 0.0)


def index_scale_true_index_r2(rho, s):
    """`indexScaleTrueIndexR2 rho s = rho^2 / (rho^2 + s^2)`."""
    return rho ** 2 / (rho ** 2 + s ** 2)


# ---------------------------------------------------------------------------
def blocked(vals):
    a = np.asarray(vals, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


def paired(pred, meas):
    p = np.asarray(pred, float)
    m = np.asarray(meas, float)
    d = m - p
    return (float(p.mean()), float(m.mean()),
            float(d.std(ddof=1) / math.sqrt(d.size)))


def logistic_slope(z, case):
    """exp(beta) from a logistic regression of case status on the score.

    Newton-Raphson on the two-parameter model, fitted over the WHOLE score
    range, which is the estimator the docstring warns recovers something
    between the first-SD odds ratio and the odds ratio elsewhere.
    """
    y = case.astype(np.float64)
    b0, b1 = 0.0, 0.0
    for _ in range(30):
        eta = b0 + b1 * z
        p = 1.0 / (1.0 + np.exp(-eta))
        w = p * (1.0 - p)
        r = y - p
        s0, s1 = float(r.sum()), float((r * z).sum())
        h00 = float(w.sum())
        h01 = float((w * z).sum())
        h11 = float((w * z * z).sum())
        det = h00 * h11 - h01 * h01
        if det <= 0:
            break
        d0 = (h11 * s0 - h01 * s1) / det
        d1 = (h00 * s1 - h01 * s0) / det
        b0 += d0
        b1 += d1
        if abs(d0) + abs(d1) < 1e-12:
            break
    return math.exp(b1)


def risk_block(r2, k, rng, want_logistic=False):
    """One replicate of the liability-threshold model at (r2, K).

    THE SCORE IS HELD AT EXACTLY `z` RATHER THAN BINNED NEAR IT, and the change
    is not cosmetic. `liabilityRiskAtScore r2 K z` is the risk AT a score; a bin
    of half-width `h` measures the risk AVERAGED over the bin, which differs by
    the curvature of the risk curve across it -- `h²/6` times the second
    derivative, to leading order. An earlier run of this battery binned at
    `h = 0.05` and its own regime string claimed the resulting smear was "far
    below the sampling error". The run refuted that: the body came back at 5.7
    sems and 0.42% relative, and 0.42% is what the curvature term predicts at
    the worst cell. The verdict survived only because the harness's 2% relative
    floor caught it, which is the floor covering for a known estimator bias
    rather than the design being right.

    Conditioning on the score exactly is also the cheaper estimator by two
    orders of magnitude: the bin held 2.4% of the draws and this holds all of
    them, which is what buys the rare-prevalence corner enough cases to sit
    inside the relative floor.

    The population draw is still made, because the marginal prevalence is this
    battery's control and the logistic competitor is fitted on it.
    """
    thr = liability_threshold(k)
    out = {}
    for lab, centre in (("z1", 1.0), ("z0", 0.0)):
        e = rng.standard_normal(N_IND)
        liability = math.sqrt(r2) * centre + math.sqrt(1.0 - r2) * e
        out[lab] = float(np.mean(liability > thr))
        out[lab + "_n"] = N_IND
    out["or"] = odds(out["z1"]) / odds(out["z0"])
    out["rr"] = out["z1"] / out["z0"]

    z = rng.standard_normal(N_IND)
    e = rng.standard_normal(N_IND)
    case = (math.sqrt(r2) * z + math.sqrt(1.0 - r2) * e) > thr
    out["prev"] = float(np.mean(case))
    if want_logistic:
        # Subsampled: the fit is O(n) per Newton step and the slope is a
        # population quantity, so a twentieth of the draws carries it.
        sub = slice(None, N_IND // 20)
        out["logit_or"] = logistic_slope(z[sub], case[sub])
    return out


def index_block(rho, s, a, b, k, r2_index, rng):
    """One replicate of the two-index projection, measured on both scales."""
    n = N_IND // 4
    z = rng.standard_normal(n)
    eps = rng.standard_normal(n)
    zhat = rho * z + s * eps
    i_true = a + b * z
    i_score = a + b * zhat
    idx = float(np.corrcoef(i_score, i_true)[0, 1]) ** 2
    risk = float(np.corrcoef(phi_arr(i_score), phi_arr(i_true))[0, 1]) ** 2
    return dict(index=idx, risk=risk, var_zhat=float(np.var(zhat)))


# ---------------------------------------------------------------------------
def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-LIAB01-AVOCET-20260810")

    rng = np.random.default_rng(20260810)

    # =====================================================================
    # GROUPS A and B: liabilityRiskAtScore and orPerSDFromLiability.
    # =====================================================================
    grid = [(r2, k) for r2 in GRID_R2 for k in GRID_K]
    runs = {}
    print("\n  %-16s %10s %10s %10s %10s %10s"
          % ("cell", "risk z=1", "risk z=0", "OR meas", "OR lean", "logistic"))
    for r2, k in grid:
        b = [risk_block(r2, k, rng, want_logistic=True) for _ in range(BLOCKS)]
        runs[(r2, k)] = b
        print("  r2=%.2f K=%.2f %10.5f %10.5f %10.4f %10.4f %10.4f"
              % (r2, k, np.mean([x["z1"] for x in b]),
                 np.mean([x["z0"] for x in b]), np.mean([x["or"] for x in b]),
                 or_per_sd_from_liability(r2, k),
                 np.mean([x["logit_or"] for x in b])))

    # CONTROL, designated A PRIORI and not selected as the worst of the design's
    # cells: the MARGINAL prevalence in a population draw at (r2=0.30, K=0.05)
    # must be K itself. It is independent of every body in this file -- no risk
    # at a score, no odds ratio, no index ratio enters it -- and it fails on a
    # wrong quantile, a wrong tail, or a liability whose two components do not
    # compose to unit variance, which is the whole engine these groups share.
    ctrl_r2, ctrl_k = 0.30, 0.05
    cm, cs = blocked([x["prev"] for x in runs[(ctrl_r2, ctrl_k)]])
    risk_control = dict(
        design="r2=%.2f [the marginal case rate must be the prevalence K=%.2f]"
               % (ctrl_r2, ctrl_k),
        lean=ctrl_k, truth=cm, sem=max(cs, 1e-12))
    print("\n  CONTROL %s: predicted %.6f measured %.6f +/- %.6f"
          % (risk_control["design"], risk_control["lean"],
             risk_control["truth"], risk_control["sem"]))

    # Printed as a diagnostic and NOT used as the gate: at r2 = 0 the risk is
    # flat at the prevalence for every score, which is
    # `liabilityRiskAtScore_at_zero_r2_eq_prevalence`. Two controls cannot both
    # gate one record, and taking whichever of them looks worse is the
    # worst-of-N selection this harness has a gate against.
    cb = [risk_block(1e-12, ctrl_k, rng) for _ in range(BLOCKS)]
    zm, zs = blocked([x["z1"] for x in cb])
    print("  DIAGNOSTIC r2=0: risk at z=1 measured %.6f +/- %.6f (must be K=%.2f)"
          % (zm, zs, ctrl_k))

    reg_risk = (
        "direct liability-threshold simulation: liability = sqrt(r2)*z + "
        "sqrt(1-r2)*e with z the standardised score and e independent standard "
        "normal, a case being a liability above liabilityThreshold K. %d "
        "individuals per block at each score, %d independent blocks. The risk "
        "at a score is measured with the score HELD AT EXACTLY that value and "
        "only the residual drawn, so the observable is the risk AT the score "
        "and not the risk averaged over a neighbourhood of it: an earlier "
        "binned version of this design carried a curvature smear of 0.42%%, "
        "which is inside the harness's relative floor but was visible at 5.7 "
        "sems, and a floor covering for a known estimator bias is not a design "
        "that is right. The prediction is evaluated at the model's own r2 and "
        "K, which the simulation realises exactly"
        % (N_IND, BLOCKS))

    risk_cells, risk_plus_cells = [], []
    for r2, k in grid:
        b = runs[(r2, k)]
        for lab, centre in (("z=1", 1.0), ("z=0", 0.0)):
            key = "z1" if centre == 1.0 else "z0"
            m, s = blocked([x[key] for x in b])
            d = "r2=%.2f K=%.2f %s" % (r2, k, lab)
            risk_cells.append(dict(design=d,
                                   lean=liability_risk_at_score(r2, k, centre),
                                   truth=m, sem=max(s, 1e-12)))
            risk_plus_cells.append(
                dict(design=d,
                     lean=liability_risk_at_score_plus_t(r2, k, centre),
                     truth=m, sem=max(s, 1e-12)))
    record("liabilityRiskAtScore", LEAN_FILE,
           "Phi((sqrt r2 * z - liabilityThreshold K) / sqrt (1 - r2))",
           risk_cells, regime=reg_risk, control=risk_control,
           realised_inputs=True, argument_source="model")
    record("liabilityRiskAtScore [the +T sign slip, FALSIFIED at 3390 sems in "
           "liabilityThreshold's record, competing]", LEAN_FILE,
           "Phi((sqrt r2 * z + liabilityThreshold K) / sqrt (1 - r2))",
           risk_plus_cells, regime=reg_risk, control=risk_control,
           realised_inputs=True, argument_source="model",
           note="the two readings coincide at K = 1/2 and nowhere else, so a "
                "design that never ran it could not say which it confirmed")

    or_cells, or_rr_cells, or_logit_cells, or_plus_cells = [], [], [], []
    for r2, k in grid:
        b = runs[(r2, k)]
        d = "r2=%.2f K=%.2f" % (r2, k)
        m, s = blocked([x["or"] for x in b])
        or_cells.append(dict(design=d, lean=or_per_sd_from_liability(r2, k),
                             truth=m, sem=max(s, 1e-12)))
        or_plus_cells.append(dict(
            design=d,
            lean=or_per_sd_from_liability(r2, k,
                                          risk=liability_risk_at_score_plus_t),
            truth=m, sem=max(s, 1e-12)))
        rm, rs = blocked([x["rr"] for x in b])
        or_rr_cells.append(dict(design=d, lean=risk_ratio_per_sd(r2, k),
                                truth=rm, sem=max(rs, 1e-12)))
        lm, ls = blocked([x["logit_or"] for x in b])
        or_logit_cells.append(dict(design=d,
                                   lean=or_per_sd_from_liability(r2, k),
                                   truth=lm, sem=max(ls, 1e-12)))
    reg_or = reg_risk + (
        ". The odds ratio is the FIRST standard deviation's specifically: it is "
        "the ratio of the odds inside the z=1 bin to the odds inside the z=0 "
        "bin, and no slope is fitted, because under a probit model the odds "
        "ratio per SD is not constant and a fitted slope is a different "
        "quantity")
    record("orPerSDFromLiability", LEAN_FILE,
           "(risk(1)/(1-risk(1))) / (risk(0)/(1-risk(0))), "
           "risk = liabilityRiskAtScore r2 K", or_cells,
           regime=reg_or, control=risk_control,
           realised_inputs=True, argument_source="model")
    record("orPerSDFromLiability [the +T sign slip carried through the same "
           "odds ratio, competing]", LEAN_FILE,
           "same ratio built from Phi((sqrt r2 * z + T)/sqrt(1-r2))",
           or_plus_cells, regime=reg_or, control=risk_control,
           realised_inputs=True, argument_source="model")
    record("orPerSDFromLiability [the RISK ratio in the odds ratio's place, "
           "competing]", LEAN_FILE, "risk(1) / risk(0)", or_rr_cells,
           regime=reg_or, control=risk_control,
           realised_inputs=True, argument_source="model",
           note="the docstring says the two agree only in the rare-disease "
                "limit; the design sweeps prevalence from 0.05 to 0.20 so the "
                "claim is decided rather than assumed")
    record("orPerSDFromLiability [against a LOGISTIC slope fitted over the "
           "whole score range, competing]", LEAN_FILE,
           "same body, oracle replaced by exp(beta) from a fitted logistic",
           or_logit_cells, regime=reg_or, control=risk_control,
           realised_inputs=True, argument_source="model",
           note="the docstring's caveat measured: a wide-range logistic fit "
                "recovers something between the first-SD odds ratio and the "
                "odds ratio at other points, so this row is EXPECTED to "
                "disagree and its disagreement is the caveat's evidence, not a "
                "defect in the body")

    # =====================================================================
    # GROUP C: indexScaleTrueIndexR2.
    # =====================================================================
    # `s^2 != 1 - rho^2` in half the cells, which is exactly where the rivals
    # part company from the body; a design confined to standardised scores
    # would validate all three forms.
    idx_grid = []
    for rho in (0.4, 0.6, 0.8):
        idx_grid.append((rho, math.sqrt(1.0 - rho ** 2), 0.0, 1.0, "standardised"))
        idx_grid.append((rho, 0.5, -1.6449, 0.6547, "s free, affine wrapper"))

    idx_cells, risk_scale_cells, rho2_cells, unsq_cells = [], [], [], []
    var_pred, var_meas = [], []
    print("\n  %-34s %10s %10s %10s" % ("cell", "lean", "index r2", "risk r2"))
    for rho, s, a, b_slope, lab in idx_grid:
        blocks = [index_block(rho, s, a, b_slope, 0.05, 0.3, rng)
                  for _ in range(BLOCKS)]
        lean = index_scale_true_index_r2(rho, s)
        m, sm = blocked([x["index"] for x in blocks])
        rm, rs = blocked([x["risk"] for x in blocks])
        d = "rho=%.1f s=%.3f a=%.2f b=%.2f [%s]" % (rho, s, a, b_slope, lab)
        print("  %-34s %10.5f %10.5f %10.5f"
              % ("rho=%.1f s=%.3f [%s]" % (rho, s, lab), lean, m, rm))
        idx_cells.append(dict(design=d, lean=lean, truth=m, sem=max(sm, 1e-12)))
        risk_scale_cells.append(dict(design=d, lean=lean, truth=rm,
                                     sem=max(rs, 1e-12)))
        rho2_cells.append(dict(design=d, lean=rho ** 2, truth=m,
                               sem=max(sm, 1e-12)))
        unsq_cells.append(dict(design=d, lean=rho / (rho + s), truth=m,
                               sem=max(sm, 1e-12)))
        vm, vs = blocked([x["var_zhat"] for x in blocks])
        var_pred.append(rho ** 2 + s ** 2)
        var_meas.append((vm, vs))

    # CONTROL: the variance decomposition, which is not the body's ratio.
    #
    # THE CELL IS DESIGNATED A PRIORI, by the largest predicted variance, and
    # the previous version of this line took the WORST of the six instead. That
    # is the worst-of-N false positive `verdict.py` documents and does not
    # correct for in a control: six draws at a 2e-4 error bar put the largest
    # residual near 3 sems by construction, the control was declared failed at
    # exactly 3.0 sems, and all three of this group's rivals came back VOID --
    # which would in turn have cost the corpus body its standing, since
    # `ledger.py` clears a MATCH only where a competitor was rejected. Selecting
    # on a PREDICTED quantity is free of that: nothing about the residual
    # decides which cell gates.
    ctrl_i = max(range(len(var_pred)), key=lambda i: var_pred[i])
    index_control = dict(
        design="Var(rho*z + s*eps) must be rho^2 + s^2 [the design's "
               "largest-variance cell, designated a priori]",
        lean=var_pred[ctrl_i], truth=var_meas[ctrl_i][0],
        sem=max(var_meas[ctrl_i][1], 1e-12))
    print("\n  CONTROL %s: predicted %.6f measured %.6f +/- %.6f"
          % (index_control["design"], index_control["lean"],
             index_control["truth"], index_control["sem"]))

    reg_idx = (
        "standard normal z and independent standard normal eps, zhat = rho*z + "
        "s*eps, with the true-liability index a + b*z and the score index "
        "a + b*zhat; %d draws per block and %d blocks. Half the cells carry "
        "s^2 != 1 - rho^2 and a nonzero intercept with a slope other than one, "
        "because that is where the standardised-score special case and the "
        "unsquared reading part company from the body and where the affine "
        "cancellation is a claim rather than a tautology. The INDEX-scale row "
        "correlates the two indices, which is what the body claims; the "
        "RISK-scale row correlates Phi of them, which is what a simulation "
        "reports most easily and what the docstring warns a battery would "
        "reach for first" % (N_IND // 4, BLOCKS))
    record("indexScaleTrueIndexR2", LEAN_FILE, "rho^2 / (rho^2 + s^2)",
           idx_cells, regime=reg_idx, control=index_control,
           realised_inputs=True, argument_source="model",
           note="the projection identity is a closed derivation, so agreement "
                "on the ratio is close to a construction check and is not "
                "claimed as more; what this group decides is carried by the "
                "rivals and by the affine cells")
    record("indexScaleTrueIndexR2 [measured on the RISK scale instead, the "
           "design the docstring warns a battery would reach for first, "
           "competing]", LEAN_FILE,
           "same body, oracle replaced by corr^2 between Phi of the indices",
           risk_scale_cells, regime=reg_idx, control=index_control,
           realised_inputs=True, argument_source="model",
           note="Phi is not affine, so the two scales are different numbers "
                "and no closed form carries one to the other; this row puts "
                "the size of the gap on the record")
    record("indexScaleTrueIndexR2 [rho^2 alone, the standardised-score special "
           "case mistaken for the general body, competing]", LEAN_FILE,
           "rho^2", rho2_cells, regime=reg_idx, control=index_control,
           realised_inputs=True, argument_source="model")
    record("indexScaleTrueIndexR2 [the unsquared reading rho/(rho+s), "
           "competing]", LEAN_FILE, "rho / (rho + s)", unsq_cells,
           regime=reg_idx, control=index_control,
           realised_inputs=True, argument_source="model")

    dump_results("battery_liab01_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-34s %-64s worst %9.2f sems, %8.2f%% rel"
              % (r["verdict"], r["name"][:64], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
