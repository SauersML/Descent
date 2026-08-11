"""Rivals on existing cells: five agreeing-uncompeted calibration bodies.

Every body here already had a MATCH that the ledger downgraded to UNINFORMATIVE,
because no competing formula was ever rejected on its cells. A zero-miss row is
also what a design with no power reports, so the agreement said nothing. This
battery gives each of the five a rival that COULD have disagreed, on cells of the
same design, and the docstring for each group says which rival that is and what
its rejection buys.

WHAT THE FIVE ARE, AND WHAT EACH RIVAL TESTS.

  R  `reliabilityRatio` (was `battery_bulk5`, 3 cells, 0 competitors). The rival
     that earns its place is the SQUARE ROOT of the same expression: reliability
     attenuates a SLOPE by `r2/(r2+s2)` and a CORRELATION by its square root, and
     confusing the two is the exact defect the corpus swept for under "correlation
     where slope belongs". A design whose oracle is a fitted slope must reject the
     square root, and if it cannot, it was never testing which of the two the body
     is. Two more corpses: the numerator swapped for the noise share, and the
     reading that divides by unit total variance instead of the realised one.

  L  `liabilityScaleH2` (was `battery_bulk8`, 3 cells, 0 competitors). The
     Dempster-Lerner transform is EXACT here, not asymptotic: for a normal
     liability the least-squares slope of the 0/1 outcome on the genetic value is
     the density at the threshold (Stein), so `h2_obs = h2_liab * z^2/(K(1-K))`
     identically. That is what makes the rivals sharp — the factor `(1-K)`
     dropped, and `z` not squared. `K` is swept from 0.02 to 0.40, a factor of
     twenty, which is what the dropped `(1-K)` needs in order to show: at K=0.02
     it is a 2% error and at K=0.40 a 67% one, so a cell grid that stayed rare
     would have reported the wrong form as a match.

  V  `liabilityControlVariance` (was `battery_max`, 3 cells, 0 competitors). Its
     docstring says the reading "is pinned the same way `liabilityCaseVariance`'s
     was" -- but `liabilityCaseVariance` was pinned by CARRYING that rival, and
     this body inherited the sentence without the measurement. So the rival is
     carried here: the variance of the LIABILITY among controls rather than of the
     standardised score, which is the same expression with `r2` set to one. Also
     the CASE formula applied to controls, and the `-T` term dropped.

  C  `prevalenceLogit` and `prevalenceCITLShift` (were `battery_bulk6`, 3 cells
     each, 0 competitors). THESE TWO NEEDED A NEW ORACLE BEFORE THEY COULD NEED A
     RIVAL, and that is the finding this group exists to record.

     `battery_bulk6` predicted `log(pi/(1-pi))` at the nominal prevalence and
     measured `log(pihat/(1-pihat))` at the realised one, with the comment that
     "the fitted intercept of an intercept-only logistic model IS the logit". It
     is -- and that is the problem. The body appears on BOTH sides of the
     comparison, so what those cells measure is whether `rng.random(n) < pi` draws
     at rate `pi`, and ANY monotone transform would have produced the same verdict
     against its own transform of the same sample mean. No rival can be
     informatively rejected on that design: a rival scored against the LOGIT of
     the sample mean dies by arithmetic, not by measurement.

     (The harness's SELF-TEST gate does not fire on it, because `lean` and `truth`
     differ by the sampling noise in `pihat` rather than to machine precision. A
     body evaluated at a nominal input against itself evaluated at the realised
     input is a self-test the gate cannot see; that is a guard blind spot of the
     same family as the uncompeted MATCH, and it is reported rather than fixed
     here.)

     So this group builds an oracle the body does not appear in: the LINEAR
     PREDICTOR INTERCEPT that generated the data. Outcomes are drawn from
     `expit(b0 + s*x)` with `x` standard normal, and the claim under test is the
     naming claim -- that the marginal prevalence logit IS that intercept, and
     that a difference of marginal logits IS the intercept shift `delta` applied
     between two populations. `b0` and `delta` are construction constants that
     never touch the prediction side, so agreement is a measurement.

     The score spread `s` is the axis, and at `s = 0` both claims are exactly
     right. They are recorded there, with three competing LINKS on the same cells
     -- probit, log-risk, complementary log-log for the logit; identity-scale,
     probit and log-risk-ratio for the shift -- so the corpus row says which
     transform of prevalence this is, which is what
     `prevalenceLogit_reflect`'s docstring claims for it ("the property that makes
     it a log-odds rather than any other increasing reparameterisation of
     prevalence") and what nothing had measured.

     The `s > 0` cells are recorded as a TAGGED regime-boundary row rather than
     folded into the corpus row, on `battery_bulk41b`'s precedent. They are where
     the qualifier binds, and they quantify what
     `PopulationCalibrationDrift.lean` derives the direction of: a mixture never
     reaches the promised prevalence. The magnitude found in `battery_pgscal01`
     under a DIFFERENT declaration name -- `prevalenceLogisticCalibrationProfile`,
     FALSIFIED at 374 sems, 17-37% undercorrection -- is the same arithmetic as
     `prevalenceCITLShift`, and nothing in the ledger connects the two rows. This
     group puts the measurement under the name the body carries.

ONE BOOKKEEPING DISCLOSURE, MADE HERE RATHER THAN LEFT FOR A READER TO FIND. The
two `[score spread above zero, the regime boundary]` rows carry the SAME source
expression as their corpus row, so `ledger.py` classifies them as CORPUS rows and
not as competitors -- which is the right call, because they are the same formula
under a different design rather than a rival to it. The consequence is that
`prevalenceLogit` and `prevalenceCITLShift` each end up with TWO corpus rows from
this one battery, one MATCH and one FALSIFIED, on disjoint cells. That is not a
contradiction and it is not double-counting: the two rows differ in their regime
strings, `s = 0` against `s > 0`, and the pair is the finding. Read either row
without the other and it misleads.

EVERY PREDICTION IS EVALUATED AT REALISED INPUTS. Where a nominal and a realised
reading of an argument both exist, both are PRINTED and the realised one is
scored, so the fork is never silent -- the practice that caught the fixation
conditional's Jensen inflation. Error bars are block sems over independent
replicates, never a formula for the bar written beside a formula for the value.

CONTROLS. Each group carries a control that is not built from the quantities the
body is built from and that CAN fail: the clean-predictor slope the construction
fixes at one (R), the same regression recovering `h2` when the outcome is the
liability itself rather than its dichotomy (L), the realised total liability
variance the construction fixes at one (V), and the realised prevalence against a
Gauss-Hermite quadrature of `E expit(b0 + s x)` at the widest score (C).
"""
import math
import os
import sys

import numpy as np

from battery_core import dump_results, record, run_groups

LEAN_CAL = "PGSCalibrationTheory.lean"
LEAN_STRAT = "StratificationConfounding.lean"
LEAN_VAR = "VarianceComponents.lean"
LEAN_DRIFT = "PortabilityDrift.lean"

QUICK = "--quick" in sys.argv
BLOCKS = 3 if QUICK else 8
N_BLOCK = 100000 if QUICK else 500000
REGIME_TAIL = ("%d blocks of %d individuals; error bars are the block sem"
               % (BLOCKS, N_BLOCK))


# ---------------------------------------------------------------------------
# Normal helpers.  `scipy` is available on the run node, but the three functions
# needed here are one line each and pinning them locally keeps the battery
# reproducible against a scipy version bump.
# ---------------------------------------------------------------------------
def phi(x):
    return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


def Phi(x):
    return 0.5 * math.erfc(-x / math.sqrt(2.0))


def Phinv(p):
    """Inverse normal CDF by bisection: 80 halvings on [-12, 12]."""
    lo, hi = -12.0, 12.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if Phi(mid) < p:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def expit(z):
    return 1.0 / (1.0 + np.exp(-z))


def logit(p):
    return math.log(p / (1.0 - p))


def blocked(vals):
    a = np.asarray(vals, float)
    if a.size < 2:
        return float(a.mean()), float("nan")
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


def cell(design, preds, meas):
    """One cell from per-block predictions and per-block measurements.

    Both sides are block quantities, so the bar is the scatter of the thing
    actually compared.  The paired bar is printed beside the measurement bar and
    the LARGER is recorded: these predictions track each block's own realised
    inputs, so the paired bar is the smaller one, and a verdict is worth more
    when it survives the conservative bar.
    """
    lean = float(np.mean(preds))
    truth, sem_m = blocked(meas)
    d = np.asarray(meas, float) - np.asarray(preds, float)
    sem_p = (float(d.std(ddof=1) / math.sqrt(d.size)) if d.size > 1
             else float("nan"))
    sem = max(sem_m, 1e-15)
    print("      %-46s pred %11.6f  meas %11.6f  sem %9.6f "
          "(paired %9.6f)  -> %8.2f sems"
          % (design, lean, truth, sem_m, sem_p,
             abs(truth - lean) / sem))
    return dict(design=design, lean=lean, truth=truth, sem=sem)


def const_cell(design, preds, truth, sem):
    """A cell whose TRUTH is a construction constant, not a measured mean.

    The bar is then the scatter of the PREDICTION across blocks, because that is
    the only side carrying noise.  Keeping this separate from `cell` is the point:
    putting a constant through the measurement path would divide by a zero sem.
    """
    lean, sem_p = blocked(preds)
    sem = max(sem_p, sem, 1e-15)
    print("      %-46s pred %11.6f  truth %11.6f  sem %9.6f  -> %8.2f sems"
          % (design, lean, truth, sem, abs(truth - lean) / sem))
    return dict(design=design, lean=lean, truth=truth, sem=sem)


# ---------------------------------------------------------------------------
# R.  reliabilityRatio -- against a fitted slope ratio, with the square root
#     carried as the rival that a slope oracle must be able to reject.
# ---------------------------------------------------------------------------
R_DESIGNS = ((0.5, 0.5), (0.2, 0.8), (0.8, 0.2), (0.9, 0.1), (0.1, 0.9))


def group_r():
    rng = np.random.default_rng(770101)
    cells, c_sqrt, c_swap, c_unit = [], [], [], []
    ctrl = None
    for r2, s2 in R_DESIGNS:
        body, sq, sw, un, meas, clean = [], [], [], [], [], []
        for _ in range(BLOCKS):
            sig = rng.normal(0.0, math.sqrt(r2), N_BLOCK)
            noi = rng.normal(0.0, math.sqrt(s2), N_BLOCK)
            obs = sig + noi
            y = sig + rng.normal(0.0, 1.0, N_BLOCK)
            # REALISED variances, named for the slice they came from: these are
            # the body's two arguments as this block actually drew them.
            v_sig = float(sig.var(ddof=1))
            v_noi = float(noi.var(ddof=1))
            oc = obs - obs.mean()
            sc = sig - sig.mean()
            yc = y - y.mean()
            b_noisy = float(oc @ yc / (oc @ oc))
            b_clean = float(sc @ yc / (sc @ sc))
            body.append(v_sig / (v_sig + v_noi))
            sq.append(math.sqrt(v_sig / (v_sig + v_noi)))
            sw.append(v_noi / (v_sig + v_noi))
            un.append(v_sig / (1.0 + v_noi))
            meas.append(b_noisy / b_clean)
            clean.append(b_clean)
        lab = "r2=%.1f s2=%.1f" % (r2, s2)
        print("    -- %s   nominal body %.6f" % (lab, r2 / (r2 + s2)))
        cells.append(cell(lab, body, meas))
        c_sqrt.append(cell(lab + " [sqrt]", sq, meas))
        c_swap.append(cell(lab + " [swap]", sw, meas))
        c_unit.append(cell(lab + " [unit]", un, meas))
        if ctrl is None:
            m, s = blocked(clean)
            ctrl = dict(design="slope on the CLEAN predictor, which the "
                               "construction fixes at 1",
                        lean=1.0, truth=m, sem=max(s, 1e-15))
    reg = ("a signal of realised variance v_sig plus independent noise of "
           "realised variance v_noi, outcome y = signal + N(0,1); the observable "
           "is the ratio of the least-squares slope of y on the NOISY predictor "
           "to the slope of y on the CLEAN one. The prediction is evaluated at "
           "each block's REALISED variances, never at the nominal pair. " +
           REGIME_TAIL)
    note = ("the competing form that could have disagreed is the SQUARE ROOT of "
            "the same expression -- the factor by which reliability attenuates a "
            "CORRELATION rather than a slope. The oracle here is a slope ratio, "
            "so rejecting the square root is what establishes which of the two "
            "this body is; the corpus swept for correlation-where-slope-belongs "
            "and this body had never been asked")
    record("reliabilityRatio", LEAN_STRAT, "r2 / (r2 + sigma2_noise)", cells,
           regime=reg, control=ctrl, realised_inputs=True,
           argument_source="model", note=note)
    record("reliabilityRatio [sqrt, the correlation-attenuation reading, "
           "competing]", LEAN_STRAT, "sqrt(r2 / (r2 + sigma2_noise))", c_sqrt,
           regime=reg, control=ctrl, realised_inputs=True,
           argument_source="model")
    record("reliabilityRatio [noise share, numerator swapped, competing]",
           LEAN_STRAT, "sigma2_noise / (r2 + sigma2_noise)", c_swap, regime=reg,
           control=ctrl, realised_inputs=True, argument_source="model")
    record("reliabilityRatio [total variance forced to one, competing]",
           LEAN_STRAT, "r2 / (1 + sigma2_noise)", c_unit, regime=reg,
           control=ctrl, realised_inputs=True, argument_source="model")


# ---------------------------------------------------------------------------
# L.  liabilityScaleH2 -- K swept twentyfold, which is what the dropped (1-K)
#     needs in order to show.
# ---------------------------------------------------------------------------
L_DESIGNS = ((0.5, 0.05), (0.5, 0.20), (0.3, 0.10), (0.2, 0.02), (0.6, 0.40))


def group_l():
    rng = np.random.default_rng(770202)
    cells, c_no1mk, c_zlin, c_none = [], [], [], []
    ctrl = None
    for h2, K in L_DESIGNS:
        body, no1mk, zlin, none, ctrl_v = [], [], [], [], []
        T = Phinv(1.0 - K)
        for _ in range(BLOCKS):
            g = rng.normal(0.0, math.sqrt(h2), N_BLOCK)
            liab = g + rng.normal(0.0, math.sqrt(1.0 - h2), N_BLOCK)
            y = (liab > T).astype(float)
            gc = g - g.mean()
            b = float(gc @ (y - y.mean()) / (gc @ gc))
            h2_obs = float(b ** 2 * gc.var() / y.var())
            # REALISED prevalence, and the threshold height taken at the
            # realised prevalence so the pair is self-consistent.  The nominal
            # pair is printed beside it; the fork is never silent.
            k_hat = float(y.mean())
            z_hat = phi(Phinv(1.0 - k_hat))
            body.append(h2_obs * k_hat * (1.0 - k_hat) / z_hat ** 2)
            no1mk.append(h2_obs * k_hat / z_hat ** 2)
            zlin.append(h2_obs * k_hat * (1.0 - k_hat) / z_hat)
            none.append(h2_obs)
            bb = float(gc @ (liab - liab.mean()) / (gc @ gc))
            ctrl_v.append(float(bb ** 2 * gc.var() / liab.var()))
        lab = "h2=%.1f K=%.2f" % (h2, K)
        z = phi(T)
        print("    -- %s   T=%.5f z=%.5f  nominal K(1-K)/z^2 = %.5f"
              % (lab, T, z, K * (1 - K) / z ** 2))
        cells.append(const_cell(lab, body, h2, h2 * math.sqrt(8.0 / N_BLOCK)))
        c_no1mk.append(const_cell(lab + " [no (1-K)]", no1mk, h2,
                                  h2 * math.sqrt(8.0 / N_BLOCK)))
        c_zlin.append(const_cell(lab + " [z linear]", zlin, h2,
                                 h2 * math.sqrt(8.0 / N_BLOCK)))
        c_none.append(const_cell(lab + " [no transform]", none, h2,
                                 h2 * math.sqrt(8.0 / N_BLOCK)))
        if ctrl is None:
            m, s = blocked(ctrl_v)
            ctrl = dict(design="the same regression recovers h2 when the "
                               "outcome is the LIABILITY, not its dichotomy",
                        lean=h2, truth=m, sem=max(s, 1e-15))
    reg = ("a normal liability of declared heritability h2 dichotomised at the "
           "threshold for prevalence K; the observed-scale heritability is "
           "fitted by least squares of the 0/1 outcome on the genetic value and "
           "the transform is applied to it. The TRUTH of each cell is the h2 the "
           "simulation was built with, a construction constant that never "
           "touches the prediction side. Prevalence and threshold height are "
           "taken at the block's REALISED case fraction. K spans 0.02 to 0.40. "
           + REGIME_TAIL)
    note = ("the competing form that could have disagreed is the transform with "
            "the (1-K) factor dropped: a 2% error at K=0.02 and a 67% error at "
            "K=0.40, so it is the twentyfold prevalence sweep and not the "
            "sample size that rejects it. On a grid that stayed rare it would "
            "have matched, which is why the earlier three-cell design could not "
            "have carried it")
    record("liabilityScaleH2", LEAN_VAR,
           "h2_observed * K * (1 - K) / z^2", cells, regime=reg, control=ctrl,
           realised_inputs=True, argument_source="model", note=note)
    record("liabilityScaleH2 [the (1-K) factor dropped, competing]", LEAN_VAR,
           "h2_observed * K / z^2", c_no1mk, regime=reg, control=ctrl,
           realised_inputs=True, argument_source="model")
    record("liabilityScaleH2 [z not squared, competing]", LEAN_VAR,
           "h2_observed * K * (1 - K) / z", c_zlin, regime=reg, control=ctrl,
           realised_inputs=True, argument_source="model")
    record("liabilityScaleH2 [no transform at all, competing]", LEAN_VAR,
           "h2_observed", c_none, regime=reg, control=ctrl,
           realised_inputs=True, argument_source="model")


# ---------------------------------------------------------------------------
# V.  liabilityControlVariance -- carrying the rival its docstring says is
#     pinned and that nothing ever ran.
# ---------------------------------------------------------------------------
V_DESIGNS = ((0.05, 0.3), (0.20, 0.3), (0.05, 0.6), (0.40, 0.5), (0.02, 0.2))


def group_v():
    rng = np.random.default_rng(770303)
    cells, c_case, c_liab, c_not = [], [], [], []
    ctrl = None
    for K, r2 in V_DESIGNS:
        body, case, liabv, nott, meas, ctrl_v = [], [], [], [], [], []
        T = Phinv(1.0 - K)
        for _ in range(BLOCKS):
            g = rng.normal(0.0, math.sqrt(r2), N_BLOCK)
            liab = g + rng.normal(0.0, math.sqrt(1.0 - r2), N_BLOCK)
            is_ctl = liab <= T
            k_hat = 1.0 - float(is_ctl.mean())
            r2_hat = float(g.var(ddof=1) / liab.var(ddof=1))
            i_c = -phi(T) / (1.0 - k_hat)
            i_case = phi(T) / k_hat
            body.append(1.0 - r2_hat * i_c * (i_c - T))
            case.append(1.0 - r2_hat * i_case * (i_case - T))
            liabv.append(1.0 - i_c * (i_c - T))
            nott.append(1.0 - r2_hat * i_c * i_c)
            # the observable: variance of the STANDARDISED score among controls
            meas.append(float(g[is_ctl].var(ddof=1) / g.var(ddof=1)))
            ctrl_v.append(float(liab.var(ddof=1)))
        lab = "K=%.2f r2=%.1f" % (K, r2)
        print("    -- %s   T=%.5f" % (lab, T))
        cells.append(cell(lab, body, meas))
        c_case.append(cell(lab + " [case form]", case, meas))
        c_liab.append(cell(lab + " [liability]", liabv, meas))
        c_not.append(cell(lab + " [no -T]", nott, meas))
        if ctrl is None:
            m, s = blocked(ctrl_v)
            ctrl = dict(design="realised total liability variance, which the "
                               "construction fixes at 1",
                        lean=1.0, truth=m, sem=max(s, 1e-15))
    reg = ("explicit normal liabilities g + e with realised r2 = Var(g)/Var(l), "
           "dichotomised at the threshold for prevalence K; the observable is "
           "the variance of the STANDARDISED score among controls, "
           "Var(g | l <= T)/Var(g). The control mean is evaluated at the "
           "block's realised case fraction. " + REGIME_TAIL)
    note = ("this body's docstring says its reading 'is pinned the same way "
            "liabilityCaseVariance's was' -- but that body was pinned by "
            "CARRYING the rival, and this one inherited the sentence without "
            "the measurement. The rival is carried here: the variance of the "
            "LIABILITY among controls rather than of the standardised score, "
            "which is the same expression with r2 set to one and is what a "
            "reader who took the other reading of the name would compute")
    record("liabilityControlVariance", LEAN_DRIFT,
           "1 - r2 * controlMean * (controlMean - T)", cells, regime=reg,
           control=ctrl, realised_inputs=True, argument_source="model",
           note=note)
    record("liabilityControlVariance [the LIABILITY variance among controls, "
           "competing]", LEAN_DRIFT,
           "1 - controlMean * (controlMean - T)", c_liab, regime=reg,
           control=ctrl, realised_inputs=True, argument_source="model")
    record("liabilityControlVariance [the CASE formula applied to controls, "
           "competing]", LEAN_DRIFT,
           "1 - r2 * caseMean * (caseMean - T)", c_case, regime=reg,
           control=ctrl, realised_inputs=True, argument_source="model")
    record("liabilityControlVariance [the -T term dropped, competing]",
           LEAN_DRIFT, "1 - r2 * controlMean^2", c_not, regime=reg,
           control=ctrl, realised_inputs=True, argument_source="model")


# ---------------------------------------------------------------------------
# C.  prevalenceLogit and prevalenceCITLShift, against the intercept that
#     generated the data rather than against themselves.
# ---------------------------------------------------------------------------
C_B0 = (-3.8918202981106265,   # logit 0.02
        -2.1972245773362196,   # logit 0.10
        -0.6190392084062235)   # logit 0.35
C_SPREAD = (0.0, 0.5, 1.0, 2.0)
C_DELTA = (1.0, 2.0, -1.5)


def _gh_prevalence(b0, s, nodes=64):
    """E expit(b0 + s x) for x standard normal, by Gauss-Hermite quadrature.

    This is the control's oracle and is deliberately computed a different way
    from the simulation -- a quadrature against a draw, not a draw against a
    draw.

    THE NODE COUNT IS LOW ON PURPOSE and the result is checked for finiteness
    before it leaves. `hermegauss(400)` overflows its weights to inf and the
    quotient comes back all-NaN; a battery in this directory printed an OK
    pre-check on an all-NaN quadrature because `max(0.0, nan)` is 0.0. Sixty-four
    nodes integrate a smooth bounded integrand to far better than the block sem,
    and the raise below means a silent NaN cannot reach a cell.
    """
    x, w = np.polynomial.hermite_e.hermegauss(nodes)
    if not np.all(np.isfinite(w)) or not np.all(np.isfinite(x)):
        raise ValueError("hermegauss(%d) is not finite" % nodes)
    w = w / w.sum()
    out = float(np.sum(w * expit(b0 + s * x)))
    if not math.isfinite(out) or not 0.0 < out < 1.0:
        raise ValueError("quadrature prevalence %r out of range" % out)
    return out


def _prev_blocks(rng, b0, s):
    """Realised marginal prevalence of expit(b0 + s x), one value per block."""
    out = []
    for _ in range(BLOCKS):
        x = rng.standard_normal(N_BLOCK)
        y = rng.random(N_BLOCK) < expit(b0 + s * x)
        out.append(float(y.mean()))
    return out


def group_c():
    rng = np.random.default_rng(770404)
    # One draw per (b0, s) reused by both bodies, so the shift cells and the
    # intercept cells are the same simulation and not two runs compared.
    prev = {}
    for b0 in C_B0:
        for s in C_SPREAD:
            prev[(b0, s)] = _prev_blocks(rng, b0, s)
    for b0 in C_B0:
        for d in C_DELTA:
            for s in C_SPREAD:
                key = (b0 + d, s)
                if key not in prev:
                    prev[key] = _prev_blocks(rng, *key)

    q = _gh_prevalence(C_B0[1] + 1.0, 2.0)
    m, sctl = blocked(prev[(C_B0[1] + 1.0, 2.0)])
    ctrl = dict(design="realised prevalence at b0=%.4f s=2.0 against a 64-node "
                       "Gauss-Hermite quadrature of E expit(b0 + s x)"
                       % (C_B0[1] + 1.0),
                lean=q, truth=m, sem=max(sctl, 1e-15))
    print("    control: quadrature %.6f  realised %.6f  sem %.6f"
          % (q, m, sctl))

    # -- prevalenceLogit ---------------------------------------------------
    at0, off0 = [], []
    r_probit, r_logrisk, r_cloglog = [], [], []
    for b0 in C_B0:
        for s in C_SPREAD:
            p = prev[(b0, s)]
            lab = "b0=%.4f s=%.1f" % (b0, s)
            lg = [logit(v) for v in p]
            row = const_cell(lab, lg, b0, 0.0)
            if s == 0.0:
                at0.append(row)
                r_probit.append(const_cell(lab + " [probit]",
                                           [Phinv(v) for v in p], b0, 0.0))
                r_logrisk.append(const_cell(lab + " [log risk]",
                                            [math.log(v) for v in p], b0, 0.0))
                r_cloglog.append(const_cell(
                    lab + " [cloglog]",
                    [math.log(-math.log(1.0 - v)) for v in p], b0, 0.0))
            else:
                off0.append(row)
    reg_p = ("binary outcomes drawn from expit(b0 + s x) with x standard "
             "normal; the TRUTH of each cell is the linear-predictor intercept "
             "b0 that generated the data, a construction constant that never "
             "enters the prediction. The corpus row is the s=0 cells, where the "
             "predictor is constant and the claim holds exactly. " + REGIME_TAIL)
    record("prevalenceLogit", LEAN_CAL, "log(pi / (1 - pi))", at0, regime=reg_p,
           control=ctrl, realised_inputs=True, argument_source="model",
           note=("the oracle is the generating intercept, NOT the fitted "
                 "intercept-only logistic intercept -- the latter is log of the "
                 "sample mean, so a design using it puts this body on both "
                 "sides and can reject nothing. Three competing LINKS are "
                 "carried on these cells: probit, log-risk and complementary "
                 "log-log. Rejecting them is what says this transform of "
                 "prevalence is the log-odds and not another increasing "
                 "reparameterisation, which is the claim "
                 "prevalenceLogit_reflect's docstring makes for it"))
    record("prevalenceLogit [probit link, competing]", LEAN_CAL,
           "Phi^{-1}(pi)", r_probit, regime=reg_p, control=ctrl,
           realised_inputs=True, argument_source="model")
    record("prevalenceLogit [log-risk link, competing]", LEAN_CAL,
           "log(pi)", r_logrisk, regime=reg_p, control=ctrl,
           realised_inputs=True, argument_source="model")
    record("prevalenceLogit [complementary log-log link, competing]", LEAN_CAL,
           "log(-log(1 - pi))", r_cloglog, regime=reg_p, control=ctrl,
           realised_inputs=True, argument_source="model")
    record("prevalenceLogit [score spread above zero, the regime boundary]",
           LEAN_CAL, "log(pi / (1 - pi))", off0, regime=reg_p, control=ctrl,
           realised_inputs=True, argument_source="model",
           note=("the marginal prevalence logit is the linear-predictor "
                 "intercept only for a CONSTANT predictor; with a score of "
                 "nonzero spread the marginal logit is attenuated toward zero. "
                 "This row measures the size of that gap and is where the "
                 "qualifier in the body's recorded empirical status -- "
                 "'intercept-only' -- is doing the work"))

    # -- prevalenceCITLShift ----------------------------------------------
    s0, sgt = [], []
    d_ident, d_probit, d_lrr = [], [], []
    for b0 in C_B0:
        for d in C_DELTA:
            for s in C_SPREAD:
                ps = prev[(b0, s)]
                pt = prev[(b0 + d, s)]
                lab = "b0=%.4f delta=%+.1f s=%.1f" % (b0, d, s)
                sh = [logit(b) - logit(a) for a, b in zip(ps, pt)]
                row = const_cell(lab, sh, d, 0.0)
                if s == 0.0:
                    s0.append(row)
                    d_ident.append(const_cell(
                        lab + " [identity]", [b - a for a, b in zip(ps, pt)],
                        d, 0.0))
                    d_probit.append(const_cell(
                        lab + " [probit]",
                        [Phinv(b) - Phinv(a) for a, b in zip(ps, pt)], d, 0.0))
                    d_lrr.append(const_cell(
                        lab + " [log RR]",
                        [math.log(b / a) for a, b in zip(ps, pt)], d, 0.0))
                else:
                    sgt.append(row)
    reg_s = ("two populations differing ONLY by a known intercept shift delta "
             "on the logistic linear predictor, outcomes drawn from "
             "expit(b0 + s x) and expit(b0 + delta + s x); the TRUTH of each "
             "cell is delta itself. The corpus row is the s=0 cells. "
             + REGIME_TAIL)
    record("prevalenceCITLShift", LEAN_CAL,
           "prevalenceLogit pi_target - prevalenceLogit pi_source", s0,
           regime=reg_s, control=ctrl, realised_inputs=True,
           argument_source="model",
           note=("the competing forms that could have disagreed are the "
                 "identity-scale difference, the probit-scale difference and "
                 "the log risk ratio, all three carried on these same cells "
                 "against the same known delta. The earlier design measured "
                 "this body against the logit of a sample mean -- itself -- so "
                 "no rival could be rejected there"))
    record("prevalenceCITLShift [identity-scale reading, competing]", LEAN_CAL,
           "pi_target - pi_source", d_ident, regime=reg_s, control=ctrl,
           realised_inputs=True, argument_source="model")
    record("prevalenceCITLShift [probit-scale reading, competing]", LEAN_CAL,
           "Phi^{-1}(pi_target) - Phi^{-1}(pi_source)", d_probit, regime=reg_s,
           control=ctrl, realised_inputs=True, argument_source="model")
    record("prevalenceCITLShift [log risk ratio, competing]", LEAN_CAL,
           "log(pi_target / pi_source)", d_lrr, regime=reg_s, control=ctrl,
           realised_inputs=True, argument_source="model")
    record("prevalenceCITLShift [score spread above zero, the regime boundary]",
           LEAN_CAL, "prevalenceLogit pi_target - prevalenceLogit pi_source",
           sgt, regime=reg_s, control=ctrl, realised_inputs=True,
           argument_source="model",
           note=("the difference of MARGINAL prevalence logits undercorrects "
                 "the intercept shift a deployment needs whenever the linear "
                 "predictor has spread -- the direction PopulationCalibration"
                 "Drift.lean derives from Jensen on the odds-multiplier action, "
                 "here measured in magnitude. battery_pgscal01 recorded the "
                 "same arithmetic under the declaration name "
                 "prevalenceLogisticCalibrationProfile at 374 sems, and nothing "
                 "in the ledger connects that row to this body"))


def main():
    print("REGIME: %s%s" % (REGIME_TAIL, "  [--quick SMOKE]" if QUICK else ""))
    failed = run_groups(group_r, group_l, group_v, group_c)
    here = os.path.dirname(os.path.abspath(__file__))
    sha = dump_results(os.path.join(here, "battery_rival01_results.json"),
                       failed_groups=failed)
    print("\nbattery sha %s" % sha)


if __name__ == "__main__":
    main()
