"""Battery pgscal01: three uncovered PGS/calibration definitions.

  effectGeneticCorrelation          TransferLearningPGS.lean
  reclassifiedBandEventPrevalence   PGSCalibrationTheory.lean
  prevalenceLogisticCalibrationProfile (its `citl` field)  PGSCalibrationTheory.lean

Each carries a competing formula on the same cells and a positive control that
can fail.  Conventions are declared per section, before any number is read.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-PGSCAL01-AVOCET-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def expit(x):
    return 1.0 / (1.0 + np.exp(-x))


# ---------------------------------------------------------------------------
# A. effectGeneticCorrelation
#
# CONVENTION: a CORRELATION, not a variance ratio and not an sd ratio -- the
# body is a cosine between two effect vectors and the oracle is a Pearson
# correlation between two genetic values, so both sides are on the same scale
# by construction and the alpha-style sd/variance ambiguity cannot enter.
#
# REGIME: the definition is the diagonal-LD specialisation, so the genotypes
# are drawn INDEPENDENT and standardised.  Under LD the sibling
# `ldEffectGeneticCorrelation` is the right body and is already VALIDATED; that
# is not what is on trial here.
#
# ARGUMENTS: the prediction is evaluated at the REALISED effect vectors, never
# at the nominal genetic correlation used to draw them -- with m = 400 the two
# differ by O(1/sqrt(m)) ~ 5%, which is the size of a spurious falsification.
# The oracle is the individual-level correlation between the two genetic values
# in a sample that the effect vectors know nothing about.
#
# COMPETITOR: the CENTRED Pearson correlation between the same two effect
# vectors.  Identical to the body when the effects have mean zero, and different
# when they do not; the design includes cells with a nonzero effect mean, which
# is what gives the competitor something to be wrong about.
# ---------------------------------------------------------------------------
def test_effect_genetic_correlation():
    rng = np.random.default_rng(90210)
    n, m = 200000, 400
    cells, comp = [], []
    control = None
    for rho, mu, lab in ((0.9, 0.0, "rho=0.9 mu=0"), (0.5, 0.0, "rho=0.5 mu=0"),
                         (0.2, 0.0, "rho=0.2 mu=0"), (0.7, 0.6, "rho=0.7 mu=0.6"),
                         (0.3, 0.9, "rho=0.3 mu=0.9")):
        bs = rng.normal(mu, 1.0, m)
        bt = rho * bs + math.sqrt(1 - rho ** 2) * rng.normal(0, 1.0, m) + \
            mu * (1 - rho)
        # realised cosine (the Lean body) and realised centred Pearson
        cos = float((bs * bt).sum() /
                    math.sqrt((bs ** 2).sum() * (bt ** 2).sum()))
        pear = float(np.corrcoef(bs, bt)[0, 1])
        X = rng.normal(0, 1, (n, m))          # independent, standardised
        gs, gt = X @ bs, X @ bt
        truth = float(np.corrcoef(gs, gt)[0, 1])
        # sem by splitting the sample into 10 independent blocks
        blocks = [float(np.corrcoef(gs[i::10], gt[i::10])[0, 1]) for i in range(10)]
        sem = float(np.std(blocks, ddof=1) / math.sqrt(10))
        print("  %-20s cosine %.5f  centred %.5f  realised corr(G_s,G_t) "
              "%.5f ± %.5f" % (lab, cos, pear, truth, sem))
        cells.append(dict(design=lab, lean=cos, truth=truth, sem=sem))
        comp.append(dict(design=lab, lean=pear, truth=truth, sem=sem))
    # control: identical effect vectors must give a realised correlation of 1
    b = rng.normal(0.4, 1.0, m)
    X = rng.normal(0, 1, (n, m))
    g = X @ b
    control = dict(design="identical effect vectors: realised corr = 1",
                   lean=1.0, truth=float(np.corrcoef(g, X @ b.copy())[0, 1]),
                   sem=1e-9)
    if abs(control["lean"] - control["truth"]) < 1e-12:
        # degenerate by construction; use a control that can actually miss --
        # orthogonalised effects must give zero realised correlation
        b2 = rng.normal(0, 1, m)
        b2 -= b * float((b * b2).sum() / (b ** 2).sum())
        g2 = X @ b2
        blocks = [float(np.corrcoef(g[i::10], g2[i::10])[0, 1]) for i in range(10)]
        control = dict(design="orthogonal effect vectors: realised corr = 0",
                       lean=0.0, truth=float(np.corrcoef(g, g2)[0, 1]),
                       sem=float(np.std(blocks, ddof=1) / math.sqrt(10)))
    print("  CONTROL %s: predicted %.5f measured %.5f ± %.5f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))
    reg = ("independent standardised genotypes (the diagonal-LD regime the "
           "definition names), 200000 individuals, 400 variants; the oracle is "
           "the realised Pearson correlation between the two genetic values and "
           "the prediction is evaluated at the REALISED effect vectors")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")
    record("effectGeneticCorrelation", "TransferLearningPGS.lean",
           "sum b_s*b_t / sqrt(sum b_s^2 * sum b_t^2)", cells, **MODEL)
    record("effectGeneticCorrelation [centred Pearson, competing]",
           "TransferLearningPGS.lean", "corr(b_s, b_t) with the means removed",
           comp, **MODEL)


# ---------------------------------------------------------------------------
# B. reclassifiedBandEventPrevalence
#
# CONVENTION: `pi` is the COHORT event prevalence, and the two band rates are
# CLASS-CONDITIONAL P(score in band | event) and P(score in band | non-event),
# which is what `thresholdBandRate mu_event` and `thresholdBandRate mu_nonevent`
# are: the band mass of the event and non-event score measures separately.
#
# WHY THIS IS NOT AN IDENTITY.  The three inputs come from the MODEL -- exact
# normal band masses and the nominal prevalence -- and never from the cohort the
# oracle counts.  Estimating them on the same cohort would make the body an
# algebraic rearrangement of the counts, which is the trap this harness names
# VACUOUS.  Here the cohort is simulated afterwards and independently.
#
# COMPETITOR: the prior-free `f_e / (f_e + f_n)`, which is what "the event rate
# in the band" reduces to if the cohort prevalence is dropped.  It is the
# ordinary base-rate mistake and it is wrong by a factor of several here.
# ---------------------------------------------------------------------------
def _phi(x):
    return 0.5 * (1.0 + np.vectorize(math.erf)(x / math.sqrt(2.0)))


def test_reclassified_band():
    rng = np.random.default_rng(4242)
    N = 4000000
    cells, comp = [], []
    for pi, mu_e, thr, delta, lab in (
            (0.10, 1.0, 0.5, 0.5, "pi=0.10 band(0.5,1.0]"),
            (0.30, 1.0, 1.0, 0.7, "pi=0.30 band(1.0,1.7]"),
            (0.05, 1.5, 0.0, 0.4, "pi=0.05 band(0.0,0.4]"),
            (0.20, 0.8, -0.5, 0.6, "pi=0.20 band(-0.5,0.1]")):
        # MODEL band masses: event scores ~ N(mu_e,1), non-event ~ N(0,1)
        f_e = float(_phi(np.array([thr + delta - mu_e]))[0] -
                    _phi(np.array([thr - mu_e]))[0])
        f_n = float(_phi(np.array([thr + delta]))[0] - _phi(np.array([thr]))[0])
        lean = pi * f_e / (pi * f_e + (1 - pi) * f_n)
        rival = f_e / (f_e + f_n)
        # independent cohort
        y = rng.random(N) < pi
        s = rng.normal(0, 1, N) + mu_e * y
        inband = (s > thr) & (s <= thr + delta)
        k = int(inband.sum())
        truth = float(y[inband].mean())
        sem = math.sqrt(truth * (1 - truth) / k)
        print("  %-28s f_e=%.5f f_n=%.5f  body %.5f  prior-free %.5f  "
              "measured %.5f ± %.5f (n=%d)"
              % (lab, f_e, f_n, lean, rival, truth, sem, k))
        cells.append(dict(design=lab, lean=lean, truth=truth, sem=sem))
        comp.append(dict(design=lab, lean=rival, truth=truth, sem=sem))
    # control: the simulated cohort reproduces its own nominal prevalence
    y = rng.random(N) < 0.17
    control = dict(design="cohort event rate reproduces the nominal 0.17",
                   lean=0.17, truth=float(y.mean()),
                   sem=math.sqrt(0.17 * 0.83 / N))
    print("  CONTROL %s: predicted %.5f measured %.5f ± %.5f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))
    reg = ("binary outcome at cohort prevalence pi, event scores N(mu_e,1) and "
           "non-event scores N(0,1), band (threshold, threshold+delta]; the "
           "band rates and pi are MODEL quantities (exact normal band masses), "
           "the oracle is the counted event fraction among band members in an "
           "independently simulated cohort of four million")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")
    record("reclassifiedBandEventPrevalence", "PGSCalibrationTheory.lean",
           "pi*f_e / (pi*f_e + (1-pi)*f_n)", cells, **MODEL)
    record("reclassifiedBandEventPrevalence [prior-free, competing]",
           "PGSCalibrationTheory.lean", "f_e / (f_e + f_n)", comp, **MODEL)


# ---------------------------------------------------------------------------
# C. prevalenceLogisticCalibrationProfile, through its `citl` field
#
# WHAT IS ON TRIAL.  The profile's own theorem pins
# `citl = prevalenceLogit pi_target - prevalenceLogit pi_source`.  The
# deployment quantity a calibration-in-the-large names is the INTERCEPT
# CORRECTION the target needs: the `a` solving
# `sum_i (y_i - expit(eta_i + a)) = 0` with the SOURCE model's linear predictor
# `eta` held as an offset.  This battery asks whether the profile's citl is that
# number, in the one regime the definition names: a target that differs from the
# source by a baseline-risk (intercept) shift and nothing else.
#
# CONVENTION: logit scale throughout; `pi` is a PREVALENCE (a probability), and
# both prevalences are fed at their REALISED values in the simulated cohorts,
# not at the nominal ones used to set the intercepts.
#
# COMPETITOR: the identity-scale reading `pi_target - pi_source`, the probability
# difference.  That is the same calibration algebra under the identity link, and
# the whole purpose of the `CalibrationLink` label is that the two differ.
#
# CONTROL: with a degenerate score (zero variance) the logit shift IS the
# intercept shift, so the fitter must return the intercept it was given.
# ---------------------------------------------------------------------------
def _fit_offset_intercept(y, eta):
    """Solve sum_i (y_i - expit(eta_i + a)) = 0 for a, by bisection."""
    lo, hi = -20.0, 20.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if (y - expit(eta + mid)).sum() > 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def test_prevalence_citl():
    rng = np.random.default_rng(777)
    N = 2000000
    cells, comp = [], []
    for a0, shift, sd, lab in ((-2.2, 0.8, 1.2, "pi~0.10 shift=0.8 sd=1.2"),
                               (-1.0, 0.6, 1.5, "pi~0.27 shift=0.6 sd=1.5"),
                               (-2.2, 1.5, 2.0, "pi~0.10 shift=1.5 sd=2.0"),
                               (-0.4, -0.9, 1.0, "pi~0.40 shift=-0.9 sd=1.0")):
        z = rng.normal(0, sd, N)
        eta = a0 + z
        ys = rng.random(N) < expit(eta)
        yt = rng.random(N) < expit(eta + shift)
        pi_s, pi_t = float(ys.mean()), float(yt.mean())     # REALISED
        lean = math.log(pi_t / (1 - pi_t)) - math.log(pi_s / (1 - pi_s))
        rival = pi_t - pi_s
        truth = _fit_offset_intercept(yt.astype(float), eta)
        # sem from 10 independent blocks
        blocks = [_fit_offset_intercept(yt[i::10].astype(float), eta[i::10])
                  for i in range(10)]
        sem = float(np.std(blocks, ddof=1) / math.sqrt(10))
        print("  %-28s pi_s=%.4f pi_t=%.4f  logit-shift %.5f  prob-diff %.5f  "
              "fitted CITL %.5f ± %.5f (true intercept shift %.2f)"
              % (lab, pi_s, pi_t, lean, rival, truth, sem, shift))
        cells.append(dict(design=lab, lean=lean, truth=truth, sem=sem))
        comp.append(dict(design=lab, lean=rival, truth=truth, sem=sem))
    # control: degenerate score, where the logit shift is the intercept shift
    eta = np.full(N, -1.3)
    yt = rng.random(N) < expit(eta + 0.7)
    control = dict(design="zero-variance score: the offset fit returns the "
                          "intercept shift it was given (0.7)",
                   lean=0.7, truth=_fit_offset_intercept(yt.astype(float), eta),
                   sem=float(np.std([_fit_offset_intercept(
                       yt[i::10].astype(float), eta[i::10])
                       for i in range(10)], ddof=1) / math.sqrt(10)))
    print("  CONTROL %s: predicted %.5f measured %.5f ± %.5f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))
    reg = ("logistic risk model, target differing from source by a baseline "
           "(intercept) shift only; two million individuals per arm; both "
           "prevalences fed at their REALISED cohort values; the oracle is the "
           "intercept correction the target needs with the source linear "
           "predictor held as an offset")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")
    record("prevalenceLogisticCalibrationProfile",
           "PGSCalibrationTheory.lean",
           "prevalenceLogit pi_target - prevalenceLogit pi_source", cells,
           **MODEL)
    record("prevalenceLogisticCalibrationProfile [identity-link reading, "
           "competing]", "PGSCalibrationTheory.lean",
           "pi_target - pi_source", comp, **MODEL)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-PGSCAL01-AVOCET-20260804")
    for fn in (test_effect_genetic_correlation, test_reclassified_band,
               test_prevalence_citl):
        print("\n---- %s ----" % fn.__name__)
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    dump_results("battery_pgscal01_results.json")
    print("\n================ SUMMARY ================")
    for rec in RESULTS:
        w = rec.get("worst", {}) or {}
        print("%-24s %-58s worst %9.2f sems, %8.2f%% rel"
              % (rec["verdict"], rec["name"][:58], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
