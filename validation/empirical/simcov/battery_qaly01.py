"""#37: `expectedThresholdQalyLoss` against an outcome-simulated realised loss.

WHY THIS BODY AND NOT THE OTHER TWELVE. Of the thirteen UNTESTED heads in
`PGSCalibrationTheory/` and `MetricSpecificPortability/`, ten are definitions
whose value is fixed by their own arguments -- accounting identities, structure
constructors, weighted means -- and one more, `thresholdBandRate`, has its single
naming claim discharged by a theorem in its own file
(`downReclassificationRate_eq_thresholdBandRate`). A claim with a proof behind it
is not awaiting a simulation.

`expectedThresholdQalyLoss` is different, and the difference is the whole point.
It is also an integral of a pointwise definition, so given the measure and the
two risk functions its value cannot come out otherwise. What it additionally
does is CLAIM, in its name, to be the expected QALY loss from miscalibration --
and whether the integral of the accounting `benefit*trueRisk - harm` equals the
loss actually realised when disease events are drawn and the decision rule is
applied is proved nowhere. That is refutable, and it is what this battery
measures.

THE TWO SIDES ARE GENUINELY DIFFERENT COMPUTATIONS, which is the property the
identity-control trap exists to demand. The predicted side integrates an
analytic per-individual loss. The measured side never evaluates that loss: it
draws a Bernoulli disease event per individual, applies the ORACLE decision rule
and the DEPLOYED one, books the realised QALYs of each, and differences them.
The two agree only if the accounting prices realised outcomes correctly -- if
the benefit were credited to non-events, or the harm charged only to events, or
the harm omitted from the untreated arm, the measured side moves and the
predicted side does not.

THE RIVALS ARE MIS-ACCOUNTINGS, not straw men. Both are confusions available to
anyone writing this body: pricing the benefit at the PREDICTED risk rather than
the true one (the quantity the deployer actually has), and charging benefit and
harm together only on events. Both are recorded on the same cells.

THE CONTROL IS THE DGP'S OWN PREVALENCE and it can fail for reasons that are not
the formula: the realised event rate must equal the mean true risk. That tests
the Bernoulli draw and the liability-to-risk map, both of which sit upstream of
every cell, and it involves no QALY accounting at all. A control built out of
the loss itself could only confirm that arithmetic is arithmetic.

THE SIX TEMPLATE CHECKS, applied:
 1. SLICE IN THE NAME. `p_true` is the individual's true event probability;
    `q_pred` is the deployed model's predicted probability. Neither is ever
    called `risk` unqualified.
 2. ESTIMAND FORM IN THE REGIME STRING. The measured quantity is the MEAN OVER
    INDIVIDUALS of the realised QALY difference -- an unweighted per-capita
    mean, matched by an unweighted mean of the predicted per-individual losses.
    Not a per-decision mean and not a per-event mean; those differ.
 3. CURRENCY. Both sides are in QALYs per individual, unweighted. The model's
    benefit and harm are in the same unit by construction.
 4. BOUNDS BESIDE QUANTITIES. Every cell prints its Monte-Carlo noise floor
    beside its measurement, and a cell is admitted only where the predicted loss
    clears three floors.
 5. NO CROSS-CONFIG COMPARISON. Config travels in the regime string.
 6. ONE FILTERED SET. The individuals are drawn once per cell and the same array
    is handed to the predicted side, the measured side and both rivals.
"""
import math
import os

import numpy as np

from battery_core import dump_results, record, run_groups

FRESH_TOKEN = "SIMCOV-BATTERY-QALY01-OUTCOME-20260811"
LEAN_FILE = "PGSCalibrationTheory/DecisionImplications.lean"

N_IND = 400000
BLOCKS = 8
BENEFIT = 0.35            # QALYs gained by treating a case
HARM = 0.02               # QALYs lost by treating anyone
THRESH = 0.10             # treat when the decision risk exceeds this
PREVALENCES = (0.02, 0.05, 0.10)
SHIFTS = (0.0, 0.25, 0.5, 1.0)   # intercept shift on the log-odds scale
R2_LIAB = 0.30            # liability-scale variance explained by the score
SEED = 370037


def freshness():
    return FRESH_TOKEN


def logit(p):
    return np.log(p / (1.0 - p))


def expit(x):
    return 1.0 / (1.0 + np.exp(-x))


# ---------------------------------------------------------------------------
# The Lean bodies, transcribed.
# ---------------------------------------------------------------------------
def threshold_qaly_gain(p_true, decision_risk):
    """`thresholdQalyGainUnderDecision`: treat when decision risk clears the
    threshold, and the gain is then priced at the TRUE risk."""
    return np.where(decision_risk > THRESH, BENEFIT * p_true - HARM, 0.0)


def threshold_qaly_loss(p_true, q_pred):
    """`thresholdQalyLoss`: the oracle's gain minus the deployed decision's."""
    return threshold_qaly_gain(p_true, p_true) - threshold_qaly_gain(p_true, q_pred)


def expected_threshold_qaly_loss(p_true, q_pred):
    """`expectedThresholdQalyLoss`: the integral, here over the empirical law."""
    return float(np.mean(threshold_qaly_loss(p_true, q_pred)))


# ---- the two rival accountings --------------------------------------------
def loss_priced_at_predicted(p_true, q_pred):
    """Benefit priced at the PREDICTED risk -- the quantity a deployer has."""
    g = lambda pr, d: np.where(d > THRESH, BENEFIT * pr - HARM, 0.0)
    return float(np.mean(g(p_true, p_true) - g(q_pred, q_pred)))


def loss_harm_only_on_events(p_true, q_pred):
    """Benefit and harm booked together, only on events."""
    g = lambda d: np.where(d > THRESH, (BENEFIT - HARM) * p_true, 0.0)
    return float(np.mean(g(p_true) - g(q_pred)))


# ---------------------------------------------------------------------------
def one_block(rng, prevalence, shift):
    """One replicate: liabilities, true risks, a shifted deployed model, and the
    REALISED QALYs of the oracle and deployed decisions."""
    # Liability-threshold DGP: a standard normal liability, the score explaining
    # R2_LIAB of it, disease when the liability clears the prevalence threshold.
    g = rng.standard_normal(N_IND) * math.sqrt(R2_LIAB)
    e = rng.standard_normal(N_IND) * math.sqrt(1.0 - R2_LIAB)
    liab = g + e
    thr_liab = -_ndtri(prevalence)
    # p_true is the individual's TRUE event probability given their score, which
    # is what the oracle would decide on. Not the realised event.
    p_true = _ndtr((g - thr_liab) / math.sqrt(1.0 - R2_LIAB))
    # The deployed model is miscalibrated by an intercept shift on the log-odds
    # scale -- the same object prevalenceCITLShift describes.
    q_pred = expit(logit(np.clip(p_true, 1e-12, 1 - 1e-12)) + shift)

    # THE MEASURED SIDE. Draw the actual event, apply each decision rule, book
    # the realised QALYs. This never evaluates threshold_qaly_loss.
    event = rng.random(N_IND) < p_true
    treat_oracle = p_true > THRESH
    treat_deployed = q_pred > THRESH
    realised = lambda treated: np.where(treated, BENEFIT * event - HARM, 0.0)
    realised_loss = float(np.mean(realised(treat_oracle) - realised(treat_deployed)))
    return dict(p_true=p_true, q_pred=q_pred, event=event,
                realised_loss=realised_loss,
                event_rate=float(np.mean(event)),
                mean_p_true=float(np.mean(p_true)))


def _ndtr(x):
    from scipy.special import ndtr
    return ndtr(x)


def _ndtri(p):
    from scipy.special import ndtri
    return float(ndtri(p))


def blocked(v):
    a = np.asarray(v, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


def group_qaly():
    print("\n== expectedThresholdQalyLoss against outcome-simulated realised loss")
    rng = np.random.default_rng(SEED)
    cells, cells_pred, cells_harm, skipped = [], [], [], []
    ctrl = []
    print("  %-26s %11s %11s %11s %9s %9s"
          % ("cell", "predicted", "realised", "floor", "sems", "readable"))
    for prev in PREVALENCES:
        for shift in SHIFTS:
            blocks = [one_block(rng, prev, shift) for _ in range(BLOCKS)]
            pred = float(np.mean([expected_threshold_qaly_loss(b["p_true"],
                                                              b["q_pred"])
                                  for b in blocks]))
            meas, sem = blocked([b["realised_loss"] for b in blocks])
            lab = "prev=%.2f shift=%.2f" % (prev, shift)
            floor = max(sem, 1e-12)
            ok = abs(pred) > 3 * floor
            print("  %-26s %11.6f %11.6f %11.6f %9.2f %9s"
                  % (lab, pred, meas, floor,
                     abs(meas - pred) / floor, "yes" if ok else "NO"))
            if not ok:
                skipped.append((lab, pred, floor))
                continue
            cells.append(dict(design=lab, lean=pred, truth=meas, sem=floor))
            cells_pred.append(dict(
                design=lab, truth=meas, sem=floor,
                lean=float(np.mean([loss_priced_at_predicted(b["p_true"], b["q_pred"])
                                    for b in blocks]))))
            cells_harm.append(dict(
                design=lab, truth=meas, sem=floor,
                lean=float(np.mean([loss_harm_only_on_events(b["p_true"], b["q_pred"])
                                    for b in blocks]))))
            # CONTROL, per cell: the DGP's own prevalence. The realised event
            # rate must equal the mean true risk. No QALY accounting in it.
            er, ersem = blocked([b["event_rate"] for b in blocks])
            mp, _ = blocked([b["mean_p_true"] for b in blocks])
            ctrl.append(dict(design="event rate vs mean p_true at " + lab,
                             lean=mp, truth=er, sem=max(ersem, 1e-12)))

    if skipped:
        print("\n  CELLS EXCLUDED BY THE PRE-SET READABILITY RULE "
              "(|predicted| < 3 x its own Monte-Carlo floor):")
        for lab, pred, floor in skipped:
            print("    %-26s predicted %.3e  floor %.3e" % (lab, pred, floor))

    reg = ("liability-threshold DGP: standard normal liability, score explaining "
           "%.2f of it on the liability scale, disease when the liability clears "
           "the prevalence threshold; %d individuals per block, %d blocks. The "
           "deployed model is miscalibrated by an intercept SHIFT on the log-odds "
           "scale. Treatment when the decision risk exceeds %.2f; benefit %.2f "
           "QALYs on an event, harm %.2f QALYs on everyone treated. THE MEASURED "
           "SIDE DRAWS THE ACTUAL EVENT and books realised QALYs under the oracle "
           "and deployed rules; it never evaluates the analytic loss. The estimand "
           "is the MEAN OVER INDIVIDUALS of the realised QALY difference, "
           "unweighted, matched by an unweighted mean of the predicted "
           "per-individual losses -- not a per-decision or per-event mean, which "
           "differ. Cells admitted only where the predicted loss clears three "
           "Monte-Carlo floors; excluded cells are printed"
           % (R2_LIAB, N_IND, BLOCKS, THRESH, BENEFIT, HARM))
    control = ctrl[len(ctrl) // 2] if ctrl else None

    record("expectedThresholdQalyLoss", LEAN_FILE,
           "integral of thresholdQalyLoss over the deployed population",
           cells, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="the predicted side integrates the analytic accounting; the "
                "measured side draws events and books realised QALYs, so the "
                "two are different computations rather than the same one twice")
    record("expectedThresholdQalyLoss [benefit priced at the PREDICTED risk "
           "rather than the true one, competing]", LEAN_FILE,
           "same integral with benefit * predictedRisk in the gain",
           cells_pred, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="the quantity a deployer actually holds, and the natural "
                "confusion; it prices the benefit at the number that is wrong")
    record("expectedThresholdQalyLoss [benefit and harm booked together only on "
           "events, competing]", LEAN_FILE,
           "same integral with (benefit - harm) * trueRisk in the gain",
           cells_harm, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="charges the harm only to treated cases rather than to everyone "
                "treated, which is the other available mis-accounting")


def main():
    print(freshness())
    failed = run_groups(group_qaly)
    here = os.path.dirname(os.path.abspath(__file__))
    sha = dump_results(os.path.join(here, "battery_qaly01_results.json"),
                       failed_groups=failed)
    print("\nbattery sha %s" % sha)


if __name__ == "__main__":
    main()
