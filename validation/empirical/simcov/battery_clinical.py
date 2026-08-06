"""Battery CLINICAL: the operating-point family in `Core/Decision.lean`.

FRESHNESS guard string: CLINICAL_GUARD_20260806

`Core/Decision.lean` is 2,387 lines of positive and negative predictive value,
net benefit and net reclassification index -- the coordinates a deployed score is
actually reported in, and the end of the corpus's longest chain -- and not one of
its declarations has a ledger row.  Every one of them says `Empirical status: NOT
AN EMPIRICAL CLAIM -- this is a SHAPE`, and for the CHAIN that is right: which
operating point a given `R^2` reaches is carried by `OperatingPointLaw.point`,
which is a function field and not a formula, so nothing about it is decidable
here.

WHAT IS DECIDABLE, and is what this battery tests: given an operating point --
a sensitivity and a specificity that a rule actually has -- the four bodies
compute the numbers a patient and a screening programme are told.  That is not a
shape.  A rule with a measured sensitivity and specificity, applied to a
population with a known prevalence, produces a countable PPV, a countable NPV, a
countable net benefit and a countable NRI, and the bodies either predict them or
they do not.

  positivePredictiveValue o pi = sens*pi / (sens*pi + (1-spec)*(1-pi))
  negativePredictiveValue o pi = spec*(1-pi) / (spec*(1-pi) + (1-sens)*pi)
  netBenefit o pi t            = pi*sens - (1-pi)*(1-spec)*t/(1-t)
  nriFromOperatingPoints old new = (sens_new - sens_old) + (spec_new - spec_old)

THE RIVAL THAT MATTERS IS THE PREVALENCE-FREE ONE.  The commonest error in this
family is reporting `sens/(sens + (1 - spec))` as the predictive value -- the
number a balanced test set gives -- and it is exactly right at `pi = 0.5` and
catastrophically wrong at screening prevalences.  A design run at one prevalence
cannot separate it; a design run at 0.5 cannot separate it at all.  So prevalence
is swept over a factor of fifty, 0.01 to 0.50, and the last cell is the one where
the rival agrees.  That cell is not a weakness: it is what makes the sweep an
argument about the prevalence dependence rather than about a constant.

The other rivals are the two sign and inversion errors that survive a spot check:
net benefit with the threshold odds inverted (`(1-t)/t`), which agrees at
`t = 0.5`, and an NRI that adds the specificity change with the wrong sign, which
agrees whenever the two rules have equal specificity.  Each is carried on the
same cells as the body.

NO SIMULATION OF A GENOME.  This battery does not need one and deliberately does
not have one.  The claim is about counting, so the oracle is a count: draw a
population, apply a rule with a chosen operating point, count the four
quantities.  A liability-threshold genome simulation would put a demography, a
genetic architecture and a scoring rule between the claim and the measurement,
and every one of those is a place for a disagreement to come from that is not the
body under test.  `battery_demesweep.py` is where the demography belongs.

THE DESIGN IS OUT-OF-SAMPLE, AND THE HARNESS'S OWN GATE IS WHY.  The first
version of this battery measured the operating point and the predictive value on
the SAME half of the same replicate, and `verdict.classify` reported DEGENERATE
ORACLE with the note "prediction equals truth to machine precision in every cell:
the oracle is the formula, not a measurement".  It was right, and the algebra is
one line: with `sens = tp/(tp+fn)`, `prev = (tp+fn)/n` and `spec = tn/(tn+fp)`
read off one sample,

    sens*prev / (sens*prev + (1-spec)*(1-prev))  =  tp / (tp + fp)

identically, for every sample, with no model in between.  On REALISED inputs the
predictive-value bodies are not predictions at all -- they are a rearrangement of
four counts, and the corpus's `NOT AN EMPIRICAL CLAIM` marker on them is correct
as far as it goes.

Feeding NOMINAL inputs instead would make it a prediction and a bad one: the
disagreement would then be the sampling gap between the rule's designed operating
point and the one the draw realised, which is exactly the trap `record`'s
`realised_inputs` parameter exists to catch, and a FALSIFIED there means nothing.

So each replicate is SPLIT.  The operating point and the prevalence are measured
on half A; the predictive value is predicted for half B from those numbers and
counted on half B.  That is a real prediction -- the two halves are independent
draws -- it is not an identity, and the error bar is the split noise rather than
a nominal/realised artefact.  `realised_inputs=True` is then honest: the inputs
are realised, on a sample disjoint from the one the oracle is counted on.

This is what the clinical family can actually be held to, and it is worth having:
a body that got the prevalence weighting wrong would predict half A's answer for
half B and miss by the prevalence ratio.
"""
import os

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

MODEL = dict(realised_inputs=True)

GUARD = "CLINICAL_GUARD_20260806"
N = 200_000
REPS = 40
PREVALENCES = (0.01, 0.05, 0.20, 0.50)
THRESHOLD = 0.10          # decision-curve threshold probability
# The two rules the reclassification index compares. They differ in BOTH
# coordinates on purpose: at equal specificity the non-event component is zero
# and the wrong-sign rival is indistinguishable from the body, which the first
# run of this battery demonstrated by getting DEGENERATE ORACLE on it.
NRI_PAIR = ((0.55, 0.90), (0.75, 0.80))


def counts(case, pos, n):
    """The four cells of a confusion matrix, and everything read off them."""
    tp = int(np.sum(case & pos)); fn = int(np.sum(case & ~pos))
    fp = int(np.sum(~case & pos)); tn = int(np.sum(~case & ~pos))
    return dict(
        sens=tp / max(tp + fn, 1), spec=tn / max(tn + fp, 1),
        prev=(tp + fn) / n,
        ppv=tp / max(tp + fp, 1), npv=tn / max(tn + fn, 1),
        net_benefit=(tp - fp * (THRESHOLD / (1 - THRESHOLD))) / n)


def draw_split(rng, n, prevalence, sens_target, spec_target):
    """One replicate, split into two independent halves A and B.

    The rule is a coin with different bias in cases and non-cases, which is the
    most general thing an operating point IS -- `OperatingPoint` carries exactly
    `P(positive | case)` and `P(negative | non-case)` and nothing else, so a
    richer generative story would be adding structure the body cannot see.
    """
    case = rng.random(n) < prevalence
    pos = np.where(case, rng.random(n) < sens_target,
                   rng.random(n) >= spec_target)
    h = n // 2
    return (counts(case[:h], pos[:h], h), counts(case[h:], pos[h:], n - h),
            (case, pos))


def cells_for(fn_body, key, rng_seed, sens_target, spec_target):
    """`fn_body(half A) -> prediction for half B`, across the prevalence sweep.

    Out of sample in both directions: the operating point comes from A and the
    oracle is counted on B, so the two never share an individual.
    """
    out = []
    for pi in PREVALENCES:
        preds, truths = [], []
        for r in range(REPS):
            rng = np.random.default_rng(rng_seed + 977 * r + int(10000 * pi))
            a, b, _ = draw_split(rng, N, pi, sens_target, spec_target)
            preds.append(fn_body(a)); truths.append(b[key])
        diff = np.array(truths) - np.array(preds)
        out.append(dict(design="prevalence=%.2f" % pi,
                        lean=float(np.mean(preds)),
                        truth=float(np.mean(truths)),
                        sem=max(float(np.std(diff, ddof=1) / np.sqrt(REPS)),
                                1e-9)))
    return out


def positive_rate_control(rng_seed, sens_target, spec_target):
    """The control every rejection here rests on: the TOTAL POSITIVE RATE.

    `P(positive) = sens*pi + (1-spec)*(1-pi)`, predicted from half A and counted
    on half B. It is the law of total probability on the same four counts, the
    same split and the same rule as every candidate, and it is none of them --
    so it fails exactly when the split, the counting or the draw is broken, and
    passes when the only thing left to be wrong is the body under test.

    Without a control a rejection is a LEAD and not a falsification, which is
    what this battery's first run produced: four rivals excluded at 218 to 1569
    sems, all of them recorded as "LEAD (no control)". A design that can only
    reject is a design that has not shown it can agree.
    """
    preds, truths = [], []
    for pi in PREVALENCES:
        for r in range(REPS):
            rng = np.random.default_rng(rng_seed + 977 * r + int(10000 * pi))
            a, b, _ = draw_split(rng, N, pi, sens_target, spec_target)
            preds.append(a["sens"] * a["prev"]
                         + (1 - a["spec"]) * (1 - a["prev"]))
            truths.append(b["prev"] * b["sens"]
                          + (1 - b["prev"]) * (1 - b["spec"]))
    d = np.array(truths) - np.array(preds)
    return dict(design="total positive rate, all prevalences pooled "
                       "[sens*pi + (1-spec)*(1-pi)]",
                lean=float(np.mean(preds)), truth=float(np.mean(truths)),
                sem=max(float(np.std(d, ddof=1) / np.sqrt(len(d))), 1e-9))


def main():
    print("FRESHNESS=OK %s" % GUARD)
    SENS, SPEC = 0.70, 0.85
    control = positive_rate_control(4400, SENS, SPEC)
    print("  CONTROL total positive rate: predicted %.5f, counted %.5f "
          "+/- %.5f" % (control["lean"], control["truth"], control["sem"]))

    ppv_cands = {
        "body [sens*pi / (sens*pi + (1-spec)*(1-pi))]":
            lambda d: d["sens"] * d["prev"]
            / (d["sens"] * d["prev"] + (1 - d["spec"]) * (1 - d["prev"])),
        "prevalence-free [sens / (sens + (1-spec))], competing":
            lambda d: d["sens"] / (d["sens"] + (1 - d["spec"])),
    }
    npv_cands = {
        "body [spec*(1-pi) / (spec*(1-pi) + (1-sens)*pi)]":
            lambda d: d["spec"] * (1 - d["prev"])
            / (d["spec"] * (1 - d["prev"]) + (1 - d["sens"]) * d["prev"]),
        "prevalence-free [spec / (spec + (1-sens))], competing":
            lambda d: d["spec"] / (d["spec"] + (1 - d["sens"])),
    }
    nb_cands = {
        "body [pi*sens - (1-pi)*(1-spec)*t/(1-t)]":
            lambda d: d["prev"] * d["sens"]
            - (1 - d["prev"]) * (1 - d["spec"]) * (THRESHOLD / (1 - THRESHOLD)),
        "inverted threshold odds [(1-t)/t], competing":
            lambda d: d["prev"] * d["sens"]
            - (1 - d["prev"]) * (1 - d["spec"]) * ((1 - THRESHOLD) / THRESHOLD),
    }

    reg = ("A rule with a fixed operating point applied to a drawn population: "
           "n = 200000 per replicate, 40 replicates, prevalence swept 0.01 / "
           "0.05 / 0.20 / 0.50, nominal sensitivity 0.70 and specificity 0.85. "
           "Sensitivity, specificity and prevalence are REALISED -- counted off "
           "the same replicate the predictive value is counted from. REGIME: "
           "the operating point is given; which operating point a score with a "
           "given R^2 reaches is `OperatingPointLaw.point`, a function field, "
           "and is NOT under test here")

    for name, cands, key in (
            ("positivePredictiveValue", ppv_cands, "ppv"),
            ("negativePredictiveValue", npv_cands, "npv"),
            ("netBenefit", nb_cands, "net_benefit")):
        corpus = list(cands)[0]
        for k, fn in cands.items():
            c = cells_for(fn, key, 5100 + 7 * len(k), SENS, SPEC)
            print("  %-24s %-52s %s" % (name, k, " ".join(
                "%.5f/%.5f" % (x["lean"], x["truth"]) for x in c)))
            record(name if k == corpus else "%s [%s]" % (name, k),
                   "Decision.lean", k, c, regime=reg, control=control,
                   **MODEL)

    # NRI.  The oracle here is a RECLASSIFICATION COUNT and not a restatement of
    # the body: the same individuals are classified by both rules, and the index
    # is counted as (moved up among cases - moved down among cases) + (moved
    # down among non-cases - moved up among non-cases). That is the definition
    # the index is named for, and it is what the body's
    # `(Delta sens) + (Delta spec)` has to reproduce. The first run of this
    # battery computed the "truth" from the two operating points, which is the
    # body, and `verdict.classify` reported DEGENERATE ORACLE for it -- rightly.
    nri_cells, nri_bad = [], []
    (s_old, p_old), (s_new, p_new) = NRI_PAIR
    for pi in PREVALENCES:
        preds, bad, truths = [], [], []
        for r in range(REPS):
            rng = np.random.default_rng(6100 + 977 * r + int(10000 * pi))
            case = rng.random(N) < pi
            old_pos = np.where(case, rng.random(N) < s_old,
                               rng.random(N) >= p_old)
            new_pos = np.where(case, rng.random(N) < s_new,
                               rng.random(N) >= p_new)
            h = N // 2
            a_old = counts(case[:h], old_pos[:h], h)
            a_new = counts(case[:h], new_pos[:h], h)
            cb, ob, nb = case[h:], old_pos[h:], new_pos[h:]
            ncase = max(int(np.sum(cb)), 1); nctrl = max(int(np.sum(~cb)), 1)
            up_case = int(np.sum(cb & ~ob & nb)) / ncase
            dn_case = int(np.sum(cb & ob & ~nb)) / ncase
            dn_ctrl = int(np.sum(~cb & ob & ~nb)) / nctrl
            up_ctrl = int(np.sum(~cb & ~ob & nb)) / nctrl
            truths.append((up_case - dn_case) + (dn_ctrl - up_ctrl))
            preds.append((a_new["sens"] - a_old["sens"])
                         + (a_new["spec"] - a_old["spec"]))
            bad.append((a_new["sens"] - a_old["sens"])
                       - (a_new["spec"] - a_old["spec"]))
        for dst, pv in ((nri_cells, preds), (nri_bad, bad)):
            d = np.array(truths) - np.array(pv)
            dst.append(dict(design="prevalence=%.2f" % pi,
                            lean=float(np.mean(pv)),
                            truth=float(np.mean(truths)),
                            sem=max(float(np.std(d, ddof=1) / np.sqrt(REPS)),
                                    1e-9)))
    print("  nriFromOperatingPoints    body/wrong-sign/counted: " + " ".join(
        "%.4f|%.4f|%.4f" % (a["lean"], b["lean"], a["truth"])
        for a, b in zip(nri_cells, nri_bad)))
    nri_reg = reg + ("; the two rules differ in BOTH coordinates (sens 0.55 -> "
                     "0.75, spec 0.90 -> 0.80) so the event and non-event "
                     "components both carry signal and have opposite signs; the "
                     "oracle is a reclassification COUNT on held-out "
                     "individuals classified by both rules")
    record("nriFromOperatingPoints", "Decision.lean",
           "body [(sens_new - sens_old) + (spec_new - spec_old)]",
           nri_cells, regime=nri_reg, control=control, **MODEL)
    record("nriFromOperatingPoints [wrong-sign non-event component], competing",
           "Decision.lean",
           "wrong sign [(sens_new - sens_old) - (spec_new - spec_old)]",
           nri_bad, regime=nri_reg, control=control, **MODEL)

    dump_results("battery_clinical_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst") or {}
        if "sems_off" in w:
            print("%-10s %-66s worst %.2f sems, %.1f%% rel"
                  % (r["verdict"], r["name"], w["sems_off"],
                     100 * w["rel_err"]))
        else:
            # A gated verdict (DEGENERATE ORACLE, NO POWER, SELF-TEST) carries
            # no worst cell, and printing it as one crashed the first run.
            print("%-10s %-66s (gated: no worst cell)"
                  % (r["verdict"], r["name"]))


if __name__ == "__main__":
    main()
