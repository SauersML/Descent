"""Verdict gates: make the harness refuse the errors it has actually made.

Across twelve batteries this harness produced roughly a dozen wrong verdicts. All
of them fell into a small number of repeatable shapes, and every one was caught
by a human noticing rather than by the harness objecting. That is the wrong place
for the check to live, so the shapes are encoded here.

FALSE POSITIVES -- a defect reported where none exists:

  BROKEN DESIGN. The asymmetric-migration cells reported 1458 sems against a
      design whose SYMMETRIC cell disagreed with an already-validated oracle.
      A battery that cannot reproduce a known result has no standing to report a
      new one, so `control=` is now mandatory for any falsification: a cell whose
      answer is independently known, run on the same code path. If the control
      misses, every verdict in that record is VOID rather than FALSIFIED.

  ASSUMED ERROR BARS. Two equilibria showed "100+ sems" from a plateau sampled at
      successive generations, which are autocorrelated, so the standard error was
      understated by the square root of the correlation time. `sem_source` must
      now be declared; anything but independent replicates downgrades a
      falsification to a lead.

  WORST-OF-N. `sourceBestLinearWeightsFromLD` reported 8 sems by taking the worst
      of 40 coordinates against a one-coordinate error bar. Declaring
      `selected_from=n` applies the sqrt(2 log n) correction.

  UNREAD REGIME. `cumulativeDrift`, `Var_Delta_Mu` and `pgsDriftVarianceFromLoci`
      were each tested against a reading their own docstring disowns. `regime=`
      was always required; it is now also compared against the definition's
      declared regime where one exists.

FALSE NEGATIVES -- a defect missed:

  SELF-TEST. Two "validations" compared a formula against a Python transcription
      of the same formula. Agreement to machine precision across every cell is
      not evidence; it is the same expression evaluated twice. Detected and
      reported as SELF-TEST, which counts as no measurement at all.

  NO POWER. A design whose prediction barely moves AND AGREES cannot reject a
      wrong functional form. This was already detected but reported alongside
      passes, where it reads as one. It is now a distinct failing verdict.
      The "and agrees" clause was added later and is the whole content of the
      gate: a flat prediction that misses by six hundred sems has been
      rejected, and filing that as NO POWER hid competitor rejections from
      `ledger.py`'s gate, which then downgraded the corpus MATCHes those
      rivals existed to clear.

  DEGENERATE ORACLE. If the simulated truth barely moves across the design, the
      oracle is not exercising the definition even if the prediction does.

  GENERATIVE SELF-TEST -- detected by declaration, not by arithmetic. The
      machine-precision check above catches a formula compared against a
      transcription of itself. It does NOT catch the subtler case where the
      SIMULATION was generated from the definition's own parameters:
      `expectedSquaredEffect = h2/M` was "validated" by drawing effects with
      variance `h2/M` and measuring their mean square, which tests the random
      number generator. Agreement there is guaranteed by construction and the
      residual is pure sampling noise, so it passes every numerical gate.
      `oracle_independent=False` must be declared for such a design, and the
      verdict is GENERATIVE SELF-TEST. The design rule this encodes: the oracle
      must not be built from the quantity under test.

  ASSUMED SEM SHAPE. `spikeAndSlabVariance` reported 10.6 sems at 2.4 percent
      because the error bar on a variance used `sqrt(2/M)`, which is the normal
      formula, against a mixture with a rare heavy component. The sem model is
      as much an assumption as the point estimate.
"""
import math
import re

# ---------------------------------------------------------------------------
# ORACLE IDENTITIES -- designs in which the definition IS its own oracle's
# estimator.  A PROPERTY OF THE DESIGN, NOT OF THE DEFINITION.
# ---------------------------------------------------------------------------
# The SELF-TEST gate below catches a formula that agrees with its oracle to
# machine precision. It does not catch this family: the estimator can reach the
# same expression by a slightly different numerical route, so the harness sees a
# few parts in 10^3 of scatter and banks a MATCH.
#
# THE ALGEBRA. `driftVariance(p0, fst) = p0(1-p0) fst`, whose `fst` is the
# per-branch Wright F. If the battery obtains F from the SAMPLE, as
# `Var(p)/(p0(1-p0))`, then the body is `Var(p)` -- what the oracle computes --
# using no Wright-Fisher property beyond the martingale, and no competitor could
# have been rejected. If the battery obtains F from the MODEL PARAMETERS, as
# `1-(1-1/(2Ne))^t`, agreement is the Wright-Fisher variance recursion and is a
# real prediction that can fail.
#
# THE CORRECTION THIS ENCODES. An earlier version keyed on the definition NAME
# and refused every MATCH for the three below. That was wrong in the expensive
# direction: `battery_bulk21` fed the sample's own F and its MATCHes are vacuous,
# but `battery_bulk41` group B feeds the model's F, MEASURES the Hudson and Nei
# readings on the same replicates as competitors, and FALSIFIES both (Nei by 157
# sems and 47% low, Hudson by 7.8 sems) while the body matches under one sem.
# Same definition, same oracle, opposite verdicts -- so vacuity cannot be a
# property of the definition, and a name-keyed gate would have discarded a real
# measurement.
#
# Hence `argument_source`: "model" -> a real prediction, "sample" -> VACUOUS, and
# silence -> LEAD, never a MATCH. Undeclared is unanswered, not innocent.
#
# TO ADD AN ENTRY you must be able to write the reduction AND name the argument
# whose source decides it. "It looks circular" is not enough.
ORACLE_IDENTITIES = {
    "driftVariance": (
        "fst",
        "with a sample-estimated F it reduces to Var(p), the oracle's own "
        "estimator; with the model's 1-(1-1/(2Ne))^t it is the Wright-Fisher "
        "variance recursion"),
    "twoPopDriftVariance": (
        "fst",
        "same reduction as driftVariance, doubled: sample-estimated F gives "
        "2 Var(p), the oracle's own estimator"),
    "expectedFreqDiffSq": (
        "fst",
        "the twoPopDriftVariance body with its arguments reordered; same "
        "reduction and the same dependence on where F came from"),
}

ARGUMENT_SOURCES = ("model", "sample")


def oracle_identity(name):
    """The (argument, reason) registry entry for `name`, or None.

    Battery labels are free text, so the match is on the definition name as a
    whole IDENTIFIER TOKEN. A bare substring test fires on
    `pgsDriftVarianceFromLoci` and silently discards a real falsification;
    `verdict_calibration.py` asserts that it does not.
    """
    if not name:
        return None
    for key, entry in ORACLE_IDENTITIES.items():
        if re.search(r"(?<![A-Za-z0-9_])" + re.escape(key) + r"(?![A-Za-z0-9_])",
                     name):
            return entry
    return None


def classify(cells, control=None, sem_source="replicates", selected_from=1,
             rel_floor=0.02, sem_gate=3.0, oracle_independent=True, name=None,
             argument_source=None):
    """Return (verdict, note, worst-cell) under the gates above.

    `name` is the definition under test; pass it, or the ORACLE_IDENTITIES gate
    cannot fire. `argument_source` is required for a registered definition and
    ignored otherwise: "model" means the identity-bearing argument came from the
    simulation's parameters, "sample" means it was estimated from the same
    replicates the oracle measures.
    """
    notes = []

    # --- FN gate: is this design's definition its own oracle's estimator? ----
    entry = oracle_identity(name)
    if entry is not None:
        arg, why = entry
        if argument_source is None:
            return "LEAD (undeclared argument source)", (
                "`%s` %s. The verdict depends entirely on where this design "
                "obtained `%s`, and this battery did not say. Declare "
                "argument_source='model' or 'sample'" % (name, why, arg)), cells[0]
        if argument_source not in ARGUMENT_SOURCES:
            return "LEAD (undeclared argument source)", (
                "argument_source=%r is not one of %s"
                % (argument_source, ", ".join(ARGUMENT_SOURCES))), cells[0]
        if argument_source == "sample":
            return "VACUOUS (oracle identity)", (
                "no verdict is available: `%s` was estimated from the same "
                "replicates the oracle measures, and %s. Feed the model's value "
                "instead, as battery_bulk41 group B does" % (arg, why)), cells[0]
        notes.append(
            "argument_source='model': `%s` comes from the simulation's "
            "parameters, so agreement is a prediction and not an identity" % arg)

    # --- FN gate: generative self-test --------------------------------------
    # Declared, not inferred: no arithmetic can tell "the formula predicts the
    # data" from "the data were generated by the formula", because in both
    # cases the residual is sampling noise around zero.
    if not oracle_independent:
        return "GENERATIVE SELF-TEST", (
            "the simulation was generated from this definition's own "
            "parameters, so agreement is guaranteed by construction and the "
            "residual is sampling noise"), cells[0]

    # --- FN gate: self-test -------------------------------------------------
    if all(abs(c["lean"] - c["truth"]) <= 1e-11 * max(1.0, abs(c["truth"]))
           for c in cells):
        return "SELF-TEST", ("prediction equals truth to machine precision in "
                             "every cell: the oracle is the formula, not a "
                             "measurement"), cells[0]

    preds = [c["lean"] for c in cells]
    truths = [c["truth"] for c in cells]
    span_pred = ((max(preds) - min(preds)) / max(abs(max(preds)), 1e-12)
                 if preds else 0.0)
    span_true = ((max(truths) - min(truths)) / max(abs(max(truths)), 1e-12)
                 if truths else 0.0)

    # --- error-bar corrections ---------------------------------------------
    infl = 1.0
    if selected_from > 1:
        infl *= math.sqrt(2 * math.log(selected_from))
        notes.append("error bar inflated by sqrt(2 log %d) for worst-of-%d "
                     "selection" % (selected_from, selected_from))
    if sem_source != "replicates":
        notes.append("sem_source=%s: not independent replicates, so a "
                     "significance claim is a lead and not a finding"
                     % sem_source)

    worst = None
    for c in cells:
        sem = c.get("sem") or float("nan")
        sem = sem * infl
        z = (abs(c["lean"] - c["truth"]) / sem
             if sem == sem and sem > 0 else float("inf"))
        rel = abs(c["lean"] - c["truth"]) / max(abs(c["truth"]), 1e-12)
        c["sems_off"], c["rel_err"] = z, rel
        if worst is None or z > worst["sems_off"]:
            worst = c

    # --- FN gates: power ----------------------------------------------------
    if span_true < 0.05:
        return "DEGENERATE ORACLE", ("the simulated truth moves by only %.1f%% "
                                     "across the design" % (100 * span_true)), worst

    disagrees = worst["sems_off"] > sem_gate and worst["rel_err"] > rel_floor

    # A FLAT PREDICTION MAKES AN AGREEMENT WORTHLESS AND A DISAGREEMENT REAL,
    # and this gate used to fire before it knew which it was looking at. The
    # rationale it carries -- "could not have rejected a wrong functional form"
    # -- is about a body that AGREES over a design it barely moves across:
    # matching a truth that also barely moves is arithmetic. It says nothing
    # about a formula that stays flat while the oracle sweeps 60% and misses by
    # six hundred sems. That is a rejection, and it was being filed as NO POWER.
    #
    # The cost was not cosmetic. Most flat predictions in this harness are
    # COMPETITORS -- `retention [no decay at all]` is the literal constant 1 --
    # and `ledger.py` clears a corpus MATCH only when a competitor was
    # REJECTED. Every rival buried under NO POWER left the body it was supposed
    # to discriminate against looking uncompeted, and the ledger then downgraded
    # that body's MATCH to UNINFORMATIVE. A gate against false validation was
    # manufacturing the appearance of one.
    if span_pred < 0.05 and not disagrees:
        return "NO POWER", ("the prediction moves by %.1f%% across the design "
                            "and agrees with the oracle, so the design could "
                            "not have rejected a wrong functional form"
                            % (100 * span_pred)), worst

    # An unreliable error bar invalidates a PASS as surely as a failure: if the
    # scatter is understated, "agrees to 0.4 percent" carries no more weight
    # than "disagrees at 100 sems" did. ibdRecurrenceFixedPoint reached MATCH
    # this way, which would have recorded a validation the design cannot support.
    if sem_source != "replicates":
        return "LEAD (weak error bar)", "; ".join(notes), worst

    # --- FP gate: positive control ------------------------------------------
    # A control whose predicted and measured values are the SAME NUMBER is not
    # a control. Battery 23 declared three of them -- `lean=1.0, truth=1.0`,
    # asserted rather than measured -- and one "passed at 0.00 sems" while the
    # battery it was gating was wrong by exactly a factor of two. A control has
    # to be capable of failing, which means both sides must come from somewhere
    # independent.
    if control is not None:
        cl, ct = control.get("lean"), control.get("truth")
        if cl is not None and ct is not None and abs(cl - ct) < 1e-12:
            notes.append("control '%s' is DEGENERATE: predicted and measured "
                         "are the same number, so it cannot fail and gates "
                         "nothing" % control.get("design", "?"))
            control = None

    if disagrees:
        if control is None:
            return "LEAD (no control)", ("a disagreement without a positive "
                                         "control is a lead: the design has not "
                                         "shown it can reproduce a known result"), worst
        cs = control.get("sem") or float("nan")
        cz = (abs(control["lean"] - control["truth"]) / cs
              if cs == cs and cs > 0 else float("inf"))
        if cz > sem_gate:
            return "VOID (control failed)", (
                "the positive control '%s' missed by %.1f sems on the same code "
                "path, so this design cannot support any verdict"
                % (control.get("design", "?"), cz)), worst
        notes.append("positive control '%s' passed at %.2f sems"
                     % (control.get("design", "?"), cz))
        if sem_source != "replicates":
            return "LEAD (weak error bar)", "; ".join(notes), worst
        return "FALSIFIED", "; ".join(notes), worst

    return "MATCH", "; ".join(notes) if notes else "", worst


def report(name, source, cells, verdict, note, worst, regime=""):
    # Backstop for a battery that computed its verdict without passing `name=`.
    # It downgrades to a LEAD, not to VACUOUS: whether the identity bites depends
    # on where the design got its identity-bearing argument, and a battery that
    # never passed `name=` cannot have passed `argument_source=` either, so the
    # answer is unknown. Claiming VACUOUS here would repeat the mistake this gate
    # was corrected for -- discarding battery_bulk41's competitor-rejecting MATCH.
    entry = oracle_identity(name)
    if entry is not None and verdict.startswith("MATCH"):
        arg, why = entry
        verdict = "LEAD (undeclared argument source)"
        note = ("DOWNGRADED FROM MATCH: `%s` %s, so the verdict turns on where "
                "`%s` came from. This battery passed neither name= nor "
                "argument_source= to classify; pass both. %s"
                % (name, why, arg, note)).strip()
    return _report(name, source, cells, verdict, note, worst, regime)


def _report(name, source, cells, verdict, note, worst, regime=""):
    print("\n%-40s %s   (pred span %s)"
          % (name, verdict,
             "%.0f%%" % (100 * (max(c["lean"] for c in cells)
                                - min(c["lean"] for c in cells))
                         / max(abs(max(c["lean"] for c in cells)), 1e-12))))
    print("  lean: %s" % source)
    if regime:
        print("  regime: %s" % regime)
    if note:
        print("  NOTE: %s" % note)
    print("  %-34s %10s %10s %8s %8s" % ("design", "lean", "sim", "sem", "sems"))
    for c in cells:
        print("  %-34s %10.5f %10.5f %8.5f %8.2f"
              % (c["design"], c["lean"], c["truth"], c.get("sem", float("nan")),
                 c.get("sems_off", float("nan"))))
