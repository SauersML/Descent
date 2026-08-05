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

  NO POWER. A design whose prediction barely moves cannot reject a wrong
      functional form. This was already detected but reported alongside passes,
      where it reads as one. It is now a distinct failing verdict.

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
# ORACLE IDENTITIES -- definitions that ARE their own oracle's estimator.
# ---------------------------------------------------------------------------
# The SELF-TEST gate below catches a formula that agrees with its oracle to
# machine precision. It does NOT catch this family, and `battery_bulk21` is the
# proof: `driftVariance`, `twoPopDriftVariance` and `expectedFreqDiffSq` each
# reduce ALGEBRAICALLY to the quantity the simulator measures, yet the harness
# saw a few parts in 10^3 of scatter -- because the estimator reaches the same
# expression by a slightly different numerical route -- and banked three MATCH
# verdicts. Machine-precision agreement is sufficient evidence of a self-test
# and not necessary for one.
#
# So the gate is DECLARED, like `oracle_independent`, and for the same reason:
# no arithmetic on the cells can distinguish "the formula predicts the
# measurement" from "the formula IS the measurement, computed twice". The
# distinguishing fact lives in the algebra, and it is established once, by
# computer algebra, and recorded here.
#
# THE ALGEBRA. The simulator estimates F_ST on the same run as Wright's
# definition, F_ST := Var(p)/(p0(1-p0)). Substituting it into each body:
#
#     driftVariance(p0, fst)        = p0(1-p0) * Var(p)/(p0(1-p0))  = Var(p)
#     twoPopDriftVariance(p0, fst)  = 2 * the same                  = 2 Var(p)
#     expectedFreqDiffSq(fst, p0)   = the same body, args reordered = 2 Var(p)
#
# and `Var(p)`, `2 Var(p)` are exactly what the oracle computes. Residual zero,
# using no Wright-Fisher property beyond the martingale E[p_t] = p0. A body that
# is genuinely a different function of the same inputs does NOT collapse.
#
# The gate is pinned in the CI-gated differential battery as well, so it cannot
# lapse silently: see `empirical/differential/checks.py` section 20 and its
# calibration `empirical/differential/test_identity_gate.py`.
#
# TO ADD AN ENTRY you must be able to write the reduction, as above. "It looks
# circular" is not enough; a wrong entry throws away a real measurement, which
# is the more expensive mistake because nobody re-runs a battery that has been
# declared vacuous.
ORACLE_IDENTITIES = {
    "driftVariance":
        "reduces to Var(p), the oracle's own estimator, under "
        "F_ST := Var(p)/(p0(1-p0))",
    "twoPopDriftVariance":
        "reduces to 2 Var(p), the oracle's own estimator, under "
        "F_ST := Var(p)/(p0(1-p0))",
    "expectedFreqDiffSq":
        "the twoPopDriftVariance body with its arguments reordered; same "
        "reduction, same vacuity",
}


def oracle_identity(name):
    """The registry reason for `name`, or None.

    Battery labels are free text -- `driftVariance [competing]`,
    `AncestrySpecificArchitecture.driftVariance`, `driftVariance / peer` -- so
    the match is on the definition name as a whole IDENTIFIER TOKEN, not as a
    substring. A bare `in` test would fire on `pgsDriftVarianceFromLoci` the
    moment someone lowercased a label, and silently discard a real measurement;
    `verdict_calibration.py` asserts that it does not.
    """
    if not name:
        return None
    for key, why in ORACLE_IDENTITIES.items():
        if re.search(r"(?<![A-Za-z0-9_])" + re.escape(key) + r"(?![A-Za-z0-9_])",
                     name):
            return why
    return None


def classify(cells, control=None, sem_source="replicates", selected_from=1,
             rel_floor=0.02, sem_gate=3.0, oracle_independent=True, name=None):
    """Return (verdict, note, worst-cell) under the gates above.

    `name` is the definition under test. Pass it: it is what lets the
    ORACLE_IDENTITIES gate fire, and a battery that omits it silently loses that
    gate. It is optional only so that existing callers keep working rather than
    crashing, which would be a worse failure than the one being fixed.
    """
    notes = []

    # --- FN gate: the definition IS the oracle's estimator -------------------
    # First, because it makes every later gate moot: there is nothing to weigh
    # when the two sides are the same expression.
    why = oracle_identity(name)
    if why is not None:
        return "VACUOUS (oracle identity)", (
            "no verdict is available from this design: the definition %s, so "
            "agreement is algebraic and disagreement would be arithmetic error. "
            "A non-vacuous design has to vary something the identity does not "
            "carry -- here, WHICH F_ST convention the caller supplies" % why), cells[0]

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
    if span_pred < 0.05:
        return "NO POWER", ("the prediction moves by %.1f%% across the design, "
                            "so it could not have rejected a wrong functional "
                            "form" % (100 * span_pred)), worst
    if span_true < 0.05:
        return "DEGENERATE ORACLE", ("the simulated truth moves by only %.1f%% "
                                     "across the design" % (100 * span_true)), worst

    disagrees = worst["sems_off"] > sem_gate and worst["rel_err"] > rel_floor

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
    # The backstop for a battery that computed its verdict without passing
    # `name=` to classify. A registered oracle identity must never appear as a
    # MATCH, whatever route the caller took to get one, because that MATCH is
    # what gets read off the console and written into the docstring.
    why = oracle_identity(name)
    if why is not None and verdict.startswith("MATCH"):
        verdict = "VACUOUS (oracle identity)"
        note = ("DOWNGRADED FROM MATCH: %s. This battery did not pass name= to "
                "classify, so the gate fired here instead; pass it. %s"
                % (why, note)).strip()
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
        # `sems_off` is set by the per-cell loop in classify, which the EARLY
        # gates -- SELF-TEST, GENERATIVE SELF-TEST and now VACUOUS (oracle
        # identity) -- return before reaching. Those gates are exactly the ones
        # whose verdict matters most, so report must not raise KeyError on
        # them; a crash here would read as a broken battery rather than as a
        # refused verdict.
        print("  %-34s %10.5f %10.5f %8.5f %8.2f"
              % (c["design"], c["lean"], c["truth"], c.get("sem", float("nan")),
                 c.get("sems_off", float("nan"))))
