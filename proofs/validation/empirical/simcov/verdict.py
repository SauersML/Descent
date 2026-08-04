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
"""
import math


def classify(cells, control=None, sem_source="replicates", selected_from=1,
             rel_floor=0.02, sem_gate=3.0):
    """Return (verdict, note, worst-cell) under the gates above."""
    notes = []

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
                 c["sems_off"]))
