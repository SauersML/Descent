"""Calibration of the verdict gates against this harness's own history.

A gate that has not been shown to fire on the errors it was written for is a
gate nobody should trust -- the same standard the oracles in this directory are
held to. So every wrong verdict this harness actually produced is replayed here
with its real numbers, together with every correct one, and the gates must
separate them.

Two failure directions matter and they trade off. Gates loose enough to pass the
true findings may pass the artefacts too; gates tight enough to kill the
artefacts may kill the findings. Both columns are therefore checked, and the
expected verdict is written down BEFORE the gate runs.
"""
import verdict

CASES = []


def case(name, expect, cells, **kw):
    CASES.append((name, expect, cells, kw))


# ---------------------------------------------------------------------------
# FALSE POSITIVES the harness produced: the gates must NOT return FALSIFIED
# ---------------------------------------------------------------------------
case("asymmetricFst (broken design)", "DEGENERATE",
     [dict(design="m12=0.004 m21=0.004", lean=0.23810, truth=0.07709, sem=0.00011),
      dict(design="m12=0.002 m21=0.006", lean=0.17241, truth=0.07909, sem=0.00010),
      dict(design="m12=0.001 m21=0.007", lean=0.15152, truth=0.07949, sem=0.00017)],
     # Refused as DEGENERATE before the control is even consulted: the truth
     # moves 3% across the design. That is the better diagnosis -- the design
     # cannot separate anything, control or no control.
     control=dict(design="symmetric cell vs validated 2-deme island F_ST",
                  lean=0.09743, truth=0.07709, sem=0.00432))

case("ibdRecurrenceFixedPoint (autocorrelated plateau)", "LEAD",
     [dict(design="Ne=200 m=0.002", lean=0.38390, truth=0.37565, sem=0.00009),
      dict(design="Ne=200 m=0.005", lean=0.19880, truth=0.19622, sem=0.00003),
      dict(design="Ne=500 m=0.005", lean=0.09029, truth=0.08924, sem=0.00001)],
     sem_source="timeseries",
     control=dict(design="one-step map on same trajectories",
                  lean=0.27083, truth=0.27079, sem=0.00365))

case("sourceBestLinearWeightsFromLD (worst of 40)", "MATCH",
     [dict(design="coalescent LD", lean=0.24305, truth=0.13688, sem=0.01315),
      dict(design="linkage equilibrium", lean=-0.19060, truth=-0.17226, sem=0.01037)],
     selected_from=40)

case("meanAbsoluteEffect (self-test)", "SELF-TEST",
     [dict(design="all equal", lean=1.0, truth=1.0, sem=0.0),
      dict(design="gaussian", lean=0.85095, truth=0.85095, sem=0.02780),
      dict(design="one dominant", lean=0.11980, truth=0.11980, sem=0.01978)])

case("liabilityCaseVariance (disambiguation, no span)", "NO POWER",
     [dict(design="var(liability|case)", lean=0.74142, truth=0.13822, sem=0.00044),
      dict(design="var(PGS|case)/r2", lean=0.74142, truth=0.74137, sem=0.00234)])

# ---------------------------------------------------------------------------
# TRUE FINDINGS: the gates must still return FALSIFIED
# ---------------------------------------------------------------------------
case("pairwiseFstFromBranchTaus (real)", "FALSIFIED",
     [dict(design="t=500", lean=0.33333, truth=0.19923, sem=0.00227),
      dict(design="t=1000", lean=0.50000, truth=0.33415, sem=0.00319),
      dict(design="t=2000", lean=0.66667, truth=0.49974, sem=0.00330)],
     control=dict(design="coalFst on the same runs",
                  lean=0.33333, truth=0.33415, sem=0.00319))

case("polygenicAdaptationShift (real)", "FALSIFIED",
     [dict(design="linkage equilibrium", lean=0.83286, truth=1.78945, sem=0.10279),
      dict(design="coalescent LD", lean=-1.83130, truth=-3.66260, sem=0.12035)],
     control=dict(design="pgsMeanShift on the same runs",
                  lean=1.66572, truth=1.78945, sem=0.10279))

case("islandDemeCorrection squared (real)", "FALSIFIED",
     [dict(design="n=2", lean=0.05882, truth=0.09743, sem=0.00432),
      dict(design="n=4", lean=0.12329, truth=0.15885, sem=0.00796),
      dict(design="n=20", lean=0.18409, truth=0.19065, sem=0.00520)],
     # The control must be INDEPENDENTLY known, not the rival candidate: using
     # the linear form here voided a true finding, because at two demes that
     # form is itself only good to 3.2 sems. Wright's many-deme limit at n = 40
     # is textbook and is what the design must reproduce to be trusted.
     control=dict(design="many-deme limit 1/(1+4Nm) at n=40",
                  lean=0.20000, truth=0.19922, sem=0.00710))

case("sharedLDRetention (real, small effect)", "FALSIFIED",
     [dict(design="r=0.01 t=20", lean=0.67032, truth=0.66902, sem=0.00100),
      dict(design="r=0.01 t=100", lean=0.13534, truth=0.13415, sem=0.00056),
      dict(design="r=0.05 t=40", lean=0.01832, truth=0.01653, sem=0.00014)],
     control=dict(design="discreteRecombinationSurvival on the same draws",
                  lean=0.12851, truth=0.12859, sem=0.00053))

# ---------------------------------------------------------------------------
# TRUE VALIDATIONS: the gates must still return MATCH
# ---------------------------------------------------------------------------
case("r2FromSourceWeights (real validation)", "MATCH",
     [dict(design="source", lean=0.05367, truth=0.05366, sem=0.00017),
      dict(design="target", lean=0.00162, truth=0.00161, sem=0.00001)])

case("coalFst (real validation)", "MATCH",
     [dict(design="t=500", lean=0.20000, truth=0.19923, sem=0.00227),
      dict(design="t=1000", lean=0.33333, truth=0.33415, sem=0.00319),
      dict(design="t=2000", lean=0.50000, truth=0.49974, sem=0.00330)])


# ---------------------------------------------------------------------------
# ORACLE IDENTITIES: all three ends of the argument_source declaration.
# ---------------------------------------------------------------------------
# SAMPLE-FED, battery_bulk21's design: F estimated from the same replicates the
# oracle measures, so the body IS the estimator and the MATCH is algebra.
case("driftVariance, F from the SAMPLE (bulk21)", "VACUOUS",
     [dict(design="t=30", lean=0.01784, truth=0.01786, sem=0.00021),
      dict(design="t=100", lean=0.05512, truth=0.05498, sem=0.00058),
      dict(design="t=250", lean=0.11627, truth=0.11640, sem=0.00121)],
     name="driftVariance", argument_source="sample")

# MODEL-FED, battery_bulk41 group B with its real numbers. Same definition, same
# oracle, and a genuine MATCH -- the competing Hudson and Nei readings are
# falsified on these very cells. A gate keyed on the definition NAME refused
# this, which was the expensive direction to be wrong in, and this row is what
# stops it recurring.
case("driftVariance, F from the MODEL (bulk41 group B)", "MATCH",
     [dict(design="Ne=200 t=50", lean=0.02470, truth=0.02464, sem=0.0000706),
      dict(design="Ne=200 t=150", lean=0.06574, truth=0.06556, sem=0.0001875),
      dict(design="Ne=500 t=100", lean=0.01999, truth=0.01997, sem=0.0000455),
      dict(design="Ne=100 t=40", lean=0.03815, truth=0.03817, sem=0.0001429)],
     name="driftVariance", argument_source="model")

# UNDECLARED: neither innocent nor guilty. This is the end most likely to be
# under-tested and the one that fires most often in practice, since no existing
# battery passes the declaration yet.
case("driftVariance, argument source not declared", "LEAD",
     [dict(design="Ne=200 t=50", lean=0.02470, truth=0.02464, sem=0.0000706),
      dict(design="Ne=200 t=150", lean=0.06574, truth=0.06556, sem=0.0001875),
      dict(design="Ne=500 t=100", lean=0.01999, truth=0.01997, sem=0.0000455)],
     name="driftVariance")

# A MISSPELLED declaration must not read as a valid one.
case("driftVariance, argument_source misspelled", "LEAD",
     [dict(design="Ne=200 t=50", lean=0.02470, truth=0.02464, sem=0.0000706),
      dict(design="Ne=200 t=150", lean=0.06574, truth=0.06556, sem=0.0001875),
      dict(design="Ne=500 t=100", lean=0.01999, truth=0.01997, sem=0.0000455)],
     name="driftVariance", argument_source="modl")

case("expectedFreqDiffSq [competing] (label decoration must not evade it)",
     "VACUOUS",
     [dict(design="t=30", lean=0.03568, truth=0.03572, sem=0.00042),
      dict(design="t=100", lean=0.11024, truth=0.10996, sem=0.00116),
      dict(design="t=250", lean=0.23254, truth=0.23280, sem=0.00242)],
     name="AncestrySpecificArchitecture.expectedFreqDiffSq [competing]",
     argument_source="sample")

# SUBSTRING TRAP: whole-identifier matching, or this real falsification is
# silently discarded.
case("pgsDriftVarianceFromLoci (NOT registered)", "FALSIFIED",
     [dict(design="t=30", lean=25.98, truth=51.55, sem=1.46),
      dict(design="t=100", lean=91.79, truth=181.14, sem=5.12),
      dict(design="t=250", lean=210.88, truth=427.79, sem=12.10)],
     name="pgsDriftVarianceFromLoci",
     control=dict(design="pgsDriftVariance_one_pop on the same draws",
                  lean=51.97, truth=51.55, sem=1.46))

case("coalFst (real validation, named)", "MATCH",
     [dict(design="t=500", lean=0.20000, truth=0.19923, sem=0.00227),
      dict(design="t=1000", lean=0.33333, truth=0.33415, sem=0.00319),
      dict(design="t=2000", lean=0.50000, truth=0.49974, sem=0.00330)],
     name="coalFst")


def check_report_backstop():
    """The report() backstop, which classify-only calibration cannot reach.

    Every case above exercises `classify`. A battery that computed MATCH without
    passing `name=` never touches that path, and the backstop in `report()` is
    the only thing standing between it and a banked MATCH -- so it needs its own
    case, at both ends.
    """
    import io
    import contextlib
    out = []
    cells = [dict(design="d", lean=1.0, truth=1.0, sem=0.1, sems_off=0.0)]
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        verdict.report("driftVariance", "p0*(1-p0)*fst", cells,
                       "MATCH", "", cells[0])
    if "LEAD" not in buf.getvalue():
        out.append("report() did not downgrade a MATCH for a registered "
                   "definition; the backstop is dead")
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        verdict.report("coalFst", "t/(t+2*Ne)", cells, "MATCH", "", cells[0])
    if "LEAD" in buf.getvalue():
        out.append("report() downgraded a MATCH for an UNREGISTERED definition; "
                   "the backstop fires on everything and is worthless")
    return out


def main():
    print("%-46s %-22s %-22s %s" % ("case", "expected", "gate verdict", "ok"))
    print("-" * 100)
    npass = 0
    for name, expect, cells, kw in CASES:
        v, note, worst = verdict.classify([dict(c) for c in cells], **kw)
        ok = v.split(" ")[0] == expect.split(" ")[0]
        npass += ok
        print("%-46s %-22s %-22s %s" % (name, expect, v, "PASS" if ok else "*** FAIL"))
        if not ok:
            print("      note: %s" % note)
    print("-" * 100)
    print("%d / %d gate outcomes as specified" % (npass, len(CASES)))
    extra = check_report_backstop()
    for e in extra:
        print("*** FAIL  %s" % e)
    print("\nThe two columns are the point: the artefacts the harness actually")
    print("produced are refused, and the real findings and real validations")
    print("survive unchanged. The oracle-identity rows add all three ends of")
    print("the argument_source declaration -- sample refused, model kept,")
    print("undeclared and misspelled both asked -- plus the report() backstop,")
    print("which no classify-only case can reach.")
    # A calibration that cannot fail the run is one nobody notices has stopped
    # holding.
    return 0 if (npass == len(CASES) and not extra) else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
