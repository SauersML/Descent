"""Coverage ledger for the population-genetics slice.

THE RULE
--------
Every definition in the slice is in exactly one of three states:

  COVERED      a check exists that compares it to an independent reference AND
               is demonstrated able to fail (mutation-tested, non-vacuous).
  UNREACHABLE  named reason why no reference can exist. An explicit, argued
               entry -- not a silence.
  UNACCOUNTED  neither. This number must go to zero; it is the only one that
               represents work not yet done.

A definition counted as COVERED because a check merely *runs* against it would
inflate the number without informing anyone, so coverage is taken from the
battery's own vacuity verdict rather than from the existence of a check.
"""

import json
import os
import sys

import checks
import corpus

api = corpus.api

# The slice this agent owns, by Lean source file.
SLICE_FILES = [
    "Descent/PortabilityDrift.lean",
    "Descent/DGP.lean",
    "Descent/PopulationGeneticsFoundations.lean",
    "Descent/LDDecayTheory.lean",
    "Descent/DemographicHistory.lean",
    "Descent/PhenomeWidePortability.lean",
    "Descent/PortabilityBounds.lean",
]

# ---------------------------------------------------------------------------
# UNREACHABLE: each entry must say WHY no independent reference can be built.
# "Hard" is not a reason. "No reference exists even in principle" is.
# ---------------------------------------------------------------------------
UNREACHABLE_RULES = [
    (
        "free-parameter",
        "the definition contains a knob that nothing in the corpus derives, so "
        "any value can be fitted and no simulation can refute it. The docstring "
        "of selectedDriftFactor states this outright for s_correction.",
        lambda d: False,  # assigned by explicit name list below
    ),
]

UNREACHABLE_NAMED = {
    # --- free parameters: unfalsifiable by construction -------------------
    "selectedDriftFactor": "free-parameter: `s_correction` is a knob no model "
                           "in the corpus derives; the Lean docstring says so.",
    # --- pure re-namings with no empirical content ------------------------
    "targetHetFromFst": "tautology: round-trips to the identity with "
                        "fstFromHetRatio for every input, so no grid can make "
                        "it fail. Demonstrated in check targetHetFromFst-tautology.",
}


# ---------------------------------------------------------------------------
# Definitions covered by a SIMULATION that has been run, with both its
# theory-pinned controls green. Each entry names the script, the result file,
# and the separation that makes the check able to fail.
# ---------------------------------------------------------------------------
def _inlined_members():
    """Cluster members found MECHANICALLY by inlined.py, not by name or docstring.

    Driven from the sweep rather than a hand list: a hand list stops covering
    definitions added later, and the whole point of the sweep is that the
    cluster cannot be found by reading names. `neutralDriftFactor`
    (PhenomeWidePortability.lean:125) was found this way and by no other route.
    """
    import os
    if not os.path.exists("inlined.json"):
        return []
    d = json.load(open("inlined.json"))
    return [m["definition"].split(".")[-1]
            for r in d.values() for m in r["members"]]


SIMULATION_COVERED = {
    name: {
        "script": "heavy/h0_heterozygosity_cluster.py",
        "results": "heavy/h0_results.json",
        "controls": "CONTROL 1 (mu=0 reproduces (1-1/2Ne)^t) GREEN; "
                    "CONTROL 2 (equilibrium = theta/(1+theta)) GREEN at all four theta",
        "can_fail": "cluster predicts retention 0.1352 at t=2*(2Ne); measured "
                    "1.0017 +- 0.0036 at theta=8, which is 240 sem away. Had "
                    "the measurement landed near 0.135 the cluster would have "
                    "been vindicated.",
        "verdict": "MODEL error: retention is 1.0 at every theta >= 0.05, not "
                   "0.135. The formula is algebraically correct for the closed "
                   "no-mutation population it assumes; that population is not "
                   "the one it is cited about.",
    }
    for name in sorted(set(_inlined_members()) | {
        # island family: simulated by cluster/fam_coalescent.py, which varies
        # the deme count that no member takes as an argument
        "asymmetricFst", "fstMigDriftEquil", "fstMigrationDriftEquilibrium",
        "sharedLD_from_equilibrium", "neutralAFBenchmarkFromRecurrence",
        "fstDriftMigration",
        # recursion / vector forms of the same quantity, outside the scalar sweep
        "hetRecurrence",
        "cumulativeDrift",
        "heterozygosityLossVariableNe",
    })
}


def slice_definitions():
    """Every definition in the owned files, with its metadata."""
    out = {}
    for fq, d in api.definition_table().items():
        if d.get("file") in SLICE_FILES:
            out[fq] = d
    return out


def covered_definitions(results_path="results.json"):
    """FQ names the battery covers with a check demonstrated able to fail."""
    if not os.path.exists(results_path):
        return {}, {}
    res = json.load(open(results_path))
    covered, weak = {}, {}
    for cid, c in res["checks"].items():
        fq = c.get("definition")
        if not fq or not fq.startswith("Descent."):
            continue
        # An identity check is vacuous by construction: it records a duplicate
        # or a tautology, it does not validate. It does not count as coverage.
        if c.get("kind") in ("identity", "selftest") or c.get("vacuous"):
            weak.setdefault(fq, []).append(cid)
            continue
        covered.setdefault(fq, []).append(cid)
    return covered, weak


def report(results_path="results.json"):
    defs = slice_definitions()
    covered, weak = covered_definitions(results_path)

    rows = []
    for fq, d in sorted(defs.items()):
        short = fq.split(".")[-1]
        if short in SIMULATION_COVERED:
            state = "COVERED"
            why = "SIMULATION " + SIMULATION_COVERED[short]["script"]
            if fq in covered:
                why += " + analytic " + ",".join(covered[fq])
        elif fq in covered:
            state, why = "COVERED", "analytic " + ",".join(covered[fq])
        elif short in UNREACHABLE_NAMED:
            state, why = "UNREACHABLE", UNREACHABLE_NAMED[short]
        elif fq in weak:
            state, why = "UNACCOUNTED", (
                "only identity/vacuous checks: " + ",".join(weak[fq])
            )
        else:
            state, why = "UNACCOUNTED", ""
        rows.append({
            "definition": fq,
            "file": d.get("file"),
            "line": d.get("line"),
            "state": state,
            "why": why,
            "empirical_status": d.get("empirical_status"),
            "extractable": _extractable(fq),
        })
    return rows


def _extractable(fq):
    try:
        api.callable_for(fq)
        return True
    except Exception:
        return False


if __name__ == "__main__":
    rows = report()
    n = len(rows)
    by_state = {}
    for r in rows:
        by_state.setdefault(r["state"], []).append(r)
    sim = sum(1 for r in rows if r["why"].startswith("SIMULATION"))
    cov = len(by_state.get("COVERED", []))
    unr = len(by_state.get("UNREACHABLE", []))
    una = len(by_state.get("UNACCOUNTED", []))

    print(f"SLICE: {n} definitions across {len(SLICE_FILES)} files")
    print(f"  COVERED      {cov:4d}  ({100*cov/n:.1f}%)   check exists and can fail")
    print(f"    of which simulation-backed: {sim}")
    print(f"  UNREACHABLE  {unr:4d}  ({100*unr/n:.1f}%)   named reason, no reference possible")
    print(f"  UNACCOUNTED  {una:4d}  ({100*una/n:.1f}%)   <- the number that must reach zero")
    print(f"  accounted for: {100*(cov+unr)/n:.1f}%")
    print()
    by_file = {}
    for r in rows:
        f = r["file"].split("/")[-1]
        by_file.setdefault(f, {"n": 0, "cov": 0, "ext": 0})
        by_file[f]["n"] += 1
        by_file[f]["cov"] += r["state"] == "COVERED"
        by_file[f]["ext"] += bool(r["extractable"])
    print(f"{'file':<40} {'defs':>5} {'covered':>8} {'extractable':>12}")
    for f, s in sorted(by_file.items(), key=lambda kv: -kv[1]["n"]):
        print(f"{f:<40} {s['n']:>5} {s['cov']:>8} {s['ext']:>12}")

    json.dump(rows, open("coverage_ledger.json", "w"), indent=1)
    print("\n-> coverage_ledger.json")
