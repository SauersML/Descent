#!/usr/bin/env python3
"""Model-family inventory: which families have a simulator, and which do not.

Run with the anaconda module (needs only stdlib + defs.json):
    module load python3/3.10.9_anaconda2023.03_libmamba
    python3 families.py

WHY FAMILIES RATHER THAN DEFINITIONS
    A modelling choice lives in a family, not in a definition. The island
    family has 8 definitions across 5 files that all compute 1/(1 + 4 Ne m) and
    none of them says it is the infinite-island limit -- so one simulator that
    varies the deme count settles all eight at once, and no amount of
    definition-by-definition checking would have grouped them.

    The number to drive to zero first is FAMILIES WITH NO SIMULATOR. A family
    with none is a blind spot with many definitions behind it, and it is
    invisible in a per-definition coverage percentage.

MEMBERSHIP IS MECHANICAL WHERE IT CAN BE
    Families whose members were found by level-set invariance carry
    `found_by: sweep` and their membership is reproducible from
    sweep_inlined.py rather than from reading names. Families assembled by hand
    carry `found_by: manual` and are explicitly less trustworthy -- that
    distinction is recorded rather than smoothed over, because the whole point
    of the sweep was that names do not identify what a definition computes.
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.normpath(os.path.join(HERE, "..", "..", "extract"))

SLICE_FILES = [
    "Calibrator/PortabilityDrift.lean",
    "Calibrator/DGP.lean",
    "Calibrator/PopulationGeneticsFoundations.lean",
    "Calibrator/LDDecayTheory.lean",
    "Calibrator/DemographicHistory.lean",
    "Calibrator/PhenomeWidePortability.lean",
    "Calibrator/PortabilityBounds.lean",
]

# ---------------------------------------------------------------------------
# Families. `simulator` is None when nothing simulates the family yet -- that
# is the count to drive down, and an honest None is worth more than a
# simulator that only exercises the easy corner of a family.
# ---------------------------------------------------------------------------
FAMILIES = [
    {
        "name": "drift_retention",
        "model": "closed population, no mutation; heterozygosity retained as "
                 "(1 - 1/(2Ne))^t",
        "simulator": "heavy/h0_heterozygosity_cluster.py",
        "status": "SIMULATED -- MODEL ERROR. Predicted retention 0.1352 at "
                  "t = 2*(2Ne); measured 1.0017 +/- 0.0036 at theta=8, both "
                  "controls green. Algebra correct, premise false.",
        "found_by": "sweep",
        "members": ["fstDerived", "heterozygosityLossFromDrift",
                    "ldRetainedFraction", "neutralDriftFactor",
                    "wrightFisherDriftRetention",
                    "wrightFisherHeterozygosityLoss", "hetRecurrence",
                    "cumulativeDrift", "fstVariableNe"],
    },
    {
        "name": "island_migration_fst",
        "model": "infinite island; F_ST = 1/(1 + 4 Ne m), no deme count",
        "simulator": "cluster/fam_coalescent.py (family_island)",
        "status": "SIMULATED -- varies deme count, which no member takes as an "
                  "argument",
        "found_by": "sweep",
        "members": ["islandModelFst", "asymmetricFst", "fstMigDriftEquil",
                    "fstMigrationDriftEquilibrium", "equilibriumFst",
                    "sharedLD_from_equilibrium",
                    "neutralAFBenchmarkFromRecurrence", "fstDriftMigration"],
    },
    {
        "name": "split_fst",
        "model": "clean split, constant sizes; Hudson F_ST = t/(t + 2 Ne)",
        "simulator": "cluster/fam_coalescent.py (family_split)",
        "status": "SIMULATED -- varies daughter sizes, which no member takes",
        "found_by": "sweep",
        "members": ["coalFst", "fstFromGenerations", "fstFromTau",
                    "coalescentTau", "hudsonFstFromCoalescenceTimes",
                    "pairwiseFstFromBranchTaus", "pairwiseFstFromBranches"],
    },
    {
        "name": "mutation_drift_balance",
        "model": "infinite alleles; H* = theta/(1+theta), theta = 4 Ne mu",
        "simulator": "heavy/h0_heterozygosity_cluster.py (control 2)",
        "status": "SIMULATED -- equilibrium level confirmed at four theta",
        "found_by": "manual",
        "members": ["hetEquilibrium", "expectedHeterozygosity",
                    "hetMutationDriftRecurrence", "hetTrajectory",
                    "hetStepWithMutation", "hetMutationFloor",
                    "scaledMutationRate", "hetDecayFactor",
                    "fstMutationDriftEquilibrium",
                    "fstMutationDriftTransient",
                    "fstMutationDriftTransientDiscrete"],
    },
    {
        "name": "ld_decay_recurrence",
        "model": "two loci, recombination c, drift; E[D] retention "
                 "(1-c)(1-1/2Ne) and E[r^2] at equilibrium",
        "simulator": None,
        "status": "NO SIMULATOR. Analytic only. This family contains the "
                  "2110x ldHalfLife error and the 37000x ldRetainedFraction "
                  "inconsistency, so it is the highest-value gap.",
        "found_by": "manual",
        "members": ["ldRetentionPerGen", "ldAfterGenerations", "ldRecurrence",
                    "ldDecayRatePerGen", "ldHalfLife", "driftLDStep",
                    "driftLDRetention", "driftLDEquilibrium",
                    "driftLDTrajectory", "excessLDAfterBottleneck",
                    "bottleneckExcessLD", "driftLDCreationRate", "tagR2"],
    },
    {
        "name": "stepping_stone",
        "model": "1D lattice, nearest-neighbour migration; decay length and "
                 "F_ST versus distance",
        "simulator": None,
        "status": "NO SIMULATOR. Contains the 500x "
                  "steppingStoneCharacteristicLength functional-form error and "
                  "an 878% contradiction between two corpus formulas.",
        "found_by": "manual",
        "members": ["steppingStoneCharacteristicLength",
                    "continuousSteppingStoneFst", "demoSteppingStoneFst",
                    "steppingStoneCoalescenceTime", "steppingStoneFst"],
    },
    {
        "name": "admixture",
        "model": "pulse admixture of two sources; F_ST and LD in the admixed "
                 "population",
        "simulator": None,
        "status": "NO SIMULATOR. admixedFst is -44% against an exact "
                  "frequency-pair reference but has never been simulated over "
                  "a frequency spectrum.",
        "found_by": "manual",
        "members": ["admixedFst", "admixedAlleleFreq", "admixtureLD",
                    "admixtureLDDecay", "admixtureLDBoost",
                    "admixtureLDTwoLocus"],
    },
    {
        "name": "site_frequency_spectrum",
        "model": "standard neutral SFS, E[xi_i] = theta/i",
        "simulator": None,
        "status": "NO SIMULATOR AND NO DEFINITIONS. singletonProportion was "
                  "removed from the corpus. The reference exists in refs.py "
                  "and currently checks nothing -- an empty family, recorded "
                  "so it is not mistaken for a covered one.",
        "found_by": "manual",
        "members": [],
    },
    {
        "name": "selection_regimes",
        "model": "selection-migration balance, stabilizing and directional "
                 "selection",
        "simulator": None,
        "status": "NO SIMULATOR. Needs forward simulation with selection; "
                  "SLiM is absent and a Wright-Fisher implementation would be "
                  "the honest substitute.",
        "found_by": "manual",
        "members": ["selectionMigrationEquilibrium",
                    "selectionMigrationEquilibriumMigrationFirst",
                    "continentIslandStepSelectionFirst",
                    "continentIslandStepMigrationFirst",
                    "selectedDriftFactor"],
    },
    {
        "name": "ascertainment",
        "model": "discovery thresholds, winner's curse, tag/causal MAF "
                 "mismatch",
        "simulator": None,
        "status": "NO SIMULATOR in this tier. Several members were falsified "
                  "analytically by earlier work; none has a generative check.",
        "found_by": "manual",
        "members": ["discoveryNCP", "truncationBias", "winnersCurseInflation",
                    "approxPower", "tagGenotypeVariance"],
    },
]


def sweep_members():
    """Family membership from sweep_inlined_results.json, not from a hand list.

    The hardcoded lists below went stale INSIDE ONE SESSION: the corpus went
    from 1003 definitions to 994 while this tier was running, and
    islandModelFst, equilibriumFst and hetEquilibrium were collapsed onto other
    definitions by another agent. A hand-maintained membership list silently
    stops describing the corpus -- which is the exact failure this tier flagged
    in someone else's code earlier today, so it is fixed here rather than
    excused.

    Sweep-derived families take their members from the sweep output when it is
    present. Only AFFINE members count: a co-function shares the form's level
    sets without computing it.
    """
    path = os.path.join(HERE, "sweep_inlined_results.json")
    if not os.path.exists(path):
        return {}
    fh = open(path)
    data = json.load(fh)
    fh.close()
    out = {}
    for ref_name, blk in (data.get("references") or {}).items():
        names = []
        for m in blk.get("members", []):
            rel = m.get("relation") or {}
            if rel.get("kind") == "AFFINE":
                names.append(m["definition"].split(".")[-1])
        out[ref_name] = sorted(names)
    return out


SWEEP_TO_FAMILY = {
    "drift_retention": "drift_retention",
    "island_fst": "island_migration_fst",
    "split_fst": "split_fst",
    "sved_ld": "ld_decay_recurrence",
}


def load_defs():
    fh = open(os.path.join(EXTRACT, "defs.json"))
    raw = json.load(fh)
    fh.close()
    entries = raw["definitions"] if isinstance(raw, dict) else raw
    return dict((e["name"], e) for e in entries)


def main():
    table = load_defs()
    live = sweep_members()
    for fam in FAMILIES:
        for sweep_name, fam_name in SWEEP_TO_FAMILY.items():
            if fam["name"] != fam_name or sweep_name not in live:
                continue
            declared = set(fam["members"])
            found = set(live[sweep_name])
            fam["members"] = sorted(declared | found)
            fam["found_by"] = "sweep (regenerated)"
            fam["sweep_only"] = sorted(found - declared)
            fam["declared_only"] = sorted(declared - found)
    by_short = {}
    for fq in table:
        by_short.setdefault(fq.split(".")[-1], []).append(table[fq])

    in_slice = set()
    for fq in table:
        if table[fq].get("file") in SLICE_FILES:
            in_slice.add(fq.split(".")[-1])

    claimed = set()
    rows = []
    for fam in FAMILIES:
        present, missing = [], []
        for m in fam["members"]:
            if m in by_short:
                present.append(m)
                claimed.add(m)
            else:
                missing.append(m)
        slice_members = [m for m in present if m in in_slice]
        rows.append({
            "family": fam["name"],
            "model": fam["model"],
            "simulator": fam["simulator"],
            "status": fam["status"],
            "found_by": fam["found_by"],
            "n_members_declared": len(fam["members"]),
            "n_members_present": len(present),
            "n_members_in_slice": len(slice_members),
            "members_in_slice": sorted(slice_members),
            "members_not_found_in_corpus": missing,
            "sweep_only": fam.get("sweep_only", []),
            "declared_only_not_confirmed_by_sweep": fam.get("declared_only", []),
        })

    n_fam = len(rows)
    n_sim = len([r for r in rows if r["simulator"]])
    stmts_with = sum(r["n_members_in_slice"] for r in rows if r["simulator"])
    stmts_without = sum(r["n_members_in_slice"] for r in rows if not r["simulator"])
    unassigned = sorted(in_slice - claimed)

    print("MODEL FAMILY INVENTORY")
    print("  families                       %d" % n_fam)
    print("  families WITH a simulator      %d" % n_sim)
    print("  families with NO simulator     %d   <- drive to zero first"
          % (n_fam - n_sim))
    print("")
    print("  in-slice statements in a simulated family      %d" % stmts_with)
    print("  in-slice statements in an unsimulated family   %d" % stmts_without)
    print("  in-slice statements in NO family at all        %d" % len(unassigned))
    print("")
    print("%-26s %-5s %-6s %s" % ("family", "slice", "sim?", "status"))
    for r in sorted(rows, key=lambda x: (x["simulator"] is not None,
                                         -x["n_members_in_slice"])):
        print("%-26s %-5d %-6s %s"
              % (r["family"], r["n_members_in_slice"],
                 "yes" if r["simulator"] else "NO",
                 r["status"].split(".")[0][:70]))
        if r["members_not_found_in_corpus"]:
            print("      declared but ABSENT FROM CORPUS (removed or renamed "
                  "since the list was written): %s"
                  % r["members_not_found_in_corpus"])
        if r.get("sweep_only"):
            print("      found by sweep, not in the hand list: %s"
                  % r["sweep_only"])
    print("")
    print("  %d in-slice statements belong to no family yet:" % len(unassigned))
    for u in unassigned[:40]:
        print("      " + u)
    if len(unassigned) > 40:
        print("      ... and %d more" % (len(unassigned) - 40))

    out = {"families": rows,
           "counts": {"families": n_fam, "families_with_simulator": n_sim,
                      "families_without_simulator": n_fam - n_sim,
                      "slice_statements_simulated_family": stmts_with,
                      "slice_statements_unsimulated_family": stmts_without,
                      "slice_statements_no_family": len(unassigned)},
           "unassigned_in_slice": unassigned}
    fh = open(os.path.join(HERE, "families_results.json"), "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("")
    print("-> families_results.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
