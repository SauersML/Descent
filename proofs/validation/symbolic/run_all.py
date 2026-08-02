"""Run every symbolic check and emit one findings table keyed by fully-qualified
name, for coverage accounting to consume.

    python3 run_all.py

Runs under whatever interpreter invokes it -- the child steps inherit
`sys.executable`, so there is no hard-coded virtualenv path and the same entry
point works locally and on the cluster.  Requires sympy; see cluster_run.sh for
the module that provides it.

Outputs, all in this directory:
    decls.json        parsed declaration table
    results_check1..6 per-check detail
    coverage.json     mutation-tested coverage, keyed by definition FQN
    findings.json     every disagreement and gap, keyed by FQN
"""

from __future__ import annotations

import json
import subprocess
import sys
from collections import Counter
from pathlib import Path
from paths import ARTIFACTS as ART

HERE = Path(__file__).parent
PY = sys.executable

STEPS = ["leanparse.py", "check1_fixedpoints.py", "check1b_joint.py", "check3_duplicates.py",
         "check2_derivations.py", "check4_limits.py", "check5_recurrences.py", "mutation.py",
         "check6_certificates.py", "homonyms.py", "check7_widened.py"]

# Modules whose claims are being revised upstream right now.  A finding here is
# not actionable and must not be reported as a defect: the author is already
# weakening the statement.  Recorded rather than filtered, so the finding still
# appears with its provenance instead of vanishing.
KNOWN_IN_FLUX = {
    "Calibrator.EpistaticChaos": (
        "coupling-coefficient variance correction 2b^2/(1-b^2) retracted by its "
        "author's own audit (tilt-bookkeeping error); the definition of b, its "
        "vanishing iff symmetry, and E[x|x|] = (1-2q)^2 all stand"),
    "Calibrator.CondensationUnification": (
        "same retracted coupling correction; statements being weakened upstream"),
}

# statuses that constitute a finding rather than a pass
FINDING = {
    "FIXED_POINT_FAILS": "error",
    "IRRELEVANT_ROOT": "error",
    "DERIVATION_DISAGREES": "error",
    "VACUOUS_DERIVATION": "vacuous",
    "VACUOUS_DERIVATION_NO_DEFS": "vacuous",
    "APPROXIMATION_UNSUPPORTED": "error",
    "JOINT_FIXED_POINT_FAILS": "error",
    "JOINT_SOLVE_FAILED": "gap",
    "HOLDS_TO_FIRST_ORDER": "linearisation",
    "no_fixed_point_theorem": "gap",
    "ONLY_REST_POINT_IS_ZERO": "degenerate_limit",
    "VACUOUS_FOR": "vacuous_certificate",
    "UNGUARDED_BINDERS_DO_NOT_CORRESPOND": "gap",
    "LINEARISATION_WITHOUT_STATED_REGIME": "unstated_regime",
    "UNGUARDED_NO_MAP": "gap",
    "UNGUARDED_ARITY_MISMATCH": "gap",
}


def main():
    for s in STEPS:
        print(f"--- {s}")
        r = subprocess.run([PY, str(HERE / s)], cwd=HERE)
        if r.returncode != 0:
            sys.exit(f"{s} failed")

    findings: dict[str, list] = {}

    def add(fqn, rec):
        findings.setdefault(fqn, []).append(rec)

    for r in json.load(open(ART / "results_check1.json")):
        if r["status"] in FINDING:
            add(r["fqn"], {"check": "check1_fixed_point", "severity": FINDING[r["status"]],
                           "status": r["status"], "file": r["file"], "line": r["line"],
                           "detail": r["detail"]})
    for r in json.load(open(ART / "results_check1b.json")):
        if r["status"] in FINDING:
            add(r["module"] + ".<joint>", {"check": "check1b_joint_system",
                                           "severity": FINDING[r["status"]],
                                           "status": r["status"],
                                           "unknowns": r["unknowns"],
                                           "detail": r["detail"]})
    for r in json.load(open(ART / "results_check2.json")):
        if r["status"] in FINDING or r["detail"].get("MENTION_GAP"):
            add(r["fqn"], {"check": "check2_derivation",
                           "severity": FINDING.get(r["status"], "naming_gap"),
                           "status": r["status"], "file": r["file"], "line": r["line"],
                           "statement": r["statement"], "detail": r["detail"]})
    c3 = json.load(open(ART / "results_check3.json"))
    for g in c3["equal_groups"]:
        if not g["cross_file"]:
            continue
        for m in g["members"]:
            add(m["fqn"], {"check": "check3_duplicate_body", "severity": "duplicate",
                           "status": "SYMBOLICALLY_IDENTICAL_ACROSS_FILES",
                           "file": m["file"], "line": m["line"],
                           "expression": g["expression"],
                           "other_members": [x["fqn"] for x in g["members"]
                                             if x["fqn"] != m["fqn"]]})
    for d in c3["disagreements"]:
        for side, other in (("a", "b"), ("b", "a")):
            add(d[side]["fqn"], {"check": "check3_name_mate_disagreement",
                                 "severity": "disagreement",
                                 "status": "NAME_MATE_BODIES_DIFFER",
                                 "file": d[side]["file"], "line": d[side]["line"],
                                 "this_expr": d[side]["expr"],
                                 "other": d[other]["fqn"],
                                 "other_expr": d[other]["expr"]})
    for h in c3["homonyms"]:
        add(h["name"], {"check": "check3_homonym", "severity": "error",
                        "status": "ONE_NAME_TWO_FUNCTIONS",
                        "distinct_bodies": h["distinct_bodies"]})
    for r in json.load(open(ART / "results_check4.json")):
        if r["status"] in FINDING:
            fqn = r.get("fqn") or r["a"]["fqn"]
            add(fqn, {"check": r["check"], "severity": FINDING[r["status"]],
                      "status": r["status"], "detail": r})

    c5 = json.load(open(ART / "results_check5.json"))
    for r in c5["recurrences"]:
        if r["status"] in FINDING:
            add(r["fqn"], {"check": "check5_recurrence_limit",
                           "severity": FINDING[r["status"]], "status": r["status"],
                           "file": r["file"], "line": r["line"], "detail": r["detail"]})

    c6 = json.load(open(ART / "results_check6.json"))
    for p_ in c6["pairs"]:
        if p_["status"] == "VACUOUS_FOR":
            add(p_["definition"], {"check": "check6_certificate_power",
                                   "severity": "vacuous_certificate",
                                   "status": "CERTIFICATE_DOES_NOT_CONSTRAIN",
                                   "theorem": p_["theorem"],
                                   "file": p_["definition_file"],
                                   "line": p_["definition_line"],
                                   "mutations_survived": p_["mutations_survived"]})
    hom = json.load(open(ART / "results_homonyms.json"))
    for fq, sites in hom["colliding_public"].items():
        add(fq, {"check": "homonyms", "severity": "error",
                 "status": "NAME_DECLARED_MORE_THAN_ONCE",
                 "sites": sites})

    cov = json.load(open(ART / "coverage.json"))
    for fqn, e in cov.items():
        for check, info in e["checks"].items():
            if not info["covered"]:
                add(fqn, {"check": check, "severity": "vacuous_coverage",
                          "status": "CHECK_CANNOT_FAIL_FOR_THIS_DEFINITION",
                          "detail": info})

    for fqn, recs in findings.items():
        for mod, why in KNOWN_IN_FLUX.items():
            if fqn.startswith(mod + "."):
                for r in recs:
                    r["in_flux"] = why
                    r["actionable"] = False

    (ART / "findings.json").write_text(json.dumps(findings, indent=1, ensure_ascii=False))
    n_flux = sum(1 for v in findings.values() for f in v if f.get("in_flux"))
    if n_flux:
        print(f"  ({n_flux} findings suppressed as not actionable: upstream revision "
              f"in {', '.join(sorted(KNOWN_IN_FLUX))})")
    sev = Counter(f["severity"] for v in findings.values() for f in v
                  if not f.get("in_flux"))
    print()
    print(f"findings.json: {len(findings)} names with at least one finding")
    for k, v in sev.most_common():
        print(f"  {k:22s} {v}")


if __name__ == "__main__":
    main()
