#!/usr/bin/env python3
"""Level-set invariance sweep over four suspect closed forms.

Python 3.6.8, numpy optional (not actually needed), no other dependencies.
Reads defs.json for signatures and lean_defs for callables. Does NOT import
api, so it runs even if api.py is not 3.6-compatible.

THE TECHNIQUE
    Let R(p) be a suspect closed form. Pick parameter points with R equal but
    the individual parameters different. Anything depending on p only through R
    must take the same value at every such point. So: evaluate a definition
    along a level set of R; if it does not move, it is a function of R alone.

    This finds definitions by what they COMPUTE, not by what they are named or
    what they import. It is the only route to definitions that inline a
    falsified closed form under a name mentioning neither the quantity nor the
    regime -- which is the situation for the drift-retention cluster, where no
    definition consumes hetRecurrence by name and `neutralDriftFactor` in
    PhenomeWidePortability.lean was found by no other means.

THE FOUR FORMS
    drift_retention  (1 - 1/(2 Ne))^t     closed population, NO mutation.
                     Measured against simulation: true retention at
                     mutation-drift equilibrium is 1.0, not the 0.135 this
                     predicts at t = 2*(2Ne). MODEL error.
    sved             1/(1 + 4 Ne c)       gametic identity by descent. Differs
                     from Ohta-Kimura E[r^2] by +120% as rho -> 0.
    island           1/(1 + 4 Ne m)       infinite-island limit. +74.5% against
                     the finite-deme form at d = 2.
    split_fst        t/(t + 2 Ne)         Hudson F_ST after a clean split. This
                     one is CORRECT where it applies; it is swept to find which
                     definitions share it, and to act as a positive control --
                     a sweep that finds nothing for a form known to have several
                     names in the corpus is broken.

TWO GUARDS, without which the verdicts are worthless
    NON-CONSTANCY. A definition ignoring its arguments is trivially invariant
    along every level set. It must VARY across level sets before invariance
    within one counts, or every constant joins every cluster.
    MULTIPLE LEVEL SETS. Invariance is required on four levels, not one. A
    single level set can be matched by coincidence, especially where a
    definition saturates.

WHAT WOULD MAKE THIS WRONG RATHER THAN THE DEFINITIONS
    If `split_fst` returns no members, the sweep is broken: coalFst,
    fstFromGenerations and fstFromTau are all known to compute it. That is the
    positive control and it is checked automatically.
"""

import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.normpath(os.path.join(HERE, "..", "..", "extract"))
if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

import lean_defs  # noqa: E402

RTOL = 1e-9
FILLERS = [0.3, 0.7, 1.5]


# ---------------------------------------------------------------------------
# Suspect forms. `solve` returns the value of the second parameter that places
# the point on the target level set, given the first.
# ---------------------------------------------------------------------------
def _solve_retention(ne, level):
    return math.log(level) / math.log(1.0 - 1.0 / (2.0 * ne))


def _solve_sved(ne, level):
    # 1/(1+4*ne*c) = level  ->  c = (1/level - 1)/(4 ne)
    return (1.0 / level - 1.0) / (4.0 * ne)


def _solve_split(ne, level):
    # t/(t+2 ne) = level  ->  t = 2 ne level/(1-level)
    return 2.0 * ne * level / (1.0 - level)


REFERENCES = [
    {
        "name": "drift_retention",
        "form": "(1 - 1/(2 Ne))^t",
        "verdict": "MODEL error: measured retention at mutation-drift "
                   "equilibrium is 1.0, not 0.135",
        "p1": "Ne", "p2": "t",
        "p1_values": [50.0, 200.0, 1000.0, 5000.0],
        "levels": [0.9, 0.6, 0.3, 0.1],
        "solve": _solve_retention,
        "aliases_p1": ["Ne", "N", "N_e", "Ne_b", "Ne_stable", "N_b", "N_r",
                       "Ne_source", "Ne_target", "NeA", "NeB", "Ne_new"],
        "aliases_p2": ["t", "t_b", "t_r", "gens", "generations", "horizon",
                       "t_div", "t_since", "generations_since"],
    },
    {
        "name": "sved_ld",
        "form": "1/(1 + 4 Ne c)",
        "verdict": "MODEL error if read as E[r^2]: Ohta-Kimura gives 0.4545 "
                   "where this gives 1.0 as rho -> 0",
        "p1": "Ne", "p2": "c",
        "p1_values": [50.0, 200.0, 1000.0, 5000.0],
        "levels": [0.8, 0.5, 0.2, 0.05],
        "solve": _solve_sved,
        "aliases_p1": ["Ne", "N", "N_e", "Ne_b", "Ne_stable", "N_b", "N_r"],
        "aliases_p2": ["c", "r", "rec", "recomb", "recombination"],
    },
    {
        "name": "island_fst",
        "form": "1/(1 + 4 Ne m)",
        "verdict": "MODEL error: infinite-island limit; +74.5% against the "
                   "finite-deme form at d = 2",
        "p1": "Ne", "p2": "m",
        "p1_values": [50.0, 200.0, 1000.0, 5000.0],
        "levels": [0.8, 0.5, 0.2, 0.05],
        "solve": _solve_sved,
        "aliases_p1": ["Ne", "N", "N_e", "Ne_source", "Ne_target"],
        "aliases_p2": ["m", "mig", "m_into", "m_rate", "migration"],
    },
    {
        "name": "split_fst",
        "form": "t/(t + 2 Ne)",
        "verdict": "CORRECT where it applies. Swept as a POSITIVE CONTROL: "
                   "coalFst, fstFromGenerations and fstFromTau all compute it, "
                   "so an empty result means the sweep is broken.",
        "p1": "Ne", "p2": "t",
        "p1_values": [50.0, 200.0, 1000.0, 5000.0],
        "levels": [0.8, 0.5, 0.2, 0.05],
        "solve": _solve_split,
        "aliases_p1": ["Ne", "N", "N_e"],
        "aliases_p2": ["t", "t_div", "gens", "generations", "horizon"],
        "positive_control": True,
    },
]


def load_table():
    fh = open(os.path.join(EXTRACT, "defs.json"))
    tbl = json.load(fh)
    fh.close()
    return tbl


def arg_names(entry):
    """Ordered explicit scalar argument names, or None if not scalar-only."""
    names = []
    for grp in entry.get("args", []):
        if grp.get("implicit"):
            continue
        if grp.get("type") != "R" and grp.get("type") not in ("ℝ", "ℕ"):
            return None
        for nm in grp.get("names", []):
            names.append(nm)
    return names or None


def resolve_callable(fq, short):
    for cand in (short, fq.replace(".", "_")):
        fn = getattr(lean_defs, cand, None)
        if fn is not None:
            return fn
    return None


def sweep(ref, table):
    members = []
    excluded = 0
    for fq in sorted(table.keys()):
        entry = table[fq]
        short = fq.split(".")[-1]
        names = arg_names(entry)
        if not names:
            continue
        a1 = None
        a2 = None
        for nm in names:
            if a1 is None and nm in ref["aliases_p1"]:
                a1 = nm
            elif a2 is None and nm in ref["aliases_p2"]:
                a2 = nm
        if a1 is None or a2 is None or a1 == a2:
            continue
        fn = resolve_callable(fq, short)
        if fn is None:
            continue

        others = [n for n in names if n not in (a1, a2)]
        all_invariant = True
        moved_across = False
        evaluated = 0
        sample = []

        for filler in FILLERS:
            level_values = []
            for level in ref["levels"]:
                vals = []
                for p1 in ref["p1_values"]:
                    try:
                        p2 = ref["solve"](p1, level)
                    except Exception:
                        continue
                    asg = {}
                    for n in others:
                        asg[n] = filler
                    asg[a1] = p1
                    asg[a2] = p2
                    try:
                        v = fn(*[asg[n] for n in names])
                    except Exception:
                        continue
                    if not isinstance(v, float) and not isinstance(v, int):
                        continue
                    if v != v or v in (float("inf"), float("-inf")):
                        continue
                    vals.append(float(v))
                if len(vals) < 2:
                    continue
                evaluated += len(vals)
                scale = max(1.0, max([abs(x) for x in vals]))
                if (max(vals) - min(vals)) > RTOL * scale:
                    all_invariant = False
                level_values.append(vals[0])
            if len(level_values) >= 2:
                sc = max(1.0, max([abs(x) for x in level_values]))
                if (max(level_values) - min(level_values)) > RTOL * sc:
                    moved_across = True
                if not sample:
                    sample = list(zip(ref["levels"], level_values))

        if evaluated < 8:
            continue
        if all_invariant and moved_across:
            members.append({
                "definition": fq,
                "source": "%s:%s" % (entry.get("file"), entry.get("line")),
                "args": names,
                "mapped": {ref["p1"]: a1, ref["p2"]: a2},
                "empirical_status": entry.get("empirical_status"),
                "level_to_value": [[l, v] for l, v in sample],
            })
        elif moved_across:
            excluded += 1
    return members, excluded


def main():
    table = load_table()
    report = {"n_definitions_in_table": len(table), "references": {}}
    control_ok = True

    for ref in REFERENCES:
        members, excluded = sweep(ref, table)
        report["references"][ref["name"]] = {
            "form": ref["form"],
            "verdict_if_member": ref["verdict"],
            "n_members": len(members),
            "members": members,
            "n_arg_compatible_but_excluded": excluded,
        }
        print("")
        print("REFERENCE %s   %s" % (ref["name"], ref["form"]))
        print("  %d definitions are functions of this form ALONE "
              "(%d compatible but excluded)" % (len(members), excluded))
        for m in members:
            print("    %-50s %s" % (m["definition"], m["source"]))
            print("        args=%s  status=%s" % (m["args"], m["empirical_status"]))
        if ref.get("positive_control"):
            control_ok = len(members) > 0
            print("  POSITIVE CONTROL: %s" % ("PASS" if control_ok else
                                              "FAIL -- sweep is broken"))

    # cross-reference: a definition matching two forms is worth a look
    seen = {}
    for name, blk in report["references"].items():
        for m in blk["members"]:
            seen.setdefault(m["definition"], []).append(name)
    multi = dict((k, v) for k, v in seen.items() if len(v) > 1)
    report["definitions_matching_multiple_forms"] = multi
    if multi:
        print("")
        print("MATCHING MORE THAN ONE FORM (expected only where forms coincide):")
        for k in sorted(multi):
            print("    %-50s %s" % (k, multi[k]))

    report["positive_control_passed"] = bool(control_ok)
    fh = open(os.path.join(HERE, "sweep_inlined_results.json"), "w")
    json.dump(report, fh, indent=1)
    fh.close()
    print("")
    print("-> sweep_inlined_results.json")
    if not control_ok:
        print("POSITIVE CONTROL FAILED. Do not read the other results: a sweep "
              "that cannot find t/(t+2Ne), which coalFst computes by "
              "definition, is not measuring what it claims.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
