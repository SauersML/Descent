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

# Values for arguments that are NOT part of the reference. Each set assigns
# DISTINCT values to distinct arguments, which matters more than it looks:
# giving every spare argument the same number manufactures cancellations.
# `demoSteppingStoneFst d Ne m sigma_sq = d/(d + 4 Ne m sigma_sq)` collapses to
# exactly 1/(1 + 4 Ne m) whenever d == sigma_sq, so a single shared filler
# reported it as computing the island form when it only does so on that
# diagonal. Distinct values per argument, and three independent assignments,
# make an accidental identity have to hold three times over.
FILLER_SETS = [
    [0.3, 0.7, 1.5, 0.45, 1.1, 0.62],
    [1.2, 0.25, 0.9, 1.7, 0.55, 1.35],
    [0.8, 1.45, 0.35, 1.05, 0.5, 0.95],
]


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


SCALAR_TYPES = ("R", "N", "ℝ", "ℕ")


def load_table():
    """Return {fully_qualified_name: entry}, whatever shape defs.json is in.

    The first version of this assumed defs.json was already keyed by name. It
    is not: the top level is a dict with keys collisions / theorems /
    definitions / structures / parse_failures, and `definitions` is a LIST.
    Iterating the top level therefore yielded the five section names and handed
    a list to code expecting a dict.

    Rather than swap one assumption for another, this accepts every plausible
    shape and REPORTS which one it found, so the next schema change is a
    one-line diagnosis instead of an AttributeError inside a loop.
    """
    fh = open(os.path.join(EXTRACT, "defs.json"))
    raw = json.load(fh)
    fh.close()

    shape = None
    entries = None
    if isinstance(raw, dict) and "definitions" in raw:
        entries = raw["definitions"]
        shape = "dict with 'definitions' section"
    elif isinstance(raw, list):
        entries = raw
        shape = "bare list"
    elif isinstance(raw, dict):
        vals = list(raw.values())
        if vals and isinstance(vals[0], dict) and "body" in vals[0]:
            print("  defs.json shape: dict already keyed by name")
            return raw
        raise SystemExit(
            "defs.json is a dict whose values are %s, not definition entries. "
            "Top-level keys: %s" % (type(vals[0]).__name__ if vals else "empty",
                                    sorted(raw.keys())))
    else:
        raise SystemExit("defs.json is a %s, which this script cannot read"
                         % type(raw).__name__)

    if isinstance(entries, dict):
        print("  defs.json shape: %s (already keyed)" % shape)
        return entries
    table = {}
    for e in entries:
        if not isinstance(e, dict):
            raise SystemExit(
                "defs.json '%s' contains a %s where a definition entry was "
                "expected" % (shape, type(e).__name__))
        key = e.get("name") or e.get("decl_name") or e.get("short")
        if key:
            table[key] = e
    print("  defs.json shape: %s -> %d definitions" % (shape, len(table)))
    return table


def arg_names(entry):
    """Explicit scalar argument names IN ORDER, or None if not scalar-only.

    `args` is a list of BINDER GROUPS, not of arguments: `(x y z : R)` is ONE
    group carrying three names. Taking one name per group would under-count
    arity and then call every such definition with the wrong number of
    arguments -- the same class of mistake as dropping a binder.
    """
    args = entry.get("args")
    if not isinstance(args, list):
        return None
    names = []
    for grp in args:
        if not isinstance(grp, dict):
            return None
        if grp.get("implicit"):
            continue
        if grp.get("type") not in SCALAR_TYPES:
            return None                      # structure/vector/function typed
        group_names = grp.get("names") or []
        if not isinstance(group_names, list):
            return None
        for nm in group_names:
            names.append(nm)
    return names or None


def resolve_callable(entry):
    """The generated callable for an entry, or None.

    Ambiguous short names are emitted fully qualified with dots replaced by
    underscores, so both spellings are tried.
    """
    fq = entry.get("name") or ""
    cands = [entry.get("short"), fq.replace(".", "_"), fq.split(".")[-1]]
    for cand in cands:
        if not cand:
            continue
        fn = getattr(lean_defs, cand, None)
        if fn is not None:
            return fn
    return None


def sweep(ref, table):
    members = []
    excluded = 0
    for fq in sorted(table.keys()):
        entry = table[fq]
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
        fn = resolve_callable(entry)
        if fn is None:
            continue

        others = [n for n in names if n not in (a1, a2)]
        all_invariant = True
        moved_across = False
        evaluated = 0
        sample = []

        for fset in FILLER_SETS:
            level_values = []
            for level in ref["levels"]:
                vals = []
                for p1 in ref["p1_values"]:
                    try:
                        p2 = ref["solve"](p1, level)
                    except Exception:
                        continue
                    asg = {}
                    for j, n in enumerate(others):
                        asg[n] = fset[j % len(fset)]
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
                "relation": classify_relation(sample),
            })
        elif moved_across:
            excluded += 1
    return members, excluded


def classify_relation(sample):
    """How a member relates to the reference: is it the form, or a co-function?

    Level-set invariance says a definition depends on its two parameters ONLY
    through the same one-dimensional statistic as the reference. That is
    necessary for computing the reference, not sufficient. The distinction
    matters and the first version of this sweep blurred it:

    for 1/(1 + 4 Ne m), the level sets are just the level sets of the PRODUCT
    Ne*m, so `scaledMigrationRate = 4*Ne*m` is invariant along them while
    computing something else entirely. For (1 - 1/(2 Ne))^t the statistic is
    t*log(1 - 1/(2Ne)), which is far more specific and has no such degeneracy.

    So members are split by whether the value is an AFFINE function of the
    reference -- fitted on two levels and checked on the rest:

      AFFINE       value = a + b * reference. Computes the reference up to
                   scale and offset; b = 1, a = 0 means it IS the reference.
      CO-FUNCTION  same level sets, not affine in the reference. Shares the
                   underlying statistic and may mean something unrelated.
    """
    pts = [(l, v) for l, v in sample if l is not None and v is not None]
    if len(pts) < 3:
        return {"kind": "UNDETERMINED", "reason": "fewer than 3 levels"}
    (x0, y0), (x1, y1) = pts[0], pts[1]
    if abs(x1 - x0) < 1e-15:
        return {"kind": "UNDETERMINED", "reason": "degenerate levels"}
    b = (y1 - y0) / (x1 - x0)
    a = y0 - b * x0
    worst = 0.0
    for x, y in pts[2:]:
        pred = a + b * x
        worst = max(worst, abs(pred - y) / max(1.0, abs(y)))
    if worst <= 1e-9:
        identity = abs(b - 1.0) <= 1e-9 and abs(a) <= 1e-9
        return {"kind": "AFFINE", "slope": b, "intercept": a,
                "is_the_reference": bool(identity), "max_rel_resid": worst}
    return {"kind": "CO-FUNCTION", "max_rel_resid_if_affine": worst}


def schema_selfcheck(table):
    """Fail before sweeping if the table is not what the sweep assumes.

    A schema mismatch that surfaces mid-loop produces a stack trace from deep
    inside the sweep; one that surfaces here names the problem. More important,
    a mismatch that does NOT crash -- an `args` shape that silently yields zero
    scalar definitions -- would make every reference return no members, and
    "no members for three suspect forms" reads as good news. This check exists
    so that outcome cannot be reached quietly.
    """
    problems = []
    if len(table) < 500:
        problems.append("only %d definitions loaded; expected ~1000" % len(table))

    n_scalar = 0
    for fq in table:
        if arg_names(table[fq]):
            n_scalar += 1
    print("  %d definitions have scalar-only explicit arguments" % n_scalar)
    if n_scalar < 100:
        problems.append(
            "only %d scalar-argument definitions found; `args` is probably not "
            "being parsed as binder groups, and every reference would return "
            "no members" % n_scalar)

    # coalFst is the anchor: two real arguments named t and Ne, and it
    # evaluates to t/(t+2Ne).
    anchor = None
    for fq in table:
        if fq.split(".")[-1] == "coalFst":
            anchor = table[fq]
            break
    if anchor is None:
        problems.append("coalFst not present in the table")
    else:
        names = arg_names(anchor)
        if names != ["t", "Ne"]:
            problems.append("coalFst args parsed as %r, expected ['t','Ne']" % names)
        fn = resolve_callable(anchor)
        if fn is None:
            problems.append("no callable resolved for coalFst")
        else:
            try:
                got = fn(100.0, 1000.0)
                if abs(got - 100.0 / 2100.0) > 1e-12:
                    problems.append("coalFst(100,1000) = %r, expected 1/21" % got)
            except Exception as exc:
                problems.append("coalFst raised: %s" % exc)

    if problems:
        print("")
        print("SCHEMA SELF-CHECK FAILED -- not sweeping:")
        for p in problems:
            print("  * " + p)
        print("")
        print("Send this output back. Do NOT read an empty member list as a")
        print("clean corpus; it would mean the table was not parsed.")
        return False
    print("  schema self-check passed (coalFst resolves and evaluates)")
    return True


def main():
    print("LOADING")
    table = load_table()
    if not schema_selfcheck(table):
        return 2
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
        n_aff = len([m for m in members if m["relation"]["kind"] == "AFFINE"])
        print("  %d share this form's level sets (%d affine in it, %d "
              "co-functions); %d compatible but excluded"
              % (len(members), n_aff, len(members) - n_aff, excluded))
        for m in members:
            rel = m["relation"]
            tag = rel["kind"]
            if tag == "AFFINE":
                tag += " (slope %.6g, intercept %.6g%s)" % (
                    rel["slope"], rel["intercept"],
                    ", IS THE REFERENCE" if rel["is_the_reference"] else "")
            print("    %-46s %-14s %s" % (m["definition"].split(".")[-1], tag,
                                          m["source"]))
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
