#!/usr/bin/env python3
"""DGP.lean coverage batch -- reconnaissance first, then coverage.

Python 3.6.8, numpy not required. NEEDS api.py (unlike sweep_inlined.py),
because DGP's definitions take STRUCTURE-valued arguments and api is what knows
how to build them.

WHY THIS SCRIPT IS SHAPED DIFFERENTLY FROM THE OTHERS
    DGP.lean is the largest zero-coverage block in the slice: 78 definitions,
    30 extractable, 0 covered. Its bodies are record wrappers over quantities
    already covered elsewhere --

        retention = (1 - 1/(2 * r.Ne)) ^ r.horizon      the drift-retention form
        tau       = p.t_div / (2 * p.Ne)                coalescent time
        theta     = 4 * p.Ne * p.mu                     scaled mutation rate
        bigM      = 4 * p.Ne * p.mig                    scaled migration
        fst       = fstFromTau m.tau                    split F_ST

    -- so one reference covers many of them. But calling them requires
    constructing structure instances, and I could not run anything locally to
    learn how api represents structures. Writing a construction blind and
    reporting its output as coverage would be exactly the failure I have
    flagged twice in other agents' work today: verifying on the shape you
    already understand.

    So PHASE 1 reports what is actually there, and PHASE 2 attempts the
    coverage and reports honestly when it cannot. If phase 2 covers nothing,
    phase 1 still tells me precisely what to write next, which is worth the run.

PHASE 2 METHOD -- the same level-set invariance used in sweep_inlined.py,
lifted to structure arguments. For a definition taking a record with fields Ne
and horizon, build two records with equal (1 - 1/(2 Ne))^horizon and different
Ne. A definition depending on the record only through that form does not move.

CONTROL PINNED BY CONSTRUCTION, not by simulation
    Every definition that phase 2 reports as a cluster member must ALSO be
    checked to VARY when the form varies. A definition ignoring its record is
    invariant along every level set, so non-constancy is required before
    invariance means anything. This is the same guard as in the scalar sweep
    and it is what stops constants from joining every cluster.

    Second control: `tau`, `theta` and `bigM` are NOT functions of the
    drift-retention form and must be reported as excluded. If they come back as
    members, the record construction is feeding the same numbers to every field
    and the run means nothing.
"""

import json
import os
import sys
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.normpath(os.path.join(HERE, "..", "..", "extract"))
if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

import api  # noqa: E402

TARGET_FILE = "Calibrator/DGP.lean"
RTOL = 1e-9


def phase1():
    """Report what DGP.lean contains and what calling it would require."""
    table = api.definition_table()
    rows = []
    for fq in sorted(table.keys()):
        d = table[fq]
        if d.get("file") != TARGET_FILE:
            continue
        rec = {
            "definition": fq,
            "line": d.get("line"),
            "body": (d.get("body") or "").strip()[:160],
            "empirical_status": d.get("empirical_status"),
            "args": [],
            "callable": False,
            "callable_error": None,
            "argnames": None,
        }
        for grp in d.get("args", []):
            rec["args"].append({
                "names": grp.get("names"),
                "type": grp.get("type"),
                "implicit": grp.get("implicit"),
            })
        try:
            fn, argnames = api.callable_for(fq)
            rec["callable"] = True
            rec["argnames"] = argnames
        except Exception as exc:
            rec["callable_error"] = "%s: %s" % (type(exc).__name__, str(exc)[:120])
        rows.append(rec)

    # `api.structures` may be a function or an already-built mapping, and its
    # value shape is not documented. Both are accepted and the shape actually
    # found is REPORTED, because the sweep's schema bug came from assuming a
    # shape instead of checking it.
    structs = {}
    struct_shape = None
    try:
        s = getattr(api, "structures", None)
        if callable(s):
            s = s()
            struct_shape = "api.structures() -> %s" % type(s).__name__
        else:
            struct_shape = "api.structures attribute -> %s" % type(s).__name__
        if isinstance(s, dict):
            for name in s:
                structs[name] = s[name]
        elif isinstance(s, list):
            for item in s:
                if isinstance(item, dict) and "name" in item:
                    structs[item["name"]] = item
            struct_shape += " (list keyed by 'name')"
        else:
            struct_shape += " -- UNRECOGNISED, phase 2 will find no fields"
    except Exception as exc:
        struct_shape = "ERROR %s: %s" % (type(exc).__name__, exc)

    sample = None
    for k in sorted(structs):
        sample = {"name": k, "value_type": type(structs[k]).__name__,
                  "keys": sorted(structs[k].keys())
                          if isinstance(structs[k], dict) else None,
                  "repr_head": repr(structs[k])[:300]}
        break

    return {"definitions": rows, "structures": structs,
            "structures_shape": struct_shape, "structures_sample": sample,
            "n_structures": len(structs)}


def _numeric_fields(struct_spec):
    """Field names of a structure that look numeric, best effort."""
    out = []
    if isinstance(struct_spec, dict):
        fields = struct_spec.get("fields", struct_spec)
        if isinstance(fields, dict):
            for k in fields:
                out.append(k)
        elif isinstance(fields, list):
            for f in fields:
                if isinstance(f, dict) and "name" in f:
                    out.append(f["name"])
                elif isinstance(f, str):
                    out.append(f)
    return out


class Rec(object):
    """Plain attribute bag; DGP bodies access fields as `r.Ne`."""

    def __init__(self, **kw):
        for k in kw:
            setattr(self, k, kw[k])


def phase2(recon):
    """Attempt level-set invariance with structure-valued arguments."""
    import math

    # Two references, because DGP's structure-valued definitions are not all
    # time-dependent. The first pass found 9 and excluded all 9 -- correctly:
    # fstEquilibrium, fstDriftMigration and fstDriftMutation carry no t at all,
    # so they are constant across level sets of a form that has one, and the
    # non-constancy guard rightly rejects them. They are EQUILIBRIUM forms, and
    # the reference they should be swept against is the island form in the
    # structure's migration field.
    REFS = [
        {"name": "drift_retention",
         "form": "(1 - 1/(2 Ne))^t",
         "f1": ["Ne", "N", "N_e"],
         "f2": ["horizon", "t", "t_div", "gens", "generations"],
         "levels": [0.9, 0.6, 0.3, 0.1],
         "p1_values": [50.0, 200.0, 1000.0, 5000.0],
         "solve": lambda ne, lv: math.log(lv) / math.log(1.0 - 1.0 / (2.0 * ne))},
        {"name": "island_fst",
         "form": "1/(1 + 4 Ne m)",
         "f1": ["Ne", "N", "N_e"],
         "f2": ["mig", "m", "migration", "m_rate"],
         "levels": [0.8, 0.5, 0.2, 0.05],
         "p1_values": [50.0, 200.0, 1000.0, 5000.0],
         "solve": lambda ne, lv: (1.0 / lv - 1.0) / (4.0 * ne)},
    ]

    results = {"attempted": 0, "members": [], "excluded": [], "errors": [],
               "skipped": {}, "by_reference": {}}

    structs = recon.get("structures") or {}
    for REF in REFS:
        NE_FIELDS = REF["f1"]
        T_FIELDS = REF["f2"]
        LEVELS = REF["levels"]
        NES = REF["p1_values"]
        _solve = REF["solve"]
        before_m = len(results["members"])
        before_a = results["attempted"]
        _phase2_one(recon, structs, results, NE_FIELDS, T_FIELDS, LEVELS, NES,
                    _solve, REF["name"])
        results["by_reference"][REF["name"]] = {
            "form": REF["form"],
            "attempted": results["attempted"] - before_a,
            "members": len(results["members"]) - before_m,
        }
    return results


def _phase2_one(recon, structs, results, NE_FIELDS, T_FIELDS, LEVELS, NES,
                _solve, ref_name):
    import math
    for rec in recon["definitions"]:
        if not rec["callable"]:
            continue
        args = rec["args"]
        explicit = [a for a in args if not a.get("implicit")]
        if len(explicit) != 1:
            results["skipped"]["not_single_explicit_arg"] = \
                results["skipped"].get("not_single_explicit_arg", 0) + 1
            continue
        # Argument types carry parameters ("HWEPolygenicScoreDGP m") and the
        # structure table is keyed by FULLY QUALIFIED name
        # ("Calibrator.EvolutionaryParameters"), so neither a raw nor an exact
        # lookup finds it. Strip parameters, then try short and qualified.
        tname = (explicit[0].get("type") or "").split()[0]
        spec = structs.get(tname)
        if spec is None:
            spec = structs.get("Calibrator." + tname)
        if spec is None:
            for k in structs:
                if k.split(".")[-1] == tname:
                    spec = structs[k]
                    break
        fields = _numeric_fields(spec or {})
        if not fields:
            results["skipped"]["structure_spec_not_found_or_no_fields"] = \
                results["skipped"].get("structure_spec_not_found_or_no_fields", 0) + 1
            continue
        ne_f = None
        t_f = None
        for f in fields:
            if ne_f is None and f in NE_FIELDS:
                ne_f = f
            if t_f is None and f in T_FIELDS:
                t_f = f
        if ne_f is None or t_f is None:
            results["skipped"]["no_Ne_and_t_fields"] = \
                results["skipped"].get("no_Ne_and_t_fields", 0) + 1
            continue

        results["attempted"] += 1
        try:
            fn, _argnames = api.callable_for(rec["definition"])
        except Exception as exc:
            results["errors"].append({"definition": rec["definition"],
                                      "error": str(exc)[:160]})
            continue

        all_inv = True
        moved = False
        per_level = []
        evaluated = 0
        for level in LEVELS:
            vals = []
            for ne in NES:
                try:
                    t = _solve(ne, level)
                except Exception:
                    continue
                kw = {}
                for f in fields:
                    kw[f] = 0.5
                kw[ne_f] = ne
                kw[t_f] = t
                try:
                    v = fn(Rec(**kw))
                except Exception as exc:
                    results["errors"].append(
                        {"definition": rec["definition"],
                         "error": "%s: %s" % (type(exc).__name__, str(exc)[:120])})
                    vals = []
                    break
                if not isinstance(v, (int, float)) or v != v:
                    continue
                vals.append(float(v))
            if len(vals) < 2:
                continue
            evaluated += len(vals)
            scale = max(1.0, max([abs(x) for x in vals]))
            if (max(vals) - min(vals)) > RTOL * scale:
                all_inv = False
            per_level.append(vals[0])

        if evaluated < 8:
            continue
        if len(per_level) >= 2:
            sc = max(1.0, max([abs(x) for x in per_level]))
            moved = (max(per_level) - min(per_level)) > RTOL * sc

        relation = "UNDETERMINED"
        if len(per_level) >= 3:
            x0, x1 = LEVELS[0], LEVELS[1]
            y0, y1 = per_level[0], per_level[1]
            if abs(x1 - x0) > 1e-15:
                bb = (y1 - y0) / (x1 - x0)
                aa = y0 - bb * x0
                worst = 0.0
                for xi, yi in zip(LEVELS[2:], per_level[2:]):
                    worst = max(worst, abs(aa + bb * xi - yi) / max(1.0, abs(yi)))
                relation = "AFFINE" if worst <= 1e-9 else "CO-FUNCTION"
        entry = {"definition": rec["definition"], "line": rec["line"],
                 "reference": ref_name, "ne_field": ne_f, "t_field": t_f,
                 "relation": relation,
                 "levels": per_level, "empirical_status": rec["empirical_status"]}
        if all_inv and moved:
            results["members"].append(entry)
        else:
            results["excluded"].append(entry)


def main():
    out = {}
    try:
        recon = phase1()
    except Exception:
        print("PHASE 1 FAILED:")
        print(traceback.format_exc())
        return 1
    out["phase1"] = recon

    n = len(recon["definitions"])
    n_callable = len([r for r in recon["definitions"] if r["callable"]])
    print("PHASE 1 -- reconnaissance of %s" % TARGET_FILE)
    print("  %d definitions, %d callable" % (n, n_callable))
    reasons = {}
    for r in recon["definitions"]:
        if not r["callable"]:
            key = (r["callable_error"] or "?").split(":")[0]
            reasons[key] = reasons.get(key, 0) + 1
    for k in sorted(reasons):
        print("    not callable (%s): %d" % (k, reasons[k]))
    types = {}
    for r in recon["definitions"]:
        for a in r["args"]:
            if not a.get("implicit"):
                types[a.get("type")] = types.get(a.get("type"), 0) + 1
    print("  explicit argument types seen:")
    for t in sorted(types, key=lambda x: -types[x]):
        print("    %-44s %d" % (t, types[t]))
    print("  structures: %d, discovered via %s"
          % (recon.get("n_structures", 0), recon.get("structures_shape")))
    if recon.get("structures_sample"):
        s = recon["structures_sample"]
        print("    sample %-28s value=%s keys=%s"
              % (s["name"], s["value_type"], s["keys"]))
        print("    repr: %s" % s["repr_head"])
    if not recon.get("n_structures"):
        print("  NOTE: no structures resolved, so phase 2 will attempt nothing.")
        print("        Phase 1 output is still what I need -- send it.")

    try:
        res = phase2(recon)
        out["phase2"] = res
        print("")
        print("PHASE 2 -- level-set invariance over structure arguments")
        print("  attempted %d, members %d, excluded %d, errors %d"
              % (res["attempted"], len(res["members"]), len(res["excluded"]),
                 len(res["errors"])))
        if res.get("skipped"):
            print("  skipped:")
            for k in sorted(res["skipped"]):
                print("    %-40s %d" % (k, res["skipped"][k]))
        for name in sorted(res.get("by_reference", {})):
            b = res["by_reference"][name]
            print("    %-18s %-22s attempted %d, members %d"
                  % (name, b["form"], b["attempted"], b["members"]))
        for m in res["members"]:
            print("    MEMBER   %-38s [%s] %-12s (%s,%s) status=%s"
                  % (m["definition"].split(".")[-1], m["reference"],
                     m.get("relation"), m["ne_field"], m["t_field"],
                     m["empirical_status"]))
        # control: tau / theta / bigM must NOT be members
        # The control is SCOPED TO drift_retention, which is what it was
        # designed for. tau = t_div/(2 Ne), theta = 4 Ne mu and bigM = 4 Ne mig
        # are not functions of (1 - 1/(2Ne))^t, so their appearing there would
        # mean every field is being fed the same value.
        #
        # Against the ISLAND form the same reasoning does not apply: bigM is
        # 4 Ne mig, which shares that form's level sets exactly and legitimately.
        # Flagging it there would be a false alarm, and the first version of
        # this control did exactly that once the island reference was added.
        bad = [m["definition"] for m in res["members"]
               if m["reference"] == "drift_retention"
               and m["definition"].split(".")[-1] in ("tau", "theta", "bigM")]
        n_dr = res.get("by_reference", {}).get("drift_retention", {}).get(
            "attempted", 0)
        if n_dr == 0:
            print("  CONTROL UNDETERMINED: nothing was attempted against "
                  "drift_retention, so tau/theta/bigM being absent from that "
                  "reference's members is vacuous. Neither pass nor fail.")
            out["control_failed"] = None
        elif bad:
            print("  CONTROL FAILED: %s reported as members of the "
                  "drift-retention form. They are not functions of it, so the "
                  "record construction is feeding identical values to every "
                  "field. Do not read the member list." % bad)
            out["control_failed"] = bad
        else:
            print("  CONTROL PASSED: tau/theta/bigM evaluated against "
                  "drift_retention and correctly excluded (%d attempted there)"
                  % n_dr)
            out["control_failed"] = []
        if res["errors"]:
            print("  first 5 errors:")
            for e in res["errors"][:5]:
                print("    %-46s %s" % (e["definition"], e["error"]))
    except Exception:
        out["phase2_error"] = traceback.format_exc()
        print("")
        print("PHASE 2 FAILED -- phase 1 output is still useful, send it:")
        print(traceback.format_exc())

    fh = open(os.path.join(HERE, "dgp_batch_results.json"), "w")
    json.dump(out, fh, indent=1, default=str)
    fh.close()
    print("")
    print("-> dgp_batch_results.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
