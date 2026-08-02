"""Unified, machine-readable coverage and findings report.

Consumes results_ranges.json, results_invariants.json and
results_falsifiability.json and emits `coverage.json`, keyed by
fully-qualified definition name (`Module.name`).

The only definitions marked `covered: true` are those with a check that has
been DEMONSTRATED to be able to fail -- either because it already rejects the
body as written, or because a named mutant of the body is rejected.  Every
other definition carries `uncovered_reason`, and the set of them is the
residue the simulation tiers inherit.

Run:  python report.py           (add --findings for the ranked defect list)
"""
from __future__ import annotations

import collections
import json
import math
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent


def blast_radius():
    """definition -> number of theorems mentioning it.

    A 5% escape in something forty theorems rest on matters more than a 300%
    escape in a leaf, so findings are ranked by dependents as well as by
    overshoot.  From the `extract` agent's table; it is a syntactic mention so
    it over-counts slightly, but it is the right order of magnitude.
    """
    try:
        import sys
        sys.path.insert(0, str(HERE.parents[0] / "extract"))
        import api
        out = {}
        for n, rec in api.definition_table().items():
            key = (rec["file"].split("/")[-1][:-5], rec["short"])
            out[key] = len(rec.get("mentioned_by") or [])
        return out
    except Exception:
        return {}


def load(name):
    p = HERE / name
    return json.loads(p.read_text()) if p.exists() else {}


def build():
    defs = {f"{d['module']}.{d['name']}": d
            for d in json.loads((HERE / "defs.json").read_text())}
    rng = load("results_ranges.json")
    inv = load("results_invariants.json")
    fal = load("results_falsifiability.json")
    sim = load("results_simulation.json")
    thm = (load("results_theorems.json") or {}).get("by_definition", {})
    radius = blast_radius()

    out = {}
    for k, d in defs.items():
        r = rng.get(k, {})
        i = inv.get(k, {})
        f = fal.get(k, {})
        checks = []
        if r.get("verdict") not in (None, "not-transpiled", "no-range", "error"):
            checks.append(dict(family="range", kind="range",
                               verdict=r["verdict"],
                               required_range=r.get("range"),
                               why=r.get("range_why")))
        for c in i.get("checks", []):
            e = dict(family="invariant", kind=c["kind"],
                     verdict={True: "holds", False: "violated",
                              None: "error"}[c["holds"]],
                     why=c["why"])
            if c["kind"] == "totality":
                # Totality defects go in the SAME stream as the range escapes:
                # they are findings with an exact triggering input, and the
                # owner needs to see which kind they have.
                e["totality_findings"] = [
                    dict(klass=f["klass"], point=f["point"],
                         value=f["value"], limit=f["limit"],
                         junk_branch=f["junk_branch"], note=f["severity_note"])
                    for f in (c.get("detail") or {}).get("findings", [])
                    if f.get("is_defect")]
            checks.append(e)
        sm = sim.get(k, {})
        if sm.get("verdict") in ("agrees", "disagrees"):
            checks.append(dict(family="simulation", kind="simulation",
                               verdict=sm["verdict"], why=sm.get("oracle"),
                               worst_excess=sm.get("worst_excess_over_allowed")))
        # Simulation is the strongest evidence available: it compares against
        # an independent reference rather than against the definition's own
        # stated properties.  It counts as coverage on the same terms as
        # everything else -- only when a mutant of the body is rejected.
        th = thm.get(k) or []
        if th:
            checks.append(dict(family="theorem", kind="theorem",
                               verdict="discriminates",
                               why=f"{len(th)} proved theorem(s) about this "
                                   "definition break when its body is mutated",
                               theorems=[t["theorem"] for t in th[:5]]))
        covered = bool(f.get("covered")) or bool(sm.get("covered")) or bool(th)
        entry = dict(
            module=d["module"], line=d["line"], path=d["path"],
            dependent_theorems=radius.get((d["module"], d["name"])),
            params=[p for p, _ in d["params"]], ret=d["ret"],
            covered=covered,
            demonstration=(("simulation-mutant-rejected" if sm.get("covered")
                            else None) or f.get("demonstration") or
                           ("theorem-mutant-rejected" if th else None)),
            # WHAT KIND of evidence, kept separate on purpose.  A coverage
            # number that pools these is how internal consistency gets
            # reported as contact with reality; it has already happened twice
            # in this project, in both cases making the number look better.
            evidence_class=(
                "external-reference" if sm.get("covered") else
                "self-property" if f.get("covered") else
                "internal-consistency" if th else None),
            simulation_oracle=sm.get("oracle"),
            simulation_seed_stability=sm.get("seed_stability"),
            mutants_rejected=sm.get("mutants_rejected") or (
                f.get("n_killed") if f.get("covered") else None),
            mutants_tried=sm.get("mutants_tried") or (
                f.get("n_mutants") if f.get("covered") else None),
            discriminating_theorems=[t["theorem"] for t in th[:5]] or None,
            falsifiability_evidence=(
                [dict(mutation=m["mutation"], rejected_by=m["rejected_by"])
                 for m in f.get("killed", [])[:3]]
                if f.get("demonstration") == "mutant-rejected"
                else f.get("rejected_by")),
            checks=checks,
            findings=[c for c in checks
                      if c["verdict"] in ("escape", "escape-unguarded",
                                          "escape-outside-theorem",
                                          "violated", "disagrees")],
        )
        if not covered:
            entry["uncovered_reason"] = _why_not(d, r, i, f)
        out[k] = entry
    return out


def _why_not(d, r, i, f):
    if r.get("verdict") == "not-transpiled":
        return dict(stage="transpile", detail=r.get("reason"))
    if f.get("reason"):
        return dict(stage="falsifiability", detail=f["reason"],
                    survived=f.get("survived"))
    bits = []
    if r.get("verdict") == "no-range":
        bits.append("the name and docstring commit it to no range")
    if r.get("verdict") == "inconclusive":
        bits.append("no range escape found and the interval proof did not close")
    if not i.get("checks"):
        for s in i.get("skipped", []):
            bits.append(f"{s['kind']}: {s['reason']}")
    return dict(stage="no-derivable-check", detail="; ".join(bits) or "unknown")


def main(argv):
    cov = build()
    (HERE / "coverage.json").write_text(json.dumps(cov, indent=1, default=str))

    n = len(cov)
    c = sum(1 for v in cov.values() if v["covered"])
    print(f"definitions in proofs/Calibrator ......... {n}")
    print(f"covered by a demonstrated check .......... {c}  ({100*c/n:.1f}%)")
    print(f"residue for the simulation tiers ......... {n - c}")
    print()
    stage = collections.Counter(v["uncovered_reason"]["stage"]
                                for v in cov.values() if not v["covered"])
    print("residue by stage:")
    for s, k in stage.most_common():
        print(f"  {k:5d}  {s}")
    print()
    tiers = collections.Counter(v["evidence_class"] for v in cov.values()
                                if v["covered"])
    print("covered by EVIDENCE CLASS (these must not be pooled):")
    labels = {
        "external-reference": "external reference (simulation) -- validation",
        "self-property": "the definition's own named range/invariant",
        "internal-consistency": "a proved theorem breaks under mutation",
    }
    for t, k in tiers.most_common():
        print(f"  {k:5d}  {labels.get(t, t)}")
    print()
    kinds = collections.Counter(ch["kind"] for v in cov.values()
                                for ch in v["checks"])
    print("checks registered by kind:")
    for s, k in kinds.most_common():
        print(f"  {k:5d}  {s}")

    if "--findings" in argv:
        rng = load("results_ranges.json")
        inv = load("results_invariants.json")
        rows = []
        for k, v in cov.items():
            if not v["findings"]:
                continue
            sev = max(rng.get(k, {}).get("severity", -1),
                      inv.get(k, {}).get("severity", -1))
            # blast radius as a multiplier, not an addend: it should reorder
            # findings of similar severity, never promote a trivial one.
            n_dep = v.get("dependent_theorems") or 0
            sev = sev * (1.0 + 0.15 * math.log10(1 + n_dep))
            rows.append((sev, k, v, rng.get(k, {}), inv.get(k, {})))
        rows.sort(key=lambda t: -t[0])
        print(f"\n{len(rows)} definitions with a finding, by severity:\n")
        for sev, k, v, r, i in rows:
            dep = v.get("dependent_theorems")
            dtxt = f", {dep} dependent theorems" if dep else ""
            print(f"[{sev:5.1f}] {k}  ({v['path']}:{v['line']}{dtxt})")
            if r.get("verdict") == "contradicts-theorem":
                print(f"        CHECKER ERROR, not a corpus defect: "
                      f"contradicts {r['contradicted']}")
            if r.get("verdict", "").startswith("escape"):
                w = ", ".join(f"{a}={b:.6g}" for a, b in r["witness"].items())
                print(f"        {r['range_why']}")
                print(f"        value {r['value']:.6g} outside "
                      f"[{r['range'][0]}, {r['range'][1]}] at {w}")
                if r.get("blind_coordinates"):
                    print(f"        NOTE: needs {r['blind_coordinates']}, "
                          "whose admissible values could not be determined")
            for ch in i.get("checks", []):
                if ch["holds"] is not False:
                    continue
                if ch["kind"] == "totality":
                    for f in (ch.get("detail") or {}).get("findings", []):
                        if not f.get("is_defect"):
                            continue
                        pt = ", ".join(f"{a}={b:.6g}"
                                       for a, b in f["point"].items())
                        print(f"        totality [{f['klass']}]: returns "
                              f"{f['value']:.6g} at {pt}; the limit there is "
                              f"{f['limit']}")
                        print(f"        {f['severity_note']}")
                else:
                    print(f"        {ch['kind']}: {ch['why']}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
