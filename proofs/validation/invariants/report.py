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
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent


def load(name):
    p = HERE / name
    return json.loads(p.read_text()) if p.exists() else {}


def build():
    defs = {f"{d['module']}.{d['name']}": d
            for d in json.loads((HERE / "defs.json").read_text())}
    rng = load("results_ranges.json")
    inv = load("results_invariants.json")
    fal = load("results_falsifiability.json")

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
            checks.append(dict(family="invariant", kind=c["kind"],
                               verdict={True: "holds", False: "violated",
                                        None: "error"}[c["holds"]],
                               why=c["why"]))
        covered = bool(f.get("covered"))
        entry = dict(
            module=d["module"], line=d["line"], path=d["path"],
            params=[p for p, _ in d["params"]], ret=d["ret"],
            covered=covered,
            demonstration=f.get("demonstration"),
            falsifiability_evidence=(
                [dict(mutation=m["mutation"], rejected_by=m["rejected_by"])
                 for m in f.get("killed", [])[:3]]
                if f.get("demonstration") == "mutant-rejected"
                else f.get("rejected_by")),
            checks=checks,
            findings=[c for c in checks
                      if c["verdict"] in ("escape", "escape-unguarded",
                                          "violated")],
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
            rows.append((sev, k, v, rng.get(k, {}), inv.get(k, {})))
        rows.sort(key=lambda t: -t[0])
        print(f"\n{len(rows)} definitions with a finding, by severity:\n")
        for sev, k, v, r, i in rows:
            print(f"[{sev:5.1f}] {k}  ({v['path']}:{v['line']})")
            if r.get("verdict", "").startswith("escape"):
                w = ", ".join(f"{a}={b:.6g}" for a, b in r["witness"].items())
                print(f"        {r['range_why']}")
                print(f"        value {r['value']:.6g} outside "
                      f"[{r['range'][0]}, {r['range'][1]}] at {w}")
                if r.get("blind_coordinates"):
                    print(f"        NOTE: needs {r['blind_coordinates']}, "
                          "whose admissible values could not be determined")
            for ch in i.get("checks", []):
                if ch["holds"] is False:
                    print(f"        {ch['kind']}: {ch['why']}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
