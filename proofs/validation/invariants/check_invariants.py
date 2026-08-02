"""Driver for FAMILY 2 -- metamorphic invariants.

Run:  python check_invariants.py  ->  results_invariants.json

Output is keyed by fully-qualified definition name.  For each definition:
  `checks`   the invariants derived, each with the evidence that it applies
             and whether it holds
  `skipped`  the invariant kinds that do NOT apply, each with the reason --
             this is the honest part of the coverage number, and the
             definitions with an empty `checks` list are the residue the
             simulation tiers must handle.
"""
from __future__ import annotations

import json
import math
import pathlib
import sys

import compile_defs as C
import invariants as INV
from check_ranges import build_feasible

HERE = pathlib.Path(__file__).resolve().parent


def check_one(c, defs):
    feasible, kept, _ = build_feasible(c, defs)
    checks, skipped = INV.derive(c, feasible=feasible)
    out = []
    for ch in checks:
        try:
            ok, detail = ch["run"](c)
        except Exception as e:
            ok, detail = None, dict(error=f"{type(e).__name__}: {e}")
        out.append(dict(kind=ch["kind"], why=ch["why"], holds=ok, detail=detail))
    return dict(checks=out, skipped=[dict(kind=k, reason=r) for k, r in skipped],
                side_constraints=[k["hyp"] for k in kept])


def severity(r):
    """Rank invariant violations.

    A violated ABSORBING boundary is the worst: it is a qualitative error, the
    formula says an allele that is lost is still segregating.  A violated
    asserted MONOTONICITY is next -- the author wrote down the direction and
    the formula disagrees.  Broken SYMMETRY and SCALE invariance follow.
    """
    weight = dict(absorbing=100, monotone=80, symmetry=60, scale=55, limit=70)
    s = -1.0
    for ch in r.get("checks", []):
        if ch["holds"] is False:
            mag = ch["detail"].get("max_relative_asymmetry") or \
                  ch["detail"].get("max_relative_change") or 0.0
            s = max(s, weight.get(ch["kind"], 40) + min(10.0, math.log10(1 + mag) * 3))
    return s


def main(argv):
    defs = C.load_defs()
    cs, why_not, _ = C.compile_all(defs)
    results = {}
    for k in sorted(cs):
        try:
            r = check_one(cs[k], defs)
        except Exception as e:
            r = dict(checks=[], skipped=[],
                     error=f"{type(e).__name__}: {e}")
        d = cs[k].d
        r.update(name=d["name"], module=d["module"], line=d["line"],
                 family="invariant", n_checks=len(r.get("checks", [])))
        r["severity"] = severity(r)
        results[k] = r
    for k, w in why_not.items():
        results.setdefault(k, dict(checks=[], skipped=[], n_checks=0,
                                   verdict="not-transpiled", reason=w,
                                   family="invariant", severity=-1.0))
    out = HERE / "results_invariants.json"
    out.write_text(json.dumps(results, indent=1, default=str))

    covered = [r for r in results.values() if r["n_checks"] > 0]
    viol = [r for r in results.values()
            if any(c["holds"] is False for c in r.get("checks", []))]
    kinds = {}
    for r in results.values():
        for c in r.get("checks", []):
            kinds.setdefault(c["kind"], [0, 0])
            kinds[c["kind"]][0] += 1
            if c["holds"] is False:
                kinds[c["kind"]][1] += 1
    print(f"{len(results)} definitions -> {out}")
    print(f"  {len(covered)} carry at least one derived invariant")
    print(f"  {len(viol)} violate one")
    for k, (n, bad) in sorted(kinds.items()):
        print(f"    {k:10s} {n:5d} checks, {bad:4d} violated")
    print("\nViolations by severity:")
    for r in sorted(viol, key=lambda r: -r["severity"])[:30]:
        for c in r["checks"]:
            if c["holds"] is False:
                print(f"  [{r['severity']:5.1f}] {r['module']}.{r['name']}:"
                      f"{r['line']}  {c['kind']}")
                print(f"           {c['why']}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
