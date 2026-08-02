"""CHECK 5 -- what each recurrence actually converges to.

A recurrence is where an equilibrium claim can go wrong without any single
formula being wrong: every step is correct, the closed form is correct, and the
limit the surrounding prose attributes to it is a different number.  The
mutation-free heterozygosity recurrence is the case in this corpus -- its only
rest point is `H = 0`, so any long-run quantity built on it is a statement about
a population that has lost all variation, and an F_ST built on it tends to 1.

For each definition given by an equation compiler (`| 0 => base`,
`| t + 1 => step`), this check recovers the step as a map of the previous value,
solves for its rest points, classifies stability, and reports the `t -> infinity`
limit.  It then flags recurrences whose only rest point is zero, which is the
signature of the drift-without-mutation cluster.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

import sympy as sp

import leansym as L
import shared

HERE = Path(__file__).parent


def step_of(d, table):
    """Recover (step_expr, state_symbol, params) from an equation-compiler def."""
    eqs = d.get("equations") or []
    base = next((e for e in eqs if e["pattern"].strip() in ("0", "Nat.zero")), None)
    step = next((e for e in eqs if "+ 1" in e["pattern"]), None)
    if base is None or step is None:
        return None
    m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_'₀-₉]*)\s*\+\s*1", step["pattern"].strip())
    tvar = m.group(1) if m else "t"
    args = [n for a in d["args"] if not a.get("implicit") for n in a["names"]]
    short = d["short"]
    rhs = " ".join(step["rhs"].split())
    # replace the self-application `NAME a b c t` with a single state symbol
    call = re.escape(short) + r"\s+" + r"\s+".join(re.escape(a) for a in args) + \
        r"\s+" + re.escape(tvar)
    rhs2, n = re.subn(call, "_H", rhs)
    if n == 0:
        return None
    conv = L.Converter(table)
    env = {a: sp.Symbol(a, positive=True) for a in args}
    env["_H"] = sp.Symbol("_H", real=True)
    try:
        expr = conv.convert(rhs2, dict(env))
    except Exception as e:
        return ("opaque", str(e), None)
    try:
        b = conv.convert(base["rhs"], dict(env))
    except Exception:
        b = None
    return (expr, env["_H"], {"params": args, "base": b, "tvar": tvar})


def run():
    table = shared.build_table()
    recs = [d for d in shared.definitions().values() if d.get("equations")]
    results = []
    for d in recs:
        got = step_of(d, table)
        if got is None:
            continue
        rec = {"check": "check5_recurrence_limit",
               "fqn": d["name"], "name": d["short"],
               "file": d["file"], "line": d["line"],
               "status": None, "detail": {}}
        if got[0] == "opaque":
            rec["status"] = "opaque"
            rec["detail"]["reason"] = got[1]
            results.append(rec)
            continue
        expr, H, info = got
        rec["detail"]["step"] = sp.sstr(expr)
        rec["detail"]["base"] = sp.sstr(info["base"]) if info["base"] is not None else None
        try:
            roots = sp.solve(sp.Eq(sp.together(expr - H), 0), H, dict=False)
            roots = [sp.simplify(r) for r in (roots if isinstance(roots, list) else [roots])]
        except Exception as e:
            rec["status"] = "solve_failed"
            rec["detail"]["reason"] = str(e)
            results.append(rec)
            continue
        rec["detail"]["rest_points"] = [sp.sstr(r) for r in roots]
        slope = sp.simplify(sp.diff(expr, H))
        rec["detail"]["slope"] = sp.sstr(slope)
        rec["detail"]["contracting_when"] = sp.sstr(sp.Abs(slope) < 1)

        # closed-form limit for an affine map H -> a*H + b with |a| < 1
        if slope.free_symbols.isdisjoint({H}):
            b = sp.simplify(expr - slope * H)
            rec["detail"]["affine"] = True
            rec["detail"]["intercept"] = sp.sstr(b)
            if sp.simplify(b) == 0:
                rec["detail"]["limit_if_contracting"] = "0"
            else:
                rec["detail"]["limit_if_contracting"] = sp.sstr(sp.simplify(b / (1 - slope)))
        if len(roots) == 1 and sp.simplify(roots[0]) == 0:
            rec["status"] = "ONLY_REST_POINT_IS_ZERO"
        else:
            rec["status"] = "has_nonzero_rest_point"
        results.append(rec)

    # who consumes a zero-limit recurrence?
    degenerate = {r["name"] for r in results if r["status"] == "ONLY_REST_POINT_IS_ZERO"}
    consumers = []
    for d in shared.definitions().values():
        body = d.get("body") or ""
        used = sorted({n for n in degenerate
                       if re.search(rf"(?<![A-Za-z0-9_]){re.escape(n)}(?![A-Za-z0-9_])", body)})
        if used and d["short"] not in degenerate:
            consumers.append({"check": "check5_zero_limit_consumer",
                              "fqn": d["name"], "file": d["file"], "line": d["line"],
                              "uses": used,
                              "body": " ".join(body.split())[:200],
                              "docstring_head": " ".join((d.get("docstring") or "").split())[:200]})
    return results, consumers


def main():
    res, consumers = run()
    (HERE / "results_check5.json").write_text(
        json.dumps({"recurrences": res, "consumers": consumers}, indent=1, ensure_ascii=False))
    c = Counter(r["status"] for r in res)
    print(f"CHECK 5: {len(res)} recurrences analysed")
    for k, v in sorted(c.items(), key=lambda kv: -kv[1]):
        print(f"  {k:28s} {v}")
    print()
    for r in res:
        if r["status"] in ("ONLY_REST_POINT_IS_ZERO", "has_nonzero_rest_point"):
            flag = "!!" if r["status"] == "ONLY_REST_POINT_IS_ZERO" else "  "
            print(f'{flag} {r["fqn"]}  ({r["file"]}:{r["line"]})')
            print(f'     step        : _H -> {r["detail"]["step"]}')
            print(f'     rest points : {r["detail"]["rest_points"]}')
            print(f'     limit       : {r["detail"].get("limit_if_contracting")}'
                  f'   when {r["detail"]["contracting_when"]}')
    print()
    print(f"=== definitions consuming a recurrence whose only limit is 0 ({len(consumers)}) ===")
    for c_ in consumers:
        print(f'  {c_["fqn"]}  ({c_["file"]}:{c_["line"]})  uses {c_["uses"]}')
        print(f'     body: {c_["body"][:150]}')


if __name__ == "__main__":
    main()
