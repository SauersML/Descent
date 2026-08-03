"""CHECK 1b -- coupled equilibrium systems, solved jointly.

An `_isFixedPoint` theorem for a coupled system proves that the claimed values
are *a* fixed point of one equation.  It does not prove they are *the* solution
of the system, and for a 2x2 system neither equation determines anything on its
own: the same-deme coalescent map mentions ETst and the different-deme map
mentions ETss.  Solving them together is information Lean's theorems do not
carry, and it is what turns "consistent" into "uniquely determined".

A system is detected structurally: a guard theorem whose map application takes
two or more arguments that are themselves applications of sibling equilibrium
definitions.  Nothing is guessed from names.
"""

from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from pathlib import Path

import sympy as sp

import leansym as L
import shared
import fixedpoint as FP
from check1_fixedpoints import EQ_NAME, _split_app_args
from paths import ARTIFACTS as ART

HERE = Path(__file__).parent


def run():
    decls = json.load(open(ART / "decls.json"))
    table = shared.build_table()
    conv = L.Converter(table)
    defs = {d["name"]: d for d in shared.def_records()}
    eq_names = {d["name"] for d in shared.def_records()
                if d["body"] and EQ_NAME.search(d["name"])}

    # guard theorems, grouped by module
    guards = defaultdict(list)
    for t in decls:
        if t["kind"] == "theorem" and t["name"].endswith("_isFixedPoint"):
            guards[t["module"]].append(t)

    results = []
    for module, thms in guards.items():
        # collect equations whose map reads >= 2 sibling equilibria
        system_thms = []
        for t in thms:
            lhs = t["body"].split("=")[0].strip()
            parts = _split_app_args(lhs)
            if len(parts) < 2:
                continue
            read = []
            for a in parts[1:]:
                head = a.strip("()").strip().split()
                if head and head[0].split(".")[-1] in eq_names:
                    read.append(head[0].split(".")[-1])
            if len(set(read)) >= 2:
                system_thms.append((t, parts[0].split(".")[-1], read))
        if len(system_thms) < 2:
            continue

        unknowns = sorted({n for _, _, read in system_thms for n in read})
        rec = {"check": "check1b_joint_system", "module": module,
               "unknowns": unknowns,
               "guard_theorems": [t["name"] for t, _, _ in system_thms],
               "status": None, "detail": {}}

        # model parameters: binders of the first unknown definition
        p0 = defs[unknowns[0]]
        params = [n for grp, ty, op in p0["binders"] if op == "(" for n in grp]
        psyms = {n.lstrip("_"): sp.Symbol(n.lstrip("_"), positive=True) for n in params}
        usyms = {n: sp.Symbol(n, positive=True) for n in unknowns}

        system, targets_seen = {}, set()
        ok = True
        for t, map_name, read in system_thms:
            # the equation's right-hand side names the state this map computes
            rhs_head = t["body"].split("=")[1].strip().split()
            target = rhs_head[0].split(".")[-1] if rhs_head else None
            if target not in usyms or target in targets_seen:
                ok = False
                break
            targets_seen.add(target)
            mbind, mbody = table.get(map_name, (None, None))
            if mbind is None:
                ok = False
                break
            # bind map arguments by matching the theorem's actual arguments
            parts = _split_app_args(t["body"].split("=")[0].strip())
            if len(parts) - 1 != len(mbind):
                ok = False
                break
            env = {}
            for binder, arg in zip(mbind, parts[1:]):
                a = arg.strip("()").strip()
                head = a.split()[0].split(".")[-1] if a.split() else a
                if head in usyms:
                    env[binder] = usyms[head]
                elif a.lstrip("_") in psyms:
                    env[binder] = psyms[a.lstrip("_")]
                else:
                    ok = False
                    break
            if not ok:
                break
            try:
                system[target] = conv.convert(mbody, dict(env))
            except Exception as e:
                rec["detail"]["convert_error"] = str(e)
                ok = False
                break
        if not ok or len(system) != len(unknowns):
            rec["status"] = "system_not_reconstructed"
            results.append(rec)
            continue

        sols, info = FP.joint_fixed_point(system, usyms)
        rec["detail"]["equations"] = info.get("equations")
        if not sols:
            rec["status"] = "JOINT_SOLVE_FAILED"
            results.append(rec)
            continue
        sol = sols[0]
        rec["detail"]["joint_solution"] = {k: sp.sstr(v) for k, v in sol.items()}
        rec["detail"]["unique"] = len(sols) == 1

        claims, mismatches = {}, []
        for n in unknowns:
            d = defs[n]
            env = {b: psyms[b.lstrip("_")] for grp, ty, op in d["binders"]
                   if op == "(" for b in grp if b.lstrip("_") in psyms}
            try:
                cl = conv.convert(d["body"], env)
            except Exception:
                continue
            claims[n] = sp.sstr(cl)
            if sp.simplify(sp.together(sol[n] - cl)) != 0:
                mismatches.append({"unknown": n, "claimed": sp.sstr(cl),
                                   "joint_solution": sp.sstr(sol[n])})
        rec["detail"]["claims"] = claims
        rec["detail"]["mismatches"] = mismatches
        rec["status"] = ("JOINT_FIXED_POINT_FAILS" if mismatches
                         else "joint_fixed_point_verified")
        results.append(rec)
    return results


def main():
    res = run()
    (ART / "results_check1b.json").write_text(json.dumps(res, indent=1, ensure_ascii=False))
    c = Counter(r["status"] for r in res)
    print(f"CHECK 1b: {len(res)} coupled equilibrium systems detected")
    for k, v in sorted(c.items(), key=lambda kv: -kv[1]):
        print(f"  {k:30s} {v}")
    print()
    for r in res:
        print(f'  {r["module"]}  unknowns={r["unknowns"]}  [{r["status"]}]')
        for e in r["detail"].get("equations", []) or []:
            print(f'      eq   : {e}')
        for k, v in (r["detail"].get("joint_solution") or {}).items():
            print(f'      solve: {k} = {v}   (claimed {r["detail"].get("claims", {}).get(k)})')
        print(f'      unique solution: {r["detail"].get("unique")}')
        for m in r["detail"].get("mismatches", []):
            print(f'      !! {m}')
        print()


if __name__ == "__main__":
    main()
