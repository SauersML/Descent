"""CHECK 1 -- equilibrium definitions against the one-step map they claim.

Design note, learned the hard way.  A first version of this check *guessed* the
one-step map for each equilibrium from name shape and arity.  It reported five
failures, and all five were the checker's fault: it paired
`selectionMigrationEquilibriumMigrationFirst` with the selection-first map, it
drove a two-dimensional coalescent system (ETss, ETst) through a
one-dimensional substitution, and it matched `sharedLD_from_equilibrium`, which
is a complement rather than a rest point.  A validator that guesses at the
model manufactures disagreements exactly as readily as a hand transcription
manufactures agreement.

So this version never guesses:

  GUARDED    an `_isFixedPoint` theorem exists.  Its *statement* is converted
             to sympy wholesale, which needs no inference about which argument
             is the state and handles coupled systems for free.  Lean has
             already proved these, so a failure here means the checker or the
             inlining table is wrong -- it is a self-test, and it is what keeps
             the unguarded arm below honest.  On top of that, sympy asks the
             question Lean does not: is the claimed root the *relevant* one.
  UNGUARDED  no such theorem.  A map is accepted only from an explicit
             backticked docstring reference in the same module.  If none is
             named, the definition is reported as an unverified equilibrium
             claim rather than paired with a plausible-looking neighbour.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

import sympy as sp

import leansym as L
import shared
import hyps as H
import fixedpoint as FP

HERE = Path(__file__).parent

EQ_NAME = re.compile(
    r"(equilibrium|Equilibrium|steadyState|SteadyState|balance|Balance|"
    r"fixedPoint|FixedPoint|stationary|Stationary|restPoint|RestPoint|"
    r"Floor|floor)"
)
MAP_NAME = re.compile(
    r"(Step|step|Recur|recur|Flow|flow|Update|update|Iterate|Next|next|Map\b)"
)
# names that carry an equilibrium word but denote a transform of one, not a rest point
NOT_A_REST_POINT = re.compile(r"(_from_|From[A-Z]|Ratio$|Scalars$|Shift$|Gap$)")


def load():
    decls = json.load(open(HERE / "decls.json"))
    return decls, shared.build_table()


def backticked(doc: str) -> list[str]:
    return re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)", doc or "")


def _split_app_args(s: str) -> list[str]:
    """Split a Lean application `f a (g b) c` into ['a', '(g b)', 'c']."""
    args, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0 and ch.isspace():
            if cur.strip():
                args.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        args.append(cur.strip())
    return args


def _is_self_map_in_last_arg(stmt: str, map_name: str, eq_name: str, table) -> bool:
    lhs = stmt.split("=")[0].strip()
    parts = _split_app_args(lhs)
    if not parts or parts[0].split(".")[-1] != map_name:
        return False
    mbind, _ = table[map_name]
    if len(parts) - 1 != len(mbind):
        return False
    last = parts[-1].strip("()").strip()
    return last.split()[0].split(".")[-1] == eq_name if last.split() else False


def state_var_analysis(conv, table, map_name, eq_name, rec):
    """Where the map is one-dimensional in its final argument, solve for every
    rest point and classify stability.  Skipped for coupled systems."""
    mbind, mbody = table[map_name]
    if not mbind:
        return
    syms = {b: sp.Symbol(b, real=True) for b in mbind}
    try:
        step = conv.convert(mbody, dict(syms))
    except L.Unsupported as e:
        rec["detail"]["root_analysis_skipped"] = str(e)
        return
    var = syms[mbind[-1]]
    # a coupled system: other binders of the map are themselves equilibrium
    # components (they appear as arguments of sibling equilibrium defs)
    if var not in step.free_symbols:
        rec["detail"]["root_analysis_skipped"] = "state variable absent from map body"
        return
    try:
        roots = sp.solve(sp.Eq(sp.together(step - var), 0), var, dict=False)
        roots = [sp.simplify(r) for r in (roots if isinstance(roots, list) else [roots])]
        deriv = sp.diff(step, var)
    except Exception as e:
        rec["detail"]["solve_error"] = str(e)
        return
    rec["detail"]["map_roots"] = [sp.sstr(r) for r in roots]
    rec["detail"]["map_derivative"] = sp.sstr(deriv)
    stab = []
    for r in roots:
        try:
            d = sp.simplify(deriv.subs(var, r))
            t = sp.simplify(sp.Abs(d) - 1)
            s = "stable" if t.is_negative else "unstable" if t.is_positive else "unknown"
        except Exception:
            d, s = None, "unknown"
        stab.append({"root": sp.sstr(r), "stability": s,
                     "derivative": sp.sstr(d) if d is not None else None})
    rec["detail"]["root_stability"] = stab
    if len(roots) > 1:
        rec["detail"]["multiple_roots"] = [sp.sstr(r) for r in roots]


def check_guarded(conv, thm, rec):
    """Convert the `_isFixedPoint` statement and verify both sides agree."""
    prop = thm["body"]
    # keep only the final proposition if hypotheses leaked in
    prop = prop.strip()
    if "=" not in prop:
        rec["status"] = "opaque_theorem"
        rec["detail"]["reason"] = "no equation in statement"
        return
    try:
        eq = conv.convert(prop)
    except L.Unsupported as e:
        rec["status"] = "opaque_theorem"
        rec["detail"]["reason"] = str(e)
        return
    if not isinstance(eq, sp.Eq):
        rec["status"] = "opaque_theorem"
        rec["detail"]["reason"] = f"statement is not an equation: {eq}"
        return
    lhs, rhs = eq.lhs, eq.rhs
    rec["detail"]["lhs_map_applied"] = sp.sstr(lhs)
    rec["detail"]["rhs_claimed"] = sp.sstr(rhs)
    verdict = L.equal(lhs, rhs)
    rec["detail"]["residual"] = sp.sstr(sp.simplify(sp.together(lhs - rhs)))
    if verdict is True:
        rec["status"] = "fixed_point_verified"
    elif verdict is False:
        rec["status"] = "FIXED_POINT_FAILS"
    else:
        rec["status"] = "inconclusive"



def try_joint(conv, table, d, named_maps, decls, equilibrium_names):
    """Solve a coupled system when a docstring names several maps.

    The two-deme coalescent is the case: `twoDemeIMFirstStepSame` mentions
    ETst and `twoDemeIMFirstStepDiff` mentions ETss, so neither equation
    determines anything on its own.
    """
    maps, states = {}, {}
    for mn in named_maps:
        mbind, mbody = table[mn]
        if not mbind:
            return None
        # the state arguments are the map binders that name sibling equilibria
        maps[mn] = (mbind, mbody)
    # the shared state variables are the binder names common to all the maps,
    # minus the model parameters this equilibrium itself takes
    own = {n for grp, ty, op in d["binders"] if op == "(" for n in grp}
    state_names = set()
    for mn, (mbind, _) in maps.items():
        for b in mbind:
            if b.lstrip("_") not in own:
                state_names.add(b.lstrip("_"))
    if len(state_names) < 2:
        return None
    syms = {n: sp.Symbol(n, positive=True) for n in state_names}
    params = {n: sp.Symbol(n, positive=True) for n in own}
    system = {}
    for mn, (mbind, mbody) in maps.items():
        env = {}
        for b in mbind:
            key = b.lstrip("_")
            env[b] = syms.get(key) or params.get(key)
        if any(v is None for v in env.values()):
            return None
        try:
            expr = conv.convert(mbody, dict(env))
        except Exception:
            return None
        # which state does this map compute?  the one it does NOT read
        # linearly on the right is ambiguous, so use the map's own name
        target = None
        for n in state_names:
            if n.lower() in mn.lower():
                target = n
                break
        if target is None:
            # fall back: the state absent from its own binder list as a
            # non-underscored argument
            cands = [b.lstrip("_") for b in mbind if b.startswith("_")]
            target = cands[0] if cands else None
        if target is None or target in system:
            return None
        system[target] = expr
    if len(system) != len(state_names):
        return None
    sols, info = FP.joint_fixed_point(system, syms)
    if not sols:
        return "JOINT_SOLVE_FAILED", {"equations": info.get("equations")}
    # compare each claimed sibling equilibrium against the joint solution
    claims, agree = {}, True
    for n in state_names:
        sib = next((x for x in decls if x["kind"] == "def" and x["module"] == d["module"]
                    and x["name"] in equilibrium_names and x["name"].endswith(n)), None)
        if sib is None:
            continue
        try:
            cl = conv.convert(sib["body"], {b: params[b] for grp, ty, op in sib["binders"]
                                            if op == "(" for b in grp if b in params})
        except Exception:
            continue
        claims[sib["name"]] = sp.sstr(cl)
        got = sols[0].get(n)
        if got is None or sp.simplify(got - cl) != 0:
            agree = False
    return (("joint_fixed_point_verified" if agree else "JOINT_FIXED_POINT_FAILS"),
            {"joint_equations": info.get("equations"),
             "joint_solution": {k: sp.sstr(v) for k, v in sols[0].items()},
             "claims": claims})


def run():
    decls, table = load()
    conv = L.Converter(table)
    thms = [d for d in decls if d["kind"] == "theorem"]

    guards: dict[str, dict] = {}
    for t in thms:
        if t["name"].endswith("_isFixedPoint"):
            base = t["name"][: -len("_isFixedPoint")].split(".")[-1]
            guards.setdefault(base, t)

    # definitions from the shared parse; theorems still from the local one,
    # because the shared API does not expose theorem statements yet
    sdefs = shared.def_records()
    targets = [d for d in sdefs if d["body"] and EQ_NAME.search(d["name"])]
    equilibrium_names = {d["name"] for d in targets}

    results = []
    for d in targets:
        name = d["name"]
        rec = {
            "fqn": f'{d["module"]}.{name}',
            "name": name, "module": d["module"],
            "file": d["file"], "line": d["line"],
            "check": "check1_fixed_point",
            "guard_theorem": guards.get(name, {}).get("name"),
            "status": None, "detail": {},
        }
        try:
            rec["detail"]["claimed"] = sp.sstr(conv.convert(d["body"]))
        except L.Unsupported as e:
            rec["detail"]["claimed"] = None
            rec["detail"]["claimed_opaque"] = str(e)

        # --- is this a quantity DERIVED from equilibria rather than a rest
        # point itself?  An F_ST is a ratio of coalescence times; it is not the
        # fixed point of anything, and checking it as one produced two of the
        # five false positives in the first run.
        built_on = [n for n in FP.is_derived_from(d["body"], table, equilibrium_names)
                    if n != name]
        if built_on and name not in guards:
            rec["status"] = "derived_from_equilibrium"
            rec["detail"]["built_on"] = built_on
            # verify differently: substitute the equilibria in and compare the
            # body against the closed form the docstring/definition claims
            rec["detail"]["substituted"] = rec["detail"].get("claimed")
            results.append(rec)
            continue

        thm = guards.get(name)
        if thm:
            rec["detail"]["guard_statement"] = " ".join(thm["body"].split())
            check_guarded(conv, thm, rec)
            m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_.']*)", thm["body"])
            map_name = m.group(1).split(".")[-1] if m else None
            if map_name in table:
                rec["detail"]["map"] = map_name
                # Root analysis is only meaningful when the map is a self-map in
                # its final argument and that argument is *this* equilibrium.
                # `twoDemeIMEquilibriumDelta` is guarded by a theorem whose head
                # is Hudson's ratio, not a self-map; solving `hudson(x) = x`
                # there would answer a question nobody asked.
                if _is_self_map_in_last_arg(thm["body"], map_name, name, table):
                    state_var_analysis(conv, table, map_name, name, rec)
                else:
                    rec["detail"]["root_analysis_skipped"] = (
                        "guard theorem is not a self-map in its final argument")
        else:
            # unguarded: accept only an explicitly named map
            named = [b.split(".")[-1] for b in backticked(d["docstring"])
                     if b.split(".")[-1] in table and MAP_NAME.search(b.split(".")[-1])]
            if len(named) > 1:
                jres = try_joint(conv, table, d, named, decls, equilibrium_names)
                if jres is not None:
                    rec["status"], extra = jres
                    rec["detail"].update(extra)
                    results.append(rec)
                    continue
            if not named:
                rec["status"] = "no_fixed_point_theorem"
                results.append(rec)
                continue
            map_name = named[0]
            rec["detail"]["map"] = map_name
            mbind, mbody = table[map_name]
            binders = [n for grp, ty, op in d["binders"]
                       if op == "(" and ty.strip() in ("ℝ", "ℕ") for n in grp]
            if len(mbind) != len(binders) + 1:
                rec["status"] = "UNGUARDED_ARITY_MISMATCH"
                rec["detail"]["map_binders"] = mbind
                rec["detail"]["eq_binders"] = binders
                results.append(rec)
                continue
            # Anti-capture: bind the map's parameters to the equilibrium's by
            # NAME.  Zipping them positionally is how an earlier version
            # substituted `M` into the slot Hudson's ratio reserves for
            # `ETss`, silently checking a formula nobody wrote.
            if mbind[:-1] != binders:
                rec["status"] = "UNGUARDED_BINDERS_DO_NOT_CORRESPOND"
                rec["detail"]["map_binders"] = mbind
                rec["detail"]["eq_binders"] = binders
                results.append(rec)
                continue
            try:
                syms = {b: sp.Symbol(b, real=True) for b in mbind}
                step = conv.convert(mbody, dict(syms))
                step = step.subs({syms[a]: sp.Symbol(b, real=True)
                                  for a, b in zip(mbind[:-1], binders)}, simultaneous=True)
                claimed = conv.convert(d["body"])
            except L.Unsupported as e:
                rec["status"] = "opaque_map"
                rec["detail"]["reason"] = str(e)
                results.append(rec)
                continue
            var = syms[mbind[-1]]
            rec["detail"]["step"] = sp.sstr(step)
            verdict, vinfo = H.verdict_for(step.subs(var, claimed), claimed,
                                           d["binders"], conv)
            rec["detail"]["residual"] = sp.sstr(
                sp.simplify(sp.together(step.subs(var, claimed) - claimed)))
            if verdict is True:
                rec["status"] = "UNGUARDED_but_verified"
            elif verdict is False:
                # Not the exact root -- but is it the exact root's leading
                # term?  "Linearised" and "wrong" are different findings.
                roots = []
                try:
                    roots = [sp.simplify(r) for r in
                             sp.solve(sp.Eq(sp.together(step - var), 0), var)]
                except Exception:
                    pass
                rec["detail"]["exact_roots"] = [sp.sstr(r) for r in roots]
                params = [sp.Symbol(b, positive=True) for b in binders]
                lin = []
                for r in roots:
                    lin = FP.linearisation_verdict(claimed, r, params)
                    if lin:
                        rec["detail"]["linearised_from_root"] = sp.sstr(r)
                        break
                if lin:
                    rec["status"] = "HOLDS_TO_FIRST_ORDER"
                    rec["detail"]["regimes"] = lin[:4]
                else:
                    rec["status"] = "FIXED_POINT_FAILS"
                    rec["detail"]["correct_closed_form"] = [sp.sstr(r) for r in roots]
                    rec["detail"]["witness"] = vinfo.get("witness")
            else:
                rec["status"] = "inconclusive"
            state_var_analysis(conv, table, map_name, name, rec)
        results.append(rec)
    return results


def main():
    res = run()
    (HERE / "results_check1.json").write_text(
        json.dumps(res, indent=1, ensure_ascii=False))
    c = Counter(r["status"] for r in res)
    print(f"CHECK 1: {len(res)} equilibrium/rest-point definitions")
    for k, v in sorted(c.items(), key=lambda kv: -kv[1]):
        print(f"  {k:26s} {v}")
    print()
    for r in res:
        if r["status"] in ("FIXED_POINT_FAILS", "IRRELEVANT_ROOT", "inconclusive"):
            print(f'!! {r["status"]}  {r["fqn"]}  ({r["file"].split("/")[-1]}:{r["line"]})')
            for k in ("claimed", "map", "step", "lhs_map_applied", "rhs_claimed",
                      "residual", "correct_closed_form"):
                if r["detail"].get(k) is not None:
                    print(f'   {k:20s}: {r["detail"][k]}')
            print()
    # root-relevance findings, reported whether or not the algebra held
    print("--- multiple rest points (relevance question Lean does not ask) ---")
    for r in res:
        mr = r["detail"].get("multiple_roots")
        if mr:
            print(f'   {r["fqn"]}: roots {mr}')
            for s in r["detail"].get("root_stability", []):
                print(f'      {s["root"]:40s} {s["stability"]}')
    print()
    print(f'unguarded equilibrium claims: '
          f'{sum(1 for r in res if str(r["status"]).startswith("UNGUARDED"))}')


if __name__ == "__main__":
    main()
