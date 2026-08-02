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
    return decls, L.build_table(decls)


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


def run():
    decls, table = load()
    conv = L.Converter(table)
    thms = [d for d in decls if d["kind"] == "theorem"]

    guards: dict[str, dict] = {}
    for t in thms:
        if t["name"].endswith("_isFixedPoint"):
            base = t["name"][: -len("_isFixedPoint")].split(".")[-1]
            guards.setdefault(base, t)

    targets = [d for d in decls if d["kind"] == "def" and d["body"]
               and EQ_NAME.search(d["name"])
               and not NOT_A_REST_POINT.search(d["name"])]

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
            if not named:
                rec["status"] = "UNGUARDED_NO_MAP"
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
            verdict = L.equal(step.subs(var, claimed), claimed)
            rec["detail"]["residual"] = sp.sstr(
                sp.simplify(sp.together(step.subs(var, claimed) - claimed)))
            if verdict is True:
                rec["status"] = "UNGUARDED_but_verified"
            elif verdict is False:
                rec["status"] = "FIXED_POINT_FAILS"
                try:
                    roots = sp.solve(sp.Eq(sp.together(step - var), 0), var)
                    rec["detail"]["correct_closed_form"] = [sp.sstr(sp.simplify(r))
                                                            for r in roots]
                except Exception:
                    pass
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
