"""CHECK 4 -- approximation and limiting-form claims.

Two arms.

  DOCSTRING CLAIMS.  Docstrings that assert an approximation ("reduces to X
  when Y", "to first order", "agree to leading order", "in the limit") and name
  a comparison target that resolves to another definition.  The claim is tested
  by series expansion in the regime variable.

  UNSTATED REGIMES.  For every pair of definitions that denote the same concept
  but are *different functions* (CHECK 3's output), search for a regime -- some
  parameter to 0 or to infinity -- in which they do agree to leading order.  A
  pair that agrees only in a limit is a linearisation and an exact form living
  under one name; if neither docstring states the regime, that is the shape of
  the error which propagated into three files here, and it is reported even
  though both definitions are individually defensible.

The regime search is deliberately small (each variable to 0 and to infinity,
one at a time).  It is a detector, not a proof: a pair it does not reconcile
may still be reconcilable in a joint limit.
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

APPROX_DOC = re.compile(
    r"(reduces to|reduce to|to first order|leading order|first-order|"
    r"approximately|approximation|in the limit|for small|for large|"
    r"when .{0,30} is (small|large|negligible)|≈|~=|linearis|lineariz|"
    r"drops? terms|dropping terms|O\(|order )", re.I)
REGIME_DOC = re.compile(
    r"(limit|regime|for small|for large|to first order|leading order|"
    r"negligible|approximation|assumes?|valid when|only after dropping|"
    r"O\(|infinite-island|asymptotic)", re.I)


def canonical(conv, d):
    binders = [n for grp, ty, op in d["binders"] if op == "(" for n in grp]
    real_binders = [n for grp, ty, op in d["binders"]
                    if op == "(" and ty.strip() in ("ℝ", "ℕ", "ℚ") for n in grp]
    if binders != real_binders:
        return None, None
    env = {b: sp.Symbol(b, positive=True) for b in binders}
    try:
        e = conv.convert(d["body"], dict(env))
    except Exception:
        return None, None
    if e.is_Relational or isinstance(e, sp.logic.boolalg.BooleanAtom):
        return None, None
    return e, binders


def agrees_in_limit(a, b, var, to):
    """Do a and b share a leading term as `var -> to`?  Returns a verdict and
    the ratio limit, which is 1 exactly when they agree to leading order."""
    try:
        r = sp.limit(sp.together(a / b), var, to)
    except Exception:
        return None, None
    try:
        r = sp.simplify(r)
    except Exception:
        pass
    if r == 1:
        return True, r
    return False, r


def find_regime(a, b, binders, max_vars=6):
    """Search single-variable limits for one that reconciles a and b."""
    out = []
    for name in binders[:max_vars]:
        v = sp.Symbol(name, positive=True)
        if v not in (a.free_symbols | b.free_symbols):
            continue
        for to, label in ((0, f"{name} -> 0"), (sp.oo, f"{name} -> infinity")):
            ok, ratio = agrees_in_limit(a, b, v, to)
            if ok:
                # how fast do they separate away from the limit?
                order = None
                try:
                    diff = sp.simplify(a - b)
                    s = sp.series(diff, v, 0, 4).removeO() if to == 0 else None
                    if s is not None and s != 0:
                        order = sp.sstr(sp.LT(sp.expand(s), v)) if False else sp.sstr(s)
                except Exception:
                    pass
                out.append({"regime": label, "ratio_limit": sp.sstr(ratio),
                            "leading_difference": order})
    return out


def run():
    decls = json.load(open(HERE / "decls.json"))
    table = shared.build_table()
    conv = L.Converter(table)
    defs = {d["name"]: d for d in decls if d["kind"] == "def"}

    exprs = {}
    for d in shared.def_records():
        if not d["body"]:
            continue
        e, b = canonical(conv, d)
        if e is not None:
            exprs[f'{d["module"]}.{d["name"]}'] = (d, e, b)

    results = []

    # ---- arm 1: docstring approximation claims naming another definition
    for fqn, (d, e, b) in exprs.items():
        doc = d["docstring"] or ""
        if not APPROX_DOC.search(doc):
            continue
        targets = [t.split(".")[-1] for t in
                   re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)", doc)]
        targets = [t for t in set(targets)
                   if t in table and t != d["name"] and f'{d["module"]}.{t}' in exprs
                   or (t in table and t != d["name"])]
        for t in targets:
            other = None
            for ofqn, (od, oe, ob) in exprs.items():
                if od["name"] == t:
                    other = (od, oe, ob)
                    break
            if other is None:
                continue
            od, oe, ob = other
            # Align binders by NAME, never by position.  An earlier version
            # renamed positionally and compared `islandFstMultiplicativeStep
            # (Ne m F)` against a definition whose arguments are ordered
            # differently, producing five "unsupported approximation" reports
            # that were purely an artefact of swapping Ne with m.
            if sorted(ob) != sorted(b):
                results.append({"check": "check4_docstring_approximation",
                                "fqn": fqn, "file": d["file"], "line": d["line"],
                                "compared_to": f'{od["module"]}.{od["name"]}',
                                "status": "skipped_binders_do_not_correspond",
                                "binders": b, "other_binders": ob})
                continue
            oe2 = oe
            v, info = H.equal_under(e, oe2, [], ())
            rec = {"check": "check4_docstring_approximation",
                   "fqn": fqn, "file": d["file"], "line": d["line"],
                   "compared_to": f'{od["module"]}.{od["name"]}',
                   "expr": sp.sstr(e), "other_expr": sp.sstr(oe2)}
            if v is True:
                rec["status"] = "exactly_equal"
            else:
                params = [sp.Symbol(x, positive=True) for x in b]
                lin = FP.linearisation_verdict(e, oe2, params)
                if not lin:
                    lin = FP.linearisation_verdict(oe2, e, params)
                rec["status"] = ("approximation_holds_in_regime" if lin
                                 else "APPROXIMATION_UNSUPPORTED")
                rec["regimes"] = lin[:4]
                rec["regime_stated_in_docstring"] = bool(REGIME_DOC.search(doc))
            results.append(rec)

    # ---- arm 2: name-mates that differ -- is one a linearisation of the other?
    try:
        c3 = json.load(open(HERE / "results_check3.json"))
    except FileNotFoundError:
        c3 = {"disagreements": []}
    for dis in c3["disagreements"]:
        fa, fb = dis["a"]["fqn"], dis["b"]["fqn"]
        if fa not in exprs or fb not in exprs:
            continue
        da, ea, ba = exprs[fa]
        db, eb, bb = exprs[fb]
        # Align by name here too.  Positional renaming across definitions with
        # different argument meanings is what turned `admixtureLDMagnitude`
        # into the nonsense `(1 - p_B)**q_B`.
        if sorted(ba) != sorted(bb):
            continue
        eb2 = eb
        params = [sp.Symbol(x, positive=True) for x in ba]
        regimes = [g for g in FP.linearisation_verdict(ea, eb2, params)
                   if (g["agree_to_order"] or 0) >= 1][:4]
        if not regimes:
            continue
        doca, docb = da["docstring"] or "", db["docstring"] or ""
        results.append({
            "check": "check4_unstated_regime",
            "status": ("LINEARISATION_WITHOUT_STATED_REGIME"
                       if not (REGIME_DOC.search(doca) or REGIME_DOC.search(docb))
                       else "linearisation_regime_stated"),
            "a": {"fqn": fa, "line": da["line"], "file": da["file"],
                  "expr": sp.sstr(ea), "regime_stated": bool(REGIME_DOC.search(doca))},
            "b": {"fqn": fb, "line": db["line"], "file": db["file"],
                  "expr": sp.sstr(eb2), "regime_stated": bool(REGIME_DOC.search(docb))},
            "regimes": regimes,
        })
    return results


def main():
    res = run()
    (HERE / "results_check4.json").write_text(json.dumps(res, indent=1, ensure_ascii=False))
    c = Counter(r["status"] for r in res)
    print(f"CHECK 4: {len(res)} approximation/limit claims tested")
    for k, v in sorted(c.items(), key=lambda kv: -kv[1]):
        print(f"  {k:38s} {v}")
    print()
    for r in res:
        if r["status"] == "APPROXIMATION_UNSUPPORTED":
            print(f'!! UNSUPPORTED APPROXIMATION  {r["fqn"]}  ({r["file"].split("/")[-1]}:{r["line"]})')
            print(f'   docstring compares it to {r["compared_to"]}')
            print(f'   {r["expr"]}')
            print(f'   {r["other_expr"]}')
            print(f'   no single-variable limit reconciles them')
            print()
    for r in res:
        if r["status"] == "LINEARISATION_WITHOUT_STATED_REGIME":
            print(f'!! LINEARISATION, REGIME NOT STATED')
            print(f'   {r["a"]["fqn"]}:{r["a"]["line"]}  = {r["a"]["expr"]}')
            print(f'   {r["b"]["fqn"]}:{r["b"]["line"]}  = {r["b"]["expr"]}')
            for g in r["regimes"]:
                print(f'      agree as {g["regime"]} to order {g["agree_to_order"]}; '
                      f'leading error O(eps^{g["leading_error_order"]}) '
                      f'coefficient {g["leading_error_coefficient"]}')
            print()
    for r in res:
        if r["status"] == "approximation_holds_in_regime" and not r.get("regime_stated_in_docstring"):
            print(f'!  approximation true only in a limit, regime not stated: '
                  f'{r["fqn"]}:{r["line"]} vs {r["compared_to"]}')
            for g in r["regimes"]:
                print(f'      {g["regime"]}')


if __name__ == "__main__":
    main()
