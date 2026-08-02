"""Fixed-point machinery: joint systems, derived quantities, and the verdict
between "wrong" and "linearised".

Three capabilities the first version of CHECK 1 lacked, each corresponding to a
class of false positive it produced:

  JOINT SYSTEMS.  `twoDemeIMEquilibriumETss` and `...ETst` are a 2x2 linear
  system: the same-deme map mentions ETst and the different-deme map mentions
  ETss.  Solving either alone, with the other symbol free, validates nothing.
  `joint_fixed_point` collects the sibling maps and solves them together.

  DERIVED QUANTITIES.  An F_ST is not the fixed point of anything; it is a ratio
  formed FROM coalescence times that are themselves fixed points.  Such a
  definition is verified by substituting the equilibria into its body and
  comparing against its claimed closed form -- a real check, and a different
  one.

  LINEARISATION.  The claimed island-model F_ST `1/(1 + 4 Ne m)` is not the
  fixed point of the multiplicative IBD recurrence; it is that fixed point's
  leading term as m -> 0 with 1/(2 Ne) -> 0 at the same rate.  Reporting this as
  a failure is wrong and reporting it as a pass is worse, because the gap is
  exactly the mechanism behind this corpus's documented factor-of-two error at
  two demes.  `linearisation_verdict` searches small/large regimes, and returns
  the order of agreement and the leading error term.
"""

from __future__ import annotations

import itertools
import sympy as sp

EPS = sp.Symbol("_eps", positive=True)


# ------------------------------------------------------------------ joint solve

def joint_fixed_point(maps: dict[str, sp.Expr], state_syms: dict[str, sp.Symbol]):
    """Solve `map_i(states) = state_i` for all i simultaneously.

    `maps` is state-name -> map expression written in the state symbols.
    Returns (solutions, equations).  A solution is a dict state-name -> value.
    """
    eqs, unknowns = [], []
    for name, expr in maps.items():
        s = state_syms[name]
        eqs.append(sp.Eq(sp.together(expr), s))
        unknowns.append(s)
    try:
        sols = sp.solve(eqs, unknowns, dict=True)
    except Exception as e:
        return None, {"error": str(e), "equations": [sp.sstr(e_) for e_ in eqs]}
    out = []
    for sol in sols:
        out.append({n: sp.simplify(sol.get(state_syms[n], state_syms[n]))
                    for n in maps})
    return out, {"equations": [sp.sstr(e_) for e_ in eqs]}


# ------------------------------------------------- derived-from-equilibrium

def referenced_defs(body: str, table) -> list[str]:
    import re
    return [n for n in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", body))
            if n.split(".")[-1] in table]


def is_derived_from(body: str, table, equilibrium_names: set[str]) -> list[str]:
    """Which equilibrium definitions does this body build on?"""
    return sorted({n.split(".")[-1] for n in referenced_defs(body, table)
                   if n.split(".")[-1] in equilibrium_names})


# ------------------------------------------------------------ linearisation

def _rescale(expr, assignments):
    """assignments: symbol -> 'small' | 'large'."""
    sub = {}
    for s, kind in assignments.items():
        sub[s] = EPS * s if kind == "small" else s / EPS
    return expr.subs(sub, simultaneous=True)


def _leading(expr):
    """Leading term of expr as _eps -> 0, or None."""
    try:
        s = sp.series(sp.simplify(expr), EPS, 0, 1)
        s = s.removeO()
        return sp.simplify(s)
    except Exception:
        return None


def linearisation_verdict(claimed, exact, params, max_vars=2, order=3):
    """Is `claimed` the leading term of `exact` in some small/large regime?

    Returns a list of matching regimes, each with the order to which the two
    agree and the leading error term.  An empty list means no regime in the
    search space reconciles them -- which is the genuine-failure signal.
    """
    params = [p for p in params if p in (claimed.free_symbols | exact.free_symbols)]
    hits = []
    for k in range(1, max_vars + 1):
        for combo in itertools.combinations(params, k):
            for kinds in itertools.product(("small", "large"), repeat=k):
                assign = dict(zip(combo, kinds))
                c = _rescale(claimed, assign)
                e = _rescale(exact, assign)
                lc, le = _leading(c), _leading(e)
                if lc is None or le is None:
                    continue
                try:
                    if sp.simplify(lc - le) != 0:
                        continue
                except Exception:
                    continue
                # they share a leading term; find the order of the first
                # disagreement and its coefficient
                err_order, err_term = None, None
                try:
                    diff = sp.simplify(e - c)
                    ser = sp.series(diff, EPS, 0, order)
                    ser = ser.removeO()
                    ser = sp.expand(ser)
                    if ser != 0:
                        poly = sp.Poly(ser, EPS) if ser.has(EPS) else None
                        if poly is not None:
                            terms = [(mon[0], coef) for mon, coef
                                     in zip(poly.monoms(), poly.coeffs())]
                            terms = [t for t in terms if sp.simplify(t[1]) != 0]
                            if terms:
                                err_order, coef = min(terms, key=lambda t: t[0])
                                err_term = sp.sstr(sp.simplify(coef))
                except Exception:
                    pass
                hits.append({
                    "regime": ", ".join(f"{s} -> {'0' if kinds[i] == 'small' else 'infinity'}"
                                        for i, s in enumerate(combo)),
                    "assignments": {str(s): k_ for s, k_ in assign.items()},
                    "agree_to_order": 0 if err_order is None else int(err_order) - 1,
                    "leading_error_order": None if err_order is None else int(err_order),
                    "leading_error_coefficient": err_term,
                })
    # prefer the regime with the fewest rescaled variables, then the highest
    # order of agreement
    hits.sort(key=lambda h: (len(h["assignments"]), -(h["agree_to_order"] or 0)))
    return hits
