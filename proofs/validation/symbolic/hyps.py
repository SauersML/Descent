"""Hypothesis-aware equality testing.

The first version of CHECK 2 reported six disagreements and every one of them
was the checker throwing away the theorem's hypotheses: `|slope - 1| = 1 -
slope` is false in general and true under `slope < 1`; `max 0 x = 0` is false
in general and true under the swamping condition; `log p - log q = log (p/q)`
needs positivity.  A validator that discards information and then reports a
defect is worse than useless, so nothing here calls a disagreement without a
concrete parameter point that satisfies every hypothesis it could parse and
still separates the two sides -- and if any hypothesis could *not* be parsed,
the verdict is downgraded to inconclusive rather than reported.
"""

from __future__ import annotations

import random
import sympy as sp

import leansym as L


def parse_hypotheses(binders, conv):
    """Return (parsed_relationals, unparsed_texts) from a declaration's binders.

    A binder is a hypothesis when its type is a proposition -- here, when it
    contains a relational operator.
    """
    rels, unparsed = [], []
    for names, ty, opener in binders:
        t = ty.strip()
        if not any(op in t for op in ("=", "≤", "≥", "<", ">", "≠")):
            continue
        if t.startswith("∀") or t.startswith("∃") or "→" in t:
            unparsed.append(t)
            continue
        try:
            r = conv.convert(t)
        except Exception:
            unparsed.append(t)
            continue
        if isinstance(r, sp.logic.boolalg.BooleanFunction) or r.is_Relational:
            rels.append(r)
        elif r is sp.true or r is sp.false:
            rels.append(r)
        else:
            unparsed.append(t)
    return rels, unparsed


def type_domains(binders):
    """Symbols declared `ℕ` are nonnegative integers; note them for sampling."""
    nats = set()
    for names, ty, opener in binders:
        if ty.strip() == "ℕ":
            nats.update(names)
    return nats


def equal_under(lhs, rhs, hyps, nats=(), trials=4000, need=12, seed=20260801):
    """Decide lhs == rhs on the region cut out by `hyps`.

    Returns (verdict, info) where verdict is True / False / None.  A False
    verdict always carries a witness point satisfying every hypothesis.
    """
    # substitute equality hypotheses of the form `x = expr`
    subs = {}
    remaining = []
    for h in hyps:
        if isinstance(h, sp.Eq):
            # solve for any symbol the equality determines, not just a bare
            # `x = e`: `q_A - q_B = p_A - p_B` constrains a measure-zero set,
            # so sampling can never satisfy it by chance.
            target = None
            for s in sorted(h.free_symbols, key=str):
                if s in subs:
                    continue
                try:
                    sols = sp.solve(h, s, dict=False)
                except Exception:
                    continue
                if len(sols) == 1 and s not in sols[0].free_symbols:
                    target, expr = s, sols[0]
                    break
            if target is not None:
                subs[target] = expr
                continue
        remaining.append(h)
    # chase substitutions to a fixed point so they do not reintroduce each other
    for _ in range(len(subs)):
        subs = {k: v.subs(subs, simultaneous=True) for k, v in subs.items()}
    if subs:
        lhs, rhs = lhs.subs(subs, simultaneous=True), rhs.subs(subs, simultaneous=True)
        remaining = [h.subs(subs, simultaneous=True) for h in remaining]

    # cheap symbolic pass first
    try:
        d = sp.simplify(sp.together(lhs - rhs))
        if d == 0:
            return True, {"method": "symbolic"}
    except Exception:
        pass

    syms = sorted(lhs.free_symbols | rhs.free_symbols
                  | set().union(*[h.free_symbols for h in remaining]) if remaining
                  else lhs.free_symbols | rhs.free_symbols, key=str)
    syms = [s for s in syms if s.is_Symbol]
    if not syms:
        try:
            v = complex(sp.N(lhs - rhs))
            return (abs(v) < 1e-12), {"method": "constant"}
        except Exception:
            return None, {"method": "constant_failed"}

    # Compile everything once; symbolic substitution per sample is far too slow
    # to run over the whole corpus.
    import cmath

    def compile_(e):
        try:
            return sp.lambdify(syms, e, modules=["cmath", "math"])
        except Exception:
            return None

    f_lhs, f_rhs = compile_(lhs), compile_(rhs)
    f_hyps = [compile_(h) for h in remaining]
    if f_lhs is None or f_rhs is None or any(f is None for f in f_hyps):
        return None, {"method": "lambdify_failed"}

    rng = random.Random(seed)
    accepted = 0
    for _ in range(trials):
        vals = []
        for s in syms:
            if str(s) in nats:
                vals.append(float(rng.randint(0, 6)))
            else:
                vals.append(rng.randint(-300, 300) / rng.randint(1, 200))
        try:
            if not all(bool(f(*vals)) for f in f_hyps):
                continue
        except Exception:
            continue
        try:
            a, b = complex(f_lhs(*vals)), complex(f_rhs(*vals))
        except Exception:
            continue
        if any(z != z or abs(z) == float("inf") for z in (a, b)):
            continue
        # a point where a side leaves the reals is a domain artefact, not a
        # disagreement
        if abs(a.imag) > 1e-9 or abs(b.imag) > 1e-9:
            continue
        accepted += 1
        if abs(a - b) > 1e-7 * max(1.0, abs(a), abs(b)):
            return False, {"method": "witness",
                           "witness": {str(k): repr(v) for k, v in zip(syms, vals)},
                           "lhs_value": a.real, "rhs_value": b.real,
                           "accepted_points": accepted}
        if accepted >= need * 8:
            break
    if accepted < need:
        return None, {"method": "too_few_admissible_points", "accepted": accepted}
    return True, {"method": "numeric", "accepted_points": accepted}


def verdict_for(lhs, rhs, binders, conv, extra_hyps=()):
    """Full pipeline: parse hypotheses, decide, and downgrade when information
    was discarded."""
    hyps, unparsed = parse_hypotheses(binders, conv)
    hyps = list(hyps) + list(extra_hyps)
    nats = type_domains(binders)
    v, info = equal_under(lhs, rhs, hyps, nats)
    info["hypotheses"] = [sp.sstr(h) for h in hyps]
    info["unparsed_hypotheses"] = unparsed
    if v is False and unparsed:
        # we could not model every constraint; the witness may violate one
        return None, dict(info, method="inconclusive_unparsed_hypotheses")
    return v, info
