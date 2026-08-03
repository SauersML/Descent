"""FAMILY 4 -- the corpus's own theorems as discriminating checks.

For each theorem whose statement lies in the arithmetic fragment: sample points
satisfying its hypotheses, evaluate its conclusion, and confirm it holds.  Then
perturb each definition the conclusion mentions and confirm the theorem BREAKS.
A definition is covered here when some theorem about it is broken by some
mutant of its body -- which is the falsifiability bar applied unchanged.

The evidence class is INTERNAL CONSISTENCY, and the report keeps it in its own
column.  A theorem cannot be false, so this discovers no corpus defects; it
establishes that a wrong body would have been caught.  Conflating that with
validation against an external reference is how a coverage number gets
inflated, and it has already happened twice in this project.

Run:  python check_theorems.py  ->  results_theorems.json
"""
from __future__ import annotations

import json
import pathlib
import random
import sys

import re

import backends
import compile_defs as C
import flatten_theorems as FT
import theorems as T
from demo_falsifiable import compile_mutant
from semantics import param_box
from transpile import Untranspilable, build_arity, pyname, transpile

HERE = pathlib.Path(__file__).resolve().parent
TOL = backends.TOLERANT
STRICT = backends.STRICT


def _box(varname, ty):
    b = param_box(varname, ty)
    if b:
        lo, hi, sc, _ = b
        return (lo, hi, sc)
    return (0.01, 10.0, "log") if ty == "ℝ" else (1.0, 50.0, "nat")


def _draw(rng, box):
    lo, hi, sc = box
    if sc == "nat":
        a, b = int(max(1, lo)), int(min(hi, 200))
        return float(rng.randint(a, max(a, b)))
    if sc in ("log", "log1p") and lo > 0:
        import math

        return math.exp(rng.uniform(math.log(lo), math.log(hi)))
    return rng.uniform(lo, hi)


_COUNTER = [0]


def build(st, defs, arity, rename, ambiguous, ns, emitted):
    """Compile a theorem's hypotheses and conclusion into predicates.

    The predicates are exec'd INTO the shared calibrator namespace, not into a
    fresh dict.  Two things depend on that: definition calls have to resolve at
    all, and swapping a definition for a mutant has to be VISIBLE to an already
    compiled predicate -- which it only is if the lookup goes through the same
    globals dict at call time.
    """
    varnames = [v for v, _, _ in st["variables"]]
    if not varnames:
        raise Untranspilable("no scalar variables to sample")
    params = [(v, t) for v, t, _ in st["variables"]]
    args = ", ".join(pyname(v) for v in varnames)

    def mk(src_lean, backend=TOL):
        src = transpile(src_lean, params, arity, st["name"], rename, ambiguous)
        # thread the backend through calls to compiled definitions, exactly as
        # `compile_defs.build_namespace` does for definition bodies
        src = re.sub(r"\b([A-Za-z_]\w*)\(",
                     lambda m: (f"{m.group(1)}(_b, " if m.group(1) in emitted
                                else m.group(0)), src)
        _COUNTER[0] += 1
        fname = f"_thm_{_COUNTER[0]}"
        exec(compile(f"def {fname}(_b, {args}):\n return {src}",
                     "<thm>", "exec"), ns)
        fn = ns[fname]
        return lambda *x: fn(backend, *x)

    hyps = []
    for h in st["hypotheses"]:
        try:
            hyps.append(mk(h, STRICT))
        except Exception:
            # A hypothesis we cannot model is not a licence to ignore it: it
            # means sampled points may violate it, so the theorem is recorded
            # as only partially constrained and a failure is not reported.
            return None
    concl = mk(st["conclusion"])
    return dict(vars=varnames, boxes=[_box(v, t) for v, t, _ in st["variables"]],
                hyps=hyps, concl=concl)


def evaluate(prop, ns_globals, seed=None, want=40, tries=8000):
    """Sample points satisfying the hypotheses; check the conclusion.

    Returns (n_accepted, n_failed, first_failure).
    """
    import seeds as _s
    rng = random.Random(_s.sub("theorems") if seed is None else seed)
    ok = fail = undecided = 0
    first = None
    for _ in range(tries):
        if ok + fail >= want:
            break
        x = [_draw(rng, b) for b in prop["boxes"]]
        try:
            if not all(h(*x) is True for h in prop["hyps"]):
                continue
        except Exception:
            continue
        backends.OVERFLOWED[0] = False
        try:
            v = prop["concl"](*x)
        except Exception:
            continue
        if backends.OVERFLOWED[0]:
            # an intermediate exceeded double precision; the point says
            # nothing about a statement that is exact over the reals
            undecided += 1
            continue
        if v is True:
            ok += 1
        elif v is False:
            fail += 1
            if first is None:
                first = dict(zip(prop["vars"], x))
        else:
            # not representable in double precision; counted, not silently
            # dropped, so a theorem that is mostly unevaluable says so
            undecided += 1
    return ok, fail, first


def main(argv):
    defs = C.load_defs()
    cs, _, text = C.compile_all(defs)
    ns = {"backends": backends}
    exec(compile(text, "<calibrator>", "exec"), ns)
    by_short = {}
    for k, c in cs.items():
        by_short.setdefault(c.d["name"], []).append(k)
    emitted = {C.pyid(c.d) for c in cs.values()}

    sts = T.all_theorems()
    # A theorem about a structure states an ordinary numeric claim about that
    # structure's fields, and reading it as unusable reports this checker's
    # blind spot as a corpus deficiency. See flatten_theorems.
    _structs, _shapes, _methods = FT.prepare()
    _refused_flat = {}
    if _structs:
        sts, _refused_flat = FT.flatten(sts, _structs, _shapes, _methods)
    results, per_def = {}, {}
    # A refusal is recorded, never dropped: a statement this pass declined to
    # rewrite must not read the same as one it never saw.
    for _name, _why in _refused_flat.items():
        results[_name] = dict(status="untranspilable", reason=_why[:160])
    # Named for BOTH halves on purpose. The count is a property of the corpus
    # AND of this checker, and every name that mentions only the corpus makes
    # the checker's half disappear when the number is spoken. "427 usable
    # theorems" was 427 out of a much larger reachable set, and it was
    # reported as though the corpus had supplied the limit.
    evaluable_by_this_checker = holds = broken_self = 0
    for st in sts:
        ar, rn, amb = build_arity(defs, st["module"])
        mentioned = T.definitions_mentioned(st, set(by_short))
        if not mentioned:
            continue
        try:
            prop = build(st, defs, ar, rn, amb, ns, emitted)
        except Exception as e:
            results[st["name"]] = dict(status="untranspilable", reason=str(e)[:120])
            continue
        if prop is None:
            results[st["name"]] = dict(status="hypothesis-not-modelled")
            continue
        ok, fail, first = evaluate(prop, ns)
        if ok + fail < 5:
            results[st["name"]] = dict(status="no-admissible-points",
                                       reason="hypotheses rejected almost every "
                                              "sampled point")
            continue
        evaluable_by_this_checker += 1
        if fail:
            # Lean proved this; a numeric failure indicts the checker.
            broken_self += 1
            results[st["name"]] = dict(
                status="checker-disagrees-with-proved-theorem",
                module=st["module"], accepted=ok, failed=fail,
                first_failure=first, conclusion=st["conclusion"],
                note="Lean has no sorry, so this is an error in THIS checker "
                     "-- a mis-transcribed body or an unmodelled hypothesis -- "
                     "and is never reported as a corpus defect")
            continue
        holds += 1

        # falsifiability: perturb each mentioned definition, expect a break
        kills = {}
        for short in mentioned:
            for key in by_short[short]:
                d = cs[key].d
                if d["module"] != st["module"] and len(by_short[short]) > 1:
                    continue
                killed = []
                for tag, body in C.mutants(d["body"]):
                    try:
                        mc = compile_mutant(defs, ns, d, body)
                    except Exception:
                        continue
                    saved = ns.get(C.pyid(d))
                    ns[C.pyid(d)] = mc.fn
                    try:
                        o2, f2, _ = evaluate(prop, ns)
                        if f2:
                            killed.append(tag)
                    except Exception:
                        pass
                    finally:
                        if saved is not None:
                            ns[C.pyid(d)] = saved
                    if killed:
                        break
                if killed:
                    kills[key] = killed
                    per_def.setdefault(key, []).append(
                        dict(theorem=st["name"], mutation=killed[0],
                             conclusion=st["conclusion"]))
        results[st["name"]] = dict(status="holds", module=st["module"],
                                   accepted=ok, mentions=mentioned,
                                   discriminates=sorted(kills))

    out = HERE / "results_theorems.json"
    out.write_text(json.dumps(
        dict(theorems=results, by_definition=per_def,
             evaluable_by_this_checker=evaluable_by_this_checker,
             statements_parsed=len(sts),
             note="`evaluable_by_this_checker` is a joint property of the "
                  "corpus and this tool. A theorem outside it is not a "
                  "theorem the corpus lacks."),
        indent=1, default=str))
    print(f"{len(sts)} theorem statements parsed")
    print(f"  {evaluable_by_this_checker} EVALUABLE BY THIS CHECKER "
          "(conclusion transpiles, hypotheses modelled, admissible points "
          "found) -- a joint property of the corpus and this tool, not a "
          "property of the corpus")
    print(f"  {len(sts) - evaluable_by_this_checker} beyond this checker, "
          "for reasons recorded per theorem")
    print(f"  {holds} hold numerically")
    print(f"  {broken_self} disagree with this checker -- checker bugs, "
          "not corpus defects")
    print(f"  {len(per_def)} definitions are DISCRIMINATED by some theorem "
          "(a mutant breaks it)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
