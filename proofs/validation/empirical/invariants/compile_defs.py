"""Turn the extracted table into callables, one per backend.

`compile_all` returns `{name: Compiled}` where `Compiled.f(backend, *args)`
evaluates the transpiled body.  Definitions calling other definitions are
resolved by emitting every body into ONE namespace, so composition works
without inlining.

`mutate` produces perturbed bodies.  This is the falsifiability instrument:
a check that accepts every mutant of a definition is a check that tests
nothing, and `demo_falsifiable.py` uses it to prove each registered check can
actually fail.
"""
from __future__ import annotations

import json
import pathlib
import re

import backends
from transpile import Untranspilable, build_arity, pyname, transpile


def _lean_sources(_r):
    # `rglob` under Calibrator/ does NOT reach `proofs/Calibrator.lean`, the corpus
    # ROOT, which sits one level above it. A scan blind to the root reported
    # `decaySlope` unreferenced; it was deleted, and `LDDecayMechanism` was then
    # deleted for having lost its only consumer. Both consumers were in the root.
    # `lean_parse.build` carries this `extra` idiom -- keep every scanner in step.
    _r = pathlib.Path(_r)
    _fs = sorted(_r.rglob("*.lean"))
    _x = _r.parent / (_r.name + ".lean")
    if _x.exists():
        _fs.append(_x)
    return _fs



def key(d):
    """Fully-qualified definition key: `Module.name`."""
    return f"{d['module']}.{d['name']}"


def pyid(d):
    return pyname(d["module"] + "_" + d["name"])

HERE = pathlib.Path(__file__).resolve().parent


class Compiled:
    __slots__ = ("d", "py", "names", "fn")

    def __init__(self, d, py, names, fn):
        self.d, self.py, self.names, self.fn = d, py, names, fn

    def __call__(self, backend, *args):
        return self.fn(backend, *args)


class StaleTable(RuntimeError):
    """defs.json is older than the Lean sources it was extracted from."""


def check_fresh(defs_path):
    """Refuse a definition table older than the corpus it describes.

    Running a checker standalone reads whatever `defs.json` is on disk. If the
    corpus has moved since it was written, every signature, body and arity may
    be wrong -- and the failures do not look like staleness. They look like
    the corpus disagreeing with a proved theorem, which is the one shape this
    project treats as important.

    That is exactly what happened: `steppingStoneCharacteristicLength` changed
    its parameters, a stale table kept the old ones, and two theorems reported
    0 accepted / 40 failed against a checker that was evaluating a function
    the corpus no longer contains.

    Refusing is right rather than silently regenerating, because a checker
    that quietly rebuilds its inputs mid-run produces numbers whose
    provenance nobody can reconstruct.
    """
    import os

    if not defs_path.exists():
        return
    table_mtime = defs_path.stat().st_mtime
    newest, newest_src = 0.0, None
    cal = HERE.parents[2] / "Calibrator"
    for src in _lean_sources(cal):
        m = src.stat().st_mtime
        if m > newest:
            newest, newest_src = m, src
    if newest > table_mtime + 1.0:
        raise StaleTable(
            f"{defs_path.name} was written before {newest_src.name} was last "
            f"modified ({newest - table_mtime:.0f}s older than the corpus). "
            "Run extract_defs.py first. Every signature and body in the table "
            "may be wrong, and the failures will look like corpus defects "
            "rather than like staleness."
        )


def load_defs():
    p = HERE / "defs.json"
    check_fresh(p)
    if not p.exists():
        import extract_defs

        ds = extract_defs.harvest_hypotheses(extract_defs.extract_all())
        p.write_text(json.dumps(ds, ensure_ascii=False, indent=1))
        return ds
    return json.loads(p.read_text())


def transpile_all(defs, overrides=None):
    """name -> python-source, for every definition in the arithmetic fragment.

    `overrides` maps a name to a replacement body, used by the mutation
    machinery to rebuild the namespace with one definition perturbed.
    """
    srcs, why_not = {}, {}
    for d in defs:
        bad = [f"{n} : {t}" for n, t in d["params"] if t not in ("ℝ", "ℕ")]
        if d["ret"] != "ℝ" or bad:
            # Name the half of the signature that actually failed.  Printing the
            # return type unconditionally filed 422 structure methods under
            # "non-scalar signature (ℝ)", where the return type was the one part
            # that was fine and the parameter was the model.
            why_not[key(d)] = (
                f"non-scalar parameter ({'; '.join(bad)})" if bad
                else f"non-scalar return ({d['ret']})")
            continue
        # A body that mentions an implicit binder needs a value this tier
        # cannot supply -- Lean infers it from the call site.  Refuse rather
        # than treat the name as an unknown identifier.
        impl = {n for n, _ in d.get("implicit_params", [])}
        if impl and re.search(r"\b(" + "|".join(re.escape(n) for n in impl)
                              + r")\b", d["body"] or ""):
            why_not[key(d)] = ("body references an implicit binder "
                               f"({sorted(impl)}), whose value Lean infers "
                               "from the call site")
            continue
        body = (overrides or {}).get(d["name"], d["body"])
        ar, rn, amb = build_arity(defs, d["module"])
        try:
            srcs[key(d)] = transpile(body, d["params"], ar, d["name"], rn, amb)
        except Untranspilable as e:
            why_not[key(d)] = str(e)
        except Exception as e:  # parser bug, not a corpus property
            why_not[key(d)] = f"internal:{type(e).__name__}:{e}"
    return srcs, why_not


def build_namespace(defs, srcs):
    """Emit all bodies into one module namespace with `_b` threaded through."""
    by = {key(d): d for d in defs}
    lines = ["import backends"]
    for name, src in srcs.items():
        d = by[name]
        args = ", ".join(pyname(p) for p, _ in d["params"])
        sig = f"_b, {args}" if args else "_b"
        lines.append(f"def {pyid(d)}({sig}):")
        lines.append(f"    return {src}")
    # calls to other definitions must forward the backend; rewrite `g(x)` to
    # `g(_b, x)` for every emitted name.
    text = "\n".join(lines)
    emitted = {pyid(by[n]) for n in srcs}
    def fix(m):
        return f"{m.group(1)}(_b, " if m.group(1) in emitted else m.group(0)
    body = re.sub(r"\b([A-Za-z_]\w*)\(", lambda m: fix(m), text)
    # undo the rewrite on the def headers themselves
    body = re.sub(r"^def (\w+)\(_b, _b, ", r"def \1(_b, ", body, flags=re.M)
    body = re.sub(r"^def (\w+)\(_b, _b\)", r"def \1(_b)", body, flags=re.M)
    ns = {"backends": backends}
    exec(compile(body, "<calibrator>", "exec"), ns)
    return ns, body


def compile_all(defs=None, overrides=None):
    defs = defs or load_defs()
    srcs, why_not = transpile_all(defs, overrides)
    ns, text = build_namespace(defs, srcs)
    out = {}
    by = {key(d): d for d in defs}
    for name in srcs:
        d = by[name]
        c = Compiled(d, srcs[name], [p for p, _ in d["params"]], ns[pyid(d)])
        # smoke test: a body that calls a definition we could not compile
        # raises NameError here.  Drop it rather than let it fail mid-search.
        try:
            c(backends.FLOAT, *[0.3] * len(c.names))
        except (NameError, TypeError) as e:
            why_not[name] = f"depends on an uncompiled definition: {e}"
            continue
        except Exception:
            pass  # domain error at 0.3 is fine; the search handles it
        out[name] = c
    return out, why_not, text


# ------------------------------------------------------------------ mutation

MUTATIONS = [
    ("const-off-by-one", lambda b: re.sub(r"\b([2-9])\b", lambda m: str(int(m.group(1)) * 2), b, count=1)),
    ("drop-a-one-minus", lambda b: b.replace("1 - ", "1 + ", 1)),
    ("negate", lambda b: "-(" + b + ")" if "\n" not in b and "let" not in b else None),
    ("swap-plus-minus", lambda b: b.replace(" + ", " - ", 1) if " + " in b else None),
    ("swap-times-div", lambda b: b.replace(" * ", " / ", 1) if " * " in b else None),
    ("drop-max-guard", lambda b: re.sub(r"max\s+0\s+", "", b, count=1) if re.search(r"max\s+0\s+", b) else None),
    ("drop-min-guard", lambda b: re.sub(r"min\s+1\s+", "", b, count=1) if re.search(r"min\s+1\s+", b) else None),
    ("shift-by-half", lambda b: f"({b}) + 0.5" if "\n" not in b and "let" not in b else None),
    ("scale-by-three", lambda b: f"3 * ({b})" if "\n" not in b and "let" not in b else None),
    ("swap-first-two-args", None),  # handled structurally in demo_falsifiable
]


def mutants(body):
    out = []
    for tag, fn in MUTATIONS:
        if fn is None:
            continue
        try:
            m = fn(body)
        except Exception:
            m = None
        if m and m != body:
            out.append((tag, m))
    return out
