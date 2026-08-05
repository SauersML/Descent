"""Flatten structure methods into scalar definitions, carrying their domain along.

WHAT IT IS FOR

`compile_defs.transpile_all` takes a definition only when every parameter and the
return type is `ℝ` or `ℕ`.  422 definitions failed that test with a parameter
that is a model rather than a number:

    AssortativeMatingPGS.AssortativeMatingModel.observedH2   params ['m']  ret ℝ

Nothing about those definitions is unreachable in principle.  `m` is a record of
reals, so the method is a function of those reals, and this pass rewrites it as
one: the parameter becomes its scalar fields and `m.field` in the body becomes
the corresponding variable.

THE PART THAT IS EASY TO GET WRONG

A structure carries two kinds of field.  `MRInstrumentModel` has `n : ℝ` and it
also has `n_pos : 0 < n`.  The first is data; the second is the domain.  Across
the corpus there are 180 data fields and 235 constraint fields, so the domain is
the larger half, and a flattening that kept only the numbers would hand the
sampler a model with a negative sample size.  Every range check downstream would
then report an escape that the Lean statement excludes by construction — a
manufactured defect, which `totality.py` names as the one thing a checking tool
must not do.

So the constraints travel with the fields.  Each becomes a hypothesis of the
flattened definition, with field names rewritten to match, recorded under a
synthetic entry so that its origin stays visible:

    {"thm": "<structure invariant: MRInstrumentModel>", "hyps": ["0 < m_n", ...]}

WHAT IT REFUSES

A body that reaches through the parameter to something other than a field —
typically another structure method — is left alone, with its reason recorded.
Those become flattenable only once the method they call is itself flattened, and
chasing that fixpoint is not attempted here.  Refusing is the honest outcome: a
half-rewritten body would transpile and compute the wrong thing.

Run after `extract_defs.py` and before `compile_defs.py`:

    python3 extract_defs.py
    python3 structures.py
    python3 flatten_structures.py
    python3 compile_defs.py
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
SCALAR = {"ℝ", "ℕ"}


def _base(type_text: str) -> str:
    """`CrossPopulationMetricModel p q` -> `CrossPopulationMetricModel`."""
    return type_text.strip().split()[0] if type_text.strip() else ""


def _rewrite_fields(text: str, prefix: str, fields: list[str]) -> str:
    """`m.het` -> `m_het`, for the named fields only."""
    for f in sorted(fields, key=len, reverse=True):
        text = re.sub(
            rf"(?<![\w'₀-₉]){re.escape(prefix)}\.{re.escape(f)}(?![\w'₀-₉])",
            f"{prefix}_{f}",
            text,
        )
    return text


def _rewrite_constraint(text: str, prefix: str, fields: list[str]) -> str:
    """Rewrite bare field names inside a structure constraint to the flat names."""
    for f in sorted(fields, key=len, reverse=True):
        text = re.sub(
            rf"(?<![\w'₀-₉.]){re.escape(f)}(?![\w'₀-₉])", f"{prefix}_{f}", text
        )
    return text


def _method_key(d: dict) -> str:
    return f"{d['module']}::{d['name']}"


def flatten_once(defs: list[dict], structs: dict,
                 flat_methods: dict) -> tuple[list[dict], dict, dict]:
    """One pass. `flat_methods` maps a single-structure-parameter method to the
    flattened argument names it now expects, so a body calling such a method can
    be rewritten into a call that passes the fields."""
    refused: dict[str, str] = {}
    learned: dict = {}
    out = []
    for d in defs:
        params = d.get("params") or []
        body = d.get("body") or ""
        struct_params = [
            (n, t) for n, t in params if t not in SCALAR and _base(t) in structs
        ]
        if not struct_params or d.get("ret") != "ℝ":
            out.append(d)
            continue
        if any(t not in SCALAR and _base(t) not in structs for n, t in params):
            out.append(d)
            continue

        new_params: list[list[str]] = []
        new_hyps = list(d.get("theorem_hyps") or [])
        ok = True
        for n, t in params:
            if t in SCALAR:
                new_params.append([n, t])
                continue
            info = structs[_base(t)]
            names = [f for f, _ in info["fields"]]
            if not names:
                ok = False
                refused[f"{d['module']}.{d['name']}"] = (
                    f"structure {_base(t)} has no scalar fields to flatten to"
                )
                break
            body = _rewrite_fields(body, n, names)
            # A call to another method of the same structure becomes a call that
            # passes the flattened fields, once that method has itself been
            # flattened.  Until then this leaves the body alone and refuses.
            for (mstruct, msuffix), (mname, argnames) in list(flat_methods.items()):
                if mstruct != _base(t):
                    continue
                args = " ".join(f"{n}_{a.split('_', 1)[1]}" for a in argnames)
                body = re.sub(
                    rf"(?<![\w'₀-₉]){re.escape(n)}\.{re.escape(msuffix)}(?![\w'₀-₉])",
                    f"({mname} {args})",
                    body,
                )
            leftover = re.search(
                rf"(?<![\w'₀-₉]){re.escape(n)}\.([\w'₀-₉]+)", body
            )
            if leftover:
                ok = False
                refused[f"{d['module']}.{d['name']}"] = (
                    f"body reaches through `{n}` to `{leftover.group(1)}`, which is "
                    f"not a field of {_base(t)} -- a structure method, flattenable "
                    "only once that method is"
                )
                break
            for f, ty in info["fields"]:
                new_params.append([f"{n}_{f}", ty])
            cons = [_rewrite_constraint(c, n, names) for c in info["constraints"]]
            if cons:
                new_hyps.append(
                    dict(
                        thm=f"<structure invariant: {_base(t)}>",
                        hyps=cons,
                        argmap={},
                    )
                )
        if not ok:
            out.append(d)
            continue
        # The shape of the ORIGINAL signature, position by position.  A caller
        # that has to rewrite `f p x` into `f p_Ne ... p_V_A x` -- which is what
        # `flatten_theorems` does to the corpus's own theorem statements -- needs
        # to know which argument positions were structures and what they expand
        # to.  The flattened parameter list alone does not say: `p_Ne` and `F`
        # are both just names by then.
        shape = []
        for n, t in params:
            if t in SCALAR:
                shape.append(["scalar", n])
            else:
                shape.append(["struct", _base(t),
                              [f for f, _ in structs[_base(t)]["fields"]]])
        e = dict(d)
        e["params"] = new_params
        e["body"] = body
        e["theorem_hyps"] = new_hyps
        e["flattened_from_structure"] = True
        e["flattened_shape"] = shape
        if len(params) == 1 and params[0][1] not in SCALAR:
            suffix = d["name"].rsplit(".", 1)[-1]
            learned[(_base(params[0][1]), suffix)] = (
                d["name"], [pn for pn, _ in new_params])
        out.append(e)
    return out, refused, learned


def flatten(defs: list[dict], structs: dict) -> tuple[list[dict], dict]:
    """Iterate `flatten_once` to a fixpoint: a method that calls another method
    becomes flattenable as soon as the callee is."""
    flat_methods: dict = {}
    refused: dict = {}
    for _ in range(8):
        defs, refused, learned = flatten_once(defs, structs, flat_methods)
        new = {k: v for k, v in learned.items() if k not in flat_methods}
        flat_methods.update(learned)
        if not new:
            break
    return defs, refused


def main(argv: list[str]) -> int:
    defs_path = HERE / "defs.json"
    structs_path = HERE / "structures.json"
    if not defs_path.exists():
        print("run extract_defs.py first", file=sys.stderr)
        return 2
    if not structs_path.exists():
        print("run structures.py first", file=sys.stderr)
        return 2
    defs = json.loads(defs_path.read_text(encoding="utf-8"))
    structs = json.loads(structs_path.read_text(encoding="utf-8"))
    flat, refused = flatten(defs, structs)
    n_flat = sum(1 for d in flat if d.get("flattened_from_structure"))
    n_hyps = sum(
        len([h for h in (d.get("theorem_hyps") or []) if str(h.get("thm", "")).startswith("<structure")])
        for d in flat
    )
    defs_path.write_text(json.dumps(flat, ensure_ascii=False, indent=1), encoding="utf-8")
    print(f"definitions flattened ... {n_flat}")
    print(f"carrying domains ........ {n_hyps}")
    print(f"refused ................. {len(refused)}")
    if "--why" in argv:
        for k, v in sorted(refused.items())[:20]:
            print(f"  {k}: {v}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
