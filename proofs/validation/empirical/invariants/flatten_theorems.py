"""Rewrite the corpus's own theorems about structures into the scalar fragment.

WHAT WENT WRONG WITHOUT THIS

`flatten_structures.py` fixed the misfiling on the DEFINITION side: a method of a
structure is a function of that structure's numeric fields, and filing it under
"non-scalar signature" pointed at the wrong half of the signature.  The same
misfiling survived one layer up, on the THEOREM side, and it is worse there
because it is invisible.

`theorems.parse_statement` splits a theorem's binders into scalar VARIABLES and
everything-else HYPOTHESES.  A binder like `(p : EvolutionaryParameters)` is not
scalar, so it becomes a hypothesis whose text is the bare type name.  The
theorem then has no variables to sample and drops out, and `unreachable.py`
reports the definition it constrains as

    no theorem's conclusion mentions it, so the corpus states no property
    of it to check

which is false.  `DGP.migrationLDBoost_ge_one` states `1 ≤ migrationLDBoost p`
and sits eleven lines below the definition.  Fourteen definitions in
`PortabilityDrift` and `DGP` alone were on the work list for a property the
corpus had already proved.

That is the failure mode the rest of this directory is written against: a
measurement that cannot report its own absence eventually reports someone
else's answer as its own.  Here the checker reported ITS OWN blind spot as a
CORPUS deficiency, which is the direction that wastes the most time, because the
suggested repair -- write more theorems -- is work that is already done.

WHAT THIS DOES

For each theorem with a structure binder `p : S` where `S` has scalar fields:

  * the binder becomes one scalar variable per field, named `p_field`, matching
    the names `flatten_structures` gave the flattened definitions;
  * `S`'s constraint fields become hypotheses, with field names rewritten, so
    the sampler never proposes a model the Lean statement excludes;
  * a call `f p x` to a flattened definition becomes `f p_Ne ... p_V_A x`,
    using the `flattened_shape` that pass records;
  * a projection `p.Ne` becomes `p_Ne`.

WHAT IT REFUSES

If any occurrence of the binder name survives all of that -- a bare `p` passed
to something not flattened, a projection to a method this pass could not expand
-- the rewrite is abandoned and the reason recorded.  A half-rewritten statement
would transpile and check the wrong claim, which is the one outcome worse than
not checking it at all.

Abandoning returns the ORIGINAL statement, not nothing.  This pass exists to
make more statements usable; one that could make a statement DISAPPEAR would
trade coverage it never had for coverage the old path already provided, and the
refusal would read as an improvement in every summary that counts what is left.

Run after `flatten_structures.py`, which must have written `defs.json`:

    python3 flatten_theorems.py            # summary
    python3 flatten_theorems.py --why      # what was refused, and why
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
SCALAR = {"ℝ", "ℕ"}
IDENT = re.compile(r"[\w'₀-₉.]")


def _base(type_text: str) -> str:
    return type_text.strip().split()[0] if type_text.strip() else ""


def _short(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def load_shapes(defs: list[dict]) -> dict:
    """`{short definition name: (flattened_shape, full name)}` for flattened defs."""
    out: dict[str, tuple] = {}
    for d in defs:
        if not d.get("flattened_shape"):
            continue
        out.setdefault(_short(d["name"]), (d["flattened_shape"], d["name"]))
    return out


def _read_atom(text: str, i: int) -> tuple[str, int] | None:
    """One atomic argument starting at or after `i`: a parenthesised group or a
    run of identifier characters.  Returns `(atom, end)`, or None at the end of
    the applicable region."""
    while i < len(text) and text[i] == " ":
        i += 1
    if i >= len(text):
        return None
    if text[i] == "(":
        depth, j = 0, i
        while j < len(text):
            if text[j] == "(":
                depth += 1
            elif text[j] == ")":
                depth -= 1
                if depth == 0:
                    return text[i:j + 1], j + 1
            j += 1
        return None
    j = i
    while j < len(text) and IDENT.match(text[j]):
        j += 1
    if j == i:
        return None
    return text[i:j], j


def expand_calls(text: str, shapes: dict, structvars: dict) -> str:
    """`f p x` -> `f p_Ne ... p_V_A x` for every flattened definition `f`."""
    out, i = [], 0
    while i < len(text):
        m = re.compile(r"[A-Za-z][\w'₀-₉]*").match(text, i)
        if not m or m.group(0) not in shapes:
            out.append(text[i])
            i += 1
            continue
        shape, _full = shapes[m.group(0)]
        if not any(s[0] == "struct" for s in shape):
            out.append(m.group(0))
            i = m.end()
            continue
        j, args, ok = m.end(), [], True
        for slot in shape:
            got = _read_atom(text, j)
            if got is None:
                ok = False
                break
            atom, j = got
            if slot[0] == "scalar":
                args.append(atom)
            elif structvars.get(atom) == slot[1]:
                args.extend(f"{atom}_{f}" for f in slot[2])
            else:
                ok = False
                break
        if not ok:
            out.append(m.group(0))
            i = m.end()
            continue
        out.append(m.group(0) + " " + " ".join(args))
        i = j
    return "".join(out)


def load_methods(defs: list[dict]) -> dict:
    """`{(structure, method short name): (short name, field names)}`.

    A flattened definition whose FIRST original slot was a structure is what dot
    notation calls: `m.observedH2` means `observedH2 m`, so once `observedH2` is
    flattened the projection can be rewritten into a call on the fields."""
    out: dict[tuple, tuple] = {}
    for d in defs:
        shape = d.get("flattened_shape")
        if not shape or shape[0][0] != "struct":
            continue
        out.setdefault((shape[0][1], _short(d["name"])),
                       (_short(d["name"]), shape[0][2]))
    return out


def expand_projections(text: str, name: str, base: str, methods: dict) -> str:
    """`m.observedH2` -> `observedH2 m_r m_V_A m_V_P`, leaving later arguments in
    place -- dot notation supplies the structure as the first argument, so the
    remaining ones already sit in the right order."""
    def sub(m):
        got = methods.get((base, m.group(1)))
        if not got:
            return m.group(0)
        short, fields = got
        return short + " " + " ".join(f"{name}_{f}" for f in fields)

    return re.sub(rf"(?<![\w'₀-₉]){re.escape(name)}\.([\w'₀-₉]+)", sub, text)


def _project(text: str, name: str, fields: list[str]) -> str:
    for f in sorted(fields, key=len, reverse=True):
        text = re.sub(
            rf"(?<![\w'₀-₉]){re.escape(name)}\.{re.escape(f)}(?![\w'₀-₉])",
            f"{name}_{f}", text)
    return text


def _rewrite_constraint(text: str, name: str, fields: list[str]) -> str:
    """Bare field names inside a structure constraint become the flat names."""
    for f in sorted(fields, key=len, reverse=True):
        text = re.sub(rf"(?<![\w'₀-₉.]){re.escape(f)}(?![\w'₀-₉])",
                      f"{name}_{f}", text)
    return text


def flatten_one(st: dict, structs: dict, shapes: dict,
                methods: dict) -> tuple[dict | None, str]:
    binders = st.get("binders") or []
    targets = []
    for names, ty, _implicit in binders:
        base = _base(ty)
        info = structs.get(base)
        if info and info["fields"]:
            targets.extend((n, base) for n in names)
    if not targets:
        return st, ""

    structvars = dict(targets)
    concl, hyps = st["conclusion"], list(st["hypotheses"])
    # Projections first: `m.observedH2` has to become a call before `f m` can be
    # recognised as one, because the projection contains the binder name too.
    for name, base in targets:
        concl = expand_projections(concl, name, base, methods)
        hyps = [expand_projections(h, name, base, methods) for h in hyps]
    concl = expand_calls(concl, shapes, structvars)
    hyps = [expand_calls(h, shapes, structvars) for h in hyps]

    variables = list(st["variables"])
    keep: list[str] = []
    for h in hyps:
        if h.strip() in {b for _n, b in targets} or _base(h) in {b for _n, b in targets}:
            continue
        keep.append(h)
    hyps = keep

    for name, base in targets:
        info = structs[base]
        fields = [f for f, _ in info["fields"]]
        concl = _project(concl, name, fields)
        hyps = [_project(h, name, fields) for h in hyps]
        for f, ty in info["fields"]:
            variables.append((f"{name}_{f}", ty, False))
        hyps.extend(_rewrite_constraint(c, name, fields) for c in info["constraints"])

    for name, _base_ in targets:
        leftover = re.search(rf"(?<![\w'₀-₉]){re.escape(name)}(?![\w'₀-₉_])",
                             " ".join([concl] + hyps))
        if leftover:
            return None, (f"`{name}` survives rewriting -- it is passed to something "
                          "this pass could not expand, so the statement would check "
                          "a different claim")

    out = dict(st)
    out["conclusion"] = concl
    out["hypotheses"] = hyps
    out["variables"] = variables
    out["flattened_from_structure"] = True
    return out, ""


def flatten(sts: list[dict], structs: dict, shapes: dict,
            methods: dict | None = None) -> tuple[list[dict], dict]:
    """Every statement comes back.  A refusal returns the ORIGINAL, not nothing:
    this pass exists to make more statements usable, and a pass that can make a
    statement DISAPPEAR would trade coverage it never had for coverage the old
    path already provided."""
    out, refused = [], {}
    for st in sts:
        got, why = flatten_one(st, structs, shapes, methods or {})
        if got is None:
            refused[st["name"]] = why
            out.append(st)
        else:
            out.append(got)
    return out, refused


def prepare() -> tuple[dict, dict, dict]:
    """`(structures, shapes, methods)`, empty if the earlier passes have not run."""
    sp, dp = HERE / "structures.json", HERE / "defs.json"
    if not sp.exists() or not dp.exists():
        return {}, {}, {}
    structs = json.loads(sp.read_text(encoding="utf-8"))
    defs = json.loads(dp.read_text(encoding="utf-8"))
    return structs, load_shapes(defs), load_methods(defs)


def main(argv: list[str]) -> int:
    import theorems as T

    structs, shapes, methods = prepare()
    if not structs:
        print("run extract_defs.py, structures.py and flatten_structures.py first",
              file=sys.stderr)
        return 2
    sts = T.all_theorems()
    flat, refused = flatten(sts, structs, shapes, methods)
    n_flat = sum(1 for s in flat if s.get("flattened_from_structure"))
    n_before = sum(1 for s in sts if s["variables"])
    n_after = sum(1 for s in flat if s["variables"])
    print(f"theorems read ........... {len(sts)}")
    print(f"with a structure binder . {n_flat + len(refused)}")
    print(f"rewritten ............... {n_flat}")
    print(f"refused ................. {len(refused)}")
    print(f"samplable, before ....... {n_before}")
    print(f"samplable, after ........ {n_after}")
    if "--why" in argv:
        for k, v in sorted(refused.items())[:25]:
            print(f"  {k}: {v}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
