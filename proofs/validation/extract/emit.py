"""Generate the executable module and the classification table.

    python3 emit.py            # writes defs.json, lean_defs.py, classes.json

`lean_defs.py` is machine-generated from parsed Lean bodies.  Other validation
scripts should import it instead of re-transcribing formulas:

    from validation.extract import lean_defs
    lean_defs.neiFst(0.4, 0.3)
"""
from __future__ import annotations

import json
import math
import pathlib
import collections
import random
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import admissible                        # noqa: E402
import lean_parse                        # noqa: E402
from translate import Untranslatable, pyname, translate_def   # noqa: E402

PROOFS = HERE.parent.parent
_ALL_STRUCTS = {}


# Definitions the corpus states non-arithmetically (measure-theoretic, abstract)
# for which we substitute a numerically equivalent implementation.  Each one is
# a place where the extraction is NOT derived from the Lean body, so every
# dependent is flagged and the reason travels with it.
NUMERIC_STANDINS = {
    "Calibrator.Phi": (
        "def Phi(x):\n    return _rt.Phi(x)",
        ["x"],
        "Mathlib `ProbabilityTheory.cdf (gaussianReal 0 1)` replaced by its erf "
        "form; mathematically equal, but not derived from the Lean body",
    ),
}


# ------------------------------------------------------------- taxonomy

PROP_RETS = {"Prop"}


TYPE_RETS = {"Type", "Type*", "Type _", "Sort*"}


def classify(d, struct_names, def_names, translated):
    """NUMERIC | STRUCTURAL | WRAPPER | NOT-EXTRACTABLE (+ reason)."""
    ret = d["ret_type"]
    body = d["body"].strip()

    if ret in TYPE_RETS or (not ret and ("→" in body or "×" in body)
                            and not any(ch.isdigit() for ch in body)
                            and "(" not in body):
        return "STRUCTURAL", "type alias"
    if body.startswith("{") or re.search(r"^\s*\w[\w'.]*\s*:=", body, re.M):
        return "STRUCTURAL", "structure literal"

    if ret in PROP_RETS or ret.endswith("→ Prop") or ret.startswith("Set "):
        return "STRUCTURAL", "Prop-valued / set-valued"
    if ret in struct_names or ret.split()[0] in struct_names if ret else False:
        return "STRUCTURAL", f"builds a structure value ({ret})"

    if d["name"] in translated:
        # wrapper: body is exactly one application of another definition
        toks = body.split()
        if toks and toks[0].split(".")[-1] in def_names and "(" not in body \
                and all(t.isidentifier() or t.replace("₀", "").isidentifier()
                        for t in toks[1:]):
            return "WRAPPER", f"delegates to {toks[0]}"
        return "NUMERIC", ""
    return "NOT-EXTRACTABLE", translated_reason(d)


def selfcheck_reason(err):
    err = err or ""
    if err.startswith("NameError"):
        import re as _re
        m = _re.search(r"name '(\w+)'", err)
        return f"self-check: calls untranslated definition {m.group(1) if m else '?'}"
    if err.startswith("AttributeError") or err.startswith("KeyError"):
        return f"self-check: structure projection unavailable ({err[:60]})"
    if err.startswith("TypeError"):
        return f"self-check: arity/type mismatch ({err[:60]})"
    if err.startswith("value is not a real"):
        return f"self-check: {err} (vector- or function-valued)"
    return f"self-check: never finite ({err[:60]})"


def translated_reason(d):
    return d.get("_reason", "unknown")


# ------------------------------------------------------------- main

HEADER = '''"""GENERATED FILE -- do not edit.

Produced by validation/extract/emit.py from the Lean sources under
proofs/Calibrator/.  Each function below was translated from the parsed body of
the corresponding Lean `def`; no formula in this file was typed by hand.

Regenerate with:  python3 validation/extract/emit.py
"""
# ruff: noqa
import lean_rt as _rt

'''


def main():
    root = PROOFS / "Calibrator"
    defs, thms, structs, failures = lean_parse.build(root)
    blob = lean_parse.to_json(defs, structs, failures)
    (HERE / "defs.json").write_text(json.dumps(blob, indent=1, ensure_ascii=False))

    D = blob["definitions"]
    struct_names = {s["short"] for s in blob["structures"]} | \
                   {s["name"] for s in blob["structures"]}
    def_names = {d["short"] for d in D}

    # ---- python names: an ambiguous short name gets NO bare alias.  If three
    # definitions are called `hetDecayFactor`, none of them may quietly own the
    # name `hetDecayFactor`, or a call resolves to whichever was emitted first.
    by_short = collections.defaultdict(list)
    for d in D:
        by_short[d["short"]].append(d)
    pynames = {}
    for short, group in by_short.items():
        for d in group:
            pynames[d["name"]] = pyname(short) if len(group) == 1 else pyname(d["name"])

    by_name = {d["name"]: d for d in D}

    def make_resolver(caller):
        """Resolve an unqualified call the way Lean would, or refuse.

        Preference: same file AND namespace, then same file, then same
        namespace, then (within the surviving set) matching explicit arity.
        A remaining tie raises rather than guessing.
        """
        def resolve(short, nargs):
            group = by_short.get(short)
            if not group:
                return pyname(short)        # not ours: Mathlib, or a `where` local
            cands = group
            for pred in (lambda t: t["file"] == caller["file"]
                         and t["namespace"] == caller["namespace"],
                         lambda t: t["file"] == caller["file"],
                         lambda t: t["namespace"] == caller["namespace"]):
                narrowed = [t for t in cands if pred(t)]
                if narrowed:
                    cands = narrowed
                    break
            if len(cands) > 1:
                arity = [t for t in cands
                         if sum(len(a["names"]) for a in t["args"]
                                if not a["implicit"]) == nargs]
                if arity:
                    cands = arity
            if len(cands) > 1:
                raise Untranslatable(
                    f"ambiguous call to {short!r} with {nargs} argument(s): "
                    f"{[t['name'] for t in cands]}")
            return pynames[cands[0]["name"]]
        return resolve

    fields_of = {}
    for sdec in blob["structures"]:
        f = {x["name"] for x in sdec["fields"]}
        fields_of[sdec["short"]] = f
        fields_of[sdec["name"]] = f

    def dot_resolver(ty, meth, nargs):
        """`m.foo a` with `m : T` means `T.foo m a`."""
        for cand in (f"Calibrator.{ty}.{meth}", f"{ty}.{meth}"):
            if cand in by_name:
                return pynames[cand]
        group = [t for t in by_short.get(meth, [])
                 if t["name"].rsplit(".", 1)[0].endswith(ty)]
        if len(group) == 1:
            return pynames[group[0]["name"]]
        raise Untranslatable(
            f"dot-notation call {ty}.{meth}: "
            + ("no such definition" if not group else
               f"ambiguous among {[g['name'] for g in group]}"))

    sources, translated, reasons, standins = {}, {}, {}, {}
    vector_arity = {}
    for d in D:
        struct_types = {}
        for a in d["args"]:
            head = a["type"].split()[0] if a["type"].split() else ""
            if head in struct_names:
                for n in a["names"]:
                    struct_types[n] = head.split(".")[-1]
        # Vector / matrix arguments: `Fin n → ℝ` becomes a Python sequence, and
        # `Matrix (Fin p) (Fin q) ℝ` a sequence of sequences.  Purely additive:
        # a definition with only scalar arguments is unaffected.
        vector_args, dims = {}, {}
        for a in d["args"]:
            if a["implicit"]:
                continue
            ty = " ".join(a["type"].split())
            mv = re.fullmatch(r"Fin\s+(\w+)\s*→\s*ℝ", ty)
            mm = re.fullmatch(r"Matrix\s*\(Fin\s+(\w+)\)\s*\(Fin\s+(\w+)\)\s*ℝ", ty)
            for n in a["names"]:
                if mv:
                    vector_args[n] = (mv.group(1), 1)
                    dims.setdefault(mv.group(1), f"len({pyname(n)})")
                elif mm:
                    vector_args[n] = (mm.group(1), 2)
                    dims.setdefault(mm.group(1), f"len({pyname(n)})")
                    dims.setdefault(mm.group(2), f"len({pyname(n)}[0])")
        struct_args = list(struct_types)
        struct_args += [n for a in d["args"] for n in a["names"]
                        if "×" in a["type"]]
        fname = pynames[d["name"]]
        if d["name"] in NUMERIC_STANDINS:
            src, argnames, why = NUMERIC_STANDINS[d["name"]]
            sources[fname] = src.replace("def Phi(", f"def {fname}(")
            translated[d["name"]] = (fname, argnames)
            standins[d["name"]] = why
            continue
        try:
            src, argnames = translate_def(
                d, struct_args, fname=fname, resolver=make_resolver(d),
                struct_types=struct_types, fields_of=fields_of,
                dot_resolver=dot_resolver, vector_args=vector_args, dims=dims)
        except Untranslatable as e:
            reasons[d["name"]] = str(e)
            continue
        except Exception as e:                                    # noqa: BLE001
            reasons[d["name"]] = f"translator error: {e!r}"
            continue
        if fname in sources:
            reasons[d["name"]] = f"name collision on {fname}"
            continue
        sources[fname] = src
        translated[d["name"]] = (fname, argnames)
        if vector_args:
            vector_arity[d["name"]] = {pyname(k): {"dim": v[0], "rank": v[1]}
                                       for k, v in vector_args.items()}

    mod = HEADER + "\n\n".join(sources[k] for k in sources) + "\n"
    (HERE / "lean_defs.py").write_text(mod)

    # ---- import + self-check
    ns = {}
    try:
        exec(compile(mod, "lean_defs.py", "exec"), ns)
    except Exception as e:                                        # noqa: BLE001
        print(f"GENERATED MODULE FAILED TO IMPORT: {e!r}", file=sys.stderr)
        return

    by_struct = {s["short"]: s for s in blob["structures"]}
    global _ALL_STRUCTS
    _ALL_STRUCTS = by_struct
    rng = random.Random(20260801)
    selfcheck = {}
    for d in D:
        if d["name"] not in translated:
            continue
        short, argnames = translated[d["name"]]
        fn = ns.get(short)
        box = admissible.box_for(d)
        # structure-typed arguments get a sampled admissible inhabitant
        structval = {}
        for a in d["args"]:
            if a["implicit"]:
                continue
            head = a["type"].split()[0] if a["type"].split() else ""
            sd = by_struct.get(head.split(".")[-1])
            if sd is not None:
                for n in a["names"]:
                    structval[pyname(n)] = sd
        ok, err = 0, None
        pts = [admissible.sample(box, rng) for _ in range(8)]
        for pt in pts:
            pt = {pyname(k): v for k, v in pt.items()}
            try:
                args = admissible.build_args(
                    argnames, pt, structval, vector_arity.get(d["name"]),
                    rng, _ALL_STRUCTS)
                v = fn(*args)
            except Exception as e:                                # noqa: BLE001
                err = repr(e)
                continue
            if isinstance(v, bool) or (isinstance(v, (int, float)) and math.isfinite(v)):
                ok += 1
            else:
                err = err or f"value is not a real number: {type(v).__name__}"
        selfcheck[d["name"]] = {"finite_points": ok, "total_points": len(pts),
                                "error": err}
        if ok == 0:
            reasons.setdefault(d["name"], selfcheck_reason(err))

    # ---- propagate stand-in provenance to every dependent
    dep_names = {}
    for d in D:
        text = d["body"] + " " + " ".join(e["rhs"] for e in d["equations"])
        dep_names[d["name"]] = {m for m in re.findall(r"[A-Za-z_][\w'₀-₉.]*", text)}
    changed = True
    while changed:
        changed = False
        for d in D:
            if d["name"] in standins:
                continue
            for src_name, why in list(standins.items()):
                if src_name.split(".")[-1] in dep_names[d["name"]]:
                    standins[d["name"]] = f"depends on {src_name}: {why}"
                    changed = True
                    break

    # ---- classification
    classes = {}
    for d in D:
        d["_reason"] = reasons.get(d["name"], "")
        good = d["name"] in translated and selfcheck.get(d["name"], {}).get(
            "finite_points", 0) > 0
        cls, why = classify(d, struct_names, def_names, translated if good else {})
        classes[d["name"]] = {
            "class": cls, "note": why, "file": d["file"], "line": d["line"],
            "short": d["short"], "ret_type": d["ret_type"],
            "empirical_status": d["empirical_status"],
            "python": translated.get(d["name"], (None, None))[0],
            "args": translated.get(d["name"], (None, []))[1],
            "box": admissible.box_for(d),
            "selfcheck": selfcheck.get(d["name"]),
            "numeric_standins": standins.get(d["name"]),
            "vector_args": vector_arity.get(d["name"]),
            "mentioned_by": d["mentioned_by"],
            "constraints": d["constraints"],
        }
    (HERE / "classes.json").write_text(json.dumps(classes, indent=1, ensure_ascii=False))

    tally = collections.Counter(v["class"] for v in classes.values())
    print(f"definitions parsed : {len(D)}")
    print(f"parse failures     : {len(failures)}")
    print(f"executable forms   : {len(translated)}")
    for k, v in tally.most_common():
        print(f"  {k:<17}: {v}")
    bad = collections.Counter(
        reasons[n].split(":")[0] for n in reasons)
    print("\ntop non-extractable reasons:")
    for k, v in bad.most_common(15):
        print(f"  {v:4d}  {k}")


if __name__ == "__main__":
    main()
