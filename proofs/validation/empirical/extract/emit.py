"""Generate the executable module and the classification table.

    python3 emit.py            # writes defs.json, lean_defs.py, classes.json

`lean_defs.py` is machine-generated from parsed Lean bodies.  Other validation
scripts should import it instead of re-transcribing formulas:

    from validation.extract import lean_defs
    lean_defs.neiFst(0.4, 0.3)
"""

# REGENERATE WITH:  python3 proofs/validation/empirical/extract/emit.py
#
# This produces lean_defs.py and defs.json, which are NOT IN GIT.
# They are generated from proofs/Calibrator/, which changes every few
# minutes, and a committed snapshot drifts by six figures -- defs.json
# measured 122994 changed lines against its last committed copy. A cache
# that far from its source is not a cache, it is a second source of truth
# that disagrees with the first. Run this in your own worktree
# immediately before use, so your numbers are pinned to the revision you
# are standing on.
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

PROOFS = lean_parse.find_proofs_root(HERE)
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

# A FINITE INDEX DOMAIN, as the corpus writes one.  `Fin n`, or a bare type
# name standing for an abstract `[Fintype]` index -- `α`, `ι`, `V`, `Band`, or
# an enumeration like `Pop`.
#
# This used to accept only `Fin n`, which meant `freq : α → ℝ` and `A : Matrix ι
# ι ℝ` were not recognised as sequences: their `∑` had no dimension, and a
# caller who passed a Python list got "'list' object is not callable" because
# the body applied them instead of indexing them.  The Lean types are the same
# shape and must get the same calling convention, or `api.vector_args` tells a
# consumer the truth for one definition and not for its neighbour.
#
# `ℝ`, `ℕ` and `ℤ` are excluded on purpose: `profile : ℝ → ℝ` is a genuine
# function evaluated at a real location, not a table, and reading it as a
# sequence would index it with a coordinate.
_IDX_NAME = re.compile(r"[A-Za-zΑ-Ωα-ωϑ-ϵ][\w'₀-₉]*")
_NOT_AN_INDEX = {"ℝ", "ℕ", "ℤ", "ℚ", "Real", "Nat", "Int", "Prop", "Type"}


def index_dim(dom):
    """The dimension KEY for a finite index domain, or None if it is not one.

    `Fin T` keys on `T`, because that is the name a `∑ i : Fin T` annotation
    uses to look the dimension up.  An abstract index type keys on its own name.
    """
    dom = " ".join(dom.split()).strip("()")
    m = re.fullmatch(r"Fin\s+(\w+)", dom)
    if m:
        return m.group(1)
    if dom in _NOT_AN_INDEX:
        return None
    return dom if _IDX_NAME.fullmatch(dom) else None


def sequence_shape(ty):
    """[index keys] if this Lean type is a real-valued finite table, else [].

    Recognises `ι → ℝ`, `ι → κ → ℝ` and `Matrix ι κ ℝ` for ANY finite index
    types, not only `Fin n`.  This used to accept `Fin n` alone, so `freq : α →
    ℝ` and `A : Matrix ι ι ℝ` were not seen as sequences: their `∑` had no
    dimension to range over, and a caller who passed a Python list got "'list'
    object is not callable" because the generated body applied them instead of
    indexing them.  The Lean types have the same shape and must get the same
    calling convention, or `api.vector_args` tells the truth about one
    definition and lies about its neighbour.

    `ℝ → ℝ` is deliberately NOT a sequence: `profile : ℝ → ℝ` is evaluated at a
    real location, and reading it as a table would index it by a coordinate.
    """
    ty = " ".join(ty.split())
    if ty.startswith("Matrix "):
        # Split on TOP-LEVEL whitespace: `Matrix (Fin p) (Fin p) ℝ` has
        # parenthesised arguments, and a regex with non-greedy groups tears
        # `(Fin p)` into `(Fin` and `p)`.  That silently produced a rank-2
        # entry under a nonsense dimension key, which turned elementwise
        # arithmetic OFF for ldMismatchFrobenius -- one of the four definitions
        # only this path can reach.
        parts, depth, cur = [], 0, ""
        for ch in ty:
            if ch in "([":
                depth += 1
            elif ch in ")]":
                depth -= 1
            if ch == " " and depth == 0:
                if cur:
                    parts.append(cur)
                cur = ""
            else:
                cur += ch
        if cur:
            parts.append(cur)
        if len(parts) == 4 and parts[-1] == "ℝ":
            a, b = index_dim(parts[1]), index_dim(parts[2])
            return [a, b] if a and b else []
        return []
    parts, depth, cur = [], 0, ""
    for ch in ty:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == "→" and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    if len(parts) < 2 or parts[-1].strip() != "ℝ":
        return []
    keys = [index_dim(x) for x in parts[:-1]]
    return keys if len(keys) <= 2 and all(keys) else []


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
    # A RETURN TYPE WITH AN ARROW IS NOT A STRUCTURE VALUE.  `Pop.pair : Pop →
    # α` and `HardyWeinbergModel.genotypeProb : DiploidGenotype → ℝ` were being
    # called structure-valued because the first word of the return type named an
    # inductive -- so a definition that translates perfectly (the enum-match
    # compiler turns it into a dispatch table taking the constructor as its last
    # argument) was filed as STRUCTURAL and never became callable, and the ten
    # definitions calling `Pop.pair` failed with NameError in turn.
    if ret and "→" not in ret and (ret in struct_names
                                   or ret.split()[0] in struct_names):
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
    if err.startswith("Uninhabitable"):
        return f"no inhabitant for an argument type: {err[14:130]}"
    if err.startswith("IndexError"):
        return f"evaluated outside the sampled dimension: {err[:90]}"
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

HEADER = '''"""GENERATED FILE -- do not edit.  NOT AUTHORITATIVE IF COMMITTED.

    THE COPY OF THIS FILE IN GIT IS STALE BY CONSTRUCTION.

`proofs/Calibrator/` changes every few minutes.  A generated table committed
alongside it is a cache of a moving target, and committing it moves the
staleness from DETECTABLE to COMMITTED -- which is worse, because a file in the
repository reads as authoritative.

DO NOT CONSUME A COMMITTED COPY.  Run `python3 validation/extract/emit.py` in
your own worktree immediately before use.  It takes about a minute, writes only
inside that worktree, pins your numbers to the revision you are standing on, and
makes `api.require_fresh()` pass for a reason rather than by luck.  It also means
no two agents write to each other's artifacts.

`api.require_fresh()` will raise if you skip this.  That is the intended
behaviour, not an obstacle.


Produced by validation/extract/emit.py from the Lean sources under
proofs/Calibrator/.  Each function below was translated from the parsed body of
the corresponding Lean `def`; no formula in this file was typed by hand.

Regenerate with:  python3 validation/extract/emit.py
"""
# ruff: noqa
import lean_rt as _rt

'''


def build_context(blob):
    """Everything `translate_def` needs, built once from a parsed corpus.

    THIS IS SHARED ON PURPOSE.  It used to live inside `emit.main`, so
    `coverage_v2.compile_variant` -- which re-translates a body in order to
    mutate it -- called `translate_def` with NONE of it: no call resolver, no
    structure types, no field table, no dot resolver, no vector arguments, no
    dimensions, no enumerations.  The consequence was that 168 definitions the
    extractor had translated perfectly well reported "could not compile body"
    inside the coverage gate and were scored UNCOVERED.  That is not a property
    of the corpus; it is two callers disagreeing about what a definition means.

    Anything that translates a Lean body must go through here, so that the body
    a check runs is the body the table describes.
    """
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

    # Enumerations, read from the Lean declarations: {type: {ctor: ordinal}}.
    # These are the corpus's finite INDEX types (`Pop`, `DiploidGenotype`), and
    # the ordinal a constructor gets here is the same position that
    # admissible.type_value keys a `Pop → …` table on.  If the two ever
    # disagreed, `m.beta Pop.target` would read the source population's entry
    # and return a number from the wrong population, so both derive the order
    # from one place: the declaration order of the constructors.
    enums = {}
    for sdec in blob["structures"]:
        if sdec["kind"] != "inductive":
            continue
        ctors = [ln.strip()[1:].strip() for ln in sdec["body"].splitlines()
                 if ln.strip().startswith("|")]
        if ctors and all(c and " " not in c.split("--")[0].strip() for c in ctors):
            table = {c: i for i, c in enumerate(ctors)}
            enums[sdec["short"]] = table
            enums[sdec["name"]] = table

    def qualified_resolver(dotted):
        """A dotted name that IS a declaration of this corpus, or None.

        Only answers when exactly one declaration bears the name, under the
        namespace prefixes Lean would try.  Ambiguity returns None and the
        caller refuses, because picking one would silently call a different
        function than the Lean names.
        """
        for cand in (dotted, f"Calibrator.{dotted}"):
            if cand in by_name:
                return pynames[cand]
        return None

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


    return {
        "blob": blob, "D": D, "struct_names": struct_names,
        "def_names": def_names, "by_short": by_short, "pynames": pynames,
        "by_name": by_name, "make_resolver": make_resolver, "enums": enums,
        "qualified_resolver": qualified_resolver, "fields_of": fields_of,
        "dot_resolver": dot_resolver,
        "structs_by_short": {sd["short"]: sd for sd in blob["structures"]},
    }


def per_def(ctx, d):
    """(fname, struct_args, translate_def kwargs) for one definition."""
    struct_types = {}
    for a in d["args"]:
        head = a["type"].split()[0] if a["type"].split() else ""
        if head in ctx["struct_names"]:
            for n in a["names"]:
                struct_types[n] = head.split(".")[-1]
    # Vector / matrix arguments: a finite table becomes a Python sequence, and a
    # matrix a sequence of sequences.  Purely additive: a definition with only
    # scalar arguments is unaffected.
    vector_args, dims = {}, {}
    for a in d["args"]:
        if a["implicit"]:
            continue
        idxs = sequence_shape(a["type"])
        for n in a["names"]:
            if not idxs:
                continue
            vector_args[n] = (idxs[0], len(idxs))
            dims.setdefault(idxs[0], f"len({pyname(n)})")
            if len(idxs) == 2:
                dims.setdefault(idxs[1], f"len({pyname(n)}[0])")
    struct_args = list(struct_types)
    struct_args += [n for a in d["args"] for n in a["names"] if "×" in a["type"]]
    kw = dict(resolver=ctx["make_resolver"](d), struct_types=struct_types,
              fields_of=ctx["fields_of"], dot_resolver=ctx["dot_resolver"],
              vector_args=vector_args, dims=dims, enums=ctx["enums"],
              qualified_resolver=ctx["qualified_resolver"])
    return ctx["pynames"].get(d["name"], pyname(d["short"])), struct_args, kw


def translate_in_context(ctx, d, body=None, fname=None):
    """Translate `d` (or `d` with `body` substituted) the way emit.py does.

    `body` is the hook the mutation gate needs: a mutant is the real definition
    with one token changed, and it must be translated under exactly the same
    resolution as the real one or the comparison is between two different
    things rather than between a body and its perturbation.
    """
    f, struct_args, kw = per_def(ctx, d)
    if body is not None:
        d = dict(d)
        d["body"] = body
        d["equations"] = []
    return translate_def(d, struct_args, fname=fname or f, **kw)


def main():
    root = PROOFS / "Calibrator"
    defs, thms, structs, failures = lean_parse.build(root)
    blob = lean_parse.to_json(defs, structs, failures, thms)
    (HERE / "defs.json").write_text(json.dumps(blob, indent=1, ensure_ascii=False))

    ctx = build_context(blob)
    D = ctx["D"]
    struct_names = ctx["struct_names"]
    def_names = ctx["def_names"]
    pynames = ctx["pynames"]

    sources, translated, reasons, standins = {}, {}, {}, {}
    vector_arity = {}
    for d in D:
        fname, struct_args, kw = per_def(ctx, d)
        vector_args = kw["vector_args"]
        if d["name"] in NUMERIC_STANDINS:
            src, argnames, why = NUMERIC_STANDINS[d["name"]]
            sources[fname] = src.replace("def Phi(", f"def {fname}(")
            translated[d["name"]] = (fname, argnames)
            standins[d["name"]] = why
            continue
        try:
            src, argnames = translate_def(d, struct_args, fname=fname, **kw)
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
        return 1

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
                    rng, _ALL_STRUCTS, admissible.arg_types(d))
                v = fn(*args)
            except Exception as e:                                # noqa: BLE001
                err = repr(e)
                continue
            # A STRUCTURE VALUE IS A LEGITIMATE RESULT.  A definition that
            # builds a record returns a dict of its fields, and judging that
            # "not a real number" would report a definition we can now evaluate
            # as unevaluable.  It is still classified STRUCTURAL -- it does
            # build a structure -- but it now carries an executable form, so
            # everything that projects a field out of it becomes reachable.
            if isinstance(v, dict):
                ok += 1 if any(k != "__uninhabited__" for k in v) else 0
            elif isinstance(v, bool) or (isinstance(v, (int, float))
                                         and math.isfinite(v)):
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

    # An EMPTY table is the one outcome this script must never report as
    # success.  It looks identical to a clean run -- no parse failures, no
    # translator errors, every tally zero -- and every downstream consumer then
    # validates an empty corpus and agrees with itself.  That is exactly what
    # happened while `PROOFS` pointed one directory too high: `rglob` on a
    # missing path yields nothing, so this printed "definitions parsed : 0" and
    # exited 0, and the extraction tier was dead without a single red signal.
    if not D:
        print("\nNO DEFINITIONS EXTRACTED -- the corpus was not found or the "
              "parser is broken. Refusing to report success on an empty table.",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
