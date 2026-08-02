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
import random
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import admissible                        # noqa: E402
import lean_parse                        # noqa: E402
from translate import Untranslatable, pyname, translate_def   # noqa: E402

PROOFS = HERE.parent.parent


# ------------------------------------------------------------- taxonomy

PROP_RETS = {"Prop"}


def classify(d, struct_names, def_names, translated):
    """NUMERIC | STRUCTURAL | WRAPPER | NOT-EXTRACTABLE (+ reason)."""
    ret = d["ret_type"]
    body = d["body"].strip()

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

    sources, translated, reasons = {}, {}, {}
    for d in D:
        struct_args = [n for a in d["args"]
                       for n in a["names"]
                       if a["type"].split() and a["type"].split()[0] in struct_names]
        struct_args += [n for a in d["args"] for n in a["names"]
                        if "×" in a["type"]]
        fname = pyname(d["short"])
        if fname in sources:
            fname = pyname(d["name"])
        try:
            src, argnames = translate_def(d, struct_args, fname=fname)
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

    mod = HEADER + "\n\n".join(sources[k] for k in sources) + "\n"
    (HERE / "lean_defs.py").write_text(mod)

    # ---- import + self-check
    ns = {}
    try:
        exec(compile(mod, "lean_defs.py", "exec"), ns)
    except Exception as e:                                        # noqa: BLE001
        print(f"GENERATED MODULE FAILED TO IMPORT: {e!r}", file=sys.stderr)
        return

    rng = random.Random(20260801)
    selfcheck = {}
    for d in D:
        if d["name"] not in translated:
            continue
        short, argnames = translated[d["name"]]
        fn = ns.get(short)
        box = admissible.box_for(d)
        pts = [admissible.sample(box, rng) for _ in range(8)]
        ok, err = 0, None
        for pt in pts:
            try:
                v = fn(*[pt.get(a, 1.0) for a in argnames])
            except Exception as e:                                # noqa: BLE001
                err = repr(e)
                continue
            if isinstance(v, bool) or (isinstance(v, (int, float)) and math.isfinite(v)):
                ok += 1
            else:
                err = err or f"non-finite value {v!r}"
        selfcheck[d["name"]] = {"finite_points": ok, "total_points": len(pts),
                                "error": err}
        if ok == 0:
            reasons.setdefault(d["name"], f"self-check: never finite ({err})")

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
            "mentioned_by": d["mentioned_by"],
            "constraints": d["constraints"],
        }
    (HERE / "classes.json").write_text(json.dumps(classes, indent=1, ensure_ascii=False))

    import collections
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
