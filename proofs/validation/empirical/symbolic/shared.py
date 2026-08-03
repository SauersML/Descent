"""Adapter onto the shared extraction API.

Definition bodies come from `proofs/validation/empirical/extract/api.py` and nowhere else.
This directory no longer parses Lean *definitions*; `leanparse.py` is retained
only for THEOREM statements, which the shared API does not yet expose, and
`audit_against_shared()` cross-checks whatever it does parse against the shared
table so a boundary disagreement is reported rather than silently used.

`leansym.py` still converts a Lean expression to sympy.  That is not a second
parse of the corpus: it consumes the raw body string the shared API hands over,
and the symbolic layer needs sympy expressions rather than the float callables
`api.callable_for` returns.
"""

from __future__ import annotations

import sys
from pathlib import Path

from paths import EXTRACT as _EXTRACT, PROOFS, require

EXTRACT = str(require(_EXTRACT, "proofs/validation/extract"))
if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

import api  # noqa: E402

REAL_TYPES = {"ℝ", "ℕ", "ℚ"}


def definitions():
    return api.definition_table()


def stamp():
    return api.stamp()


def checksum(name):
    try:
        return api.body_checksum(name)
    except Exception:
        return None


def build_table():
    """bare short name -> (explicit real binder names, raw Lean body).

    A short name that resolves to more than one definition is omitted, so an
    inlining can never silently pick one of two different bodies.  Definitions
    with a non-real explicit binder are omitted too: the converter would have
    to guess at their arity.
    """
    table, ambiguous = {}, set()
    for fq, d in definitions().items():
        body = (d.get("body") or "").strip()
        if not body:
            continue
        explicit = [a for a in d["args"] if not a.get("implicit")]
        if any(a["type"].strip() not in REAL_TYPES for a in explicit):
            continue
        names = [n for a in explicit for n in a["names"]]
        short = d["short"]
        if short in table and (table[short][0] != names or table[short][1] != body):
            ambiguous.add(short)
            continue
        table[short] = (names, body)
    for s in ambiguous:
        table.pop(s, None)
    return table


def fq_for(short: str) -> str | None:
    try:
        return api.resolve(short)
    except Exception:
        return None


def audit_against_shared(local_decls) -> dict:
    """Compare a local parse against the shared table.

    Returns the disagreements: definitions the local parse invented, ones it
    missed, and ones whose body text differs.
    """
    shared = definitions()
    by_short = {}
    for fq, d in shared.items():
        by_short.setdefault(d["short"], []).append(d)

    invented, body_mismatch, missing = [], [], []
    local_names = set()
    for d in local_decls:
        if d["kind"] != "def" or not d["body"]:
            continue
        local_names.add(d["name"])
        cands = by_short.get(d["name"])
        if not cands:
            invented.append({"name": d["name"], "module": d["module"],
                             "line": d["line"], "body": d["body"][:160]})
            continue
        if not any(" ".join(c["body"].split()) == " ".join(d["body"].split())
                   for c in cands):
            body_mismatch.append({
                "name": d["name"], "module": d["module"], "line": d["line"],
                "local_body": " ".join(d["body"].split())[:220],
                "shared_body": " ".join(cands[0]["body"].split())[:220],
                "shared_file": cands[0]["file"], "shared_line": cands[0]["line"]})
    for short, cands in by_short.items():
        if short not in local_names:
            missing.append({"name": short, "file": cands[0]["file"],
                            "line": cands[0]["line"]})
    return {"invented_by_local": invented, "body_mismatch": body_mismatch,
            "missing_from_local": missing,
            "shared_total": len(shared), "local_total": len(local_names)}


def main():
    import json
    local = json.load(open(Path(__file__).parent / "decls.json"))
    rep = audit_against_shared(local)
    print(f"shared definitions : {rep['shared_total']}")
    print(f"local definitions  : {rep['local_total']}")
    print(f"invented by local  : {len(rep['invented_by_local'])}")
    for x in rep["invented_by_local"][:15]:
        print(f"    {x['module']}.{x['name']}:{x['line']}  {x['body'][:90]}")
    print(f"body mismatches    : {len(rep['body_mismatch'])}")
    for x in rep["body_mismatch"][:15]:
        print(f"    {x['name']}  ({x['shared_file']}:{x['shared_line']})")
        print(f"        local : {x['local_body'][:150]}")
        print(f"        shared: {x['shared_body'][:150]}")
    print(f"missed by local    : {len(rep['missing_from_local'])}")
    Path(Path(__file__).parent / "parser_audit.json").write_text(
        json.dumps(rep, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()


def def_records():
    """Shared definitions rendered in the local declaration schema.

    Lets the checks consume the shared parse without each one growing its own
    translation of the API's record shape.
    """
    out = []
    for fq, d in definitions().items():
        module = "Calibrator." + d["file"].replace("Calibrator/", "").replace(".lean", "").replace("/", ".")
        # opener must match the local schema: "(" explicit, "{" implicit
        binders = [(a["names"], a["type"], "{" if a.get("implicit") else "(")
                   for a in d["args"]]
        out.append({
            "kind": "def", "name": d["short"], "fq": fq, "module": module,
            "file": str(PROOFS / d["file"]), "line": d["line"],
            "docstring": d.get("docstring") or "",
            "signature": d.get("signature") or "",
            "body": (d.get("body") or "").strip(),
            "proof": "", "binders": binders, "raw": "",
        })
    return out
