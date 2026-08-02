"""Diff this definition table against the other parsers in the repo.

Four independent Lean parsers were written in parallel.  Any disagreement about
a body, a parameter list, or a parameter ORDER is a bug in at least one of them,
and a checker built on the wrong one will be silently checking something else.
This script finds those disagreements before that happens.

    python3 validation/extract/reconcile.py

Comparison is on normalised whitespace.  Parameter order is compared exactly,
because an order disagreement is the single most damaging kind: both parsers
produce a callable, both callables run, and they compute different functions.
"""
from __future__ import annotations

import ast
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import api                                               # noqa: E402

PROOFS = HERE.parent.parent


def norm(s: str) -> str:
    return " ".join((s or "").split())


def ours():
    out = {}
    for name, d in api.definition_table().items():
        params = [(n, norm(a["type"])) for a in d["args"]
                  if not a["implicit"] for n in a["names"]]
        out[name.split(".")[-1]] = {
            "fq": name, "body": norm(d["body"]), "params": params,
            "ret": norm(d["ret_type"]), "file": d["file"], "line": d["line"],
        }
    return out


def load_invariants():
    p = PROOFS / "validation/invariants/defs.json"
    if not p.exists():
        return None, "absent"
    recs = json.loads(p.read_text())
    out = {}
    for r in recs:
        params = r.get("params")
        if isinstance(params, str):
            try:
                params = ast.literal_eval(params)
            except Exception:                                   # noqa: BLE001
                params = []
        out[r["name"].split(".")[-1]] = {
            "body": norm(r.get("body", "")),
            "params": [(p_[0], norm(p_[1])) for p_ in (params or [])],
            "ret": norm(r.get("ret", "")),
            "file": r.get("path", ""), "line": r.get("line", ""),
        }
    return out, f"{len(recs)} records"


def load_symbolic():
    p = PROOFS / "validation/symbolic/decls.json"
    if not p.exists():
        return None, "absent"
    recs = json.loads(p.read_text())
    out, kinds = {}, {}
    for r in recs:
        kinds[r.get("kind", "?")] = kinds.get(r.get("kind", "?"), 0) + 1
        if r.get("kind") not in ("def", "abbrev"):
            continue
        binders = r.get("binders")
        if isinstance(binders, str):
            try:
                binders = ast.literal_eval(binders)
            except Exception:                                   # noqa: BLE001
                binders = []
        params = []
        for b in binders or []:
            if isinstance(b, dict):
                if b.get("implicit") or b.get("binder", "(") != "(":
                    continue
                for n in b.get("names", []) or []:
                    params.append((n, norm(b.get("type", ""))))
            elif isinstance(b, (list, tuple)):
                # symbolic/ stores binder groups as [[names], type, open_bracket]
                if len(b) >= 3 and isinstance(b[0], (list, tuple)):
                    if b[2] != "(":                      # implicit / instance
                        continue
                    params.extend((n, norm(str(b[1]))) for n in b[0])
                elif b and all(isinstance(x, str) for x in b):
                    params.extend((x, "") for x in b)
                elif len(b) >= 2:
                    params.append((b[0], norm(str(b[1]))))
        out[r["name"].split(".")[-1]] = {
            "body": norm(r.get("body", "")),
            "params": params, "ret": norm(r.get("signature", "")),
            "file": r.get("file", ""), "line": r.get("line", ""),
        }
    return out, f"{len(recs)} records ({kinds})"


def load_differential():
    """differential/ has no JSON table; parse whatever it caches, else skip."""
    for cand in ("results.json",):
        p = PROOFS / "validation/differential" / cand
        if p.exists():
            try:
                blob = json.loads(p.read_text())
            except Exception:                                   # noqa: BLE001
                continue
            recs = blob if isinstance(blob, list) else blob.get("defs", [])
            if not isinstance(recs, list) or not recs:
                return None, f"{cand} present but holds no definition table"
            out = {}
            for r in recs:
                if not isinstance(r, dict) or "name" not in r:
                    continue
                out[str(r["name"]).split(".")[-1]] = {
                    "body": norm(str(r.get("body", r.get("lean", "")))),
                    "params": [], "ret": "", "file": "", "line": ""}
            return (out, f"{len(out)} from {cand}") if out else (
                None, f"{cand} has no per-definition bodies")
    return None, "no JSON table emitted"


def compare(name, mine, theirs):
    rows = []
    shared = sorted(set(mine) & set(theirs))
    only_mine = sorted(set(mine) - set(theirs))
    only_theirs = sorted(set(theirs) - set(mine))
    body_diff, param_diff, order_diff = [], [], []
    for k in shared:
        a, b = mine[k], theirs[k]
        if b["body"] and a["body"] != b["body"]:
            body_diff.append(k)
        if b["params"]:
            an = [p[0] for p in a["params"]]
            bn = [p[0] for p in b["params"]]
            if an != bn:
                (order_diff if sorted(an) == sorted(bn) else param_diff).append(k)
    print(f"\n--- vs {name} ---")
    print(f"  shared definitions        : {len(shared)}")
    print(f"  only in ours              : {len(only_mine)}")
    print(f"  only in theirs            : {len(only_theirs)}")
    print(f"  BODY disagreements        : {len(body_diff)}")
    print(f"  PARAMETER-SET disagreements: {len(param_diff)}")
    print(f"  PARAMETER-ORDER disagreements: {len(order_diff)}")
    for k in order_diff[:10]:
        print(f"    ORDER {k}: ours={[p[0] for p in mine[k]['params']]} "
              f"theirs={[p[0] for p in theirs[k]['params']]}")
    for k in param_diff[:10]:
        print(f"    PARAMS {k}: ours={[p[0] for p in mine[k]['params']]} "
              f"theirs={[p[0] for p in theirs[k]['params']]}")
    for k in body_diff[:12]:
        print(f"    BODY {k}  ({mine[k]['file']}:{mine[k]['line']})")
        print(f"      ours  : {mine[k]['body'][:130]}")
        print(f"      theirs: {theirs[k]['body'][:130]}")
    if only_theirs[:12]:
        print(f"    names they have and we do not: {only_theirs[:12]}")
    # Publish BOTH SIDES of every disagreement, keyed by name.  A count tells
    # someone there is a problem; both parses plus the source location tell them
    # which side is wrong and let them fix it without re-deriving anything.
    detail = {}
    for k in body_diff + param_diff + order_diff:
        kinds = ([] + (["body"] if k in body_diff else [])
                 + (["params"] if k in param_diff else [])
                 + (["order"] if k in order_diff else []))
        detail[k] = {
            "disagreement": kinds,
            "source": f"{mine[k]['file']}:{mine[k]['line']}",
            "ours": {"params": mine[k]["params"], "body": mine[k]["body"],
                     "ret": mine[k]["ret"], "fq": mine[k]["fq"]},
            "theirs": {"params": theirs[k]["params"], "body": theirs[k]["body"],
                       "ret": theirs[k]["ret"],
                       "at": f"{theirs[k]['file']}:{theirs[k]['line']}"},
        }
    rows = {"shared": len(shared), "only_ours": len(only_mine),
            "only_theirs": len(only_theirs), "body": len(body_diff),
            "params": len(param_diff), "order": len(order_diff),
            "body_names": body_diff, "param_names": param_diff,
            "order_names": order_diff, "only_theirs_names": only_theirs,
            "detail": detail}
    return rows


def main():
    mine = ours()
    print(f"canonical table: {len(mine)} definitions, "
          f"{len(api.parse_failures())} parse failures")
    report = {"ours": len(mine), "stamp": api.stamp()}
    for label, loader in (("invariants/defs.json", load_invariants),
                          ("symbolic/decls.json", load_symbolic),
                          ("differential/", load_differential)):
        tbl, note = loader()
        if tbl is None:
            print(f"\n--- vs {label} ---\n  skipped: {note}")
            report[label] = {"skipped": note}
            continue
        print(f"\n({label}: {note})")
        report[label] = compare(label, mine, tbl)
    (HERE / "reconcile.json").write_text(json.dumps(report, indent=1,
                                                    ensure_ascii=False))
    tot = sum(v.get("body", 0) + v.get("params", 0) + v.get("order", 0)
              for v in report.values() if isinstance(v, dict))
    print(f"\nTOTAL DISAGREEMENTS ACROSS PARSERS: {tot}")
    print("Each one is a bug in at least one parser.  Both sides' parse and the")
    print("source location are in reconcile.json under [<table>][\"detail\"],")
    print("keyed by definition name -- routable without re-deriving anything.")

    # The dominant cause is worth naming rather than leaving to be rediscovered.
    multiline = []
    for label, v in report.items():
        if not isinstance(v, dict) or "detail" not in v:
            continue
        for k, row in v["detail"].items():
            ours = [p[0] for p in row["ours"]["params"]]
            theirs_p = [p[0] for p in row["theirs"]["params"]]
            if len(theirs_p) < len(ours) and set(theirs_p) <= set(ours):
                multiline.append((label, k, sorted(set(ours) - set(theirs_p))))
    if multiline:
        print(f"\n{len(multiline)} of these are the SAME failure: a parameter "
              "dropped from a\nmulti-line signature.  A callable built from the "
              "short list mis-binds every\nargument after the missing one.")
        for label, k, missing in multiline[:20]:
            print(f"  {label}  {k}: missing {missing}")


if __name__ == "__main__":
    main()
