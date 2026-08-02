"""CHECK 3 -- definitions that are the same function, and name-mates that are not.

Two directions, both of which have already bitten this corpus:

  EQUAL BODIES, DIFFERENT FILES.  Three definitions of one quantity lived in
  three files, two of them wrong, and fixing one left two.  Syntactic scanning
  misses these whenever the two copies are written differently; sympy does not
  care how they are written.
  NAME-MATES, DIFFERENT BODIES.  Definitions whose names denote the same
  concept but whose bodies are different functions -- the `d/(d+4Ne m sigma^2)`
  vs `d/(d+4Ne sigma^2 m^2)` shape.

Pairwise sympy over ~950 definitions is 450k simplifications, so equality is
first screened by a numeric fingerprint (evaluation at fixed pseudo-random
rationals).  The fingerprint can only produce false *collisions*, never false
splits, and every collision is then confirmed symbolically.
"""

from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from pathlib import Path

import sympy as sp

import leansym as L
import shared

HERE = Path(__file__).parent
PROBES = 7


def canonical(conv, d):
    """Convert a def body to sympy with binders renamed positionally.

    Positional renaming is what makes two files' copies of one quantity
    comparable when they spell their arguments differently (`Ne m` vs `N mig`).
    """
    binders = [n for grp, ty, op in d["binders"]
               if op == "(" and ty.strip() in ("ℝ", "ℕ", "ℚ") for n in grp]
    all_binders = [n for grp, ty, op in d["binders"] if op == "(" for n in grp]
    if len(binders) != len(all_binders):
        return None, None, "non-real binder"
    env = {b: sp.Symbol(f"x{i}", real=True) for i, b in enumerate(binders)}
    try:
        e = conv.convert(d["body"], dict(env))
    except (L.Unsupported, RecursionError, Exception) as ex:
        return None, binders, str(ex)[:120]
    if isinstance(e, (sp.logic.boolalg.BooleanAtom,)) or e.is_Relational:
        return None, binders, "propositional"
    return e, binders, None


def fingerprint(e, arity):
    """Evaluate at fixed rationals; None if the expression will not evaluate."""
    import random
    rng = random.Random(1234567)
    out = []
    for _ in range(PROBES):
        sub = {sp.Symbol(f"x{i}", real=True): sp.Rational(rng.randint(3, 97), 41)
               for i in range(arity)}
        try:
            v = complex(sp.N(e.subs(sub), 30))
        except Exception:
            return None
        if v != v or abs(v) == float("inf"):
            return None
        out.append(round(v.real, 10) + 0j if abs(v.imag) < 1e-12 else round(v.real, 10) + round(v.imag, 10) * 1j)
    return tuple(out)


CONCEPT_STRIP = re.compile(
    r"(_?(from|From|of|Of|at|At|under|Under|eq|Eq|approx|Approx|exact|Exact|"
    r"model|Model|formula|Formula|value|Value|closed|Closed)[A-Z0-9_]?.*$)"
)


def concept(name: str) -> str:
    """A coarse concept key: the leading camel-case words, lowercased."""
    base = name.split(".")[-1]
    words = re.findall(r"[A-Z]+(?![a-z])|[A-Z][a-z0-9]*|^[a-z0-9]+", base)
    if not words:
        return base.lower()
    key = "".join(words[:2]).lower()
    return key


def run():
    decls = json.load(open(HERE / "decls.json"))
    table = shared.build_table()
    conv = L.Converter(table)
    defs = [d for d in shared.def_records() if d["body"]]

    parsed, opaque = [], []
    for d in defs:
        e, binders, err = canonical(conv, d)
        if e is None:
            opaque.append((d, err))
            continue
        parsed.append((d, e, binders))

    # ---------- direction A: symbolically equal definitions
    buckets = defaultdict(list)
    for d, e, binders in parsed:
        fp = fingerprint(e, len(binders))
        if fp is None:
            continue
        buckets[(len(binders), fp)].append((d, e, binders))

    equal_groups = []
    for key, members in buckets.items():
        if len(members) < 2:
            continue
        # confirm symbolically, and split into confirmed-equal classes
        classes = []
        for d, e, b in members:
            for cls in classes:
                if L.equal(e, cls[0][1]) is True:
                    cls.append((d, e, b))
                    break
            else:
                classes.append([(d, e, b)])
        for cls in classes:
            if len(cls) < 2:
                continue
            modules = {d["module"] for d, _, _ in cls}
            equal_groups.append({
                "check": "check3_duplicate_body",
                "arity": key[0],
                "expression": sp.sstr(cls[0][1]),
                "cross_file": len(modules) > 1,
                "members": [{"fqn": f'{d["module"]}.{d["name"]}', "name": d["name"],
                             "file": d["file"], "line": d["line"],
                             "binders": b, "body": " ".join(d["body"].split())}
                            for d, _, b in cls],
            })

    # ---------- direction B: name-mates whose bodies differ
    by_concept = defaultdict(list)
    for d, e, binders in parsed:
        by_concept[concept(d["name"])].append((d, e, binders))

    disagreements = []
    for key, members in by_concept.items():
        if len(members) < 2:
            continue
        for i in range(len(members)):
            for j in range(i + 1, len(members)):
                (d1, e1, b1), (d2, e2, b2) = members[i], members[j]
                if len(b1) != len(b2):
                    continue
                if d1["module"] == d2["module"] and d1["name"] == d2["name"]:
                    continue
                v = L.equal(e1, e2)
                if v is False:
                    disagreements.append({
                        "check": "check3_name_mate_disagreement",
                        "concept": key,
                        "a": {"fqn": f'{d1["module"]}.{d1["name"]}', "line": d1["line"],
                              "file": d1["file"], "expr": sp.sstr(e1), "binders": b1,
                              "body": " ".join(d1["body"].split())},
                        "b": {"fqn": f'{d2["module"]}.{d2["name"]}', "line": d2["line"],
                              "file": d2["file"], "expr": sp.sstr(e2), "binders": b2,
                              "body": " ".join(d2["body"].split())},
                    })

    # ---------- ambiguous names: one bare name, several different bodies
    by_name = defaultdict(list)
    for d, e, binders in parsed:
        by_name[d["name"]].append((d, e, binders))
    homonyms = []
    for name, members in by_name.items():
        if len(members) < 2:
            continue
        classes = []
        for d, e, b in members:
            for cls in classes:
                if len(b) == len(cls[0][2]) and L.equal(e, cls[0][1]) is True:
                    cls.append((d, e, b))
                    break
            else:
                classes.append([(d, e, b)])
        if len(classes) > 1:
            homonyms.append({
                "check": "check3_homonym",
                "name": name,
                "distinct_bodies": [
                    {"expr": sp.sstr(cls[0][1]),
                     "sites": [f'{d["module"]}:{d["line"]}' for d, _, _ in cls]}
                    for cls in classes],
            })

    return {"equal_groups": equal_groups, "disagreements": disagreements,
            "homonyms": homonyms, "parsed": len(parsed), "opaque": len(opaque),
            "opaque_reasons": Counter(err for _, err in opaque).most_common(15)}


def main():
    res = run()
    (HERE / "results_check3.json").write_text(json.dumps(res, indent=1, ensure_ascii=False))
    print(f'CHECK 3: converted {res["parsed"]} definitions to sympy '
          f'({res["opaque"]} opaque)')
    cross = [g for g in res["equal_groups"] if g["cross_file"]]
    print(f'  symbolically identical groups: {len(res["equal_groups"])} '
          f'({len(cross)} spanning more than one file)')
    print(f'  name-mate disagreements      : {len(res["disagreements"])}')
    print(f'  homonyms with distinct bodies: {len(res["homonyms"])}')
    print()
    print("=== identical bodies across files ===")
    for g in cross:
        print(f'  {g["expression"]}')
        for m in g["members"]:
            print(f'      {m["fqn"]}  ({m["file"].split("/")[-1]}:{m["line"]})  {m["binders"]}')
        print()
    print("=== homonyms ===")
    for h in res["homonyms"]:
        print(f'  {h["name"]}:')
        for b in h["distinct_bodies"]:
            print(f'      {b["expr"]}   @ {b["sites"]}')
    print()
    print("=== opaque reasons ===")
    for r, n in res["opaque_reasons"]:
        print(f"  {n:5d}  {r}")


if __name__ == "__main__":
    main()
