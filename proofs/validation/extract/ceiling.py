"""Where does mechanical extraction actually top out?

A definition can fail to become callable for two very different reasons:

  INTRINSIC   its own body is outside real arithmetic -- an integral, a Finset
              sum, a matrix literal, a quantifier.  No amount of translator work
              helps; it needs a different kind of model.
  INHERITED   its own body is fine, but it calls something that is blocked.
              These collapse for free the moment their blocker is fixed.

Conflating the two makes the ceiling look lower than it is and makes translator
work look less valuable than it is.  This script separates them, propagates the
blockage through the call graph, and reports the ceiling: how many definitions
would be callable if every INHERITED blockage were resolved, and which root
blockers are load-bearing for the most dependents.

    python3 validation/extract/ceiling.py
"""
from __future__ import annotations

import collections
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import api                                                # noqa: E402


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'₀-₉]*(?:\.[A-Za-z0-9_'₀-₉]+)*")

# Reasons that are properties of the body itself, not of its dependencies.
INTRINSIC = (
    "Finset", "indexed sum", "indexed product", "integral", "derivative",
    "Matrix", "matrix", "quantifier", "norm of a vector", "set membership",
    "set operation", "function composition", "anonymous constructor",
    "tuple literal", "floor", "measure", "sigma-algebra", "sample-space",
    "vector-valued", "structure literal", "type alias", "product type",
    "unit / empty",
)


def is_intrinsic(note: str) -> bool:
    return any(k in note for k in INTRINSIC)


def main():
    api.refresh()
    table = api.definition_table()
    classes = json.loads((HERE / "classes.json").read_text())

    by_short = collections.defaultdict(list)
    for n in table:
        by_short[n.split(".")[-1]].append(n)

    # ---- call graph over definitions, from the parsed bodies
    deps = {}
    for name, d in table.items():
        binders = {n for a in d["args"] for n in a["names"]}
        text = d["body"] + " " + " ".join(e["rhs"] for e in d["equations"])
        out = set()
        for m in IDENT.finditer(text):
            tok = m.group(0)
            if tok in binders or tok == d["short"]:
                continue
            cands = by_short.get(tok.split(".")[-1], [])
            if not cands:
                continue
            same = [c for c in cands if table[c]["file"] == d["file"]]
            out.add((same or cands)[0] if len(same or cands) == 1
                    else (same or cands)[0])
        deps[name] = out

    ok = {n for n, e in classes.items() if e["class"] != "NOT-EXTRACTABLE"}
    blocked = {n for n in classes if n not in ok}

    roots = {n for n in blocked if is_intrinsic(classes[n]["note"])}
    unknown = set()
    for n in blocked - roots:
        note = classes[n]["note"]
        # "calls untranslated definition X" / a self-check failure caused by a
        # dependency is inherited; anything else we cannot attribute is unknown.
        if "untranslated definition" in note or "no admissible point" in note \
                or "self-check" in note:
            continue
        unknown.add(n)

    # ---- propagate: anything reaching a root through the call graph is blocked
    contaminated = set(roots)
    changed = True
    while changed:
        changed = False
        for n in blocked:
            if n in contaminated:
                continue
            if deps.get(n, set()) & contaminated:
                contaminated.add(n)
                changed = True

    inherited = (blocked & contaminated) - roots
    unexplained = blocked - contaminated

    total = len(classes)
    print("=" * 70)
    print("MECHANICAL EXTRACTION CEILING")
    print("=" * 70)
    print(f"definitions                        : {total}")
    print(f"extractable today                  : {len(ok)}  "
          f"({100*len(ok)/total:.1f}%)")
    print(f"blocked                            : {len(blocked)}")
    print(f"  INTRINSIC (root blockers)        : {len(roots)}")
    print(f"  INHERITED (blocked only by a dep): {len(inherited)}")
    print(f"  unexplained by the call graph    : {len(unexplained)}")
    print()
    print(f"CEILING if every INHERITED blockage were resolved: "
          f"{len(ok) + len(inherited)} / {total} "
          f"({100*(len(ok)+len(inherited))/total:.1f}%)")
    print(f"HARD FLOOR of definitions no translator can reach: {len(roots)} "
          f"({100*len(roots)/total:.1f}%)")

    # ---- which root blockers carry the most dependents
    rdeps = collections.defaultdict(set)
    for n, ds in deps.items():
        for t in ds:
            rdeps[t].add(n)

    def reach(root):
        seen, stack = set(), [root]
        while stack:
            cur = stack.pop()
            for parent in rdeps.get(cur, ()):
                if parent not in seen:
                    seen.add(parent)
                    stack.append(parent)
        return seen

    scored = sorted(((len(reach(r) & blocked), r) for r in roots), reverse=True)
    print("\nroot blockers carrying the most blocked dependents:")
    print("(fixing one of these frees everything beneath it)")
    for k, r in scored[:15]:
        if not k:
            continue
        print(f"  {k:4d}  {r}")
        print(f"        {classes[r]['note'][:76]}")

    kinds = collections.Counter()
    for r in roots:
        note = classes[r]["note"]
        for key in INTRINSIC:
            if key in note:
                kinds[key] += 1
                break
    print("\nhard floor by mathematics:")
    for k, v in kinds.most_common():
        print(f"  {v:4d}  {k}")

    if unexplained:
        print(f"\nblocked but NOT reachable from any root blocker "
              f"({len(unexplained)}) -- these are translator gaps, not "
              f"mathematics, and are the actionable list:")
        for n in sorted(unexplained)[:20]:
            print(f"  {n}\n        {classes[n]['note'][:76]}")

    (HERE / "ceiling.json").write_text(json.dumps(
        {"total": total, "extractable": len(ok), "roots": sorted(roots),
         "inherited": sorted(inherited), "unexplained": sorted(unexplained),
         "ceiling": len(ok) + len(inherited)}, indent=1))


if __name__ == "__main__":
    main()
