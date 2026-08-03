"""Account for every definition this checker does not cover.

The target is not that every definition passes.  It is that every definition is
ACCOUNTED FOR: either covered by a check demonstrated able to fail, or on this
list with a specific reason.  A definition that is simply absent from both is
the failure mode -- it looks like nothing is wrong with it.

Reasons are graded by whether they are a property of the CORPUS or a limit of
THIS CHECKER, because only the second kind is worth more of my time:

  corpus     the definition genuinely offers nothing to check -- no name-implied
             range, no derivable invariant, no theorem constraining it, and no
             named quantity a simulation could reference
  checker    something is checkable in principle and this tool cannot reach it
             yet, with the specific obstacle named

Run:  python unreachable.py  ->  unreachable.json (+ a summary)
"""
from __future__ import annotations

import collections
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent


import re

# Names that denote a quantity a simulation can reference.  Deliberately
# generous: over-calling something reachable keeps it on the work list, which
# is the safe direction.  Under-calling it retires it silently.
SIMULATABLE = re.compile(
    r"variance|freq|heterozyg|fst|drift|ld|linkage|recomb|admix|migration|"
    r"mutation|selection|coalesc|ibd|haplotype|genotype|allele|r2|rsq|auc|"
    r"brier|loss|risk|power|prevalence|sensitivity|specificity|shrink|mse|"
    r"correlation|heritab|polygenic|effect|decay|equilib|expected|mean|"
    r"probability|proportion|fraction|entropy|information|sample|screen",
    re.I)


def _simulatable(d):
    return bool(d) and bool(SIMULATABLE.search(d.get("name", "")))


def load(n):
    p = HERE / n
    return json.loads(p.read_text()) if p.exists() else {}


def main(argv):
    cov = load("coverage.json")
    defs = {f"{d['module']}.{d['name']}": d
            for d in json.loads((HERE / "defs.json").read_text())}
    thm_res = load("results_theorems.json")
    inv = load("results_invariants.json")
    rng = load("results_ranges.json")
    sim = load("results_simulation.json")

    # which definitions any theorem's CONCLUSION mentions at all
    constrained = set(thm_res.get("by_definition", {}))
    mentioned_anywhere = set()
    for t in thm_res.get("theorems", {}).values():
        for m in t.get("mentions", []) or []:
            mentioned_anywhere.add(m)

    rows = {}
    for k, v in cov.items():
        if v["covered"]:
            continue
        d = defs.get(k, {})
        stage = v["uncovered_reason"]["stage"]
        if stage == "transpile":
            detail = v["uncovered_reason"]["detail"] or ""
            if "non-scalar signature" in detail:
                kind, why = "corpus", (
                    "the signature is not scalar (" + detail.split("(")[-1]
                    .rstrip(")") + "); this tier evaluates real-valued "
                    "functions of real arguments and cannot form a value here")
            elif "ambiguous call" in detail:
                kind, why = "checker", (
                    "the body calls a bare name that several definitions in "
                    "other files share; resolution refuses rather than "
                    "guessing, so the body is not evaluated")
            elif "depends on an uncompiled" in detail:
                kind, why = "checker", (
                    "the body calls a definition this tier could not compile")
            else:
                kind, why = "checker", (
                    f"outside the arithmetic fragment: {detail}")
            rows[k] = dict(kind=kind, reason=why, stage=stage,
                           module=d.get("module"), line=d.get("line"))
            continue

        # transpiled but undiscriminated: say exactly what is missing
        bits = []
        r = rng.get(k, {})
        if r.get("verdict") == "no-range":
            bits.append("its name and docstring commit it to no range")
        i = inv.get(k, {})
        kinds_held = {c["kind"] for c in i.get("checks", []) if c["holds"]}
        if kinds_held <= {"continuity", "totality"}:
            bits.append("the only invariants that apply are continuity and the "
                        "totality scan, and no mutation of the body breaks "
                        "either")
        if k not in mentioned_anywhere:
            bits.append("no theorem's conclusion mentions it, so the corpus "
                        "states no property of it to check")
        elif k not in constrained:
            bits.append("theorems mention it but none of their conclusions "
                        "could be evaluated (outside the arithmetic fragment, "
                        "or their hypotheses admitted no sampled point)")
        if k not in sim:
            bits.append("no simulation spec is written for it")
        # "no simulation spec is written for it" is a limit of THIS TOOL, not
        # a property of the corpus.  Classifying it as corpus-unreachable
        # would retire work I am supposed to do as though it were impossible.
        # A definition is corpus-unreachable only when nothing states a
        # property of it AND its name does not denote a quantity a simulation
        # could reference.
        checkerish = (
            (k in mentioned_anywhere and k not in constrained)
            or _simulatable(d))
        rows[k] = dict(kind="checker" if checkerish else "corpus",
                       reason="; ".join(bits) or "unclassified",
                       stage=stage, module=d.get("module"), line=d.get("line"),
                       params=[p[0] for p in d.get("params", [])],
                       body=(d.get("body") or "")[:120])

    (HERE / "unreachable.json").write_text(json.dumps(rows, indent=1))
    by_kind = collections.Counter(v["kind"] for v in rows.values())
    print(f"{len(rows)} definitions not covered, all accounted for:")
    for kk, n in by_kind.most_common():
        print(f"  {n:5d}  {kk}")
    print()
    nt = {k: v for k, v in rows.items() if v["stage"] != "transpile"}
    print(f"of the {len(nt)} that ARE transpilable:")
    c2 = collections.Counter(v["kind"] for v in nt.values())
    for kk, n in c2.most_common():
        print(f"  {n:5d}  {kk}")
    print()
    print("transpilable + checker-limited -- the live work list:")
    for k, v in sorted(nt.items()):
        if v["kind"] == "checker":
            print(f"  {k:58s} ({', '.join(v['params'])})")
    print()
    print("transpilable + corpus-unreachable -- nothing states a property and "
          "the name denotes no simulatable quantity:")
    for k, v in sorted(nt.items()):
        if v["kind"] == "corpus":
            print(f"  {k:58s} = {v['body'][:60]}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
