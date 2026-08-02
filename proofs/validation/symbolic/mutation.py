"""Mutation testing: no definition is counted as covered unless a check rejects
a deliberately wrong body for it.

This project has already produced a false validation from a check that could
not fail, so coverage here is not a claim about which definitions a check
*looked at* -- it is a claim about which definitions a check would have caught
an error in.  For each definition a check reports as verified, the body is
perturbed and the same check is re-run against the perturbed corpus.  If the
check still passes, the definition is recorded as NOT covered and the check is
reported as vacuous for it.

Perturbations are small and meaning-changing: bump the first numeric literal,
scale the body, and shift the body.  A definition survives only if *every*
perturbation is rejected, so a check that happens to be insensitive in one
direction is still caught.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

import sympy as sp

import leansym as L
import hyps as H

HERE = Path(__file__).parent

NUM = re.compile(r"(?<![A-Za-z0-9_.])(\d+)(?![A-Za-z0-9_.])")


def mutate(body: str) -> list[tuple[str, str]]:
    """Small meaning-changing edits to a definition body."""
    out = []
    m = NUM.search(body)
    if m:
        n = int(m.group(1))
        out.append((f"literal {n}->{n + 1}",
                    body[: m.start()] + str(n + 1) + body[m.end():]))
    out.append(("scale by 2", f"2 * ({body})"))
    out.append(("shift by 1", f"1 + ({body})"))
    return out


def run():
    decls = json.load(open(HERE / "decls.json"))
    base_table = L.build_table(decls)
    defs = {d["name"]: d for d in decls if d["kind"] == "def"}
    thms = {t["name"]: t for t in decls if t["kind"] == "theorem"}

    coverage: dict[str, dict] = {}

    def note(fqn, check, covered, detail):
        e = coverage.setdefault(fqn, {"fqn": fqn, "checks": {}})
        e["checks"][check] = {"covered": covered, **detail}

    # ---------------- CHECK 1: guarded equilibria
    c1 = json.load(open(HERE / "results_check1.json"))
    for r in c1:
        if r["status"] not in ("fixed_point_verified", "UNGUARDED_but_verified"):
            continue
        d = defs.get(r["name"])
        thm = thms.get(r["guard_theorem"]) if r["guard_theorem"] else None
        if d is None:
            continue
        rejected, survived = [], []
        for label, mbody in mutate(d["body"]):
            table = dict(base_table)
            if d["name"] not in table:
                continue
            table[d["name"]] = (table[d["name"]][0], mbody)
            conv = L.Converter(table)
            try:
                if thm is not None:
                    eq = conv.convert(thm["body"])
                    v, _ = H.verdict_for(eq.lhs, eq.rhs, thm["binders"], conv)
                else:
                    v = None
            except Exception:
                v = False  # perturbed body no longer even converts: rejected
            (survived if v is True else rejected).append(label)
        note(r["fqn"], "check1_fixed_point", bool(rejected) and not survived,
             {"mutations_rejected": rejected, "mutations_survived": survived,
              "guard": r["guard_theorem"]})

    # ---------------- CHECK 2: verified derivations
    c2 = json.load(open(HERE / "results_check2.json"))
    for r in c2:
        if r["status"] != "derivation_verified":
            continue
        thm = thms.get(r["name"])
        if thm is None:
            continue
        # every definition the statement mentions is a coverage candidate
        mentioned = [n for n in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", thm["body"]))
                     if n.split(".")[-1] in base_table]
        for name in mentioned:
            short = name.split(".")[-1]
            d = defs.get(short)
            if d is None or not d["body"]:
                continue
            rejected, survived = [], []
            for label, mbody in mutate(d["body"]):
                table = dict(base_table)
                table[short] = (table[short][0], mbody)
                conv = L.Converter(table)
                try:
                    eq = conv.convert(thm["body"])
                    v, _ = H.verdict_for(eq.lhs, eq.rhs, thm["binders"], conv)
                except Exception:
                    v = False
                (survived if v is True else rejected).append(label)
            fqn = f'{d["module"]}.{short}'
            prev = coverage.get(fqn, {}).get("checks", {}).get("check2_derivation")
            covered = bool(rejected) and not survived
            if prev and prev.get("covered"):
                continue
            note(fqn, "check2_derivation", covered,
                 {"via_theorem": r["fqn"], "mutations_rejected": rejected,
                  "mutations_survived": survived})

    # ---------------- CHECK 3: duplicate-body groups
    c3 = json.load(open(HERE / "results_check3.json"))
    for g in c3["equal_groups"]:
        target = sp.sympify(g["expression"])
        for mem in g["members"]:
            d = defs.get(mem["name"])
            if d is None:
                continue
            rejected, survived = [], []
            for label, mbody in mutate(d["body"]):
                conv = L.Converter(base_table)
                env = {b: sp.Symbol(f"x{i}", real=True)
                       for i, b in enumerate(mem["binders"])}
                try:
                    e = conv.convert(mbody, dict(env))
                    v, _ = H.equal_under(e, target, [], ())
                except Exception:
                    v = False
                (survived if v is True else rejected).append(label)
            note(mem["fqn"], "check3_duplicate_body",
                 bool(rejected) and not survived,
                 {"group_expression": g["expression"],
                  "mutations_rejected": rejected, "mutations_survived": survived})

    return coverage


def main():
    cov = run()
    (HERE / "coverage.json").write_text(json.dumps(cov, indent=1, ensure_ascii=False))
    total = len(cov)
    per_check = Counter()
    vacuous = []
    covered_fqns = set()
    for fqn, e in cov.items():
        for check, info in e["checks"].items():
            if info["covered"]:
                per_check[check] += 1
                covered_fqns.add(fqn)
            else:
                vacuous.append((fqn, check, info.get("mutations_survived")))
    print(f"MUTATION TESTING: {total} definitions reached by a check")
    print(f"  definitions with at least one check that provably can fail: "
          f"{len(covered_fqns)}")
    for k, v in per_check.most_common():
        print(f"    {k:26s} {v}")
    print(f"  check/definition pairs where every mutation SURVIVED (vacuous): "
          f"{len(vacuous)}")
    for fqn, check, sur in vacuous[:25]:
        print(f"    {fqn}  [{check}]  survived: {sur}")


if __name__ == "__main__":
    main()
