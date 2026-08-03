"""CHECK 8 -- why no theorem noticed: four causes, only one of them a defect.

CHECK 7 leaves a population of definitions that HAVE theorems -- one has
thirty-five -- where no theorem rejects any perturbation of the body.  That is
tempting to report as "surrounded by machine-checked statements that constrain
nothing", and for some of them it is exactly that.  For others it is my own
checker failing and wearing a corpus finding's clothes, which is the same
mislabel that produced the reason-string bug one level down.

So this separates the causes before anything is called a defect:

  CONVERTER_LIMIT   no mentioning theorem converted to sympy at all, so "no
                    theorem noticed" means "I could not evaluate any of them".
                    A checker limitation. Not reportable.
  BOTH_SIDES        the definition occurs on both sides of every theorem that
                    did convert, so any substitution cancels by construction.
                    The theorems may say a great deal; none of it is disturbable
                    by changing this body. Structural, not a defect in itself,
                    but it is the effectiveSubgroupSize shape and it means the
                    definition is unconstrained BY THESE THEOREMS.
  UNPERTURBED       converted, appears on one side, and still nothing fired.
                    Either genuinely vacuous or a blind spot in the mutation
                    set. This is the only bucket worth reading by hand, and the
                    two are not separable statically -- a richer mutation set is
                    the honest response, not a claim of vacuity.
  NO_THEOREM        nothing mentions it. Merely uncovered.

The reportable number is the third bucket, and it will be much smaller than the
population. Reporting the population would be the larger interesting number
rather than the smaller true one.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

import leansym as L
import shared
from paths import ARTIFACTS as ART, HERE


def sides_of(stmt: str):
    """Split a proposition at its top-level '=' into the two sides."""
    depth = 0
    for i, ch in enumerate(stmt):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == "=" and depth == 0:
            if i and stmt[i - 1] in "<>≤≥!≠" or (i + 1 < len(stmt) and stmt[i + 1] == "="):
                continue
            return stmt[:i], stmt[i + 1:]
    return stmt, ""


def occurs(name: str, text: str) -> bool:
    return re.search(rf"(?<![A-Za-z0-9_.]){re.escape(name)}(?![A-Za-z0-9_])", text) is not None


def run():
    c7 = json.loads((ART / "results_check7.json").read_text())
    decls = json.loads((ART / "decls.json").read_text())
    table = shared.build_table()
    thms = [t for t in decls if t["kind"] == "theorem" and t["body"]]

    mentions = {}
    for t in thms:
        for n in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", t["body"])):
            mentions.setdefault(n.split(".")[-1], []).append(t)

    targets = [r for r in c7 if r["status"] in ("still_unreachable",
                                                "no_theorem_mentions_it")]
    out = []
    for r in targets:
        short = r["short"]
        cands = mentions.get(short, [])
        rec = {"fqn": r["fqn"], "short": short,
               "theorems_mentioning": len(cands),
               "mutations_evaluated": r.get("mutations_evaluated", 0),
               "convert_errors": r.get("convert_errors", [])}
        if not cands:
            rec["cause"] = "NO_THEOREM"
            out.append(rec)
            continue
        if rec["mutations_evaluated"] == 0:
            rec["cause"] = "CONVERTER_LIMIT"
            out.append(rec)
            continue

        # of the theorems that converted, does the name sit on both sides?
        conv = L.Converter(table)
        both, oneside, unconverted = 0, 0, 0
        examples = []
        for t in cands[:12]:
            try:
                conv.convert(t["body"])
            except Exception:
                unconverted += 1
                continue
            lhs, rhs = sides_of(t["body"])
            if occurs(short, lhs) and occurs(short, rhs):
                both += 1
            else:
                oneside += 1
                if len(examples) < 3:
                    examples.append(t["name"])
        rec.update({"converted_both_sides": both,
                    "converted_one_side": oneside,
                    "did_not_convert": unconverted,
                    "one_sided_examples": examples})
        if oneside == 0 and both > 0:
            rec["cause"] = "BOTH_SIDES"
        elif oneside > 0:
            rec["cause"] = "UNPERTURBED"
        else:
            rec["cause"] = "CONVERTER_LIMIT"
        out.append(rec)
    return out


def main():
    res = run()
    (ART / "results_check8.json").write_text(json.dumps(res, indent=1, ensure_ascii=False))
    c = Counter(r["cause"] for r in res)
    print(f"CHECK 8: triage of {len(res)} definitions no theorem constrains")
    for k in ("UNPERTURBED", "BOTH_SIDES", "CONVERTER_LIMIT", "NO_THEOREM"):
        if c.get(k):
            print(f"  {k:18s} {c[k]:5d}")
    print()
    print("REPORTABLE -- converted, one-sided, and still nothing fired.")
    print("Read these by hand; a mutation-set blind spot is not distinguishable")
    print("from genuine vacuity without looking.")
    for r in sorted((r for r in res if r["cause"] == "UNPERTURBED"),
                    key=lambda r: -r["theorems_mentioning"]):
        print(f'  {r["fqn"]}  ({r["theorems_mentioning"]} theorems, '
              f'{r["converted_one_side"]} one-sided)')
        for e in r["one_sided_examples"]:
            print(f'      {e}')
    print()
    print("BOTH_SIDES -- every converting theorem has the definition on both")
    print("sides, so no substitution can disturb it (the effectiveSubgroupSize shape):")
    for r in sorted((r for r in res if r["cause"] == "BOTH_SIDES"),
                    key=lambda r: -r["theorems_mentioning"])[:20]:
        print(f'  {r["fqn"]}  ({r["theorems_mentioning"]} theorems)')


if __name__ == "__main__":
    main()
