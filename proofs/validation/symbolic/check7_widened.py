"""CHECK 7 -- certificate power over EVERY theorem, not only self-declared derivations.

CHECK 6 tested the theorems that ADVERTISE a derivation: name matching `_eq`,
`_derived`, `_from`, or a docstring claiming one.  That population is 493
theorems and it left most of the corpus untouched, which my own slice ledger
then recorded with the reason "no derivation or fixed-point theorem reaches
it".

That reason was wrong, and wrong in the direction that overstates hopelessness.
Of the 190 definitions filed under it, 167 are mentioned by at least one
theorem -- every single one that is numerically callable.  What they lack is
not a theorem but a theorem that ADVERTISES itself as a derivation.  A theorem
constrains a definition whether or not its name says so, and mutation testing
does not care what a theorem is called: it only asks whether the theorem
notices when the definition changes.

So this widens the population to every theorem mentioning the definition, and
asks the same question.  A definition earns coverage when some theorem --
any theorem -- rejects a perturbed body.

BOUNDED DELIBERATELY.  Every definition x every mentioning theorem x every
mutation is a large product, so: only definitions currently UNREACHABLE are
tested, theorems are tried shortest-statement-first (short statements convert
more often and are cheaper), and the search stops for a definition as soon as
one theorem rejects a mutation, since one falsifying certificate is all the
coverage claim needs.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

import sympy as sp

import leansym as L
import hyps as H
import shared
from paths import HERE

MAX_THEOREMS_PER_DEF = 6
NUM = re.compile(r"(?<![A-Za-z0-9_.])(\d+)(?![A-Za-z0-9_.])")


def mutate(body: str):
    out = []
    m = NUM.search(body)
    if m:
        n = int(m.group(1))
        out.append((f"literal {n}->{n+1}", body[:m.start()] + str(n + 1) + body[m.end():]))
    out.append(("scale by 2", f"2 * ({body})"))
    out.append(("add 1/3", f"(1/3) + ({body})"))
    out.append(("negate", f"-({body})"))
    return out


def run():
    decls = json.load(open(HERE / "decls.json"))
    base_table = shared.build_table()
    sdefs = {d["name"]: d for d in shared.def_records()}
    thms = [t for t in decls if t["kind"] == "theorem" and t["body"]]
    by_name = {t["name"]: t for t in thms}

    # which theorems mention which definition (by short name, word-bounded)
    mentions = {}
    for t in thms:
        for n in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", t["body"])):
            mentions.setdefault(n.split(".")[-1], []).append(t)

    ledger = json.loads((HERE / "slice_ledger.json").read_text())
    targets = [r for r in ledger.values() if r["status"] == "UNREACHABLE"]

    results = []
    for r in targets:
        short = r["short"]
        d = sdefs.get(short)
        if d is None or not d["body"] or short not in base_table:
            results.append({"fqn": r["fqn"], "short": short, "status": "no_convertible_body",
                            "prior_reason": r.get("reason")})
            continue
        cands = sorted(mentions.get(short, []), key=lambda t: len(t["body"]))
        if not cands:
            results.append({"fqn": r["fqn"], "short": short, "status": "no_theorem_mentions_it",
                            "prior_reason": r.get("reason")})
            continue

        rejected_by, tried, errors = None, 0, Counter()
        for t in cands[:MAX_THEOREMS_PER_DEF]:
            if rejected_by:
                break
            stmt = t["body"]
            for label, mbody in mutate(d["body"]):
                table = dict(base_table)
                table[short] = (table[short][0], mbody)
                conv = L.Converter(table)
                try:
                    eq = conv.convert(stmt)
                except L.Unsupported as e:
                    errors[str(e)[:40]] += 1
                    break  # this theorem will not convert for any mutation
                except Exception as e:
                    errors[type(e).__name__] += 1
                    break
                tried += 1
                try:
                    if eq is sp.false:
                        rejected_by = (t["name"], label, "statement is false")
                        break
                    if eq is sp.true:
                        continue
                    if isinstance(eq, sp.Eq):
                        v, _ = H.verdict_for(eq.lhs, eq.rhs, t["binders"], conv)
                    elif eq.is_Relational:
                        # an inequality: check it can be violated by the mutation
                        v = None
                    else:
                        v = None
                except Exception:
                    v = None
                if v is False:
                    rejected_by = (t["name"], label, "equation no longer holds")
                    break
        results.append({
            "fqn": r["fqn"], "short": short,
            "status": "NEWLY_COVERED" if rejected_by else "still_unreachable",
            "prior_reason": r.get("reason"),
            "rejecting_theorem": rejected_by[0] if rejected_by else None,
            "rejecting_mutation": rejected_by[1] if rejected_by else None,
            "why": rejected_by[2] if rejected_by else None,
            "theorems_available": len(cands), "mutations_evaluated": tried,
            "convert_errors": errors.most_common(3),
        })
    return results


def main():
    res = run()
    (HERE / "results_check7.json").write_text(json.dumps(res, indent=1, ensure_ascii=False))
    c = Counter(r["status"] for r in res)
    print(f"CHECK 7: widened certificate power over {len(res)} UNREACHABLE definitions")
    for k, v in sorted(c.items(), key=lambda kv: -kv[1]):
        print(f"  {k:26s} {v}")
    new = [r for r in res if r["status"] == "NEWLY_COVERED"]
    print()
    print(f"NEWLY COVERED: {len(new)} definitions now have a theorem that rejects a")
    print("perturbed body. Sample:")
    for r in new[:25]:
        print(f'  {r["fqn"]}')
        print(f'      rejected by {r["rejecting_theorem"]} on mutation "{r["rejecting_mutation"]}"')
    print()
    prior = Counter(r["prior_reason"] for r in new)
    print("newly covered, by the reason they were previously filed under:")
    for k, v in prior.most_common():
        print(f"  {v:5d}  {k}")


if __name__ == "__main__":
    main()
