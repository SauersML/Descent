"""CHECK 2 -- theorems that claim a definition is derived from something.

Targets theorems whose *name* claims a derivation (`_eq`, `_derived`,
`_from`, `derivation_matches`) or whose docstring asserts one ("derived from
first principles", "not stipulated", "not asserted").  Two things are tested,
and the second is the one with teeth:

  AGREEMENT   both sides of the statement are converted to sympy with every
              definition inlined, and compared.  Lean has proved these, so a
              disagreement means the checker is wrong -- it is a self-test.
              It is also the check that catches a definition whose body and
              whose derivation theorem have drifted apart, because the
              *definition* is compared against what the theorem concludes, not
              just the theorem against itself.

  CONTENT     every definition is replaced by an uninterpreted function symbol
              and the two sides are compared again.  If they are *still* equal,
              the theorem holds for any bodies whatsoever: it is pure algebra
              and says nothing about the definitions it names.  This is the
              precise form of "a derivation theorem whose proof is `by ring` on
              an identity connecting nothing".

  MENTION     a theorem named `foo_derived` that never mentions `foo`.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

import sympy as sp

import leansym as L
import shared
import hyps as H

HERE = Path(__file__).parent

NAME_CLAIM = re.compile(r"(_eq$|_eq_|_derived|_derivation|_from_|_from$|"
                        r"derivation_matches|_isDerived|_closedForm|_formula)")
DOC_CLAIM = re.compile(
    r"(derived from|first principles|not stipulated|not asserted|"
    r"derive[sd]? the|is the formal derivation|rather than asserted|"
    r"impossible to stipulate)", re.I)
RING_PROOF = re.compile(r"^\s*by\s+(ring|ring_nf|norm_num|simp|rfl|field_simp;?\s*ring|"
                        r"unfold[^\n]*\n\s*(ring|norm_num|field_simp;?\s*ring))\s*$")


def base_name(thm_name: str) -> str | None:
    n = thm_name.split(".")[-1]
    for suf in ("_derivation_matches", "_derived", "_derivation", "_closedForm",
                "_formula", "_eq"):
        if n.endswith(suf):
            return n[: -len(suf)]
    m = re.match(r"(.+?)_from_", n)
    if m:
        return m.group(1)
    return None


def run():
    decls = json.load(open(HERE / "decls.json"))
    table = shared.build_table()
    inline = L.Converter(table)
    opaque = L.Converter(table, opaque_defs=True)
    defnames = {d["name"] for d in decls if d["kind"] == "def"}

    targets = []
    for t in decls:
        if t["kind"] != "theorem":
            continue
        by_name = bool(NAME_CLAIM.search(t["name"].split(".")[-1]))
        by_doc = bool(DOC_CLAIM.search(t["docstring"] or ""))
        if by_name or by_doc:
            targets.append((t, by_name, by_doc))

    results = []
    for t, by_name, by_doc in targets:
        rec = {
            "check": "check2_derivation",
            "fqn": f'{t["module"]}.{t["name"]}',
            "name": t["name"], "module": t["module"],
            "file": t["file"], "line": t["line"],
            "claim_source": ("name" if by_name else "") + ("+doc" if by_doc else ""),
            "statement": " ".join(t["body"].split())[:400],
            "status": None, "detail": {},
        }
        # --- MENTION: does a theorem named for a definition mention it?
        b = base_name(t["name"])
        if b and b in defnames:
            rec["detail"]["names_definition"] = b
            mentioned = re.search(rf"(?<![A-Za-z0-9_]){re.escape(b)}(?![A-Za-z0-9_])",
                                 t["body"]) is not None
            rec["detail"]["mentions_definition"] = mentioned
            if not mentioned:
                rec["detail"]["MENTION_GAP"] = (
                    f"theorem is named for `{b}` but its statement never mentions it")

        prop = t["body"].strip()
        if "=" not in prop:
            rec["status"] = "not_an_equation"
            results.append(rec)
            continue

        # --- AGREEMENT
        try:
            eq = inline.convert(prop)
        except L.Unsupported as e:
            rec["status"] = "opaque"
            rec["detail"]["reason"] = str(e)
            results.append(rec)
            continue
        if not isinstance(eq, sp.Eq):
            rec["status"] = "not_an_equation"
            results.append(rec)
            continue
        rec["detail"]["lhs"] = sp.sstr(eq.lhs)
        rec["detail"]["rhs"] = sp.sstr(eq.rhs)
        verdict, info = H.verdict_for(eq.lhs, eq.rhs, t["binders"], inline)
        rec["detail"]["hypotheses"] = info.get("hypotheses")
        rec["detail"]["unparsed_hypotheses"] = info.get("unparsed_hypotheses")
        rec["detail"]["method"] = info.get("method")
        if verdict is False:
            rec["status"] = "DERIVATION_DISAGREES"
            rec["detail"]["witness"] = info.get("witness")
            rec["detail"]["lhs_value"] = info.get("lhs_value")
            rec["detail"]["rhs_value"] = info.get("rhs_value")
            results.append(rec)
            continue
        if verdict is None:
            rec["status"] = "inconclusive"
            results.append(rec)
            continue

        # --- CONTENT: are the sides equal with definitions uninterpreted?
        try:
            oeq = opaque.convert(prop)
            if isinstance(oeq, sp.Eq):
                ov, _oinfo = H.equal_under(oeq.lhs, oeq.rhs, [], ())
                rec["detail"]["opaque_lhs"] = sp.sstr(oeq.lhs)
                rec["detail"]["opaque_rhs"] = sp.sstr(oeq.rhs)
                # a statement mentioning no definition at all is also contentless
                uses_defs = bool(oeq.atoms(sp.Function))
                rec["detail"]["mentions_any_definition"] = uses_defs
                if ov is True:
                    rec["status"] = ("VACUOUS_DERIVATION" if uses_defs
                                     else "VACUOUS_DERIVATION_NO_DEFS")
                    results.append(rec)
                    continue
        except L.Unsupported as e:
            rec["detail"]["opaque_reason"] = str(e)

        rec["status"] = "derivation_verified"
        results.append(rec)
    return results


def main():
    res = run()
    (HERE / "results_check2.json").write_text(json.dumps(res, indent=1, ensure_ascii=False))
    c = Counter(r["status"] for r in res)
    print(f"CHECK 2: {len(res)} derivation-claiming theorems")
    for k, v in sorted(c.items(), key=lambda kv: -kv[1]):
        print(f"  {k:26s} {v}")
    print()
    for tag in ("DERIVATION_DISAGREES", "VACUOUS_DERIVATION", "VACUOUS_DERIVATION_NO_DEFS"):
        hits = [r for r in res if r["status"] == tag]
        if not hits:
            continue
        print(f"=== {tag} ({len(hits)}) ===")
        for r in hits:
            print(f'  {r["fqn"]}  ({r["file"].split("/")[-1]}:{r["line"]})')
            print(f'     statement : {r["statement"]}')
            if tag == "DERIVATION_DISAGREES":
                print(f'     lhs       : {r["detail"].get("lhs")}')
                print(f'     rhs       : {r["detail"].get("rhs")}')
                print(f'     hypotheses: {r["detail"].get("hypotheses")}')
                print(f'     witness   : {r["detail"].get("witness")}')
                print(f'     values    : lhs={r["detail"].get("lhs_value")}  rhs={r["detail"].get("rhs_value")}')
            else:
                print(f'     opaque    : {r["detail"].get("opaque_lhs")}'
                      f'  ==  {r["detail"].get("opaque_rhs")}')
        print()
    gaps = [r for r in res if r["detail"].get("MENTION_GAP")]
    print(f"=== theorems named for a definition they never mention ({len(gaps)}) ===")
    for r in gaps[:40]:
        print(f'  {r["fqn"]}:{r["line"]}  -> {r["detail"]["MENTION_GAP"]}')


if __name__ == "__main__":
    main()
